// SPDX-License-Identifier: MIT
//
// A conservative structured TJS2 bytecode parser for the common TJS2/DATA/OBJS layout.
//
// Important:
//  - This parser targets a widely described layout used by TJS2 compiled script images.
//  - Real-world Kirikiri builds may add flags/sections or encrypt/compress some parts.
//  - If parsing fails on your sample, you may need to add detection and alternative layouts.
//
// The resulting object graph provides:
//  - top_level (top-level context)
//  - objects with parent_index (subroutines recursively under a parent)
//  - DATA area pools (bytes/shorts/ints/longs/doubles/strings/octets)
//  - each object's raw code array (i16 words)

use anyhow::{bail, Context, Result};
use std::convert::TryInto;

use crate::reader::Reader;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ChunkSizeMode {
    /// `size` is the payload length following the size field.
    PayloadLen,
    /// `size` is the number of bytes after the FOURCC, including the 4-byte size field itself.
    AfterFourccIncludingSizeField,
}

fn align_up_u64(v: u64, a: u64) -> u64 {
    if a == 0 {
        return v;
    }
    let rem = v % a;
    if rem == 0 { v } else { v + (a - rem) }
}


#[derive(Debug)]
pub struct Tjs2Bytecode {
    pub version: [u8; 4],
    pub file_size: u32,

    pub data: DataArea,
    pub top_level: Option<usize>,
    pub objects: Vec<Object>,

    pub children: Vec<Vec<usize>>,
}

/// A best-effort view of a constant-pool entry.
///
/// In TJS2 compiled images, each Object has a small CONST table that points
/// into the shared DATA pools (bytes/shorts/ints/longs/doubles/strings/octets).
///
/// The exact `ty` values can vary between implementations; we implement the
/// common layout and keep an Unknown fallback.
#[derive(Debug, Clone)]
pub enum ConstValue {
    Void,
    Byte(u8),
    Short(i16),
    Int(i32),
    Long(i64),
    Double(f64),
    String(String),
    Octet(Vec<u8>),
    Unknown { ty: u16, ix: u16 },
}

impl Tjs2Bytecode {
    /// Resolve an object-local constant pool index (`*idx`) into a concrete value.
    pub fn resolve_const(&self, obj_index: usize, const_index: u16) -> Option<ConstValue> {
        let obj = self.objects.get(obj_index)?;
        let (ty, ix) = *obj.consts.get(const_index as usize)?;

        // Common mapping used by multiple public format descriptions:
        //   0: bytes
        //   1: shorts
        //   2: ints
        //   3: longs
        //   4: doubles
        //   5: strings
        //   6: octets
        //   7: void
        // Unknown/engine-specific types fall back to ConstValue::Unknown.
        match ty {
            0 => self.data.bytes.get(ix as usize).copied().map(ConstValue::Byte),
            1 => self.data.shorts.get(ix as usize).copied().map(ConstValue::Short),
            2 => self.data.ints.get(ix as usize).copied().map(ConstValue::Int),
            3 => self.data.longs.get(ix as usize).copied().map(ConstValue::Long),
            4 => self.data.doubles.get(ix as usize).copied().map(ConstValue::Double),
            5 => self.data.strings.get(ix as usize).cloned().map(ConstValue::String),
            6 => self.data.octets.get(ix as usize).cloned().map(ConstValue::Octet),
            7 => Some(ConstValue::Void),
            _ => Some(ConstValue::Unknown { ty, ix }),
        }
    }
}

#[derive(Debug, Default)]
pub struct DataArea {
    pub bytes: Vec<u8>,
    pub shorts: Vec<i16>,
    pub ints: Vec<i32>,
    pub longs: Vec<i64>,
    pub doubles: Vec<f64>,
    pub strings: Vec<String>,
    pub octets: Vec<Vec<u8>>,
}

#[derive(Debug)]
pub struct Object {
    pub index: usize,
    pub size_bytes: u32,

    pub parent_index: i32,
    pub name_string_index: i32,
    pub context_type: i32,

    pub max_variable_count: i32,
    pub variable_reserve_count: i32,
    pub max_frame_count: i32,

    pub func_decl_arg_count: i32,
    pub func_decl_unnamed_arg_array_base: i32,
    pub func_decl_collapse_base: i32,

    pub prop_setter_obj_index: i32,
    pub prop_getter_obj_index: i32,
    pub super_class_getter_obj_index: i32,

    pub unknown_14: i32,

    pub src_code_pos: Vec<i32>,
    pub src_source_pos: Vec<i32>,

    pub code: Vec<i16>,
    pub consts: Vec<(u16, u16)>,
    pub super_getter_ptrs: Vec<i32>,
    pub members: Vec<(i32, i32)>,
}

fn parse_data_area_sequential(r: &mut Reader) -> Result<DataArea> {
    // Sequential layout:
    //   u32 count; payload; padding-to-4
    // Pools order:
    //   bytes, shorts, ints, longs, doubles, strings(utf16le), octets.
    let bytes = read_vec_u8_aligned(r, 4)?;
    let shorts = read_vec_i16_aligned(r, 4)?;
    let ints = read_vec_i32_aligned(r, 4)?;
    let longs = read_vec_i64_aligned(r, 4)?;
    let doubles = read_vec_f64_aligned(r, 4)?;
    let strings = read_vec_string_utf16le_aligned(r, 4)?;
    let octets = read_vec_octet_aligned(r, 4)?;

    Ok(DataArea { bytes, shorts, ints, longs, doubles, strings, octets })
}

fn parse_data_area_detect(buf: &[u8]) -> Result<DataArea> {
    // Some builds place a 7-entry offset table at the start of the DATA payload.
    // Others store pools sequentially.
    if let Some(offs) = detect_data_area_offsets(buf) {
        return parse_data_area_by_offsets(buf, offs).context("parse DATA via offset table");
    }
    let mut r = Reader::new(buf);
    parse_data_area_sequential(&mut r).context("parse DATA sequential layout")
}

fn align_up_usize(v: usize, a: usize) -> usize {
    if a == 0 { return v; }
    let rem = v % a;
    if rem == 0 { v } else { v + (a - rem) }
}

/// Detect a 7-entry little-endian offset table at the beginning of the DATA payload.
///
/// Assumed pool order:
///   bytes, shorts, ints, longs, doubles, strings, octets
///
/// We validate fixed-size pools against segment bounds to avoid false positives.
fn detect_data_area_offsets(buf: &[u8]) -> Option<[u32; 7]> {
    if buf.len() < 28 {
        return None;
    }

    let mut r = Reader::new(buf);
    let mut offs = [0u32; 7];
    for i in 0..7 {
        offs[i] = r.read_u32().ok()?;
    }

    let len = buf.len() as u32;

    // Basic plausibility: within range, 4-byte aligned, monotonic.
    if offs.iter().all(|&o| o == 0) {
        return None;
    }
    if offs[0] < 28 {
        return None;
    }
    if offs.iter().any(|&o| o >= len) {
        return None;
    }
    if offs.iter().any(|&o| (o & 3) != 0) {
        return None;
    }
    for i in 0..6 {
        if offs[i] > offs[i + 1] {
            return None;
        }
    }

    // Build bounds array: [off0, off1, ..., off6, end]
    let mut bounds = [0usize; 8];
    for i in 0..7 {
        bounds[i] = offs[i] as usize;
    }
    bounds[7] = buf.len();

    for i in 0..7 {
        if bounds[i] > bounds[i + 1] {
            return None;
        }
    }

    // Validate fixed-size pools (bytes/shorts/ints/longs/doubles).
    // Each segment is expected to contain:
    //   u32 count + count*elem_size + padding-to-4
    let elem_sizes: [usize; 5] = [1, 2, 4, 8, 8];
    for (i, esz) in elem_sizes.iter().enumerate() {
        let off = bounds[i];
        let end = bounds[i + 1];

        // Allow a completely empty segment (off == end) to represent an empty pool.
        if end == off {
            continue;
        }
        if end < off + 4 {
            return None;
        }

        let cnt = u32::from_le_bytes(buf[off..off + 4].try_into().ok()?) as usize;
        let payload = 4usize.checked_add(cnt.checked_mul(*esz)?)?;
        let need = align_up_usize(payload, 4);

        if need > (end - off) {
            return None;
        }
    }

    Some(offs)
}

fn parse_data_area_by_offsets(buf: &[u8], offs: [u32; 7]) -> Result<DataArea> {
    let mut bounds = [0usize; 8];
    for i in 0..7 {
        bounds[i] = offs[i] as usize;
    }
    bounds[7] = buf.len();

    for i in 0..7 {
        if bounds[i] > bounds[i + 1] {
            bail!("DATA offset table not monotonic ({} > {})", bounds[i], bounds[i + 1]);
        }
    }

    let bytes = if bounds[0] == bounds[1] {
        Vec::new()
    } else {
        let mut r = Reader::new(&buf[bounds[0]..bounds[1]]);
        read_vec_u8_aligned(&mut r, 4)?
    };

    let shorts = if bounds[1] == bounds[2] {
        Vec::new()
    } else {
        let mut r = Reader::new(&buf[bounds[1]..bounds[2]]);
        read_vec_i16_aligned(&mut r, 4)?
    };

    let ints = if bounds[2] == bounds[3] {
        Vec::new()
    } else {
        let mut r = Reader::new(&buf[bounds[2]..bounds[3]]);
        read_vec_i32_aligned(&mut r, 4)?
    };

    let longs = if bounds[3] == bounds[4] {
        Vec::new()
    } else {
        let mut r = Reader::new(&buf[bounds[3]..bounds[4]]);
        read_vec_i64_aligned(&mut r, 4)?
    };

    let doubles = if bounds[4] == bounds[5] {
        Vec::new()
    } else {
        let mut r = Reader::new(&buf[bounds[4]..bounds[5]]);
        read_vec_f64_aligned(&mut r, 4)?
    };

    let strings = if bounds[5] == bounds[6] {
        Vec::new()
    } else {
        let mut r = Reader::new(&buf[bounds[5]..bounds[6]]);
        read_vec_string_utf16le_aligned(&mut r, 4)?
    };

    let octets = if bounds[6] == bounds[7] {
        Vec::new()
    } else {
        let mut r = Reader::new(&buf[bounds[6]..bounds[7]]);
        read_vec_octet_aligned(&mut r, 4)?
    };

    Ok(DataArea { bytes, shorts, ints, longs, doubles, strings, octets })
}

/// Compute the end position (absolute file offset) of the current chunk payload.
///
/// Different implementations interpret the size field differently. We try common variants
/// and pick the one that places `next_fourcc` at the computed boundary.
fn find_chunk_payload_end(
    file: &[u8],
    payload_start: u64,
    chunk_size: u32,
    next_fourcc: &[u8; 4],
) -> Option<u64> {
    let sz = chunk_size as i64;
    let candidates = [
        payload_start as i64 + (sz - 8), // size includes FourCC + size-field
        payload_start as i64 + (sz - 4), // size includes FourCC only
        payload_start as i64 + sz,       // size is payload size
    ];

    let file_len = file.len() as u64;
    for end_i64 in candidates {
        if end_i64 < payload_start as i64 {
            continue;
        }
        let end = end_i64 as u64;
        if end + 4 > file_len {
            continue;
        }
        if &file[end as usize..end as usize + 4] == next_fourcc {
            return Some(end);
        }
    }
    None
}

pub fn parse_tjs2_bytecode(buf: &[u8]) -> Result<Tjs2Bytecode> {
    let mut r = Reader::new(buf);

    r.expect_fourcc(b"TJS2")?;
    let version = r.read_fourcc()?;
    let file_size = r.read_u32()?;

    // r.expect_fourcc(b"DATA")?;
    // let _data_area_size = r.read_u32()?;
    // let data = parse_data_area(&mut r).context("parse DATA area")?;

    r.expect_fourcc(b"DATA")?;
    let data_area_size = r.read_u32()?;
    let data_payload_start = r.pos()?;

    // Compute the DATA payload boundary by validating where the next chunk tag (OBJS) lands.
    let data_payload_end = find_chunk_payload_end(buf, data_payload_start, data_area_size, b"OBJS")
        .context("locate end of DATA chunk")?;
    let data_payload = &buf[data_payload_start as usize..data_payload_end as usize];

    // Deterministic layout detection: sequential pools vs offset-table pools.
    let data = parse_data_area_detect(data_payload).context("parse DATA area")?;

    // Advance the main reader to the end of DATA so the next read begins at OBJS.
    r.seek(data_payload_end)?;


    r.expect_fourcc(b"OBJS")?;
    let _obj_area_size = r.read_u32()?;
    let top_level_index = r.read_i32()?;
    let obj_count = r.read_u32()? as usize;

    let top_level = if top_level_index < 0 {
        None
    } else {
        Some(top_level_index as usize)
    };

    let mut objects = Vec::with_capacity(obj_count);
    for idx in 0..obj_count {
        let obj = parse_object(&mut r, idx).with_context(|| format!("parse object {}", idx))?;
        objects.push(obj);
    }

    let mut children = vec![Vec::<usize>::new(); obj_count];
    for i in 0..obj_count {
        let p = objects[i].parent_index;
        if p >= 0 {
            let p = p as usize;
            if p < obj_count {
                children[p].push(i);
            }
        }
    }

    Ok(Tjs2Bytecode {
        version,
        file_size,
        data,
        top_level,
        objects,
        children,
    })
}


/// Read a chunk header and return the absolute [payload_start, payload_end) range.
///
/// Layout:
///   fourcc[4], size_after_fourcc[u32], payload[size_after_fourcc - 4]
///
/// Kirikiri's convention here is:
///   size_after_fourcc counts bytes after the fourcc and includes the 4-byte size field itself.
/// Therefore payload_len = size_after_fourcc - 4.
fn read_chunk_payload(
    r: &mut Reader,
    expected_fourcc: &[u8; 4],
    file_len: usize,
) -> Result<(u64, u64)> {
    r.expect_fourcc(expected_fourcc)?;
    let size_after_fourcc = r.read_u32()?;
    if size_after_fourcc < 4 {
        bail!(
            "chunk {:?} has invalid size {} (<4)",
            expected_fourcc,
            size_after_fourcc
        );
    }

    let payload_len = (size_after_fourcc - 4) as u64;
    let payload_start = r.pos()?;
    let payload_end = payload_start + payload_len;

    if payload_end > file_len as u64 {
        bail!(
            "chunk {:?} payload out of bounds: end {} > file_len {}",
            expected_fourcc,
            payload_end,
            file_len
        );
    }

    Ok((payload_start, payload_end))
}


fn parse_data_area(r: &mut Reader) -> Result<DataArea> {
    let bytes = read_vec_u8_aligned(r, 4)?;
    let shorts = read_vec_i16_aligned(r, 4)?;
    let ints = read_vec_i32_aligned(r, 4)?;
    let longs = read_vec_i64_aligned(r, 4)?;
    let doubles = read_vec_f64_aligned(r, 4)?;
    let strings = read_vec_string_utf16le_aligned(r, 4)?;
    let octets = read_vec_octet_aligned(r, 4)?;

    Ok(DataArea {
        bytes,
        shorts,
        ints,
        longs,
        doubles,
        strings,
        octets,
    })
}

fn parse_object(r: &mut Reader, index: usize) -> Result<Object> {
    r.expect_fourcc(b"TJS2")?;
    let size_bytes = r.read_u32()?;
    let start = r.pos()?;
    let end = start + size_bytes as u64;

    let parent_index = r.read_i32()?;
    let name_string_index = r.read_i32()?;
    let context_type = r.read_i32()?;

    let max_variable_count = r.read_i32()?;
    let variable_reserve_count = r.read_i32()?;
    let max_frame_count = r.read_i32()?;

    let func_decl_arg_count = r.read_i32()?;
    let func_decl_unnamed_arg_array_base = r.read_i32()?;
    let func_decl_collapse_base = r.read_i32()?;

    let prop_setter_obj_index = r.read_i32()?;
    let prop_getter_obj_index = r.read_i32()?;
    let super_class_getter_obj_index = r.read_i32()?;

    let unknown_14 = r.read_i32()?;

    let mut src_code_pos = Vec::new();
    let mut src_source_pos = Vec::new();
    if r.pos()? < end {
        let cnt = r.read_u32()? as usize;
        if cnt > 0 {
            src_code_pos = (0..cnt).map(|_| r.read_i32()).collect::<Result<Vec<_>>>()?;
            src_source_pos = (0..cnt).map(|_| r.read_i32()).collect::<Result<Vec<_>>>()?;
        }
    }

    let code = read_vec_i16_aligned(r, 4)?;

    let consts = {
        let cnt = r.read_u32()? as usize;
        let mut v = Vec::with_capacity(cnt);
        for _ in 0..cnt {
            let ty = r.read_u16()?;
            let ix = r.read_u16()?;
            v.push((ty, ix));
        }
        v
    };

    let super_getter_ptrs = read_vec_i32_aligned(r, 4)?;

    let members = {
        let cnt = r.read_u32()? as usize;
        let mut v = Vec::with_capacity(cnt);
        for _ in 0..cnt {
            let name_ix = r.read_i32()?;
            let obj_ix = r.read_i32()?;
            v.push((name_ix, obj_ix));
        }
        v
    };

    if r.pos()? > end {
        bail!("object {} over-read: pos {} > end {}", index, r.pos()?, end);
    }
    if r.pos()? < end {
        r.seek(end)?;
    }

    println!("Parsed object {}: size_bytes={}, code_words={}, consts={}", index, size_bytes, code.len(), consts.len());

    Ok(Object {
        index,
        size_bytes,
        parent_index,
        name_string_index,
        context_type,
        max_variable_count,
        variable_reserve_count,
        max_frame_count,
        func_decl_arg_count,
        func_decl_unnamed_arg_array_base,
        func_decl_collapse_base,
        prop_setter_obj_index,
        prop_getter_obj_index,
        super_class_getter_obj_index,
        unknown_14,
        src_code_pos,
        src_source_pos,
        code,
        consts,
        super_getter_ptrs,
        members,
    })
}

fn read_vec_u8_aligned(r: &mut Reader, align: u64) -> Result<Vec<u8>> {
    let cnt = r.read_u32()? as usize;
    let v = if cnt == 0 { Vec::new() } else { r.read_exact(cnt)? };
    r.align(align)?;
    Ok(v)
}

fn read_vec_i16_aligned(r: &mut Reader, align: u64) -> Result<Vec<i16>> {
    let cnt = r.read_u32()? as usize;
    let mut v = Vec::with_capacity(cnt);
    for _ in 0..cnt {
        v.push(r.read_i16()?);
    }
    r.align(align)?;
    Ok(v)
}

fn read_vec_i32_aligned(r: &mut Reader, align: u64) -> Result<Vec<i32>> {
    let cnt = r.read_u32()? as usize;
    let mut v = Vec::with_capacity(cnt);
    for _ in 0..cnt {
        v.push(r.read_i32()?);
    }
    r.align(align)?;
    Ok(v)
}

fn read_vec_i64_aligned(r: &mut Reader, align: u64) -> Result<Vec<i64>> {
    let cnt = r.read_u32()? as usize;
    let mut v = Vec::with_capacity(cnt);
    for _ in 0..cnt {
        v.push(r.read_i64()?);
    }
    r.align(align)?;
    Ok(v)
}

fn read_vec_f64_aligned(r: &mut Reader, align: u64) -> Result<Vec<f64>> {
    let cnt = r.read_u32()? as usize;
    let mut v = Vec::with_capacity(cnt);
    for _ in 0..cnt {
        v.push(r.read_f64()?);
    }
    r.align(align)?;
    Ok(v)
}

fn read_vec_string_utf16le_aligned(r: &mut Reader, align: u64) -> Result<Vec<String>> {
    let cnt = r.read_u32()? as usize;
    let mut out = Vec::with_capacity(cnt);
    for _ in 0..cnt {
        let len = r.read_u32()? as usize;
        // Defensive bound: avoid allocating absurd lengths on corrupt input.
        if len > 64 * 1024 * 1024 {
            bail!("string length too large: {}", len);
        }
        let raw = r.read_exact(len * 2)?;
        let mut u16s = Vec::with_capacity(len);
        for i in 0..len {
            let lo = raw[i * 2] as u16;
            let hi = raw[i * 2 + 1] as u16;
            u16s.push(lo | (hi << 8));
        }
        out.push(String::from_utf16_lossy(&u16s));
        r.align(align)?;
    }
    Ok(out)
}

fn read_vec_octet_aligned(r: &mut Reader, align: u64) -> Result<Vec<Vec<u8>>> {
    let cnt = r.read_u32()? as usize;
    let mut out = Vec::with_capacity(cnt);
    for _ in 0..cnt {
        let len = r.read_u32()? as usize;
        if len > 256 * 1024 * 1024 {
            bail!("octet length too large: {}", len);
        }
        let raw = r.read_exact(len)?;
        out.push(raw);
        r.align(align)?;
    }
    Ok(out)
}

impl Tjs2Bytecode {
    pub fn dump_summary(&self) {
        println!("TJS2 bytecode:");
        println!("  version: {:?}, file_size: {}", self.version, self.file_size);
        println!(
            "  data: bytes={} shorts={} ints={} longs={} doubles={} strings={} octets={}",
            self.data.bytes.len(),
            self.data.shorts.len(),
            self.data.ints.len(),
            self.data.longs.len(),
            self.data.doubles.len(),
            self.data.strings.len(),
            self.data.octets.len(),
        );
        println!("  objects: {}", self.objects.len());
        println!("  top_level: {:?}", self.top_level);

        if let Some(top) = self.top_level {
            self.dump_tree(top, 0);
        } else {
            for (i, o) in self.objects.iter().enumerate() {
                if o.parent_index < 0 {
                    self.dump_tree(i, 0);
                }
            }
        }
    }

    fn dump_tree(&self, idx: usize, depth: usize) {
        let o = &self.objects[idx];
        let indent = "  ".repeat(depth);

        let name = if o.name_string_index >= 0 {
            self.data
                .strings
                .get(o.name_string_index as usize)
                .map(|s| s.as_str())
                .unwrap_or("<bad-name-idx>")
        } else {
            "<anon>"
        };

        println!(
            "{indent}- obj#{idx} name={name:?} ctx={} parent={} code_words={} consts={} members={}",
            o.context_type,
            o.parent_index,
            o.code.len(),
            o.consts.len(),
            o.members.len()
        );

        for &c in &self.children[idx] {
            self.dump_tree(c, depth + 1);
        }
    }

    /// Dump the per-object constant tables (Object.consts) in a compact form.
    ///
    /// The disassembler uses `*idx` to reference entries in this table. Each entry is a pair
    /// `(ty, ix)` where `ty` selects a shared DATA pool and `ix` is an index into that pool.
    pub fn dump_consts(&self) {
        fn escape_string(s: &str) -> String {
            // Escape a few common characters and keep the output bounded.
            let mut t = s
                .replace('\\', "\\\\")
                .replace('"', "\\\"")
                .replace('\n', "\\n")
                .replace('\r', "\\r")
                .replace('\t', "\\t");
            if t.len() > 120 {
                t.truncate(120);
                t.push_str("...");
            }
            t
        }

        fn fmt_const(v: &ConstValue) -> String {
            match v {
                ConstValue::Void => "void".to_string(),
                ConstValue::Byte(x) => format!("byte 0x{:02X} ({})", x, x),
                ConstValue::Short(x) => format!("short {}", x),
                ConstValue::Int(x) => format!("int {}", x),
                ConstValue::Long(x) => format!("long {}", x),
                ConstValue::Double(x) => format!("double {}", x),
                ConstValue::String(s) => format!("string \"{}\"", escape_string(s)),
                ConstValue::Octet(b) => {
                    let take = std::cmp::min(16, b.len());
                    let mut hex = String::new();
                    for (i, byte) in b.iter().take(take).enumerate() {
                        if i > 0 {
                            hex.push(' ');
                        }
                        hex.push_str(&format!("{:02X}", byte));
                    }
                    if b.len() > take {
                        hex.push_str(" ...");
                    }
                    format!("octet {} bytes [{}]", b.len(), hex)
                }
                ConstValue::Unknown { ty, ix } => format!("unknown ty={} ix={}", ty, ix),
            }
        }

        for o in &self.objects {
            println!(
                "== obj#{} (ctx={}, parent={}, consts={}) ==",
                o.index,
                o.context_type,
                o.parent_index,
                o.consts.len()
            );
            for (i, (ty, ix)) in o.consts.iter().enumerate() {
                let mut line = format!("  *{:05} = ty={} ix={}", i, ty, ix);
                if i <= u16::MAX as usize {
                    if let Some(v) = self.resolve_const(o.index, i as u16) {
                        line.push_str(" /* ");
                        line.push_str(&fmt_const(&v));
                        line.push_str(" */");
                    } else {
                        line.push_str(" /* <unresolved> */");
                    }
                }
                println!("{line}");
            }
        }
    }


    pub fn dump_code_words(&self) {
        for o in &self.objects {
            println!(
                "== obj#{} (ctx={}, parent={}, code_words={}) ==",
                o.index, o.context_type, o.parent_index, o.code.len()
            );
            for (i, w) in o.code.iter().enumerate() {
                println!("  {:05}: {}", i, *w as i32);
            }
        }
    }
}
