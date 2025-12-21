use anyhow::{anyhow, bail, Context, Result};

use crate::model::{ConstPools, Tjs2File, Tjs2Object, Variant};

const FILE_TAG_LE: u32 = ('T' as u32) | (('J' as u32) << 8) | (('S' as u32) << 16) | (('2' as u32) << 24);
const VER_TAG_LE: u32 = ('1' as u32) | (('0' as u32) << 8) | (('0' as u32) << 16) | (0u32 << 24);

const OBJ_TAG_LE: u32 = ('O' as u32) | (('B' as u32) << 8) | (('J' as u32) << 16) | (('S' as u32) << 24);
const DATA_TAG_LE: u32 = ('D' as u32) | (('A' as u32) << 8) | (('T' as u32) << 16) | (('A' as u32) << 24);

// Variant types (krkrz tTJSByteCodeLoader)
const TYPE_VOID: i16 = 0;
const TYPE_OBJECT: i16 = 1;
const TYPE_INTER_OBJECT: i16 = 2;
const TYPE_STRING: i16 = 3;
const TYPE_OCTET: i16 = 4;
const TYPE_REAL: i16 = 5;
const TYPE_BYTE: i16 = 6;
const TYPE_SHORT: i16 = 7;
const TYPE_INTEGER: i16 = 8;
const TYPE_LONG: i16 = 9;
const TYPE_INTER_GENERATOR: i16 = 10;
const TYPE_UNKNOWN: i16 = -1;

pub fn load_tjs2_bytecode(buf: &[u8]) -> Result<Tjs2File> {
    if buf.len() < 12 {
        bail!("bytecode too small: {} bytes", buf.len());
    }
    let mut r = Reader::new(buf);

    // File header: "TJS2100\0" (8 bytes) + filesize (u32)
    let file_tag = r.read_u32_le().context("read file tag")?;
    let ver_tag = r.read_u32_le().context("read version tag")?;
    if file_tag != FILE_TAG_LE {
        bail!("fourcc mismatch: expect {:?}, got {:?}", b"TJS2", u32_to_4cc(file_tag));
    }
    if ver_tag != VER_TAG_LE {
        bail!("version mismatch: expect {:?}, got {:?}", b"100\0", u32_to_4cc(ver_tag));
    }
    let file_size = r.read_u32_le().context("read file size")? as usize;
    if file_size != buf.len() {
        bail!("file size mismatch: header={}, actual={}", file_size, buf.len());
    }

    // DATA chunk: tag + chunk_size (includes tag+size) + payload
    let data_tag = r.read_u32_le().context("read DATA tag")?;
    if data_tag != DATA_TAG_LE {
        bail!("fourcc mismatch: expect {:?}, got {:?}", b"DATA", u32_to_4cc(data_tag));
    }
    let data_chunk_size = r.read_u32_le().context("read DATA chunk size")? as usize;
    if data_chunk_size < 8 {
        bail!("DATA chunk size too small: {}", data_chunk_size);
    }
    let data_payload_size = data_chunk_size - 8;
    let data_start = r.pos();
    let data_end = data_start.checked_add(data_payload_size).ok_or_else(|| anyhow!("overflow computing DATA end"))?;
    if data_end > buf.len() {
        bail!("DATA payload out of range: end={}, file={}", data_end, buf.len());
    }
    let pools = read_data_area(&buf[data_start..data_end]).context("parse DATA area")?;
    r.set_pos(data_end);

    // OBJS chunk: tag + chunk_size (includes tag+size) + payload
    let objs_tag = r.read_u32_le().context("read OBJS tag")?;
    if objs_tag != OBJ_TAG_LE {
        bail!("fourcc mismatch: expect {:?}, got {:?}", b"OBJS", u32_to_4cc(objs_tag));
    }
    let objs_chunk_size = r.read_u32_le().context("read OBJS chunk size")? as usize;
    if objs_chunk_size < 8 {
        bail!("OBJS chunk size too small: {}", objs_chunk_size);
    }
    let objs_payload_size = objs_chunk_size - 8;
    let objs_start = r.pos();
    let objs_end = objs_start.checked_add(objs_payload_size).ok_or_else(|| anyhow!("overflow computing OBJS end"))?;
    if objs_end > buf.len() {
        bail!("OBJS payload out of range: end={}, file={}", objs_end, buf.len());
    }

    let (toplevel, objects) = read_objects(&buf[objs_start..objs_end], &pools).context("parse OBJS area")?;
    r.set_pos(objs_end);

    // No extra trailing bytes are expected in krkrz's exporter.
    if r.pos() != buf.len() {
        bail!("unexpected trailing bytes: pos={}, file={}", r.pos(), buf.len());
    }

    Ok(Tjs2File { toplevel, const_pools: pools, objects })
}

fn read_data_area(payload: &[u8]) -> Result<ConstPools> {
    let mut r = Reader::new(payload);
    let mut pools = ConstPools::default();

    // byte
    let count = r.read_u32_le().context("DATA.bytes.count")? as usize;
    if count > 0 {
        let b = r.read_bytes(count).context("DATA.bytes.data")?;
        pools.bytes = b.iter().map(|x| *x as i8).collect();
        r.align4().context("DATA.bytes.align4")?;
    }

    // short
    let count = r.read_u32_le().context("DATA.shorts.count")? as usize;
    if count > 0 {
        pools.shorts.reserve(count);
        for _ in 0..count {
            pools.shorts.push(r.read_i16_le().context("DATA.shorts.elem")?);
        }
        if (count & 1) == 1 {
            // alignment
            let _ = r.read_u16_le().context("DATA.shorts.pad")?;
        }
    }

    // int
    let count = r.read_u32_le().context("DATA.ints.count")? as usize;
    if count > 0 {
        pools.ints.reserve(count);
        for _ in 0..count {
            pools.ints.push(r.read_i32_le().context("DATA.ints.elem")?);
        }
    }

    // long (i64)
    let count = r.read_u32_le().context("DATA.longs.count")? as usize;
    if count > 0 {
        pools.longs.reserve(count);
        for _ in 0..count {
            pools.longs.push(r.read_i64_le().context("DATA.longs.elem")?);
        }
    }

    // double
    let count = r.read_u32_le().context("DATA.doubles.count")? as usize;
    if count > 0 {
        pools.doubles.reserve(count);
        for _ in 0..count {
            let bits = r.read_u64_le().context("DATA.doubles.bits")?;
            pools.doubles.push(f64::from_bits(bits));
        }
    }

    // string (UTF-16LE)
    let count = r.read_u32_le().context("DATA.strings.count")? as usize;
    pools.strings.reserve(count);
    for _ in 0..count {
        let len = r.read_u32_le().context("DATA.strings.len")? as usize;
        let mut units = Vec::with_capacity(len);
        for _ in 0..len {
            units.push(r.read_u16_le().context("DATA.strings.unit")?);
        }
        if (len & 1) == 1 {
            let _ = r.read_u16_le().context("DATA.strings.pad")?;
        }
        pools.strings.push(String::from_utf16_lossy(&units));
    }

    // octet buffers
    let count = r.read_u32_le().context("DATA.octets.count")? as usize;
    pools.octets.reserve(count);
    for _ in 0..count {
        let cap = r.read_u32_le().context("DATA.octets.len")? as usize;
        let data = r.read_bytes(cap).context("DATA.octets.data")?.to_vec();
        pools.octets.push(data);
        r.align4().context("DATA.octets.align4")?;
    }

    if r.pos() != payload.len() {
        bail!("DATA: payload not fully consumed: pos={}, payload={}", r.pos(), payload.len());
    }

    Ok(pools)
}

fn read_objects(payload: &[u8], pools: &ConstPools) -> Result<(i32, Vec<Tjs2Object>)> {
    let mut r = Reader::new(payload);

    let toplevel = r.read_i32_le().context("OBJS.toplevel")?;
    let objcount = r.read_i32_le().context("OBJS.objcount")?;
    if objcount < 0 {
        bail!("OBJS.objcount is negative: {}", objcount);
    }
    let objcount = objcount as usize;

    let mut objects: Vec<Tjs2Object> = Vec::with_capacity(objcount);

    // We keep raw property pairs here; we do not execute propSet logic.
    for o in 0..objcount {
        let tag = r.read_u32_le().context("OBJS.obj.tag")?;
        if tag != FILE_TAG_LE {
            bail!("object fourcc mismatch: expect {:?}, got {:?}", b"TJS2", u32_to_4cc(tag));
        }
        let _obj_payload_size = r.read_u32_le().context("OBJS.obj.size")? as usize;

        let parent = r.read_i32_le().context("obj.parent")?;
        let name_idx = r.read_i32_le().context("obj.name_idx")?;
        let context_type = r.read_i32_le().context("obj.context_type")?;
        let max_variable_count = r.read_i32_le().context("obj.max_variable_count")?;
        let variable_reserve_count = r.read_i32_le().context("obj.variable_reserve_count")?;
        let max_frame_count = r.read_i32_le().context("obj.max_frame_count")?;
        let func_decl_arg_count = r.read_i32_le().context("obj.func_decl_arg_count")?;
        let func_decl_unnamed_arg_array_base = r.read_i32_le().context("obj.func_decl_unnamed_arg_array_base")?;
        let func_decl_collapse_base = r.read_i32_le().context("obj.func_decl_collapse_base")?;
        let prop_setter = r.read_i32_le().context("obj.prop_setter")?;
        let prop_getter = r.read_i32_le().context("obj.prop_getter")?;
        let super_class_getter = r.read_i32_le().context("obj.super_class_getter")?;

        // srcpos
        let srcpos_count = r.read_i32_le().context("obj.srcpos.count")?;
        if srcpos_count < 0 {
            bail!("obj.srcpos.count is negative: {}", srcpos_count);
        }
        let srcpos_count = srcpos_count as usize;
        // We do not use srcpos mapping for now; just skip it.
        for _ in 0..srcpos_count {
            let _ = r.read_i32_le().context("obj.srcpos.codepos")?;
        }
        for _ in 0..srcpos_count {
            let _ = r.read_i32_le().context("obj.srcpos.srcpos")?;
        }

        // code area
        let code_count = r.read_i32_le().context("obj.code.count")?;
        if code_count < 0 {
            bail!("obj.code.count is negative: {}", code_count);
        }
        let code_count = code_count as usize;
        let mut code: Vec<i32> = Vec::with_capacity(code_count);
        for _ in 0..code_count {
            code.push(r.read_i16_le().context("obj.code.word")? as i32);
        }
        // align to 4 bytes if odd
        if (code_count & 1) == 1 {
            let _ = r.read_u16_le().context("obj.code.pad")?;
        }

        // data area (vdata)
        let data_count = r.read_i32_le().context("obj.data.count")?;
        if data_count < 0 {
            bail!("obj.data.count is negative: {}", data_count);
        }
        let data_count = data_count as usize;
        let mut data: Vec<Variant> = Vec::with_capacity(data_count);
        for _ in 0..data_count {
            let ty = r.read_i16_le().context("obj.data.type")?;
            let idx = r.read_i16_le().context("obj.data.index")? as i32;
            let v = match ty {
                TYPE_VOID => Variant::Void,
                TYPE_OBJECT => Variant::NullObject,
                TYPE_INTER_OBJECT => Variant::InterObject(idx),
                TYPE_INTER_GENERATOR => Variant::InterGenerator(idx),
                TYPE_STRING => Variant::String(idx),
                TYPE_OCTET => Variant::Octet(idx),
                TYPE_REAL => Variant::Real(idx),
                TYPE_BYTE => Variant::Byte(idx),
                TYPE_SHORT => Variant::Short(idx),
                TYPE_INTEGER => Variant::Integer(idx),
                TYPE_LONG => Variant::Long(idx),
                TYPE_UNKNOWN | _ => Variant::Unknown,
            };
            data.push(v);
        }

        // super class getter pointer
        let scg_count = r.read_i32_le().context("obj.scgetterps.count")?;
        if scg_count < 0 {
            bail!("obj.scgetterps.count is negative: {}", scg_count);
        }
        let scg_count = scg_count as usize;
        let mut scgetterps: Vec<i32> = Vec::with_capacity(scg_count);
        for _ in 0..scg_count {
            scgetterps.push(r.read_i32_le().context("obj.scgetterps.elem")?);
        }

        // properties
        let prop_count = r.read_i32_le().context("obj.properties.count")?;
        if prop_count < 0 {
            bail!("obj.properties.count is negative: {}", prop_count);
        }
        let prop_count = prop_count as usize;
        let mut properties = Vec::new();
        if prop_count > 0 {
            properties.reserve(prop_count);
            for _ in 0..prop_count {
                let pname = r.read_i32_le().context("obj.properties.name")?;
                let pobj = r.read_i32_le().context("obj.properties.obj")?;
                properties.push((pname, pobj));
            }
        }

        let name = if name_idx >= 0 {
            pools.strings.get(name_idx as usize).cloned()
        } else {
            None
        };

        objects.push(Tjs2Object {
            index: o,
            parent,
            name_string_index: name_idx,
            name,
            context_type,
            max_variable_count,
            variable_reserve_count,
            max_frame_count,
            func_decl_arg_count,
            func_decl_unnamed_arg_array_base,
            func_decl_collapse_base,
            prop_setter,
            prop_getter,
            super_class_getter,
            code,
            data,
            scgetterps,
            properties,
        });
    }

    if r.pos() != payload.len() {
        bail!("OBJS: payload not fully consumed: pos={}, payload={}", r.pos(), payload.len());
    }

    Ok((toplevel, objects))
}

fn u32_to_4cc(x: u32) -> [u8; 4] {
    [(x & 0xff) as u8, ((x >> 8) & 0xff) as u8, ((x >> 16) & 0xff) as u8, ((x >> 24) & 0xff) as u8]
}

struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(buf: &'a [u8]) -> Self { Self { buf, pos: 0 } }
    fn pos(&self) -> usize { self.pos }
    fn set_pos(&mut self, pos: usize) { self.pos = pos; }

    fn read_bytes(&mut self, n: usize) -> Result<&'a [u8]> {
        let end = self.pos.checked_add(n).ok_or_else(|| anyhow!("overflow"))?;
        if end > self.buf.len() {
            bail!("failed to fill whole buffer");
        }
        let out = &self.buf[self.pos..end];
        self.pos = end;
        Ok(out)
    }

    fn read_u16_le(&mut self) -> Result<u16> {
        let b = self.read_bytes(2)?;
        Ok(u16::from_le_bytes([b[0], b[1]]))
    }
    fn read_i16_le(&mut self) -> Result<i16> { Ok(self.read_u16_le()? as i16) }

    fn read_u32_le(&mut self) -> Result<u32> {
        let b = self.read_bytes(4)?;
        Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }
    fn read_i32_le(&mut self) -> Result<i32> { Ok(self.read_u32_le()? as i32) }

    fn read_u64_le(&mut self) -> Result<u64> {
        let b = self.read_bytes(8)?;
        Ok(u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]))
    }
    fn read_i64_le(&mut self) -> Result<i64> { Ok(self.read_u64_le()? as i64) }

    fn align4(&mut self) -> Result<()> {
        let rem = self.pos & 3;
        if rem != 0 {
            let pad = 4 - rem;
            let _ = self.read_bytes(pad)?;
        }
        Ok(())
    }
}
