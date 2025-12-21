use anyhow::{bail, Result};

use crate::model::{ConstPools, Tjs2File, Tjs2Object};
use crate::vmcodes::vm;

const FAT_NORMAL: i32 = 0;
const FAT_EXPAND: i32 = 1;
const FAT_UNNAMED_EXPAND: i32 = 2;

pub fn disassemble_file(file: &Tjs2File) -> Result<String> {
    let mut out = String::new();
    out.push_str(&format!("toplevel: {}\n", file.toplevel));
    out.push_str(&format!("objects: {}\n\n", file.objects.len()));

    for obj in &file.objects {
        out.push_str(&format_object_header(obj));
        out.push('\n');
        out.push_str(&disassemble_object(obj, &file.const_pools)?);
        out.push('\n');
    }

    Ok(out)
}

fn format_object_header(obj: &Tjs2Object) -> String {
    let name = obj.name.as_deref().unwrap_or("<anonymous>");
    format!(
        "== object {}: name={} context_type={} parent={} ==",
        obj.index, quote(name), obj.context_type, obj.parent
    )
}

pub fn disassemble_object(obj: &Tjs2Object, pools: &ConstPools) -> Result<String> {
    let mut out = String::new();
    let code = &obj.code;

    let mut i: usize = 0;
    while i < code.len() {
        let (msg, comment, size) = format_insn(code, i, obj, pools)?;
        out.push_str(&format!("{:08} {}", i, msg));
        if !comment.is_empty() {
            out.push_str("\t// ");
            out.push_str(&comment);
        }
        out.push('\n');
        i += size;
    }
    Ok(out)
}

fn format_insn(code: &[i32], i: usize, obj: &Tjs2Object, pools: &ConstPools) -> Result<(String, String, usize)> {
    let op = code[i];
    let mut msg = String::new();
    let mut com = String::new();
    let mut size: usize = 1;

    // Helpers
    let reg = |x: i32| -> i32 { x };
    let data_idx = |x: i32| -> i32 { x };
    let target = |rel: i32| -> i32 { rel + i as i32 };

    // const
    if op == vm::VM_CONST {
        ensure(code, i, 3)?;
        let dst = reg(code[i + 1]);
        let src = data_idx(code[i + 2]);
        msg = format!("const %{}, *{}", dst, src);
        if let Some(v) = obj.data.get(src as usize) {
            com = format!("*{} = {}", src, v.to_readable(pools));
        }
        size = 3;
        return Ok((msg, com, size));
    }

    // OP2 no property access
    for (base, name) in [
        (vm::VM_CP, "cp"),
        (vm::VM_CEQ, "ceq"),
        (vm::VM_CDEQ, "cdeq"),
        (vm::VM_CLT, "clt"),
        (vm::VM_CGT, "cgt"),
        (vm::VM_CHKINS, "chkins"),
        (vm::VM_ADDCI, "addci"),
        (vm::VM_CHGTHIS, "chgthis"),
    ] {
        if op == base {
            ensure(code, i, 3)?;
            msg = format!("{} %{}, %{}", name, reg(code[i + 1]), reg(code[i + 2]));
            size = 3;
            return Ok((msg, com, size));
        }
    }

    // cl / srv / global / throw: one reg
    for (base, name) in [
        (vm::VM_CL, "cl"),
        (vm::VM_SRV, "srv"),
        (vm::VM_GLOBAL, "global"),
        (vm::VM_THROW, "throw"),
        (vm::VM_TT, "tt"),
        (vm::VM_TF, "tf"),
        (vm::VM_SETF, "setf"),
        (vm::VM_SETNF, "setnf"),
        (vm::VM_LNOT, "lnot"),
        (vm::VM_BNOT, "bnot"),
        (vm::VM_ASC, "asc"),
        (vm::VM_CHR, "chr"),
        (vm::VM_NUM, "num"),
        (vm::VM_CHS, "chs"),
        (vm::VM_INV, "inv"),
        (vm::VM_CHKINV, "chkinv"),
        (vm::VM_TYPEOF, "typeof"),
        (vm::VM_EVAL, "eval"),
        (vm::VM_EEXP, "eexp"),
        (vm::VM_INT, "int"),
        (vm::VM_REAL, "real"),
        (vm::VM_STR, "str"),
        (vm::VM_OCTET, "octet"),
    ] {
        if op == base {
            ensure(code, i, 2)?;
            msg = format!("{} %{}", name, reg(code[i + 1]));
            size = 2;
            return Ok((msg, com, size));
        }
    }

    if op == vm::VM_CCL {
        ensure(code, i, 3)?;
        let r0 = reg(code[i + 1]);
        let cnt = code[i + 2];
        msg = format!("ccl %{}-%{}", r0, r0 + cnt - 1);
        size = 3;
        return Ok((msg, com, size));
    }

    // JF/JNF/JMP (one code operand)
    for (base, name) in [
        (vm::VM_JF, "jf"),
        (vm::VM_JNF, "jnf"),
        (vm::VM_JMP, "jmp"),
    ] {
        if op == base {
            ensure(code, i, 2)?;
            msg = format!("{} {:09}", name, target(code[i + 1]));
            size = 2;
            return Ok((msg, com, size));
        }
    }

    // entry
    if op == vm::VM_ENTRY {
        ensure(code, i, 3)?;
        msg = format!("entry {:09}, %{}", target(code[i + 1]), reg(code[i + 2]));
        size = 3;
        return Ok((msg, com, size));
    }

    // RET / NOP / NF / EXTRY / REGMEMBER / DEBUGGER
    for (base, name) in [
        (vm::VM_RET, "ret"),
        (vm::VM_NOP, "nop"),
        (vm::VM_NF, "nf"),
        (vm::VM_EXTRY, "extry"),
        (vm::VM_REGMEMBER, "regmember"),
        (vm::VM_DEBUGGER, "debugger"),
    ] {
        if op == base {
            msg = name.to_string();
            size = 1;
            return Ok((msg, com, size));
        }
    }

    // SETP / GETP
    if op == vm::VM_SETP || op == vm::VM_GETP {
        ensure(code, i, 3)?;
        let n = if op == vm::VM_SETP { "setp" } else { "getp" };
        msg = format!("{} %{}, %{}", n, reg(code[i + 1]), reg(code[i + 2]));
        size = 3;
        return Ok((msg, com, size));
    }

    // deld/typeofd
    if op == vm::VM_DELD || op == vm::VM_TYPEOFD {
        ensure(code, i, 4)?;
        let n = if op == vm::VM_DELD { "deld" } else { "typeofd" };
        let a = reg(code[i + 1]);
        let b = reg(code[i + 2]);
        let c = data_idx(code[i + 3]);
        msg = format!("{} %{}, %{}.*{}", n, a, b, c);
        if let Some(v) = obj.data.get(c as usize) {
            com = format!("*{} = {}", c, v.to_readable(pools));
        }
        size = 4;
        return Ok((msg, com, size));
    }

    // deli/typeofi
    if op == vm::VM_DELI || op == vm::VM_TYPEOFI {
        ensure(code, i, 4)?;
        let n = if op == vm::VM_DELI { "deli" } else { "typeofi" };
        msg = format!("{} %{}, %{}.%{}", n, reg(code[i + 1]), reg(code[i + 2]), reg(code[i + 3]));
        size = 4;
        return Ok((msg, com, size));
    }

    // gpd/gpds
    if op == vm::VM_GPD || op == vm::VM_GPDS {
        ensure(code, i, 4)?;
        let n = if op == vm::VM_GPD { "gpd" } else { "gpds" };
        let a = reg(code[i + 1]);
        let b = reg(code[i + 2]);
        let c = data_idx(code[i + 3]);
        msg = format!("{} %{}, %{}.*{}", n, a, b, c);
        if let Some(v) = obj.data.get(c as usize) {
            com = format!("*{} = {}", c, v.to_readable(pools));
        }
        size = 4;
        return Ok((msg, com, size));
    }

    // spd/spde/spdeh/spds
    if op == vm::VM_SPD || op == vm::VM_SPDE || op == vm::VM_SPDEH || op == vm::VM_SPDS {
        ensure(code, i, 4)?;
        let n = match op {
            x if x == vm::VM_SPD => "spd",
            x if x == vm::VM_SPDE => "spde",
            x if x == vm::VM_SPDEH => "spdeh",
            _ => "spds",
        };
        let a = reg(code[i + 1]);
        let b = data_idx(code[i + 2]);
        let c = reg(code[i + 3]);
        msg = format!("{} %{}.*{}, %{}", n, a, b, c);
        if let Some(v) = obj.data.get(b as usize) {
            com = format!("*{} = {}", b, v.to_readable(pools));
        }
        size = 4;
        return Ok((msg, com, size));
    }

    // gpi/gpis
    if op == vm::VM_GPI || op == vm::VM_GPIS {
        ensure(code, i, 4)?;
        let n = if op == vm::VM_GPI { "gpi" } else { "gpis" };
        msg = format!("{} %{}, %{}.%{}", n, reg(code[i + 1]), reg(code[i + 2]), reg(code[i + 3]));
        size = 4;
        return Ok((msg, com, size));
    }

    // spi/spie/spis
    if op == vm::VM_SPI || op == vm::VM_SPIE || op == vm::VM_SPIS {
        ensure(code, i, 4)?;
        let n = match op {
            x if x == vm::VM_SPI => "spi",
            x if x == vm::VM_SPIE => "spie",
            _ => "spis",
        };
        msg = format!("{} %{}.%{}, %{}", n, reg(code[i + 1]), reg(code[i + 2]), reg(code[i + 3]));
        size = 4;
        return Ok((msg, com, size));
    }

    // inc/dec with property access variants
    if let Some((m, c, s)) = op1_prop(code, i, obj, pools, vm::VM_INC, "inc")? {
        return Ok((m, c, s));
    }
    if let Some((m, c, s)) = op1_prop(code, i, obj, pools, vm::VM_DEC, "dec")? {
        return Ok((m, c, s));
    }

    // binary ops with property access variants
    for (base, name) in [
        (vm::VM_LOR, "lor"),
        (vm::VM_LAND, "land"),
        (vm::VM_BOR, "bor"),
        (vm::VM_BXOR, "bxor"),
        (vm::VM_BAND, "band"),
        (vm::VM_SAR, "sar"),
        (vm::VM_SAL, "sal"),
        (vm::VM_SR, "sr"),
        (vm::VM_ADD, "add"),
        (vm::VM_SUB, "sub"),
        (vm::VM_MOD, "mod"),
        (vm::VM_DIV, "div"),
        (vm::VM_IDIV, "idiv"),
        (vm::VM_MUL, "mul"),
    ] {
        if let Some((m, c, s)) = op2_prop(code, i, obj, pools, base, name)? {
            return Ok((m, c, s));
        }
    }

    // call / calld / calli / new
    if op == vm::VM_CALL || op == vm::VM_CALLD || op == vm::VM_CALLI || op == vm::VM_NEW {
        return format_call(code, i, obj, pools);
    }

    // add missing simple opcodes
    if op == vm::VM_REGMEMBER || op == vm::VM_DEBUGGER {
        msg = vm::name(op).to_lowercase();
        size = 1;
        return Ok((msg, com, size));
    }

    // Fallback
    msg = format!("unknown instruction {}", op);
    Ok((msg, com, 1))
}

fn op2_prop(code: &[i32], i: usize, obj: &Tjs2Object, pools: &ConstPools, base: i32, name: &str)
    -> Result<Option<(String, String, usize)>> {
    let op = code[i];
    if op < base || op > base + 3 {
        return Ok(None);
    }
    match op - base {
        0 => {
            ensure(code, i, 3)?;
            Ok(Some((format!("{} %{}, %{}", name, code[i + 1], code[i + 2]), String::new(), 3)))
        }
        1 => {
            ensure(code, i, 5)?;
            let a = code[i + 1];
            let b = code[i + 2];
            let c = code[i + 3];
            let d = code[i + 4];
            let mut com = String::new();
            if let Some(v) = obj.data.get(c as usize) {
                com = format!("*{} = {}", c, v.to_readable(pools));
            }
            Ok(Some((format!("{}pd %{}, %{}.*{}, %{}", name, a, b, c, d), com, 5)))
        }
        2 => {
            ensure(code, i, 5)?;
            Ok(Some((format!("{}pi %{}, %{}.%{}, %{}", name, code[i + 1], code[i + 2], code[i + 3], code[i + 4]), String::new(), 5)))
        }
        3 => {
            ensure(code, i, 4)?;
            Ok(Some((format!("{}p %{}, %{}, %{}", name, code[i + 1], code[i + 2], code[i + 3]), String::new(), 4)))
        }
        _ => Ok(None),
    }
}

fn op1_prop(code: &[i32], i: usize, obj: &Tjs2Object, pools: &ConstPools, base: i32, name: &str)
    -> Result<Option<(String, String, usize)>> {
    let op = code[i];
    if op < base || op > base + 3 {
        return Ok(None);
    }
    match op - base {
        0 => {
            ensure(code, i, 2)?;
            Ok(Some((format!("{} %{}", name, code[i + 1]), String::new(), 2)))
        }
        1 => {
            ensure(code, i, 4)?;
            let a = code[i + 1];
            let b = code[i + 2];
            let c = code[i + 3];
            let mut com = String::new();
            if let Some(v) = obj.data.get(c as usize) {
                com = format!("*{} = {}", c, v.to_readable(pools));
            }
            Ok(Some((format!("{}pd %{}, %{}.*{}", name, a, b, c), com, 4)))
        }
        2 => {
            ensure(code, i, 4)?;
            Ok(Some((format!("{}pi %{}, %{}.%{}", name, code[i + 1], code[i + 2], code[i + 3]), String::new(), 4)))
        }
        3 => {
            ensure(code, i, 3)?;
            Ok(Some((format!("{}p %{}, %{}", name, code[i + 1], code[i + 2]), String::new(), 3)))
        }
        _ => Ok(None),
    }
}

fn format_call(code: &[i32], i: usize, obj: &Tjs2Object, pools: &ConstPools) -> Result<(String, String, usize)> {
    let op = code[i];
    // Base layout:
    // CALL:  op, dst, func, argc, [args...]
    // CALLD: op, dst, obj, member_data, func, argc, ...
    // CALLI: op, dst, obj, member_reg,  func, argc, ...
    // NEW:   op, dst, func, argc, ...
    let (prefix, st, member_data_index_opt): (&str, usize, Option<i32>) = match op {
        x if x == vm::VM_CALL => ("call", 4, None),
        x if x == vm::VM_NEW => ("new", 4, None),
        x if x == vm::VM_CALLD => ("calld", 5, Some(code[i + 3])),
        _ => ("calli", 5, None),
    };

    // Header
    let mut msg = String::new();
    match op {
        x if x == vm::VM_CALL => {
            ensure(code, i, 4)?;
            msg = format!("call %{}, %{}(", code[i + 1], code[i + 2]);
        }
        x if x == vm::VM_NEW => {
            ensure(code, i, 4)?;
            msg = format!("new %{}, %{}(", code[i + 1], code[i + 2]);
        }
        x if x == vm::VM_CALLD => {
            ensure(code, i, 5)?;
            msg = format!("calld %{}, %{}.*{}(", code[i + 1], code[i + 2], code[i + 3]);
        }
        _ => {
            ensure(code, i, 5)?;
            msg = format!("calli %{}, %{}.%{}(", code[i + 1], code[i + 2], code[i + 3]);
        }
    }

    let argc = code[i + st - 1];
    let mut size: usize;

    if argc == -1 {
        // omit args
        size = st;
        msg.push_str("...");
    } else if argc == -2 {
        // expand args
        ensure(code, i, st + 1)?;
        let num = code[i + st];
        let num = num as usize;
        size = st + 1 + num * 2;
        for j in 0..num {
            if j != 0 {
                msg.push_str(", ");
            }
            let ty = code[i + st + 1 + j * 2];
            let v = code[i + st + 1 + j * 2 + 1];
            match ty {
                FAT_NORMAL => msg.push_str(&format!("%{}", v)),
                FAT_EXPAND => msg.push_str(&format!("%{}*", v)),
                FAT_UNNAMED_EXPAND => msg.push('*'),
                _ => msg.push_str(&format!("<bad-fat:{}>", ty)),
            }
        }
    } else {
        // normal args: argc registers follow
        let num = argc as usize;
        size = st + num;
        for j in 0..num {
            if j != 0 {
                msg.push_str(", ");
            }
            msg.push_str(&format!("%{}", code[i + st + j]));
        }
    }

    msg.push(')');

    let mut com = String::new();
    if op == vm::VM_CALLD {
        // in krkrz, comment prints the member string stored in data area at code[i+3]
        let c = code[i + 3];
        if let Some(v) = obj.data.get(c as usize) {
            com = format!("*{} = {}", c, v.to_readable(pools));
        }
    }

    Ok((msg, com, size))
}

fn ensure(code: &[i32], i: usize, need: usize) -> Result<()> {
    if i + need > code.len() {
        bail!("truncated instruction at {}: need {}, code_len {}", i, need, code.len());
    }
    Ok(())
}

fn quote(s: &str) -> String {
    let mut out = String::new();
    out.push('"');
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(ch),
        }
    }
    out.push('"');
    out
}
