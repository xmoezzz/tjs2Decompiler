// SPDX-License-Identifier: MIT
//
// Disassembler for the TJS2 VM code stream (Object.code: little-endian i16 word stream).
//
// Output style (requested):
//   - constants are printed as *idx
//   - if --resolve-consts=true, resolved values are printed as trailing comments: /* ... */
//   - direct member access uses %obj.*idx (with optional comment for the name)
//   - indirect member access uses %obj.%reg
//   - CALL/NEW consume argc and all args; we print explicit arg registers.
//
// This module focuses on *opcode restoration correctness*: instruction boundaries and operand decoding.

use anyhow::{bail, Context, Result};

use crate::opcode::Opcode;
use crate::tjs2::{ConstValue, Tjs2Bytecode};

#[derive(Debug, Clone)]
pub struct Insn {
    pub ip: usize,
    pub op: Opcode,
    pub operands: Vec<i16>, // raw operand words (signed); some are indices/argc/ips
}

pub fn disasm_all(bc: &Tjs2Bytecode, resolve_consts: bool) -> Result<()> {
    if let Some(root) = bc.top_level {
        disasm_tree(bc, root, 0, resolve_consts)?;
    } else {
        for i in 0..bc.objects.len() {
            disasm_object(bc, i, resolve_consts)?;
        }
    }
    Ok(())
}

pub fn disasm_object(bc: &Tjs2Bytecode, obj_index: usize, resolve_consts: bool) -> Result<()> {
    if obj_index >= bc.objects.len() {
        bail!("object index out of range: {}", obj_index);
    }

    let obj = &bc.objects[obj_index];
    println!(
        "== obj#{} name_idx={} ctx={} parent={} code_words={} consts={} members={} ==",
        obj_index,
        obj.name_string_index,
        obj.context_type,
        obj.parent_index,
        obj.code.len(),
        obj.consts.len(),
        obj.members.len(),
    );

    let insns = disasm_code(bc, obj_index).context("disasm object code")?;
    for insn in &insns {
        println!("{}", format_insn(bc, obj_index, insn, resolve_consts));
    }

    Ok(())
}

fn disasm_tree(bc: &Tjs2Bytecode, obj_index: usize, indent: usize, resolve_consts: bool) -> Result<()> {
    let pad = " ".repeat(indent);
    let obj = &bc.objects[obj_index];

    println!(
        "{}== obj#{} name_idx={} ctx={} parent={} code_words={} consts={} members={} ==",
        pad,
        obj_index,
        obj.name_string_index,
        obj.context_type,
        obj.parent_index,
        obj.code.len(),
        obj.consts.len(),
        obj.members.len(),
    );

    let insns = disasm_code(bc, obj_index).context("disasm object code")?;
    for insn in &insns {
        println!("{}{}", pad, format_insn(bc, obj_index, insn, resolve_consts));
    }

    if let Some(children) = bc.children.get(obj_index) {
        for &ch in children {
            disasm_tree(bc, ch, indent + 2, resolve_consts)?;
        }
    }

    Ok(())
}

fn disasm_code(bc: &Tjs2Bytecode, obj_index: usize) -> Result<Vec<Insn>> {
    let code = &bc
        .objects
        .get(obj_index)
        .context("object not found")?
        .code;

    let mut out = Vec::new();
    let mut ip: usize = 0;

    while ip < code.len() {
        let opw = code[ip] as u16;
        let op = Opcode::from_u16(opw).with_context(|| format!("unknown opcode {} at ip {}", opw, ip))?;

        let operand_words = operand_words(op, code, ip)
            .with_context(|| format!("decode operand length for {} at ip {}", op.mnemonic(), ip))?;

        if ip + 1 + operand_words > code.len() {
            bail!(
                "truncated instruction at ip {}: {} expects {} operand words but only {} remain",
                ip,
                op.mnemonic(),
                operand_words,
                code.len().saturating_sub(ip + 1)
            );
        }

        let operands = code[ip + 1..ip + 1 + operand_words].to_vec();
        out.push(Insn { ip, op, operands });
        ip += 1 + operand_words;
    }

    Ok(out)
}

fn operand_words(op: Opcode, code: &[i16], ip: usize) -> Result<usize> {
    if let Some(n) = op.fixed_operand_words() {
        return Ok(n);
    }

    // Variable length: CALL/NEW family.
    // Layouts (operand words after opcode):
    //   call  : %dest, %func, argc, args...
    //   new   : %dest, %func, argc, args...
    //   calld : %dest, %obj, *name, argc, args...
    //   calli : %dest, %obj, %name, argc, args...
    let base = match op {
        Opcode::Call | Opcode::New => 3,
        Opcode::Calld | Opcode::Calli => 4,
        _ => bail!("unexpected variable-length opcode: {}", op.mnemonic()),
    };

    if ip + 1 + base > code.len() {
        bail!("truncated {} header at ip {}", op.mnemonic(), ip);
    }

    let argc = code[ip + 1 + (base - 1)] as i32;
    if argc < 0 {
        bail!("negative argc {} for {} at ip {}", argc, op.mnemonic(), ip);
    }

    Ok(base + (argc as usize))
}

fn fmt_reg(r: i16) -> String {
    format!("%{}", r)
}

fn fmt_ip_word(ip: i16) -> String {
    // Most bytecode uses non-negative absolute word indices.
    if ip >= 0 {
        format!("{:08}", ip as u32)
    } else {
        format!("-{}", -ip)
    }
}

fn fmt_const_ref(idx: u16) -> String {
    format!("*{}", idx)
}

fn escape_comment_string(s: &str) -> String {
    // Keep comments readable and compact.
    let mut t = s.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n").replace('\r', "\\r").replace('\t', "\\t");
    if t.len() > 120 {
        t.truncate(120);
        t.push_str("...");
    }
    format!("\"{}\"", t)
}

fn fmt_const_comment(v: &ConstValue) -> String {
    match v {
        ConstValue::Void => "void".to_string(),
        ConstValue::Byte(x) => format!("byte {}", *x as u64),
        ConstValue::Short(x) => format!("short {}", x),
        ConstValue::Int(x) => format!("int {}", x),
        ConstValue::Long(x) => format!("long {}", x),
        ConstValue::Double(x) => format!("double {}", x),
        ConstValue::String(s) => format!("string {}", escape_comment_string(s)),
        ConstValue::Octet(b) => format!("octet {} bytes", b.len()),
        ConstValue::Unknown { ty, ix } => format!("unknown ty={} ix={}", ty, ix),
    }
}

fn fmt_const_with_comment(bc: &Tjs2Bytecode, obj_index: usize, idx: u16, resolve: bool) -> String {
    if !resolve {
        return fmt_const_ref(idx);
    }
    match bc.resolve_const(obj_index, idx) {
        Some(v) => format!("{} /* {} */", fmt_const_ref(idx), fmt_const_comment(&v)),
        None => format!("{} /* <unresolved> */", fmt_const_ref(idx)),
    }
}

fn fmt_member_d(bc: &Tjs2Bytecode, obj_index: usize, obj_reg: i16, name_const: i16, resolve: bool) -> String {
    let idx = name_const as u16;
    if !resolve {
        return format!("{}.{}", fmt_reg(obj_reg), fmt_const_ref(idx));
    }

    match bc.resolve_const(obj_index, idx) {
        Some(ConstValue::String(s)) => format!("{}.{} /* {} */", fmt_reg(obj_reg), fmt_const_ref(idx), escape_comment_string(&s)),
        Some(v) => format!("{}.{} /* {} */", fmt_reg(obj_reg), fmt_const_ref(idx), fmt_const_comment(&v)),
        None => format!("{}.{} /* <unresolved> */", fmt_reg(obj_reg), fmt_const_ref(idx)),
    }
}

fn fmt_member_i(obj_reg: i16, name_reg: i16) -> String {
    format!("{}.{}", fmt_reg(obj_reg), fmt_reg(name_reg))
}

fn fmt_args(args: &[i16]) -> String {
    args.iter().map(|r| fmt_reg(*r)).collect::<Vec<_>>().join(", ")
}

fn format_insn(bc: &Tjs2Bytecode, obj_index: usize, insn: &Insn, resolve_consts: bool) -> String {
    use Opcode::*;

    let op = insn.op;
    let o = &insn.operands;

    let body = match op {
        Nop | Nf | Ret | Extry | Regmember | Debugger => op.mnemonic().to_string(),

        Const => {
            let dest = o[0];
            let idx = o[1] as u16;
            format!("{} {}, {}", op.mnemonic(), fmt_reg(dest), fmt_const_with_comment(bc, obj_index, idx, resolve_consts))
        }

        Cp => format!("{} {}, {}", op.mnemonic(), fmt_reg(o[0]), fmt_reg(o[1])),

        Cl | Tt | Tf | Setf | Setnf | Lnot | Inc | Dec | Bnot | Asc | Chr | Num | Chs | Inv | Chkinv | Int | Real
        | Str | Octet | Typeof | Eval | Eexp | Srv | Throw | Global => {
            format!("{} {}", op.mnemonic(), fmt_reg(o[0]))
        }

        Ccl => format!("{} {}-{}", op.mnemonic(), fmt_reg(o[0]), fmt_reg(o[1])),

        Ceq | Cdeq | Clt | Cgt | Lor | Land | Bor | Bxor | Band | Sar | Sal | Sr | Add | Sub | Mod | Div | Idiv
        | Mul | Chgthis | Addci => {
            format!("{} {}, {}", op.mnemonic(), fmt_reg(o[0]), fmt_reg(o[1]))
        }

        Jf | Jnf | Jmp => format!("{} {}", op.mnemonic(), fmt_ip_word(o[0])),

        Entry => format!("{} {}, {}", op.mnemonic(), fmt_ip_word(o[0]), fmt_reg(o[1])),

        Typeofd => format!("{} {}", op.mnemonic(), fmt_member_d(bc, obj_index, o[0], o[1], resolve_consts)),
        Typeofi => format!("{} {}", op.mnemonic(), fmt_member_i(o[0], o[1])),

        Chkins => {
            // (reg, classname) where classname is commonly a const ref.
            let cls = o[1] as u16;
            format!("{} {}, {}", op.mnemonic(), fmt_reg(o[0]), fmt_const_with_comment(bc, obj_index, cls, resolve_consts))
        }

        // Unary member/property.
        Incpd | Incpi | Decpd | Decpi => {
            // Operands: %res, %obj, name
            if matches!(op, Incpd | Decpd) {
                format!(
                    "{} {}, {}",
                    op.mnemonic(),
                    fmt_reg(o[0]),
                    fmt_member_d(bc, obj_index, o[1], o[2], resolve_consts)
                )
            } else {
                format!("{} {}, {}", op.mnemonic(), fmt_reg(o[0]), fmt_member_i(o[1], o[2]))
            }
        }

        Incp | Decp => format!("{} {}, {}", op.mnemonic(), fmt_reg(o[0]), fmt_reg(o[1])),

        // Binary member/property.
        Lorpd | Lorpi | Lorp | Landpd | Landpi | Landp | Borpd | Borpi | Borp | Bxorpd | Bxorpi | Bxorp | Bandpd
        | Bandpi | Bandp | Sarpd | Sarpi | Sarp | Salpd | Salpi | Salp | Srpd | Srpi | Srp | Addpd | Addpi | Addp
        | Subpd | Subpi | Subp | Modpd | Modpi | Modp | Divpd | Divpi | Divp | Idivpd | Idivpi | Idivp | Mulpd
        | Mulpi | Mulp => {
            let mnem = op.mnemonic();
            if mnem.ends_with("pd") {
                format!(
                    "{} {}, {}, {}",
                    mnem,
                    fmt_reg(o[0]),
                    fmt_member_d(bc, obj_index, o[1], o[2], resolve_consts),
                    fmt_reg(o[3])
                )
            } else if mnem.ends_with("pi") {
                format!("{} {}, {}, {}", mnem, fmt_reg(o[0]), fmt_member_i(o[1], o[2]), fmt_reg(o[3]))
            } else {
                format!("{} {}, {}, {}", mnem, fmt_reg(o[0]), fmt_reg(o[1]), fmt_reg(o[2]))
            }
        }

        // get member (direct/indirect)
        Gpd | Gpds => {
            format!(
                "{} {}, {}",
                op.mnemonic(),
                fmt_reg(o[0]),
                fmt_member_d(bc, obj_index, o[1], o[2], resolve_consts)
            )
        }
        Gpi | Gpis => format!("{} {}, {}", op.mnemonic(), fmt_reg(o[0]), fmt_member_i(o[1], o[2])),

        // set member (direct/indirect). Operands: %obj, name, %src
        Spd | Spde | Spdeh | Spds => {
            format!(
                "{} {}, {}",
                op.mnemonic(),
                fmt_member_d(bc, obj_index, o[0], o[1], resolve_consts),
                fmt_reg(o[2])
            )
        }
        Spi | Spie | Spis => format!("{} {}, {}", op.mnemonic(), fmt_member_i(o[0], o[1]), fmt_reg(o[2])),

        Getp => format!("{} {}, {}", op.mnemonic(), fmt_reg(o[0]), fmt_reg(o[1])),
        Setp => format!("{} {}, {}", op.mnemonic(), fmt_reg(o[0]), fmt_reg(o[1])),

        Deld => {
            format!(
                "{} {}, {}",
                op.mnemonic(),
                fmt_reg(o[0]),
                fmt_member_d(bc, obj_index, o[1], o[2], resolve_consts)
            )
        }
        Deli => format!("{} {}, {}", op.mnemonic(), fmt_reg(o[0]), fmt_member_i(o[1], o[2])),

        Call | New => {
            // %dest, %func, argc, args...
            let argc = o[2] as usize;
            let args = &o[3..(3 + argc)];
            format!("{} {}, {}({})", op.mnemonic(), fmt_reg(o[0]), fmt_reg(o[1]), fmt_args(args))
        }
        Calld => {
            // %dest, %obj, *name, argc, args...
            let argc = o[3] as usize;
            let args = &o[4..(4 + argc)];
            format!(
                "{} {}, {}({})",
                op.mnemonic(),
                fmt_reg(o[0]),
                fmt_member_d(bc, obj_index, o[1], o[2], resolve_consts),
                fmt_args(args)
            )
        }
        Calli => {
            let argc = o[3] as usize;
            let args = &o[4..(4 + argc)];
            format!(
                "{} {}, {}({})",
                op.mnemonic(),
                fmt_reg(o[0]),
                fmt_member_i(o[1], o[2]),
                fmt_args(args)
            )
        }

    };

    format!("{:08} {}", insn.ip, body)
}
