use anyhow::{bail, Result};

use crate::model::Tjs2Object;
use crate::vmcodes::vm;

/// A decoded instruction. `words[0]` is the opcode; the remaining entries are operands.
#[derive(Debug, Clone)]
pub struct Insn {
    pub pc: usize,
    pub op: i32,
    pub size: usize,
    pub words: Vec<i32>,
}

impl Insn {
    pub fn mnemonic(&self) -> &'static str {
        vm::name(self.op)
    }

    pub fn operands(&self) -> &[i32] {
        &self.words[1..]
    }
}

/// Decode an entire object's code area into a linear instruction list.
pub fn decode_object(obj: &Tjs2Object) -> Result<Vec<Insn>> {
    let mut out = Vec::new();
    let code = &obj.code;
    let mut pc: usize = 0;
    while pc < code.len() {
        let insn = decode_one(code, pc)?;
        pc += insn.size;
        out.push(insn);
    }
    Ok(out)
}

pub fn decode_one(code: &[i32], pc: usize) -> Result<Insn> {
    if pc >= code.len() {
        bail!("pc out of range: {} (len={})", pc, code.len());
    }
    let op = code[pc];

    // Sizes are derived from the same patterns as `disasm.rs`.
    let size: usize = if op == vm::VM_CONST {
        3
    } else if matches!(
        op,
        vm::VM_CP
            | vm::VM_CEQ
            | vm::VM_CDEQ
            | vm::VM_CLT
            | vm::VM_CGT
            | vm::VM_CHKINS
            | vm::VM_ADDCI
            | vm::VM_CHGTHIS
    ) {
        3
    } else if matches!(
        op,
        vm::VM_CL
            | vm::VM_SRV
            | vm::VM_GLOBAL
            | vm::VM_THROW
            | vm::VM_TT
            | vm::VM_TF
            | vm::VM_SETF
            | vm::VM_SETNF
            | vm::VM_LNOT
            | vm::VM_BNOT
            | vm::VM_ASC
            | vm::VM_CHR
            | vm::VM_NUM
            | vm::VM_CHS
            | vm::VM_INV
            | vm::VM_CHKINV
            | vm::VM_TYPEOF
            | vm::VM_EVAL
            | vm::VM_EEXP
            | vm::VM_INT
            | vm::VM_REAL
            | vm::VM_STR
            | vm::VM_OCTET
    ) {
        2
    } else if op == vm::VM_CCL {
        3
    } else if op == vm::VM_JF || op == vm::VM_JNF || op == vm::VM_JMP {
        2
    } else if op == vm::VM_ENTRY {
        3
    } else if matches!(op, vm::VM_RET | vm::VM_NOP | vm::VM_NF | vm::VM_EXTRY | vm::VM_REGMEMBER | vm::VM_DEBUGGER)
    {
        1
    } else if op == vm::VM_SETP || op == vm::VM_GETP {
        3
    } else if op == vm::VM_DELD || op == vm::VM_TYPEOFD {
        4
    } else if op == vm::VM_DELI || op == vm::VM_TYPEOFI {
        4
    } else if op == vm::VM_GPD || op == vm::VM_GPDS {
        4
    } else if matches!(op, vm::VM_SPD | vm::VM_SPDE | vm::VM_SPDEH | vm::VM_SPDS) {
        4
    } else if op == vm::VM_GPI || op == vm::VM_GPIS {
        4
    } else if op == vm::VM_SPI || op == vm::VM_SPIE || op == vm::VM_SPIS {
        4
    } else if (vm::VM_INC..=vm::VM_INCP).contains(&op) {
        // INC / INCPD / INCPI / INCP
        match op - vm::VM_INC {
            0 => 2,
            1 | 2 => 4,
            3 => 3,
            _ => 1,
        }
    } else if (vm::VM_DEC..=vm::VM_DECP).contains(&op) {
        // DEC / DECPD / DECPI / DECP
        match op - vm::VM_DEC {
            0 => 2,
            1 | 2 => 4,
            3 => 3,
            _ => 1,
        }
    } else if is_op2_prop(op) {
        // OP2 with property access variants: base..=base+3.
        let base = op2_prop_base(op);
        match op - base {
            0 => 3,
            1 | 2 => 5,
            3 => 4,
            _ => 1,
        }
    } else if op == vm::VM_CALL || op == vm::VM_CALLD || op == vm::VM_CALLI || op == vm::VM_NEW {
        decode_call_size(code, pc)?
    } else {
        1
    };

    ensure(code, pc, size)?;
    let mut words = Vec::with_capacity(size);
    for j in 0..size {
        words.push(code[pc + j]);
    }
    Ok(Insn { pc, op, size, words })
}

fn is_op2_prop(op: i32) -> bool {
    matches!(
        op,
        // Each of these is the base of a 4-variant family: x/xPD/xPI/xP
        _ if (vm::VM_LOR..=vm::VM_LOR + 3).contains(&op)
            || (vm::VM_LAND..=vm::VM_LAND + 3).contains(&op)
            || (vm::VM_BOR..=vm::VM_BOR + 3).contains(&op)
            || (vm::VM_BXOR..=vm::VM_BXOR + 3).contains(&op)
            || (vm::VM_BAND..=vm::VM_BAND + 3).contains(&op)
            || (vm::VM_SAR..=vm::VM_SAR + 3).contains(&op)
            || (vm::VM_SAL..=vm::VM_SAL + 3).contains(&op)
            || (vm::VM_SR..=vm::VM_SR + 3).contains(&op)
            || (vm::VM_ADD..=vm::VM_ADD + 3).contains(&op)
            || (vm::VM_SUB..=vm::VM_SUB + 3).contains(&op)
            || (vm::VM_MOD..=vm::VM_MOD + 3).contains(&op)
            || (vm::VM_DIV..=vm::VM_DIV + 3).contains(&op)
            || (vm::VM_IDIV..=vm::VM_IDIV + 3).contains(&op)
            || (vm::VM_MUL..=vm::VM_MUL + 3).contains(&op)
    )
}

fn op2_prop_base(op: i32) -> i32 {
    // Return the family base for an opcode known to be within a family.
    for base in [
        vm::VM_LOR,
        vm::VM_LAND,
        vm::VM_BOR,
        vm::VM_BXOR,
        vm::VM_BAND,
        vm::VM_SAR,
        vm::VM_SAL,
        vm::VM_SR,
        vm::VM_ADD,
        vm::VM_SUB,
        vm::VM_MOD,
        vm::VM_DIV,
        vm::VM_IDIV,
        vm::VM_MUL,
    ] {
        if (base..=base + 3).contains(&op) {
            return base;
        }
    }
    op
}

fn decode_call_size(code: &[i32], pc: usize) -> Result<usize> {
    // Mirror `disasm::format_call` size logic.
    // Layout:
    // CALL:  op, dst, func, argc, [args...]
    // CALLD: op, dst, obj, member_data, func, argc, ...
    // CALLI: op, dst, obj, member_reg,  func, argc, ...
    // NEW:   op, dst, func, argc, ...
    let op = code[pc];
    let header = match op {
        x if x == vm::VM_CALL => 4,
        x if x == vm::VM_NEW => 4,
        _ => 5,
    };
    ensure(code, pc, header)?;
    let argc = code[pc + header - 1];

    if argc == -1 {
        Ok(header)
    } else if argc == -2 {
        ensure(code, pc, header + 1)?;
        let num = code[pc + header] as usize;
        // +1 for num, and 2*num for (type,value) pairs.
        Ok(header + 1 + num * 2)
    } else {
        let num = argc as usize;
        Ok(header + num)
    }
}

fn ensure(code: &[i32], pc: usize, need: usize) -> Result<()> {
    if pc + need > code.len() {
        bail!(
            "truncated instruction at {}: need {}, code_len {}",
            pc,
            need,
            code.len()
        );
    }
    Ok(())
}


