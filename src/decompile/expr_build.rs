use anyhow::Result;

use crate::model::{ConstPools, Tjs2File, Tjs2Object, Variant};
use crate::vmcodes::vm as vm;

use super::expr::{BinOp, Expr, UnOp};
use super::ssa::{Phi, SsaBlock, SsaInsn, SsaProgram, Var, VarId};

#[derive(Debug, Clone)]
pub enum Stmt {
    Assign { dst: VarId, expr: Expr },
    Store { target: Expr, value: Expr },
    /// Read-modify-write update: target = target (op) rhs; optionally write the value into dst.
    Update {
        dst: Option<VarId>,
        target: Expr,
        op: BinOp,
        rhs: Expr,
    },
    Expr(Expr),
    Opaque { op: &'static str, args: Vec<Expr>, defs: Vec<VarId> },
}

#[derive(Debug, Clone)]
pub enum Terminator {
    Jmp(usize),
    Br {
        cond: Expr,
        if_true: usize,
        if_false: usize,
    },
    Ret,
    Throw(Expr),
    Exit,
    Fallthrough,
}

#[derive(Debug, Clone)]
pub struct ExprBlock {
    pub id: usize,
    pub start_pc: usize,
    pub pred: Vec<usize>,
    pub succ: Vec<usize>,
    pub phi: Vec<Phi>,
    pub stmts: Vec<Stmt>,
    pub term: Terminator,
}

#[derive(Debug, Clone)]
pub struct ExprProgram {
    pub obj_index: usize,
    pub entry_block: usize,
    pub blocks: Vec<ExprBlock>,
}

impl ExprProgram {
    pub fn from_ssa(file: &Tjs2File, obj: &Tjs2Object, ssa: &SsaProgram) -> Result<Self> {
        let mut blocks = Vec::new();
        for b in &ssa.blocks {
            blocks.push(lower_block(file, obj, b));
        }
        Ok(Self {
            obj_index: ssa.obj_index,
            entry_block: ssa.entry_block,
            blocks,
        })
    }

    pub fn dump(&self) -> String {
        let mut out = String::new();
        for b in &self.blocks {
            out.push_str(&format!(
                "-- bb{} @{} (pred={:?}, succ={:?})\n",
                b.id, b.start_pc, b.pred, b.succ
            ));
            for p in &b.phi {
                out.push_str(&format!("  {} = phi [", fmt_vid(p.result)));
                for (i, (pred, v)) in p.args.iter().enumerate() {
                    if i != 0 { out.push_str(", "); }
                    out.push_str(&format!("bb{}: {}", pred, fmt_vid(*v)));
                }
                out.push_str("]\n");
            }
            for st in &b.stmts {
                match st {
                    Stmt::Assign { dst, expr } => {
                        out.push_str(&format!("  {} = {};\n", fmt_vid(*dst), expr));
                    }
                    Stmt::Store { target, value } => {
                        out.push_str(&format!("  {} = {};\n", target, value));
                    }
                    Stmt::Update { dst, target, op, rhs } => {
                        if let Some(d) = dst {
                            out.push_str(&format!("  {} = ({} {} {}); {} = {};\n",
                                fmt_vid(*d), target, op.op_str(), rhs, target, fmt_vid(*d)));
                        } else {
                            out.push_str(&format!("  {} = ({} {} {});\n", target, target, op.op_str(), rhs));
                        }
                    }
                    Stmt::Expr(e) => out.push_str(&format!("  {};\n", e)),
                    Stmt::Opaque { op, args, defs } => {
                        if !defs.is_empty() {
                            out.push_str("  ");
                            for (i, d) in defs.iter().enumerate() {
                                if i != 0 { out.push_str(", "); }
                                out.push_str(&fmt_vid(*d));
                            }
                            out.push_str(" = ");
                        } else {
                            out.push_str("  ");
                        }
                        out.push_str(op);
                        if !args.is_empty() {
                            out.push('(');
                            for (i, a) in args.iter().enumerate() {
                                if i != 0 { out.push_str(", "); }
                                out.push_str(&a.to_string());
                            }
                            out.push(')');
                        }
                        out.push('\n');
                    }
                }
            }
            out.push_str(&format!("  ;; term = {}\n\n", fmt_term(&b.term)));
        }
        out
    }
}

fn lower_block(file: &Tjs2File, obj: &Tjs2Object, b: &SsaBlock) -> ExprBlock {
    let mut stmts = Vec::new();

    // Keep φ nodes verbatim for now (next stage will resolve them during structuring).
    let phi = b.phi.clone();

    // Lower instructions.
    for insn in &b.insns {
        lower_insn(file, obj, insn, &mut stmts);
    }

    // Derive terminator from last instruction when possible.
    let term = derive_terminator(b, b.insns.last());

    ExprBlock {
        id: b.id,
        start_pc: b.start_pc,
        pred: b.pred.clone(),
        succ: b.succ.clone(),
        phi,
        stmts,
        term,
    }
}

fn derive_terminator(b: &SsaBlock, last: Option<&SsaInsn>) -> Terminator {
    let Some(insn) = last else {
        return Terminator::Fallthrough;
    };

    match insn.op {
        vm::VM_JMP => {
            let tgt = b.succ.get(0).copied().unwrap_or(b.id);
            Terminator::Jmp(tgt)
        }
        vm::VM_JF | vm::VM_JNF => {
            let tgt = b.succ.get(0).copied().unwrap_or(b.id);
            let fall = b.succ.get(1).copied().unwrap_or(b.id);
            let flag = insn.uses.get(0).copied().map(Expr::SsaVar).unwrap_or(Expr::Flag);
            // JF: jump if !flag ; JNF: jump if flag
            let cond = if insn.op == vm::VM_JF {
                Expr::Unary(UnOp::Not, Box::new(flag))
            } else {
                flag
            };
            Terminator::Br { cond, if_true: tgt, if_false: fall }
        }
        vm::VM_RET => Terminator::Ret,
        vm::VM_THROW => {
            let e = insn.uses.get(0).copied().map(Expr::SsaVar).unwrap_or(Expr::Opaque("throw".into(), vec![]));
            Terminator::Throw(e)
        }
        vm::VM_EXTRY => Terminator::Exit,
        _ => Terminator::Fallthrough,
    }
}

fn lower_insn(file: &Tjs2File, obj: &Tjs2Object, insn: &SsaInsn, out: &mut Vec<Stmt>) {
    // Helpers
    let use_e = |i: usize| insn.uses.get(i).copied().map(Expr::SsaVar);
    let def0 = || insn.defs.get(0).copied();

    match insn.op {
        vm::VM_CP => {
            if let (Some(dst), Some(src)) = (def0(), use_e(0)) {
                out.push(Stmt::Assign { dst, expr: src });
            } else {
                out.push(Stmt::Opaque { op: insn.mnemonic, args: vec![], defs: insn.defs.clone() });
            }
        }

        vm::VM_CONST => {
            // raw_ops: [dst_reg, data_idx]
            if let Some(dst) = def0() {
                let data_idx = insn.raw_ops.get(1).copied().unwrap_or(0);
                out.push(Stmt::Assign { dst, expr: data_to_expr(file, obj, data_idx) });
            }
        }

        vm::VM_CL => {
            if let Some(dst) = def0() {
                out.push(Stmt::Assign { dst, expr: Expr::Void });
            }
        }

        vm::VM_CCL => {
            // multiple defs: clear to void
            for d in &insn.defs {
                out.push(Stmt::Assign { dst: *d, expr: Expr::Void });
            }
        }

        vm::VM_GLOBAL => {
            if let Some(dst) = def0() {
                out.push(Stmt::Assign { dst, expr: Expr::Opaque("global".into(), vec![]) });
            }
        }

        vm::VM_SETF => {
            if let Some(dst) = def0() {
                out.push(Stmt::Assign { dst, expr: Expr::Bool(true) });
            }
        }
        vm::VM_SETNF => {
            if let Some(dst) = def0() {
                out.push(Stmt::Assign { dst, expr: Expr::Bool(false) });
            }
        }

        // Flag producers (CEQ/CDEQ/CLT/CGT/CHKINS/TT/TF/NF already SSA-versioned)
        vm::VM_CEQ | vm::VM_CDEQ | vm::VM_CLT | vm::VM_CGT | vm::VM_CHKINS => {
            if let Some(dst) = def0() {
                let a = use_e(0).unwrap_or(Expr::Opaque("a".into(), vec![]));
                let b = use_e(1).unwrap_or(Expr::Opaque("b".into(), vec![]));
                let op = match insn.op {
                    vm::VM_CEQ => BinOp::Eq,
                    vm::VM_CDEQ => BinOp::StrictEq,
                    vm::VM_CLT => BinOp::Lt,
                    vm::VM_CGT => BinOp::Gt,
                    vm::VM_CHKINS => BinOp::In,
                    _ => BinOp::Eq,
                };
                out.push(Stmt::Assign { dst, expr: Expr::Binary(op, Box::new(a), Box::new(b)) });
            }
        }
        vm::VM_TT => {
            if let Some(dst) = def0() {
                let a = use_e(0).unwrap_or(Expr::Opaque("a".into(), vec![]));
                // !!a
                let e = Expr::Unary(UnOp::Not, Box::new(Expr::Unary(UnOp::Not, Box::new(a))));
                out.push(Stmt::Assign { dst, expr: e });
            }
        }
        vm::VM_TF => {
            if let Some(dst) = def0() {
                let a = use_e(0).unwrap_or(Expr::Opaque("a".into(), vec![]));
                out.push(Stmt::Assign { dst, expr: Expr::Unary(UnOp::Not, Box::new(a)) });
            }
        }
        vm::VM_NF => {
            if let Some(dst) = def0() {
                let a = use_e(0).unwrap_or(Expr::Opaque("flag".into(), vec![]));
                out.push(Stmt::Assign { dst, expr: Expr::Unary(UnOp::Not, Box::new(a)) });
            }
        }

        // Property read
        vm::VM_GPD | vm::VM_GPDS => {
            if let Some(dst) = def0() {
                let obj_e = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
                let data_idx = insn.raw_ops.get(2).copied().unwrap_or(0);
                let key_e = data_to_expr(file, obj, data_idx);
                let expr = prop_read(obj_e, key_e);
                out.push(Stmt::Assign { dst, expr });
            }
        }
        vm::VM_GPI | vm::VM_GPIS => {
            if let Some(dst) = def0() {
                let obj_e = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
                let key_e = use_e(1).unwrap_or(Expr::Opaque("key".into(), vec![]));
                let expr = Expr::Index(Box::new(obj_e), Box::new(key_e));
                out.push(Stmt::Assign { dst, expr });
            }
        }
        vm::VM_GETP => {
            if let Some(dst) = def0() {
                let prop = use_e(0).unwrap_or(Expr::Opaque("prop".into(), vec![]));
                out.push(Stmt::Assign { dst, expr: Expr::Deref(Box::new(prop)) });
            }
        }

        // Property store
        vm::VM_SPD | vm::VM_SPDE | vm::VM_SPDEH | vm::VM_SPDS => {
            let obj_e = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
            let val_e = use_e(1).unwrap_or(Expr::Opaque("val".into(), vec![]));
            let data_idx = insn.raw_ops.get(1).copied().unwrap_or(0);
            let key_e = data_to_expr(file, obj, data_idx);
            let target = prop_lvalue(obj_e, key_e);
            out.push(Stmt::Store { target, value: val_e });
        }
        vm::VM_SPI | vm::VM_SPIE | vm::VM_SPIS => {
            let obj_e = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
            let key_e = use_e(1).unwrap_or(Expr::Opaque("key".into(), vec![]));
            let val_e = use_e(2).unwrap_or(Expr::Opaque("val".into(), vec![]));
            let target = Expr::Index(Box::new(obj_e), Box::new(key_e));
            out.push(Stmt::Store { target, value: val_e });
        }
        vm::VM_SETP => {
            let prop = use_e(0).unwrap_or(Expr::Opaque("prop".into(), vec![]));
            let val = use_e(1).unwrap_or(Expr::Opaque("val".into(), vec![]));
            out.push(Stmt::Store { target: Expr::Deref(Box::new(prop)), value: val });
        }

        // Calls
        vm::VM_CALL => {
            let dst = def0();
            let func = use_e(0).unwrap_or(Expr::Opaque("func".into(), vec![]));
            let args = insn.uses.iter().skip(1).map(|v| Expr::SsaVar(*v)).collect::<Vec<_>>();
            let call = Expr::Call(Box::new(func), args);
            if let Some(d) = dst {
                out.push(Stmt::Assign { dst: d, expr: call });
            } else {
                out.push(Stmt::Expr(call));
            }
        }
        vm::VM_NEW => {
            let dst = def0();
            let ctor = use_e(0).unwrap_or(Expr::Opaque("ctor".into(), vec![]));
            let args = insn.uses.iter().skip(1).map(|v| Expr::SsaVar(*v)).collect::<Vec<_>>();
            let e = Expr::New(Box::new(ctor), args);
            if let Some(d) = dst {
                out.push(Stmt::Assign { dst: d, expr: e });
            } else {
                out.push(Stmt::Expr(e));
            }
        }
        vm::VM_CALLD => {
            let dst = def0();
            let obj_e = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
            let data_idx = insn.raw_ops.get(2).copied().unwrap_or(0);
            let key_e = data_to_expr(file, obj, data_idx);
            let args = insn.uses.iter().skip(1).map(|v| Expr::SsaVar(*v)).collect::<Vec<_>>();
            let call = method_call_or_index_call(obj_e, key_e, args);
            if let Some(d) = dst {
                out.push(Stmt::Assign { dst: d, expr: call });
            } else {
                out.push(Stmt::Expr(call));
            }
        }
        vm::VM_CALLI => {
            let dst = def0();
            let obj_e = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
            let key_e = use_e(1).unwrap_or(Expr::Opaque("key".into(), vec![]));
            let args = insn.uses.iter().skip(2).map(|v| Expr::SsaVar(*v)).collect::<Vec<_>>();
            let func = Expr::Index(Box::new(obj_e), Box::new(key_e));
            let call = Expr::Call(Box::new(func), args);
            if let Some(d) = dst {
                out.push(Stmt::Assign { dst: d, expr: call });
            } else {
                out.push(Stmt::Expr(call));
            }
        }

        // Fallback: represent as opaque op(defs, uses)
        _ => {
            let args = insn.uses.iter().map(|v| Expr::SsaVar(*v)).collect::<Vec<_>>();
            out.push(Stmt::Opaque { op: insn.mnemonic, args, defs: insn.defs.clone() });
        }
    }
}

fn data_to_expr(file: &Tjs2File, obj: &Tjs2Object, data_idx: i32) -> Expr {
    let v = obj.data.get(data_idx as usize).unwrap_or(&Variant::Unknown);
    variant_to_expr(v, &file.const_pools)
}

fn variant_to_expr(v: &Variant, pools: &ConstPools) -> Expr {
    match *v {
        Variant::Void => Expr::Void,
        Variant::NullObject => Expr::Null,
        Variant::String(i) => Expr::Str(pools.strings.get(i as usize).cloned().unwrap_or_default()),
        Variant::Octet(i) => Expr::Octet(pools.octets.get(i as usize).cloned().unwrap_or_default()),
        Variant::Real(i) => Expr::Real(*pools.doubles.get(i as usize).unwrap_or(&f64::NAN)),
        Variant::Byte(i) => Expr::Int(*pools.bytes.get(i as usize).unwrap_or(&0) as i64),
        Variant::Short(i) => Expr::Int(*pools.shorts.get(i as usize).unwrap_or(&0) as i64),
        Variant::Integer(i) => Expr::Int(*pools.ints.get(i as usize).unwrap_or(&0) as i64),
        Variant::Long(i) => Expr::Int(*pools.longs.get(i as usize).unwrap_or(&0)),
        Variant::InterObject(idx) => Expr::Opaque(format!("#InterObject({})", idx), vec![]),
        Variant::InterGenerator(idx) => Expr::Opaque(format!("#InterGenerator({})", idx), vec![]),
        Variant::Unknown => Expr::Opaque("#Unknown".into(), vec![]),
    }
}

fn prop_read(obj: Expr, key: Expr) -> Expr {
    // Prefer member when key is identifier string.
    if let Expr::Str(s) = &key {
        if is_ident_ascii(s) {
            return Expr::Member(Box::new(obj), s.clone());
        }
    }
    Expr::Index(Box::new(obj), Box::new(key))
}

fn prop_lvalue(obj: Expr, key: Expr) -> Expr {
    // Same policy as read.
    prop_read(obj, key)
}

fn method_call_or_index_call(base: Expr, key: Expr, args: Vec<Expr>) -> Expr {
    if let Expr::Str(s) = &key {
        if is_ident_ascii(s) {
            return Expr::MethodCall { base: Box::new(base), member: s.clone(), args };
        }
    }
    let f = Expr::Index(Box::new(base), Box::new(key));
    Expr::Call(Box::new(f), args)
}

pub fn is_ident_ascii(s: &str) -> bool {
    let mut it = s.chars();
    let Some(first) = it.next() else { return false; };
    let ok_first = first == '_' || first.is_ascii_alphabetic();
    if !ok_first { return false; }
    it.all(|c| c == '_' || c.is_ascii_alphanumeric())
}

fn fmt_vid(v: VarId) -> String {
    match v.var {
        Var::Reg(r) => format!("r{}#{}", r, v.ver),
        Var::Flag => format!("flag#{}", v.ver),
        Var::Exception => format!("exc#{}", v.ver),
    }
}

fn fmt_term(t: &Terminator) -> String {
    match t {
        Terminator::Jmp(b) => format!("jmp bb{}", b),
        Terminator::Br { cond, if_true, if_false } => format!("br ({}) ? bb{} : bb{}", cond, if_true, if_false),
        Terminator::Ret => "ret".into(),
        Terminator::Throw(e) => format!("throw {}", e),
        Terminator::Exit => "exit".into(),
        Terminator::Fallthrough => "fallthrough".into(),
    }
}
