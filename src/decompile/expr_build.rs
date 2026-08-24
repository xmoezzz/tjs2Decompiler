use anyhow::Result;

use crate::model::{ConstPools, Tjs2File, Tjs2Object, Variant};
use crate::vmcodes::vm;

use super::expr::{BinOp, Expr, UnOp};
use super::ssa::{Phi, SsaBlock, SsaInsn, SsaProgram, Var, VarId};

const FAT_NORMAL: i32 = 0;
const FAT_EXPAND: i32 = 1;
const FAT_UNNAMED_EXPAND: i32 = 2;

#[derive(Debug, Clone)]
pub enum Stmt {
    Assign {
        dst: VarId,
        expr: Expr,
    },
    Store {
        target: Expr,
        value: Expr,
    },
    /// A source-level class member declaration.  The compiler emits this as
    /// VM_SPDS on objthis from the ctClass context (AddLocalVariable).
    MemberDecl {
        name: String,
        value: Expr,
    },
    /// Read-modify-write update: target = target (op) rhs; optionally write the value into dst.
    Update {
        dst: Option<VarId>,
        target: Expr,
        op: BinOp,
        rhs: Expr,
    },
    IncDec {
        dst: Option<VarId>,
        target: Expr,
        increment: bool,
    },
    Expr(Expr),
    Opaque {
        op: &'static str,
        args: Vec<Expr>,
        defs: Vec<VarId>,
    },
}

#[derive(Debug, Clone)]
pub enum Terminator {
    Jmp(usize),
    Br {
        cond: Expr,
        if_true: usize,
        if_false: usize,
    },
    Ret(Expr),
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
    /// Exception SSA value injected at this handler entry by EXCIN.  Keep this
    /// as block metadata because copy propagation may remove the EXCDEF
    /// assignment that originally made the value visible in `stmts`.
    pub exception_in: Option<VarId>,
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
                    if i != 0 {
                        out.push_str(", ");
                    }
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
                    Stmt::MemberDecl { name, value } => {
                        out.push_str(&format!("  var {} = {};\n", name, value));
                    }
                    Stmt::Update {
                        dst,
                        target,
                        op,
                        rhs,
                    } => {
                        if let Some(d) = dst {
                            out.push_str(&format!(
                                "  {} = ({} {} {}); {} = {};\n",
                                fmt_vid(*d),
                                target,
                                op.op_str(),
                                rhs,
                                target,
                                fmt_vid(*d)
                            ));
                        } else {
                            out.push_str(&format!(
                                "  {} = ({} {} {});\n",
                                target,
                                target,
                                op.op_str(),
                                rhs
                            ));
                        }
                    }
                    Stmt::IncDec {
                        dst,
                        target,
                        increment,
                    } => {
                        let op = if *increment { "++" } else { "--" };
                        if let Some(d) = dst {
                            out.push_str(&format!("  {} = {}{};\n", fmt_vid(*d), op, target));
                        } else {
                            out.push_str(&format!("  {}{};\n", op, target));
                        }
                    }
                    Stmt::Expr(e) => out.push_str(&format!("  {};\n", e)),
                    Stmt::Opaque { op, args, defs } => {
                        if !defs.is_empty() {
                            out.push_str("  ");
                            for (i, d) in defs.iter().enumerate() {
                                if i != 0 {
                                    out.push_str(", ");
                                }
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
                                if i != 0 {
                                    out.push_str(", ");
                                }
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

    // EXCIN is an implicit handler-entry definition.  Preserve it separately
    // from executable statements so later propagation/DCE cannot erase the
    // information needed to bind the generated catch parameter.
    let exception_in = b.insns.iter().find_map(|insn| {
        if insn.mnemonic.eq_ignore_ascii_case("EXCIN") {
            insn.defs
                .first()
                .copied()
                .filter(|v| matches!(v.var, Var::Exception))
        } else {
            None
        }
    });

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
        exception_in,
        stmts,
        term,
    }
}

fn ssa_value_expr(v: VarId) -> Expr {
    if matches!(v.var, Var::Reg(-2)) {
        Expr::ScopeProxy
    } else {
        Expr::SsaVar(v)
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
            let flag = insn
                .uses
                .get(0)
                .copied()
                .map(ssa_value_expr)
                .unwrap_or(Expr::Flag);
            // TJS2 VM semantics: JF jumps when flag is true; JNF jumps when false.
            let cond = if insn.op == vm::VM_JF {
                flag
            } else {
                Expr::Unary(UnOp::Not, Box::new(flag))
            };
            Terminator::Br {
                cond,
                if_true: tgt,
                if_false: fall,
            }
        }
        vm::VM_RET => {
            // A RET with a CFG successor is a protected RET: the official VM
            // returns from the ENTRY-created ExecuteCode level and resumes at
            // RET+1.  Only a level-zero RET has no successor and is a true
            // function return.
            if !b.succ.is_empty() {
                Terminator::Exit
            } else {
                let result = insn
                    .uses
                    .get(0)
                    .copied()
                    .map(ssa_value_expr)
                    .unwrap_or(Expr::Void);
                Terminator::Ret(result)
            }
        },
        vm::VM_THROW => {
            let e = insn
                .uses
                .get(0)
                .copied()
                .map(ssa_value_expr)
                .unwrap_or(Expr::Opaque("throw".into(), vec![]));
            Terminator::Throw(e)
        }
        vm::VM_EXTRY => Terminator::Exit,
        _ => Terminator::Fallthrough,
    }
}

fn lower_insn(file: &Tjs2File, obj: &Tjs2Object, insn: &SsaInsn, out: &mut Vec<Stmt>) {
    // Helpers
    let use_e = |i: usize| insn.uses.get(i).copied().map(ssa_value_expr);
    let def0 = || insn.defs.get(0).copied();

    // EXCIN is an implicit SSA definition bound by the generated catch
    // parameter; it has no executable VM statement of its own.
    if insn.mnemonic.eq_ignore_ascii_case("EXCIN") {
        return;
    }

    // SSA inserts EXCDEF at a catch entry to materialize the current exception
    // token into the handler register.  It is not a real VM opcode and lowers
    // to an ordinary SSA assignment.
    if insn.mnemonic.eq_ignore_ascii_case("EXCDEF") {
        if let (Some(dst), Some(src)) = (def0(), use_e(0)) {
            out.push(Stmt::Assign { dst, expr: src });
        }
        return;
    }

    match insn.op {
        vm::VM_SRV => {
            if let (Some(dst), Some(src)) = (def0(), use_e(0)) {
                out.push(Stmt::Assign { dst, expr: src });
            }
        }

        vm::VM_CP => {
            if let (Some(dst), Some(src)) = (def0(), use_e(0)) {
                out.push(Stmt::Assign { dst, expr: src });
            } else {
                out.push(Stmt::Opaque {
                    op: insn.mnemonic,
                    args: vec![],
                    defs: insn.defs.clone(),
                });
            }
        }

        vm::VM_CONST => {
            // raw_ops: [dst_reg, data_idx]
            if let Some(dst) = def0() {
                let data_idx = insn.raw_ops.get(1).copied().unwrap_or(0);
                out.push(Stmt::Assign {
                    dst,
                    expr: data_to_expr(file, obj, data_idx),
                });
            }
        }

        vm::VM_CL => {
            if let Some(dst) = def0() {
                out.push(Stmt::Assign {
                    dst,
                    expr: Expr::Void,
                });
            }
        }

        vm::VM_CCL => {
            // multiple defs: clear to void
            for d in &insn.defs {
                out.push(Stmt::Assign {
                    dst: *d,
                    expr: Expr::Void,
                });
            }
        }

        vm::VM_GLOBAL => {
            if let Some(dst) = def0() {
                out.push(Stmt::Assign {
                    dst,
                    expr: Expr::Opaque("global".into(), vec![]),
                });
            }
        }

        vm::VM_SETF => {
            if let (Some(dst), Some(flag)) = (def0(), use_e(0)) {
                out.push(Stmt::Assign { dst, expr: flag });
            }
        }
        vm::VM_SETNF => {
            if let (Some(dst), Some(flag)) = (def0(), use_e(0)) {
                out.push(Stmt::Assign {
                    dst,
                    expr: Expr::Unary(UnOp::Not, Box::new(flag)),
                });
            }
        }

        // Comparison instructions write the VM condition flag. The compiler maps
        // source `<` to VM_CLT and source `>` to VM_CGT.
        vm::VM_CEQ | vm::VM_CDEQ | vm::VM_CLT | vm::VM_CGT => {
            if let Some(dst) = def0() {
                let a = use_e(0).unwrap_or(Expr::Opaque("a".into(), vec![]));
                let b = use_e(1).unwrap_or(Expr::Opaque("b".into(), vec![]));
                let op = match insn.op {
                    vm::VM_CEQ => BinOp::Eq,
                    vm::VM_CDEQ => BinOp::StrictEq,
                    vm::VM_CLT => BinOp::Lt,
                    vm::VM_CGT => BinOp::Gt,
                    _ => unreachable!(),
                };
                out.push(Stmt::Assign {
                    dst,
                    expr: Expr::Binary(op, Box::new(a), Box::new(b)),
                });
            }
        }

        // CHKINS replaces its first register with the instance-test result.
        vm::VM_CHKINS => {
            if let Some(dst) = def0() {
                let value = use_e(0).unwrap_or(Expr::Opaque("value".into(), vec![]));
                let class = use_e(1).unwrap_or(Expr::Opaque("class".into(), vec![]));
                out.push(Stmt::Assign {
                    dst,
                    expr: Expr::Binary(BinOp::InstanceOf, Box::new(value), Box::new(class)),
                });
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
                out.push(Stmt::Assign {
                    dst,
                    expr: Expr::Unary(UnOp::Not, Box::new(a)),
                });
            }
        }
        vm::VM_NF => {
            if let Some(dst) = def0() {
                let a = use_e(0).unwrap_or(Expr::Opaque("flag".into(), vec![]));
                out.push(Stmt::Assign {
                    dst,
                    expr: Expr::Unary(UnOp::Not, Box::new(a)),
                });
            }
        }

        // INC/DEC families. The property variants are read-modify-write operations
        // on the property itself; do not collapse them to arithmetic on the object
        // register. OperateProperty*0 returns the updated value in the optional
        // result register, so Stmt::IncDec preserves both the exact ++/--
        // operation and its optional result.
        x if (vm::VM_INC..=vm::VM_INCP).contains(&x)
            || (vm::VM_DEC..=vm::VM_DECP).contains(&x) =>
        {
            let (base, op) = if (vm::VM_INC..=vm::VM_INCP).contains(&x) {
                (vm::VM_INC, BinOp::Add)
            } else {
                (vm::VM_DEC, BinOp::Sub)
            };
            match x - base {
                0 => {
                    // inc/dec %r: SSA already gives us the old value as use[0]
                    // and the updated register version as def[0].
                    if let (Some(dst), Some(src)) = (def0(), use_e(0)) {
                        out.push(Stmt::Assign {
                            dst,
                            expr: Expr::Binary(op, Box::new(src), Box::new(Expr::Int(1))),
                        });
                    }
                }
                1 => {
                    // incpd/decpd %res, %obj.*data
                    let base_obj = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
                    let data_idx = insn.raw_ops.get(2).copied().unwrap_or(0);
                    let target = prop_lvalue(base_obj, data_to_expr(file, obj, data_idx));
                    out.push(Stmt::IncDec {
                        dst: def0(),
                        target,
                        increment: op == BinOp::Add,
                    });
                }
                2 => {
                    // incpi/decpi %res, %obj.%key
                    let base_obj = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
                    let key = use_e(1).unwrap_or(Expr::Opaque("key".into(), vec![]));
                    out.push(Stmt::IncDec {
                        dst: def0(),
                        target: Expr::Index(Box::new(base_obj), Box::new(key)),
                        increment: op == BinOp::Add,
                    });
                }
                3 => {
                    // incp/decp %res, %property: operate on the property closure
                    // itself, represented by the TJS dereference syntax.
                    let prop = use_e(0).unwrap_or(Expr::Opaque("prop".into(), vec![]));
                    out.push(Stmt::IncDec {
                        dst: def0(),
                        target: Expr::Deref(Box::new(prop)),
                        increment: op == BinOp::Add,
                    });
                }
                _ => unreachable!(),
            }
        }

        // Binary read-modify-write families, including property variants.
        // The PD/PI/P forms update the property and optionally return the updated
        // value; lowering them as arithmetic on the object register loses the
        // member access entirely.
        x if op2_prop_info(x).is_some() => {
            let (base, op) = op2_prop_info(x).expect("guarded above");
            match x - base {
                0 => {
                    if let (Some(dst), Some(lhs), Some(rhs)) = (def0(), use_e(0), use_e(1)) {
                        out.push(Stmt::Assign {
                            dst,
                            expr: Expr::Binary(op, Box::new(lhs), Box::new(rhs)),
                        });
                    }
                }
                1 => {
                    let base_obj = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
                    let rhs = use_e(1).unwrap_or(Expr::Opaque("rhs".into(), vec![]));
                    let data_idx = insn.raw_ops.get(2).copied().unwrap_or(0);
                    let target = prop_lvalue(base_obj, data_to_expr(file, obj, data_idx));
                    out.push(Stmt::Update {
                        dst: def0(),
                        target,
                        op,
                        rhs,
                    });
                }
                2 => {
                    let base_obj = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
                    let key = use_e(1).unwrap_or(Expr::Opaque("key".into(), vec![]));
                    let rhs = use_e(2).unwrap_or(Expr::Opaque("rhs".into(), vec![]));
                    out.push(Stmt::Update {
                        dst: def0(),
                        target: Expr::Index(Box::new(base_obj), Box::new(key)),
                        op,
                        rhs,
                    });
                }
                3 => {
                    let prop = use_e(0).unwrap_or(Expr::Opaque("prop".into(), vec![]));
                    let rhs = use_e(1).unwrap_or(Expr::Opaque("rhs".into(), vec![]));
                    out.push(Stmt::Update {
                        dst: def0(),
                        target: Expr::Deref(Box::new(prop)),
                        op,
                        rhs,
                    });
                }
                _ => unreachable!(),
            }
        }

        // Unary operators and conversions.
        vm::VM_LNOT
        | vm::VM_BNOT
        | vm::VM_CHS
        | vm::VM_ASC
        | vm::VM_CHR
        | vm::VM_NUM
        | vm::VM_TYPEOF
        | vm::VM_INT
        | vm::VM_REAL
        | vm::VM_STR
        | vm::VM_OCTET
        | vm::VM_INV
        | vm::VM_CHKINV => {
            if let (Some(dst), Some(src)) = (def0(), use_e(0)) {
                let op = match insn.op {
                    vm::VM_LNOT => UnOp::Not,
                    vm::VM_BNOT => UnOp::BitNot,
                    vm::VM_CHS => UnOp::Neg,
                    // Runtime semantics: ASC is first-character code (#), while
                    // CHR builds a one-character string from a numeric code ($).
                    vm::VM_ASC => UnOp::CharCode,
                    vm::VM_CHR => UnOp::CharFromCode,
                    vm::VM_NUM => UnOp::Num,
                    vm::VM_TYPEOF => UnOp::Typeof,
                    vm::VM_INT => UnOp::Int,
                    vm::VM_REAL => UnOp::Real,
                    vm::VM_STR => UnOp::String,
                    vm::VM_OCTET => UnOp::Octet,
                    vm::VM_INV => UnOp::Invalidate,
                    vm::VM_CHKINV => UnOp::IsValid,
                    _ => unreachable!(),
                };
                out.push(Stmt::Assign {
                    dst,
                    expr: Expr::Unary(op, Box::new(src)),
                });
            }
        }

        // CHGTHIS mutates the closure context of the destination value. In source
        // form this is the `incontextof` operator, not a change to the currently
        // executing function's `this`.
        vm::VM_CHGTHIS => {
            if let (Some(dst), Some(clo), Some(ctx)) = (def0(), use_e(0), use_e(1)) {
                out.push(Stmt::Assign {
                    dst,
                    expr: Expr::Binary(BinOp::InContextOf, Box::new(clo), Box::new(ctx)),
                });
            }
        }

        // Property typeof/delete variants need their member operand reconstructed
        // here because SSA's use list intentionally contains registers only.
        vm::VM_TYPEOFD => {
            let dst = def0();
            let base = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
            let data_idx = insn.raw_ops.get(2).copied().unwrap_or(0);
            let target = prop_read(base, data_to_expr(file, obj, data_idx));
            let e = Expr::Unary(UnOp::Typeof, Box::new(target));
            if let Some(d) = dst {
                out.push(Stmt::Assign { dst: d, expr: e });
            } else {
                out.push(Stmt::Expr(e));
            }
        }
        vm::VM_TYPEOFI => {
            let dst = def0();
            let base = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
            let key = use_e(1).unwrap_or(Expr::Opaque("key".into(), vec![]));
            let e = Expr::Unary(
                UnOp::Typeof,
                Box::new(Expr::Index(Box::new(base), Box::new(key))),
            );
            if let Some(d) = dst {
                out.push(Stmt::Assign { dst: d, expr: e });
            } else {
                out.push(Stmt::Expr(e));
            }
        }
        vm::VM_DELD => {
            let dst = def0();
            let base = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
            let data_idx = insn.raw_ops.get(2).copied().unwrap_or(0);
            let target = prop_lvalue(base, data_to_expr(file, obj, data_idx));
            let e = Expr::Unary(UnOp::Delete, Box::new(target));
            if let Some(d) = dst {
                out.push(Stmt::Assign { dst: d, expr: e });
            } else {
                out.push(Stmt::Expr(e));
            }
        }
        vm::VM_DELI => {
            let dst = def0();
            let base = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
            let key = use_e(1).unwrap_or(Expr::Opaque("key".into(), vec![]));
            let e = Expr::Unary(
                UnOp::Delete,
                Box::new(Expr::Index(Box::new(base), Box::new(key))),
            );
            if let Some(d) = dst {
                out.push(Stmt::Assign { dst: d, expr: e });
            } else {
                out.push(Stmt::Expr(e));
            }
        }

        // Property read
        vm::VM_GPD | vm::VM_GPDS => {
            if let Some(dst) = def0() {
                let obj_e = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
                let data_idx = insn.raw_ops.get(2).copied().unwrap_or(0);
                let key_e = data_to_expr(file, obj, data_idx);
                let target = prop_read(obj_e, key_e);
                let expr = if insn.op == vm::VM_GPDS {
                    Expr::Unary(UnOp::IgnoreProp, Box::new(target))
                } else {
                    target
                };
                out.push(Stmt::Assign { dst, expr });
            }
        }
        vm::VM_GPI | vm::VM_GPIS => {
            if let Some(dst) = def0() {
                let obj_e = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
                let key_e = use_e(1).unwrap_or(Expr::Opaque("key".into(), vec![]));
                let target = Expr::Index(Box::new(obj_e), Box::new(key_e));
                let expr = if insn.op == vm::VM_GPIS {
                    Expr::Unary(UnOp::IgnoreProp, Box::new(target))
                } else {
                    target
                };
                out.push(Stmt::Assign { dst, expr });
            }
        }
        vm::VM_GETP => {
            if let Some(dst) = def0() {
                let prop = use_e(0).unwrap_or(Expr::Opaque("prop".into(), vec![]));
                out.push(Stmt::Assign {
                    dst,
                    expr: Expr::Deref(Box::new(prop)),
                });
            }
        }

        // Property stores retain the dispatch flags in the typed expression.
        // SPDEH creates a hidden member and has no ordinary source-level
        // assignment equivalent, so leave an opaque semantic marker which the
        // high-level semantic audit will reject unless a declaration pattern
        // consumes it first.
        vm::VM_SPD | vm::VM_SPDE | vm::VM_SPDEH | vm::VM_SPDS => {
            let obj_e = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
            let val_e = use_e(1).unwrap_or(Expr::Opaque("val".into(), vec![]));
            let data_idx = insn.raw_ops.get(1).copied().unwrap_or(0);
            let key_e = data_to_expr(file, obj, data_idx);

            if insn.op == vm::VM_SPDEH {
                out.push(Stmt::Opaque {
                    op: "__tjs2dec_hidden_member_store",
                    args: vec![obj_e, key_e, val_e],
                    defs: vec![],
                });
            } else if (insn.op == vm::VM_SPD && !matches!(obj_e, Expr::ScopeProxy))
                || (insn.op == vm::VM_SPDE && matches!(obj_e, Expr::ScopeProxy))
            {
                out.push(Stmt::Opaque {
                    op: "__tjs2dec_unrepresentable_store_flags",
                    args: vec![obj_e, key_e, val_e],
                    defs: vec![],
                });
            } else if insn.op == vm::VM_SPDS && obj.context_type == 6 {
                if let Expr::Str(name) = &key_e {
                    out.push(Stmt::MemberDecl {
                        name: name.clone(),
                        value: val_e,
                    });
                } else {
                    let target = Expr::Unary(
                        UnOp::IgnoreProp,
                        Box::new(prop_lvalue(obj_e, key_e)),
                    );
                    out.push(Stmt::Store { target, value: val_e });
                }
            } else {
                let plain = prop_lvalue(obj_e, key_e);
                let target = if insn.op == vm::VM_SPDS {
                    Expr::Unary(UnOp::IgnoreProp, Box::new(plain))
                } else {
                    plain
                };
                out.push(Stmt::Store { target, value: val_e });
            }
        }
        vm::VM_SPI | vm::VM_SPIE | vm::VM_SPIS => {
            let obj_e = use_e(0).unwrap_or(Expr::Opaque("obj".into(), vec![]));
            let key_e = use_e(1).unwrap_or(Expr::Opaque("key".into(), vec![]));
            let val_e = use_e(2).unwrap_or(Expr::Opaque("val".into(), vec![]));
            if insn.op == vm::VM_SPI && !matches!(obj_e, Expr::ScopeProxy)
                || insn.op == vm::VM_SPIE && matches!(obj_e, Expr::ScopeProxy)
            {
                out.push(Stmt::Opaque {
                    op: "__tjs2dec_unrepresentable_store_flags",
                    args: vec![obj_e, key_e, val_e],
                    defs: vec![],
                });
            } else {
                let plain = Expr::Index(Box::new(obj_e), Box::new(key_e));
                let target = if insn.op == vm::VM_SPIS {
                    Expr::Unary(UnOp::IgnoreProp, Box::new(plain))
                } else {
                    plain
                };
                out.push(Stmt::Store { target, value: val_e });
            }
        }
        vm::VM_SETP => {
            let prop = use_e(0).unwrap_or(Expr::Opaque("prop".into(), vec![]));
            let val = use_e(1).unwrap_or(Expr::Opaque("val".into(), vec![]));
            out.push(Stmt::Store {
                target: Expr::Deref(Box::new(prop)),
                value: val,
            });
        }

        // Calls
        vm::VM_CALL => {
            let dst = def0();
            let func = use_e(0).unwrap_or(Expr::Opaque("func".into(), vec![]));
            let args = lower_call_args(insn, 2, 3, 1);
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
            let args = lower_call_args(insn, 2, 3, 1);
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
            let args = lower_call_args(insn, 3, 4, 1);
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
            let args = lower_call_args(insn, 3, 4, 2);
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
            let args = insn
                .uses
                .iter()
                .map(|v| ssa_value_expr(*v))
                .collect::<Vec<_>>();
            out.push(Stmt::Opaque {
                op: insn.mnemonic,
                args,
                defs: insn.defs.clone(),
            });
        }
    }
}

fn op2_prop_info(op: i32) -> Option<(i32, BinOp)> {
    for (base, binop) in [
        (vm::VM_LOR, BinOp::LogOr),
        (vm::VM_LAND, BinOp::LogAnd),
        (vm::VM_BOR, BinOp::BitOr),
        (vm::VM_BXOR, BinOp::BitXor),
        (vm::VM_BAND, BinOp::BitAnd),
        (vm::VM_SAR, BinOp::Shr),
        (vm::VM_SAL, BinOp::Shl),
        (vm::VM_SR, BinOp::UShr),
        (vm::VM_ADD, BinOp::Add),
        (vm::VM_SUB, BinOp::Sub),
        (vm::VM_MOD, BinOp::Mod),
        (vm::VM_DIV, BinOp::Div),
        (vm::VM_IDIV, BinOp::IDiv),
        (vm::VM_MUL, BinOp::Mul),
    ] {
        if (base..=base + 3).contains(&op) {
            return Some((base, binop));
        }
    }
    None
}

fn lower_call_args(
    insn: &SsaInsn,
    argc_index: usize,
    arg_data_start: usize,
    use_start: usize,
) -> Vec<Expr> {
    let argc = insn.raw_ops.get(argc_index).copied().unwrap_or(0);

    if argc == -1 {
        // TJS2's omitted-argument call syntax forwards the current argument list.
        return vec![Expr::ArgForwardAll];
    }

    if argc == -2 {
        let count = insn
            .raw_ops
            .get(arg_data_start)
            .copied()
            .unwrap_or(0)
            .max(0) as usize;
        let mut out = Vec::with_capacity(count);
        let mut use_cursor = use_start;
        for i in 0..count {
            let ty = insn
                .raw_ops
                .get(arg_data_start + 1 + i * 2)
                .copied()
                .unwrap_or(-1);
            match ty {
                FAT_NORMAL => {
                    if let Some(v) = insn.uses.get(use_cursor).copied() {
                        out.push(ssa_value_expr(v));
                        use_cursor += 1;
                    } else {
                        out.push(Expr::Opaque("__tjs2dec_missing_arg".into(), vec![]));
                    }
                }
                FAT_EXPAND => {
                    if let Some(v) = insn.uses.get(use_cursor).copied() {
                        out.push(Expr::ArgExpand(Box::new(ssa_value_expr(v))));
                        use_cursor += 1;
                    } else {
                        out.push(Expr::ArgExpand(Box::new(Expr::Opaque(
                            "__tjs2dec_missing_arg".into(),
                            vec![],
                        ))));
                    }
                }
                FAT_UNNAMED_EXPAND => out.push(Expr::ArgUnnamedExpand),
                other => out.push(Expr::Opaque(
                    format!("__tjs2dec_bad_fat_{}", other),
                    vec![],
                )),
            }
        }
        return out;
    }

    let count = argc.max(0) as usize;
    insn.uses
        .iter()
        .skip(use_start)
        .take(count)
        .copied()
        .map(ssa_value_expr)
        .collect()
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
        Variant::InterObject(idx) => Expr::ObjectRef(idx),
        Variant::InterGenerator(idx) => Expr::GeneratorRef(idx),
        Variant::Unknown => Expr::Opaque("#Unknown".into(), vec![]),
    }
}

fn prop_read(obj: Expr, key: Expr) -> Expr {
    // GPD/SPD/*PD encode a direct string member dispatch. Re-emitting a
    // non-identifier key through bracket syntax would compile as the indirect
    // PI family and can change numeric/string dispatch behavior. Fail closed.
    if let Expr::Str(s) = &key {
        if is_ident_ascii(s) {
            return Expr::Member(Box::new(obj), s.clone());
        }
    }
    Expr::Opaque("__tjs2dec_unrepresentable_direct_property".into(), vec![obj, key])
}

fn prop_lvalue(obj: Expr, key: Expr) -> Expr {
    prop_read(obj, key)
}

fn method_call_or_index_call(base: Expr, key: Expr, args: Vec<Expr>) -> Expr {
    if let Expr::Str(s) = &key {
        if is_ident_ascii(s) {
            return Expr::MethodCall {
                base: Box::new(base),
                member: s.clone(),
                args,
            };
        }
    }
    let mut opaque_args = vec![base, key];
    opaque_args.extend(args);
    Expr::Opaque("__tjs2dec_unrepresentable_direct_call".into(), opaque_args)
}

pub fn is_ident_ascii(s: &str) -> bool {
    let mut it = s.chars();
    let Some(first) = it.next() else {
        return false;
    };
    let ok_first = first == '_' || first.is_ascii_alphabetic();
    if !ok_first {
        return false;
    }
    it.all(|c| c == '_' || c.is_ascii_alphanumeric())
}

fn fmt_vid(v: VarId) -> String {
    match v.var {
        Var::Reg(r) => format!("r{}#{}", r, v.ver),
        Var::Flag => format!("flag#{}", v.ver),
        Var::Result => format!("result#{}", v.ver),
        Var::Exception => format!("exc#{}", v.ver),
    }
}

fn fmt_term(t: &Terminator) -> String {
    match t {
        Terminator::Jmp(b) => format!("jmp bb{}", b),
        Terminator::Br {
            cond,
            if_true,
            if_false,
        } => format!("br ({}) ? bb{} : bb{}", cond, if_true, if_false),
        Terminator::Ret(e) => format!("ret {}", e),
        Terminator::Throw(e) => format!("throw {}", e),
        Terminator::Exit => "exit".into(),
        Terminator::Fallthrough => "fallthrough".into(),
    }
}
