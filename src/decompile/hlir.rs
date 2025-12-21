use anyhow::Result;

use super::ssa::{SsaBlock, SsaInsn, SsaProgram, Var, VarId};

/// HLIR is a higher-level intermediate representation intended to be "decompile-friendly".
///
/// In this initial implementation, HLIR is deliberately conservative:
/// - It preserves basic blocks, φ-nodes, and explicit side-effects.
/// - It does not attempt structured control-flow reconstruction.
/// - It only folds a subset of simple unary/binary register operations.
///
/// The goal is to provide a stable foundation for later passes (SSA cleanup, DCE, type info,
/// control-flow structuring, and finally TJS pretty-printing).

#[derive(Debug, Clone)]
pub enum HExpr {
    Var(VarId),
    Opaque { op: &'static str, args: Vec<VarId> },
}

#[derive(Debug, Clone)]
pub enum HStmt {
    Phi { result: VarId, args: Vec<(usize, VarId)> },
    Let { defs: Vec<VarId>, expr: HExpr },
    Opaque { defs: Vec<VarId>, op: &'static str, uses: Vec<VarId> },
}

#[derive(Debug, Clone)]
pub struct HlirBlock {
    pub id: usize,
    pub start_pc: usize,
    pub pred: Vec<usize>,
    pub succ: Vec<usize>,
    pub stmts: Vec<HStmt>,
}

#[derive(Debug, Clone)]
pub struct HlirProgram {
    pub obj_index: usize,
    pub blocks: Vec<HlirBlock>,
    pub entry_block: usize,
}

impl HlirProgram {
    pub fn from_ssa(ssa: &SsaProgram) -> Result<Self> {
        let mut blocks = Vec::new();
        for b in &ssa.blocks {
            blocks.push(lower_block(b));
        }
        Ok(Self {
            obj_index: ssa.obj_index,
            blocks,
            entry_block: ssa.entry_block,
        })
    }

    pub fn dump(&self) -> String {
        let mut out = String::new();
        for b in &self.blocks {
            out.push_str(&format!(
                "-- bb{} @{} (pred={:?}, succ={:?})\n",
                b.id, b.start_pc, b.pred, b.succ
            ));
            for st in &b.stmts {
                match st {
                    HStmt::Phi { result, args } => {
                        out.push_str(&format!("  {} = phi [", fmt_vid(*result)));
                        for (i, (pred, v)) in args.iter().enumerate() {
                            if i != 0 {
                                out.push_str(", ");
                            }
                            out.push_str(&format!("bb{}: {}", pred, fmt_vid(*v)));
                        }
                        out.push_str("]\n");
                    }
                    HStmt::Let { defs, expr } => {
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
                        match expr {
                            HExpr::Var(v) => out.push_str(&fmt_vid(*v)),
                            HExpr::Opaque { op, args } => {
                                out.push_str(op);
                                if !args.is_empty() {
                                    out.push('(');
                                    for (i, a) in args.iter().enumerate() {
                                        if i != 0 {
                                            out.push_str(", ");
                                        }
                                        out.push_str(&fmt_vid(*a));
                                    }
                                    out.push(')');
                                }
                            }
                        }
                        out.push('\n');
                    }
                    HStmt::Opaque { defs, op, uses } => {
                        out.push_str("  ");
                        if !defs.is_empty() {
                            for (i, d) in defs.iter().enumerate() {
                                if i != 0 {
                                    out.push_str(", ");
                                }
                                out.push_str(&fmt_vid(*d));
                            }
                            out.push_str(" = ");
                        }
                        out.push_str(op);
                        if !uses.is_empty() {
                            out.push('(');
                            for (i, u) in uses.iter().enumerate() {
                                if i != 0 {
                                    out.push_str(", ");
                                }
                                out.push_str(&fmt_vid(*u));
                            }
                            out.push(')');
                        }
                        out.push('\n');
                    }
                }
            }
        }
        out
    }
}

fn lower_block(b: &SsaBlock) -> HlirBlock {
    let mut stmts = Vec::new();
    for p in &b.phi {
        stmts.push(HStmt::Phi {
            result: p.result,
            args: p.args.clone(),
        });
    }
    for insn in &b.insns {
        stmts.push(lower_insn(insn));
    }
    HlirBlock {
        id: b.id,
        start_pc: b.start_pc,
        pred: b.pred.clone(),
        succ: b.succ.clone(),
        stmts,
    }
}

fn lower_insn(insn: &SsaInsn) -> HStmt {
    // Very conservative lowering for now.
    // As we learn more semantics, this can fold into structured expressions.
    if insn.op == -1 {
        return HStmt::Opaque {
            defs: insn.defs.clone(),
            op: insn.mnemonic,
            uses: insn.uses.clone(),
        };
    }

    if insn.mnemonic == "VM_CP" && insn.defs.len() == 1 && insn.uses.len() == 1 {
        return HStmt::Let {
            defs: insn.defs.clone(),
            expr: HExpr::Var(insn.uses[0]),
        };
    }

    HStmt::Opaque {
        defs: insn.defs.clone(),
        op: insn.mnemonic,
        uses: insn.uses.clone(),
    }
}

fn fmt_vid(v: VarId) -> String {
    match v.var {
        Var::Reg(r) => format!("r{}#{}", r, v.ver),
        Var::Flag => format!("flag#{}", v.ver),
        Var::Exception => format!("exc#{}", v.ver),
    }
}

