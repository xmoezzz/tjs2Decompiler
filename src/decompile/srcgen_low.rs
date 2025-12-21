use anyhow::Result;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use crate::model::{Tjs2File, Tjs2Object};

use super::cfg::Cfg;
use super::expr::Expr;
use super::expr_build::{ExprBlock, ExprProgram, Stmt, Terminator};
use super::ssa::{Var, VarId};

pub struct SrcgenOptions {
    pub inline: bool,
}

impl Default for SrcgenOptions {
    fn default() -> Self {
        SrcgenOptions { inline: true }
    }
}

pub fn dump_src_file(file: &Tjs2File, _opt: SrcgenOptions) -> Result<String> {
    let mut out = String::new();

    writeln!(
        out,
        "// Decompiled from TJS2 bytecode (decompile_low)\n// objects: {}\n",
        file.objects.len()
    )?;
    writeln!(out, "var __tjs2dec_objs = [];\n")?;

    for obj in &file.objects {
        if obj.code.is_empty() {
            continue;
        }

        writeln!(
            out,
            "// == object {}: {} ==",
            obj.index,
            obj.name.as_deref().unwrap_or("<anonymous>")
        )?;

        let lhs = obj_lhs(obj.index, obj.name.as_deref());
        writeln!(out, "{} = function() {{", lhs)?;

        let cfg = Cfg::build(obj)?;
        let ssa = super::ssa::SsaProgram::from_cfg(&cfg)?;
        let prog = ExprProgram::from_ssa(file, obj, &ssa)?;

        emit_function(&mut out, &prog, &cfg, obj)?;

        writeln!(out, "}};\n")?;
    }

    Ok(out)
}

fn obj_lhs(idx: usize, name: Option<&str>) -> String {
    if let Some(n) = name {
        let n = n.trim();
        if !n.is_empty() {
            return n.to_string();
        }
    }
    format!("__tjs2dec_objs[{}]", idx)
}

fn fmt_vid(vid: VarId) -> String {
    match vid.var {
        Var::Reg(r) => format!("__r{}_{}", r, vid.ver),
        Var::Flag => format!("__flag_{}", vid.ver),
        Var::Exception => format!("__exc_{}", vid.ver),
    }
}

fn emit_function(out: &mut String, prog: &ExprProgram, cfg: &Cfg, obj: &Tjs2Object) -> Result<()> {
    // helper to keep opaque ops executable
    writeln!(out, "  function __tjs2dec_opaque(op) {{ return void; }}")?;

    let fmt_var = |v: VarId| fmt_vid(v);

    // collect + declare SSA vars
    let vars = collect_all_vars(prog);
    if !vars.is_empty() {
        for name in vars {
            writeln!(out, "  var {} = void;", name)?;
        }
    }

    writeln!(out, "  var __rv = void;")?;
    writeln!(out, "  var __bb = {};", prog.entry_block)?;
    writeln!(out, "  var __exobj = void;")?;
    writeln!(out, "  while(true) {{")?;
    writeln!(out, "    switch(__bb) {{")?;

    // precompute phi edge moves: (pred, succ) -> [(dst, src)...]
    let phi_moves = build_phi_edge_moves(prog);

    for b in &prog.blocks {
        writeln!(out, "      case {}: {{", b.id)?;

        // optional: if this block is a catch entry (by pc), you may want to materialize __exobj.
        // We do NOT guess register bindings here; SSA should already encode catch semantics.

        let exc_succ = exceptional_succ(b);

        if let Some(ex) = exc_succ {
            writeln!(out, "        try {{")?;
            emit_block_body(out, b, &fmt_var, &phi_moves, obj, ex)?;
            writeln!(out, "        }} catch(__e) {{")?;
            writeln!(out, "          __exobj = __e;")?;
            emit_phi_parallel_copies(out, &fmt_var, &phi_moves, b.id, ex, "          ")?;
            writeln!(out, "          __bb = {};", ex)?;
            writeln!(out, "          continue;")?;
            writeln!(out, "        }}")?;
        } else {
            emit_block_body(out, b, &fmt_var, &phi_moves, obj, usize::MAX)?;
        }

        writeln!(out, "      }}")?;
    }

    // default escape hatch
    writeln!(out, "      default: return __rv;")?;
    writeln!(out, "    }}")?;
    writeln!(out, "  }}")?;

    Ok(())
}

fn emit_block_body(
    out: &mut String,
    b: &ExprBlock,
    fmt_var: &dyn Fn(VarId) -> String,
    phi_moves: &HashMap<(usize, usize), Vec<(VarId, VarId)>>,
    _obj: &Tjs2Object,
    _exc_succ: usize,
) -> Result<()> {
    for st in &b.stmts {
        emit_stmt(out, st, fmt_var)?;
    }

    emit_terminator(out, b, fmt_var, phi_moves)?;

    Ok(())
}

fn emit_stmt(out: &mut String, st: &Stmt, fmt_var: &dyn Fn(VarId) -> String) -> Result<()> {
    match st {
        Stmt::Assign { dst, expr } => {
            writeln!(
                out,
                "        {} = {};",
                fmt_var(*dst),
                expr.to_tjs_with(fmt_var)
            )?;
        }
        Stmt::Store { target, value } => {
            writeln!(
                out,
                "        {} = {};",
                target.to_tjs_with(fmt_var),
                value.to_tjs_with(fmt_var)
            )?;
        }
        Stmt::Update { dst, target, op, rhs } => {
            // Evaluate once to avoid re-evaluating target if it's not trivial.
            // This is still a static lowering; if you want stricter "no temp" policy, tell me.
            let tmp = "__tjs2dec_u";
            writeln!(
                out,
                "        var {} = ({} {} {});",
                tmp,
                target.to_tjs_with(fmt_var),
                op.op_str(),
                rhs.to_tjs_with(fmt_var)
            )?;
            writeln!(out, "        {} = {};", target.to_tjs_with(fmt_var), tmp)?;
            if let Some(d) = dst {
                writeln!(out, "        {} = {};", fmt_var(*d), tmp)?;
            }
        }
        Stmt::Expr(e) => {
            writeln!(out, "        {};", e.to_tjs_with(fmt_var))?;
        }
        Stmt::Opaque { op, args, defs } => {
            let mut call = String::new();
            write!(&mut call, "__tjs2dec_opaque(\"{}\"", op)?;
            for a in args {
                write!(&mut call, ", {}", a.to_tjs_with(fmt_var))?;
            }
            call.push(')');

            if defs.is_empty() {
                writeln!(out, "        {};", call)?;
            } else if defs.len() == 1 {
                writeln!(out, "        {} = {};", fmt_var(defs[0]), call)?;
            } else {
                // multi-def: we do one call, copy result to all defs
                writeln!(out, "        var __tjs2dec_o = {};", call)?;
                for d in defs {
                    writeln!(out, "        {} = __tjs2dec_o;", fmt_var(*d))?;
                }
            }
        }
    }
    Ok(())
}

fn emit_terminator(
    out: &mut String,
    b: &ExprBlock,
    fmt_var: &dyn Fn(VarId) -> String,
    phi_moves: &HashMap<(usize, usize), Vec<(VarId, VarId)>>,
) -> Result<()> {
    match &b.term {
        Terminator::Jmp(t) => {
            emit_phi_parallel_copies(out, fmt_var, phi_moves, b.id, *t, "        ")?;
            writeln!(out, "        __bb = {};", t)?;
            writeln!(out, "        continue;")?;
        }
        Terminator::Br { cond, if_true, if_false } => {
            writeln!(out, "        if ({}) {{", cond.to_tjs_with(fmt_var))?;
            emit_phi_parallel_copies(out, fmt_var, phi_moves, b.id, *if_true, "          ")?;
            writeln!(out, "          __bb = {};", if_true)?;
            writeln!(out, "          continue;")?;
            writeln!(out, "        }} else {{")?;
            emit_phi_parallel_copies(out, fmt_var, phi_moves, b.id, *if_false, "          ")?;
            writeln!(out, "          __bb = {};", if_false)?;
            writeln!(out, "          continue;")?;
            writeln!(out, "        }}")?;
        }
        Terminator::Ret => {
            writeln!(out, "        return __rv;")?;
        }
        Terminator::Throw(e) => {
            writeln!(out, "        throw {};", e.to_tjs_with(fmt_var))?;
        }
        Terminator::Exit => {
            writeln!(out, "        return __rv;")?;
        }
        Terminator::Fallthrough => {
            if let Some(t) = b.succ.first().copied() {
                emit_phi_parallel_copies(out, fmt_var, phi_moves, b.id, t, "        ")?;
                writeln!(out, "        __bb = {};", t)?;
                writeln!(out, "        continue;")?;
            } else {
                writeln!(out, "        return __rv;")?;
            }
        }
    }
    Ok(())
}

fn exceptional_succ(b: &ExprBlock) -> Option<usize> {
    let normal = match b.term {
        Terminator::Jmp(_) => 1,
        Terminator::Br { .. } => 2,
        Terminator::Fallthrough => if b.succ.is_empty() { 0 } else { 1 },
        Terminator::Ret | Terminator::Throw(_) | Terminator::Exit => 0,
    };
    if b.succ.len() > normal {
        // CFG builder appends exceptional succ conservatively at the end.
        b.succ.last().copied()
    } else {
        None
    }
}

fn build_phi_edge_moves(prog: &ExprProgram) -> HashMap<(usize, usize), Vec<(VarId, VarId)>> {
    let mut m: HashMap<(usize, usize), Vec<(VarId, VarId)>> = HashMap::new();
    for blk in &prog.blocks {
        let succ = blk.id;
        for p in &blk.phi {
            let dst = p.result;
            for (pred, src) in &p.args {
                m.entry((*pred, succ)).or_default().push((dst, *src));
            }
        }
    }
    m
}

fn emit_phi_parallel_copies(
    out: &mut String,
    fmt_var: &dyn Fn(VarId) -> String,
    phi_moves: &HashMap<(usize, usize), Vec<(VarId, VarId)>>,
    pred: usize,
    succ: usize,
    indent: &str,
) -> Result<()> {
    let Some(moves) = phi_moves.get(&(pred, succ)) else { return Ok(()); };

    // Filter identity moves
    let mut mv: Vec<(VarId, VarId)> = moves.iter().copied().filter(|(d, s)| d != s).collect();
    if mv.is_empty() {
        return Ok(());
    }

    // Simple parallel-copy: pre-save any src that is also a dst.
    let dst_set: HashSet<VarId> = mv.iter().map(|(d, _)| *d).collect();
    let mut saved: HashMap<VarId, String> = HashMap::new();
    let mut tmp_i = 0usize;

    for (_, s) in &mv {
        if dst_set.contains(s) && !saved.contains_key(s) {
            let tname = format!("__tjs2dec_phi{}", tmp_i);
            tmp_i += 1;
            writeln!(out, "{}var {} = {};", indent, tname, fmt_var(*s))?;
            saved.insert(*s, tname);
        }
    }

    for (d, s) in mv.drain(..) {
        if let Some(tn) = saved.get(&s) {
            writeln!(out, "{}{} = {};", indent, fmt_var(d), tn)?;
        } else {
            writeln!(out, "{}{} = {};", indent, fmt_var(d), fmt_var(s))?;
        }
    }

    Ok(())
}

fn collect_all_vars(prog: &ExprProgram) -> Vec<String> {
    let mut set: HashSet<VarId> = HashSet::new();

    for b in &prog.blocks {
        for p in &b.phi {
            set.insert(p.result);
            for (_, v) in &p.args {
                set.insert(*v);
            }
        }

        for st in &b.stmts {
            match st {
                Stmt::Assign { dst, expr } => {
                    set.insert(*dst);
                    collect_expr_vars(expr, &mut set);
                }
                Stmt::Store { target, value } => {
                    collect_expr_vars(target, &mut set);
                    collect_expr_vars(value, &mut set);
                }
                Stmt::Update { dst, target, rhs, .. } => {
                    if let Some(d) = dst {
                        set.insert(*d);
                    }
                    collect_expr_vars(target, &mut set);
                    collect_expr_vars(rhs, &mut set);
                }
                Stmt::Expr(e) => collect_expr_vars(e, &mut set),
                Stmt::Opaque { args, defs, .. } => {
                    for d in defs {
                        set.insert(*d);
                    }
                    for a in args {
                        collect_expr_vars(a, &mut set);
                    }
                }
            }
        }

        match &b.term {
            Terminator::Br { cond, .. } => collect_expr_vars(cond, &mut set),
            Terminator::Throw(e) => collect_expr_vars(e, &mut set),
            _ => {}
        }
    }

    let mut names: Vec<String> = set.into_iter().map(fmt_vid).collect();
    names.sort();
    names.dedup();
    names
}

fn collect_expr_vars(e: &Expr, out: &mut HashSet<VarId>) {
    match e {
        Expr::SsaVar(v) => {
            out.insert(*v);
        }
        Expr::Unary(_, x) | Expr::Deref(x) => {
            collect_expr_vars(x, out);
        }
        Expr::Binary(_, a, b) => {
            collect_expr_vars(a, out);
            collect_expr_vars(b, out);
        }
        Expr::Call(f, args) | Expr::New(f, args) => {
            collect_expr_vars(f, out);
            for a in args {
                collect_expr_vars(a, out);
            }
        }
        Expr::Index(a, b) => {
            collect_expr_vars(a, out);
            collect_expr_vars(b, out);
        }
        Expr::Member(base, _) => {
            collect_expr_vars(base, out);
        }
        Expr::MethodCall { base, args, .. } => {
            collect_expr_vars(base, out);
            for a in args {
                collect_expr_vars(a, out);
            }
        }
        Expr::Opaque(_, args) => {
            for a in args {
                collect_expr_vars(a, out);
            }
        }
        _ => {}
    }
}
