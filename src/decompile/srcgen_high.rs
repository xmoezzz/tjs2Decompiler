use anyhow::Result;
use std::collections::{HashMap, HashSet, BTreeMap};
use std::fmt::Write as _;

use crate::{Tjs2File, Tjs2Object};
use crate::Variant;

use super::cfg::Cfg;
use super::expr::{BinOp, Expr, UnOp};
use super::expr_build::{ExprProgram, Stmt, Terminator};
use super::ssa::{SsaProgram, Var, VarId};

fn vm_binop(op: &str) -> Option<BinOp> {
    match op {
        "VM_ADD" | "ADD" => Some(BinOp::Add),
        "VM_SUB" | "SUB" => Some(BinOp::Sub),
        "VM_MUL" | "MUL" => Some(BinOp::Mul),
        "VM_DIV" | "DIV" => Some(BinOp::Div),
        "VM_MOD" | "MOD" => Some(BinOp::Mod),

        "VM_SAL" | "SHL" => Some(BinOp::Shl),
        "VM_SAR" | "SHR" => Some(BinOp::Shr),
        "VM_SR"  | "USHR" => Some(BinOp::UShr),

        "VM_BAND" | "BAND" => Some(BinOp::BitAnd),
        "VM_BXOR" | "BXOR" => Some(BinOp::BitXor),
        "VM_BOR"  | "BOR"  => Some(BinOp::BitOr),

        "VM_LAND" | "LAND" => Some(BinOp::LogAnd),
        "VM_LOR"  | "LOR"  => Some(BinOp::LogOr),

        "VM_EQ" | "EQ" => Some(BinOp::Eq),
        "VM_NE" | "NE" => Some(BinOp::Ne),
        "VM_DEQ" | "DEQ" => Some(BinOp::StrictEq),
        "VM_DNE" | "DNE" => Some(BinOp::StrictNe),

        "VM_LT" | "LT" => Some(BinOp::Lt),
        "VM_LE" | "LE" => Some(BinOp::Le),
        "VM_GT" | "GT" => Some(BinOp::Gt),
        "VM_GE" | "GE" => Some(BinOp::Ge),

        "VM_IN" | "CHKINS" => Some(BinOp::In),

        _ => None,
    }
}

fn vm_unop(op: &str) -> Option<UnOp> {
    match op {
        "VM_CHS" | "CHS" => Some(UnOp::Neg),
        "VM_LNOT" | "LNOT" => Some(UnOp::Not),
        "VM_BNOT" | "BNOT" => Some(UnOp::BitNot),
        "VM_TYPEOF" | "TYPEOF" => Some(UnOp::Typeof),
        "VM_DELETE" | "DELETE" => Some(UnOp::Delete),
        _ => None,
    }
}


fn fmt_octet_literal(bytes: &[u8]) -> String {
    // B: official usage style
    let mut s = String::new();
    s.push_str("octet([");
    for (k, b) in bytes.iter().enumerate() {
        if k != 0 {
            s.push_str(", ");
        }
        s.push_str(&format!("0x{:02X}", b));
    }
    s.push_str("])");
    s
}

fn escape_tjs_string_min(s: &str) -> String {
    let mut out = String::new();
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            _ => out.push(ch),
        }
    }
    out
}


/// Options controlling how code is emitted.
pub struct SrcgenOptions {
    pub inline: bool,
}

impl Default for SrcgenOptions {
    fn default() -> Self {
        SrcgenOptions { inline: true }
    }
}

fn split_class_method(name: &str) -> Option<(&str, &str)> {
    let (a, b) = name.split_once('.')?;
    if a.is_empty() || b.is_empty() { return None; }
    if !a.split('.').all(is_identifier) { return None; }
    if !b.split('.').all(is_identifier) { return None; }
    Some((a, b))
}


// pub fn dump_src_file(file: &Tjs2File, _opt: SrcgenOptions) -> Result<String> {
//     let mut out = String::new();
//     writeln!(
//         out,
//         "// Decompiled from TJS2 bytecode\n// objects: {}\n",
//         file.objects.len()
//     )?;

//     for obj in &file.objects {
//         if obj.code.is_empty() {
//             continue;
//         }
//         writeln!(
//             out,
//             "// == object {}: {} ==",
//             obj.index,
//             obj.name.as_deref().unwrap_or("<anonymous>")
//         )?;

//         let lhs = obj_lhs(obj.index, obj.name.as_deref());
//         writeln!(out, "{} = function() {{", lhs)?;

//         let cfg = Cfg::build(obj)?;
//         let ssa = SsaProgram::from_cfg(&cfg)?;
//         let prog = ExprProgram::from_ssa(file, obj, &ssa)?;

//         let fmt_var = |vid: VarId| -> String { fmt_vid_tjs(vid) };
//         emit_var_decls(&mut out, &prog, &fmt_var)?;

//         // Recover return expressions from SSA (expr_build's Terminator::Ret has no expr).
//         let mut ret_expr: Vec<Option<Expr>> = vec![None; prog.blocks.len()];
//         for b in &ssa.blocks {
//             if let Some(last) = b.insns.last() {
//                 // VM_RET has the return value in uses[0] (static, no guessing).
//                 if last.mnemonic.eq_ignore_ascii_case("RET") || last.mnemonic.eq_ignore_ascii_case("VM_RET") {
//                     if let Some(v) = last.uses.get(0).copied() {
//                         ret_expr[b.id] = Some(Expr::SsaVar(v));
//                     }
//                 }
//             }
//         }

//         let mut s = Structurer::new(&cfg, &prog, &fmt_var, ret_expr);
//         let lines = s.emit_function_body(prog.entry_block, 2);

//         for l in lines {
//             writeln!(out, "{}", l)?;
//         }
//         writeln!(out, "}};\n")?;
//     }

//     Ok(out)
// }

fn emit_object_body(obj: &Tjs2Object, file: &Tjs2File, indent: usize) -> Result<(String, String)> {
    // let lhs = obj_lhs(obj.index, obj.name.as_deref());
    // writeln!(out, "{} = function() {{", lhs)?;
    let mut out = String::new();

    let cfg = Cfg::build(obj)?;
    let ssa = SsaProgram::from_cfg(&cfg)?;
    let prog = ExprProgram::from_ssa(file, obj, &ssa)?;
    let arg_regs = infer_arg_regs(&prog); 
    let params = arg_regs.iter().map(|&r| arg_name_for_reg(r)).collect::<Vec<_>>().join(", ");

    let fmt_var = |vid: VarId| -> String { fmt_vid_tjs(vid) };
    emit_var_decls(&mut out, &prog, &fmt_var)?;

    // Recover return expressions from SSA (expr_build's Terminator::Ret has no expr).
    let mut ret_expr: Vec<Option<Expr>> = vec![None; prog.blocks.len()];
    for b in &ssa.blocks {
        if let Some(last) = b.insns.last() {
            // VM_RET has the return value in uses[0] (static, no guessing).
            if last.mnemonic.eq_ignore_ascii_case("RET") || last.mnemonic.eq_ignore_ascii_case("VM_RET") {
                if let Some(v) = last.uses.get(0).copied() {
                    ret_expr[b.id] = Some(Expr::SsaVar(v));
                }
            }
        }
    }

    let mut s = Structurer::new(&cfg, &prog, &fmt_var, ret_expr);
    let lines = s.emit_function_body(prog.entry_block, 2);

    for l in lines {
        writeln!(out, "{}", l)?;
    }
    writeln!(out, "}};\n")?;
    Ok((out, params))
}


pub fn dump_src_file(file: &Tjs2File, _opt: SrcgenOptions) -> Result<String> {
    let mut out = String::new();
    writeln!(out, "// ---- TJS2 Decompiled Source ----")?;

    // 1) build class_methods: cls -> [object]
    let mut class_methods: BTreeMap<String, Vec<&Tjs2Object>> = BTreeMap::new();
    let mut in_class: HashSet<usize> = HashSet::new();

    for obj in &file.objects {
        if obj.code.is_empty() {
            continue;
        }
        let Some(name) = obj.name.as_deref() else {
            continue;
        };

        // only accept "Class.method" (single dot). If more dots exist, don't treat as class method.
        let Some((cls, mname)) = name.split_once('.') else {
            continue;
        };
        if cls.is_empty() || mname.is_empty() {
            continue;
        }
        if mname.contains('.') {
            continue;
        }

        // reuse your existing identifier rule (you already have is_identifier used by obj_lhs)
        if !is_identifier(cls) || !is_identifier(mname) {
            continue;
        }

        class_methods.entry(cls.to_string()).or_default().push(obj);
        in_class.insert(obj.index);
    }

    // 2) emit classes first
    for (cls, methods) in &class_methods {
        writeln!(out, "class {} {{", cls)?;
        for mobj in methods {
            let name = mobj.name.as_deref().unwrap();
            let (_cls, mname) = name.split_once('.').unwrap();

            writeln!(out, "  // == object {}: {} ==", mobj.index, name)?;
            write!(out, "  function {}", mname)?;

            let (body, params) = emit_object_body(mobj, file, /*indent=*/4)?;
            writeln!(out, "  ({}) {{", params)?;
            for line in body.lines() {
                writeln!(out, "{}", line)?;
            }

            writeln!(out, "  }}")?;
            writeln!(out)?;
        }
        writeln!(out, "}}")?;
        writeln!(out)?;
    }

    // 3) emit remaining objects as globals (skip those already emitted in class)
    for obj in &file.objects {
        if obj.code.is_empty() {
            continue;
        }
        if in_class.contains(&obj.index) {
            continue;
        }

        let lhs = obj_lhs(obj.index, obj.name.as_deref());
        write!(out, "{} = function", lhs)?;


        let (body, params) = emit_object_body(obj, file, /*indent=*/2)?;
        writeln!(out, "({}) {{", params)?;
        for line in body.lines() {
            writeln!(out, "{}", line)?;
        }

        writeln!(out)?;
    }

    Ok(out)
}


/* ------------------------- structuring ------------------------- */

#[derive(Clone)]
struct LoopCtx {
    header: usize,
    exit: Option<usize>,
}

#[derive(Clone, Copy)]
struct RegionOutcome {
    falls_through: bool,
}

struct Structurer<'a> {
    cfg: &'a Cfg,
    prog: &'a ExprProgram,
    fmt_var: &'a dyn Fn(VarId) -> String,

    // (pred, succ) -> list of (phi_result, incoming_value)
    edge_copies: HashMap<(usize, usize), Vec<(VarId, VarId)>>,

    // dominators / postdominators on reachable blocks
    dom: Vec<HashSet<usize>>,
    pdom: Vec<HashSet<usize>>,
    ipdom: Vec<Option<usize>>,

    // loop header -> natural loop node set
    loops: HashMap<usize, HashSet<usize>>,

    emitted: HashSet<usize>,

    // return expression per block (from SSA)
    ret_expr: Vec<Option<Expr>>,
}

impl<'a> Structurer<'a> {
    fn new(
        cfg: &'a Cfg,
        prog: &'a ExprProgram,
        fmt_var: &'a dyn Fn(VarId) -> String,
        ret_expr: Vec<Option<Expr>>,
    ) -> Self {
        let edge_copies = build_edge_copies(prog);
        let reachable = compute_reachable(prog, prog.entry_block);

        let dom = compute_dominators(prog, prog.entry_block, &reachable);
        let pdom = compute_postdominators(prog, &reachable);
        let ipdom = compute_ipdom(&pdom);

        let loops = compute_natural_loops(prog, &dom, &reachable);

        Self {
            cfg,
            prog,
            fmt_var,
            edge_copies,
            dom,
            pdom,
            ipdom,
            loops,
            emitted: HashSet::new(),
            ret_expr,
        }
    }

    fn emit_function_body(&mut self, entry: usize, indent: usize) -> Vec<String> {
        let mut lines = Vec::new();
        let _ = self.emit_seq(entry, None, indent, None, &mut lines);

        // Optionally dump unreachable blocks (still no goto/state-machine).
        let reachable = compute_reachable(self.prog, self.prog.entry_block);
        for b in 0..self.prog.blocks.len() {
            if !reachable.contains(&b) {
                lines.push(format!("{}// unreachable bb{}", " ".repeat(indent), b));
                self.emit_block_stmts(b, indent, &mut lines);
            }
        }
        lines
    }

    fn emit_seq(
        &mut self,
        mut cur: usize,
        stop: Option<usize>,
        indent: usize,
        loop_ctx: Option<LoopCtx>,
        out: &mut Vec<String>,
    ) -> RegionOutcome {
        while Some(cur) != stop {
            let loop_ctx = loop_ctx.clone();
            if self.emitted.contains(&cur) {
                out.push(format!(
                    "{}// re-entry to already-emitted bb{}",
                    " ".repeat(indent),
                    cur
                ));
                return RegionOutcome { falls_through: true };
            }

            if self.is_loop_header(cur) && stop != Some(cur) {
                let oc = self.emit_loop(cur, indent, out);
                if let Some(n) = self.loop_exit(cur) {
                    cur = n;
                    continue;
                }
                return oc;
            }

            self.emitted.insert(cur);

            self.emit_block_stmts(cur, indent, out);

            let blk = &self.prog.blocks[cur];
            match blk.term.clone() {
                Terminator::Ret => {
                    if let Some(e) = self.ret_expr.get(cur).and_then(|x| x.clone()) {
                        out.push(format!(
                            "{}return {};",
                            " ".repeat(indent),
                            self.expr_to_tjs(&e)
                        ));
                    } else {
                        out.push(format!("{}return;", " ".repeat(indent)));
                    }
                    return RegionOutcome { falls_through: false };
                }
                Terminator::Throw(e) => {
                    out.push(format!(
                        "{}throw {};",
                        " ".repeat(indent),
                        self.expr_to_tjs(&e)
                    ));
                    return RegionOutcome { falls_through: false };
                }
                Terminator::Exit | Terminator::Fallthrough => {
                    if let Some(n) = blk.succ.get(0).copied() {
                        self.emit_edge_copies(cur, n, indent, out);
                        cur = n;
                        continue;
                    }
                    out.push(format!("{}return;", " ".repeat(indent)));
                    return RegionOutcome { falls_through: false };
                }
                Terminator::Jmp(t) => {
                    if let Some(ctx) = loop_ctx.clone() {
                        if t == ctx.header {
                            self.emit_edge_copies(cur, t, indent, out);
                            out.push(format!("{}continue;", " ".repeat(indent)));
                            return RegionOutcome { falls_through: false };
                        }
                        if ctx.exit == Some(t) {
                            self.emit_edge_copies(cur, t, indent, out);
                            out.push(format!("{}break;", " ".repeat(indent)));
                            return RegionOutcome { falls_through: false };
                        }
                    }
                    if stop == Some(t) {
                        self.emit_edge_copies(cur, t, indent, out);
                        return RegionOutcome { falls_through: true };
                    }
                    self.emit_edge_copies(cur, t, indent, out);
                    cur = t;
                    continue;
                }
                Terminator::Br {
                    cond,
                    if_true,
                    if_false,
                } => {
                    // If this branch is a loop-exit/continue inside a loop body, prioritize break/continue patterns.
                    if let Some(ctx) = loop_ctx.clone() {
                        if if_true == ctx.header || if_false == ctx.header || ctx.exit == Some(if_true) || ctx.exit == Some(if_false) {
                            let oc = self.emit_branch_in_loop(
                                cur,
                                &cond,
                                if_true,
                                if_false,
                                indent,
                                ctx,
                                out,
                            );
                            return oc;
                        }
                    }

                    let join = self.ipdom.get(cur).and_then(|x| *x).or(stop);

                    out.push(format!(
                        "{}if ({}) {{",
                        " ".repeat(indent),
                        self.expr_to_tjs(&cond)
                    ));

                    // then
                    self.emit_edge_copies(cur, if_true, indent + 2, out);
                    let then_oc = self.emit_seq(if_true, join, indent + 2, loop_ctx.clone(), out);
                    out.push(format!("{}}}", " ".repeat(indent)));

                    // else
                    out.push(format!("{}else {{", " ".repeat(indent)));
                    self.emit_edge_copies(cur, if_false, indent + 2, out);
                    let else_oc = self.emit_seq(if_false, join, indent + 2, loop_ctx, out);
                    out.push(format!("{}}}", " ".repeat(indent)));

                    if let Some(j) = join {
                        if then_oc.falls_through || else_oc.falls_through {
                            cur = j;
                            continue;
                        }
                        return RegionOutcome { falls_through: false };
                    }
                    return RegionOutcome { falls_through: then_oc.falls_through || else_oc.falls_through };
                }
            }
        }

        RegionOutcome { falls_through: true }
    }

    fn emit_branch_in_loop(
        &mut self,
        cur: usize,
        cond: &Expr,
        t: usize,
        f: usize,
        indent: usize,
        ctx: LoopCtx,
        out: &mut Vec<String>,
    ) -> RegionOutcome {
        // Pattern:
        // if (cond) { ... } else { ... }
        // but allow branches to be break/continue.
        out.push(format!(
            "{}if ({}) {{",
            " ".repeat(indent),
            self.expr_to_tjs(cond)
        ));

        self.emit_edge_copies(cur, t, indent + 2, out);
        let then_oc = self.emit_seq(t, None, indent + 2, Some(ctx.clone()), out);
        out.push(format!("{}}}", " ".repeat(indent)));

        out.push(format!("{}else {{", " ".repeat(indent)));
        self.emit_edge_copies(cur, f, indent + 2, out);
        let else_oc = self.emit_seq(f, None, indent + 2, Some(ctx), out);
        out.push(format!("{}}}", " ".repeat(indent)));

        RegionOutcome { falls_through: then_oc.falls_through || else_oc.falls_through }
    }

    fn is_loop_header(&self, h: usize) -> bool {
        self.loops.contains_key(&h)
    }

    fn loop_exit(&self, h: usize) -> Option<usize> {
        let body = self.loops.get(&h)?;
        let blk = &self.prog.blocks[h];
        for &s in &blk.succ {
            if !body.contains(&s) {
                return Some(s);
            }
        }
        None
    }

    fn emit_loop(&mut self, header: usize, indent: usize, out: &mut Vec<String>) -> RegionOutcome {
        let body_nodes = match self.loops.get(&header) {
            Some(s) => s.clone(),
            None => return RegionOutcome { falls_through: true },
        };

        // Choose loop exit as header successor not in loop set.
        let exit = self.loop_exit(header);

        out.push(format!("{}while (true) {{", " ".repeat(indent)));

        // Emit header statements inside loop.
        self.emit_block_stmts(header, indent + 2, out);

        // Handle header terminator as loop guard / dispatch.
        let blk = &self.prog.blocks[header];
        match blk.term.clone() {
            Terminator::Br { cond, if_true, if_false } => {
                // Decide which successor stays in loop.
                let t_in = body_nodes.contains(&if_true);
                let f_in = body_nodes.contains(&if_false);

                if exit.is_some() && (t_in ^ f_in) {
                    let (body_succ, exit_succ, break_on_true) = if t_in {
                        (if_true, if_false, false)
                    } else {
                        (if_false, if_true, true)
                    };

                    if break_on_true {
                        // if (cond) { copies; break; }
                        out.push(format!(
                            "{}if ({}) {{",
                            " ".repeat(indent + 2),
                            self.expr_to_tjs(&cond)
                        ));
                        self.emit_edge_copies(header, exit_succ, indent + 4, out);
                        out.push(format!("{}break;", " ".repeat(indent + 4)));
                        out.push(format!("{}}}", " ".repeat(indent + 2)));
                    } else {
                        // if (!cond) { copies; break; }
                        let ncond = Expr::Unary(UnOp::Not, Box::new(cond));
                        out.push(format!(
                            "{}if ({}) {{",
                            " ".repeat(indent + 2),
                            self.expr_to_tjs(&ncond)
                        ));
                        self.emit_edge_copies(header, exit_succ, indent + 4, out);
                        out.push(format!("{}break;", " ".repeat(indent + 4)));
                        out.push(format!("{}}}", " ".repeat(indent + 2)));
                    }

                    // fall into body
                    self.emit_edge_copies(header, body_succ, indent + 2, out);
                    let _ = self.emit_seq(
                        body_succ,
                        Some(header),
                        indent + 2,
                        Some(LoopCtx { header, exit }),
                        out,
                    );
                } else {
                    // Fallback: still emit both arms inside loop (no goto/state machine).
                    out.push(format!(
                        "{}if ({}) {{",
                        " ".repeat(indent + 2),
                        self.expr_to_tjs(&cond)
                    ));
                    self.emit_edge_copies(header, if_true, indent + 4, out);
                    let _ = self.emit_seq(
                        if_true,
                        Some(header),
                        indent + 4,
                        Some(LoopCtx { header, exit }),
                        out,
                    );
                    out.push(format!("{}}}", " ".repeat(indent + 2)));
                    out.push(format!("{}else {{", " ".repeat(indent + 2)));
                    self.emit_edge_copies(header, if_false, indent + 4, out);
                    let _ = self.emit_seq(
                        if_false,
                        Some(header),
                        indent + 4,
                        Some(LoopCtx { header, exit }),
                        out,
                    );
                    out.push(format!("{}}}", " ".repeat(indent + 2)));
                }
            }
            Terminator::Jmp(t) => {
                if t == header {
                    out.push(format!("{}continue;", " ".repeat(indent + 2)));
                } else {
                    self.emit_edge_copies(header, t, indent + 2, out);
                    let _ = self.emit_seq(
                        t,
                        Some(header),
                        indent + 2,
                        Some(LoopCtx { header, exit }),
                        out,
                    );
                }
            }
            Terminator::Ret => {
                if let Some(e) = self.ret_expr.get(header).and_then(|x| x.clone()) {
                    out.push(format!(
                        "{}return {};",
                        " ".repeat(indent + 2),
                        self.expr_to_tjs(&e)
                    ));
                } else {
                    out.push(format!("{}return;", " ".repeat(indent + 2)));
                }
            }
            Terminator::Throw(e) => {
                out.push(format!(
                    "{}throw {};",
                    " ".repeat(indent + 2),
                    self.expr_to_tjs(&e)
                ));
            }
            Terminator::Exit | Terminator::Fallthrough => {
                if let Some(n) = blk.succ.get(0).copied() {
                    self.emit_edge_copies(header, n, indent + 2, out);
                    let _ = self.emit_seq(
                        n,
                        Some(header),
                        indent + 2,
                        Some(LoopCtx { header, exit }),
                        out,
                    );
                } else {
                    out.push(format!("{}return;", " ".repeat(indent + 2)));
                }
            }
        }

        out.push(format!("{}}}", " ".repeat(indent)));

        // Mark all nodes in this loop as emitted (except those already).
        for n in body_nodes {
            self.emitted.insert(n);
        }
        self.emitted.insert(header);

        RegionOutcome { falls_through: exit.is_some() }
    }

    fn emit_block_stmts(&self, bid: usize, indent: usize, out: &mut Vec<String>) {
        let blk = &self.prog.blocks[bid];

        // Optional block header comment (helps debugging; not a helper function).
        out.push(format!(
            "{}// bb{} @{}",
            " ".repeat(indent),
            blk.id,
            blk.start_pc
        ));

        for st in &blk.stmts {
            if let Stmt::Opaque { op, .. } = st {
                // Skip CFG-control ops (they are represented by Terminator).
                if is_control_op(op) {
                    continue;
                }
            }
            out.push(format!("{}{}", " ".repeat(indent), self.stmt_to_tjs(st)));
        }
    }

    fn emit_edge_copies(&self, pred: usize, succ: usize, indent: usize, out: &mut Vec<String>) {
        if let Some(xs) = self.edge_copies.get(&(pred, succ)) {
            for (dst, src) in xs {
                let d = (self.fmt_var)(*dst);
                let s = (self.fmt_var)(*src);
                out.push(format!("{}{} = {};", " ".repeat(indent), d, s));
            }
        }
    }

    fn stmt_to_tjs(&self, st: &Stmt) -> String {
        match st {
            Stmt::Assign { dst, expr } => {
                format!("{} = {};", (self.fmt_var)(*dst), self.expr_to_tjs(expr))
            }
            Stmt::Store { target, value } => {
                format!("{} = {};", self.expr_to_tjs(target), self.expr_to_tjs(value))
            }
            Stmt::Update { dst, target, op, rhs } => {
                if let Some(comp) = to_compound_assign(*op) {
                    if let Some(d) = dst {
                        format!(
                            "{} = ({} {} {});",
                            (self.fmt_var)(*d),
                            self.expr_to_tjs(target),
                            comp.op_str(),
                            self.expr_to_tjs(rhs)
                        )
                    } else {
                        format!(
                            "{} {} {};",
                            self.expr_to_tjs(target),
                            comp.op_str(),
                            self.expr_to_tjs(rhs)
                        )
                    }
                } else {
                    if let Some(d) = dst {
                        format!(
                            "{} = ({} = ({} {} {}));",
                            (self.fmt_var)(*d),
                            self.expr_to_tjs(target),
                            self.expr_to_tjs(target),
                            op.op_str(),
                            self.expr_to_tjs(rhs)
                        )
                    } else {
                        format!(
                            "{} = ({} {} {});",
                            self.expr_to_tjs(target),
                            self.expr_to_tjs(target),
                            op.op_str(),
                            self.expr_to_tjs(rhs)
                        )
                    }
                }
            }
            Stmt::Expr(e) => format!("{};", self.expr_to_tjs(e)),
            Stmt::Opaque { op, args, defs } => {
                match op.to_string().as_str() {
                    "JF" | "JNF" | "JMP" | "RET" | "THROW" | "ENTRY" | "EXTRY" |
                    "VM_JF" | "VM_JNF" | "VM_JMP" | "VM_RET" | "VM_THROW" | "VM_ENTRY" | "VM_EXTRY" => {
                        return "// (control op omitted)".to_string();
                    }
                    _ => {}
                }
                let op_name = op.to_string();
                if op_name == "VM_CHGTHIS" || op_name == "CHGTHIS" {
                    return "// (this-change op omitted)".to_string();
                }

                if (op_name == "VM_TYPEOFD" || op_name == "TYPEOFD" || op_name == "VM_TYPEOF" || op_name == "TYPEOF") && args.len() == 1 {
                    let x = args[0].to_tjs_with(self.fmt_var);
                    let expr = format!("(typeof {})", x);

                    if defs.is_empty() {
                        return format!("{};", expr);
                    } else if defs.len() == 1 {
                        return format!("{} = {};", (self.fmt_var)(defs[0]), expr);
                    } else {
                        let mut s = String::new();
                        let _ = write!(&mut s, "{{ var __t = {}; ", expr);
                        for (i, d) in defs.iter().enumerate() {
                            let _ = write!(&mut s, "{} = __t[{}]; ", (self.fmt_var)(*d), i);
                        }
                        let _ = write!(&mut s, "}}");
                        return s;
                    }
                }

                if (op_name == "VM_SRV" || op_name == "SRV") && args.len() == 1 {
                    let x = args[0].to_tjs_with(self.fmt_var);
                    let mut s = format!("__rv = {};", x);
                    if defs.len() == 1 {
                        s.push_str(&format!(" {} = __rv;", (self.fmt_var)(defs[0])));
                    }
                    return s;
                }

                if (op_name == "VM_NUM" || op_name == "NUM") && args.len() == 1 {
                    let x = args[0].to_tjs_with(self.fmt_var);

                    let expr = format!("real({})", x);

                    if defs.len() == 1 {
                        return format!("{} = {};", (self.fmt_var)(defs[0]), expr);
                    } else {
                        return format!("{};", expr);
                    }
                }

                if (op_name.starts_with("VM_STR") || op_name == "STR") && args.len() == 1 {
                    let x = args[0].to_tjs_with(self.fmt_var);
                    let expr = format!("string({})", x);

                    if defs.len() == 1 {
                        return format!("{} = {};", (self.fmt_var)(defs[0]), expr);
                    } else {
                        return format!("{};", expr);
                    }
                }

                if op_name == "VM_CHGTHIS" || op_name == "CHGTHIS" {
                    if args.len() == 2 {
                        return format!("chgthis({}, {});",
                            args[0].to_tjs_with(self.fmt_var),
                            args[1].to_tjs_with(self.fmt_var),
                        );
                    }
                    return "// chgthis();".to_string();
                }

                if op_name.starts_with("VM_REGMEMBER") && args.len() == 3 {
                    return format!("{}.{} = {};", 
                        args[0].to_tjs_with(self.fmt_var),
                        args[1].to_tjs_with(self.fmt_var),
                        args[2].to_tjs_with(self.fmt_var));
                }

                if op_name.starts_with("VM_INV") && args.len() >= 2 {
                    let recv = args[0].to_tjs_with(self.fmt_var);
                    let method = args[1].to_tjs_with(self.fmt_var);
                    let call_args = args.iter().skip(2)
                        .map(|x| x.to_tjs_with(self.fmt_var))
                        .collect::<Vec<_>>()
                        .join(", ");
                    let call = format!("{}.{}({})", recv, method, call_args);
                    if defs.len() == 1 {
                        return format!("{} = {};", (self.fmt_var)(defs[0]), call);
                    } else {
                        return format!("{};", call);
                    }
                }


                let call = if args.is_empty() {
                    format!("{}()", op)
                } else {
                    // let mut s = String::new();
                    // s.push_str(op);
                    // s.push('(');
                    // for (i, a) in args.iter().enumerate() {
                    //     if i != 0 {
                    //         s.push_str(", ");
                    //     }
                    //     s.push_str(&self.expr_to_tjs(a));
                    // }
                    // s.push(')');

                    let a0 = args.get(0).map(|x| x.to_tjs_with(self.fmt_var));
                    let a1 = args.get(1).map(|x| x.to_tjs_with(self.fmt_var));

                    let opname = op;

                    let call = if let (Some(x), Some(y)) = (a0.as_deref(), a1.as_deref()) {
                        // binary families (cover D/I/P variants by starts_with)
                        if opname.starts_with("VM_ADD") { format!("({} + {})", x, y) }
                        else if opname.starts_with("VM_SUB") { format!("({} - {})", x, y) }
                        else if opname.starts_with("VM_MUL") { format!("({} * {})", x, y) }
                        else if opname.starts_with("VM_DIV") { format!("({} / {})", x, y) }
                        else if opname.starts_with("VM_IDIV") { format!("({} \\ {})", x, y) }
                        else if opname.starts_with("VM_MOD") { format!("({} % {})", x, y) }

                        else if opname.starts_with("VM_SAL") { format!("({} << {})", x, y) }
                        else if opname.starts_with("VM_SAR") { format!("({} >> {})", x, y) }
                        else if opname.starts_with("VM_SR")  { format!("({} >>> {})", x, y) }

                        else if opname.starts_with("VM_BAND") { format!("({} & {})", x, y) }
                        else if opname.starts_with("VM_BXOR") { format!("({} ^ {})", x, y) }
                        else if opname.starts_with("VM_BOR")  { format!("({} | {})", x, y) }

                        else if opname.starts_with("VM_LAND") { format!("({} && {})", x, y) }
                        else if opname.starts_with("VM_LOR")  { format!("({} || {})", x, y) }

                        else if opname.starts_with("VM_EQ")  { format!("({} == {})", x, y) }
                        else if opname.starts_with("VM_NE")  { format!("({} != {})", x, y) }
                        else if opname.starts_with("VM_DEQ") { format!("({} === {})", x, y) }
                        else if opname.starts_with("VM_DNE") { format!("({} !== {})", x, y) }

                        else if opname.starts_with("VM_LT") { format!("({} < {})", x, y) }
                        else if opname.starts_with("VM_LE") { format!("({} <= {})", x, y) }
                        else if opname.starts_with("VM_GT") { format!("({} > {})", x, y) }
                        else if opname.starts_with("VM_GE") { format!("({} >= {})", x, y) }

                        else if opname.to_string() == "CHKINS" || opname.starts_with("VM_IN") { format!("({} in {})", x, y) }

                        else {
                            // fallback to original call form
                            let mut s = String::new();
                            s.push_str(op);
                            s.push('(');
                            for (i, a) in args.iter().enumerate() {
                                if i != 0 { s.push_str(", "); }
                                s.push_str(&a.to_tjs_with(self.fmt_var));
                            }
                            s.push(')');
                            s
                        }
                    } else if let Some(x) = a0.as_deref() {
                        // unary families (also cover variants)
                        if opname.starts_with("VM_CHS") { format!("(-{})", x) }
                        else if opname.starts_with("VM_LNOT") { format!("(!{})", x) }
                        else if opname.starts_with("VM_BNOT") { format!("(~{})", x) }
                        else if opname.starts_with("VM_TYPEOF") { format!("(typeof {})", x) }
                        else if opname.starts_with("VM_DELETE") { format!("(delete {})", x) }
                        else if opname.starts_with("VM_INC") { format!("({} + 1)", x) } 
                        else if opname.starts_with("VM_DEC") { format!("({} - 1)", x) } 
                        else {
                            // fallback
                            let mut s = String::new();
                            s.push_str(op);
                            s.push('(');
                            for (i, a) in args.iter().enumerate() {
                                if i != 0 { s.push_str(", "); }
                                s.push_str(&a.to_tjs_with(self.fmt_var));
                            }
                            s.push(')');
                            s
                        }
                    } else {
                        format!("{}()", op)
                    };


                    call
                };

                if defs.is_empty() {
                    format!("{};", call)
                } else if defs.len() == 1 {
                    format!("{} = {};", (self.fmt_var)(defs[0]), call)
                } else {
                    // Multiple defs: use a temp array-like value.
                    // Still no helper functions; just structured, explicit assignments.
                    let mut s = String::new();
                    s.push_str("{ ");
                    s.push_str("var __t = ");
                    s.push_str(&call);
                    s.push_str("; ");
                    for (i, d) in defs.iter().enumerate() {
                        let _ = write!(
                            &mut s,
                            "{} = __t[{}]; ",
                            (self.fmt_var)(*d),
                            i
                        );
                    }
                    s.push_str("}");
                    s
                }
            }
        }
    }

    fn expr_to_tjs(&self, e: &Expr) -> String {
        e.to_tjs_with(self.fmt_var)
    }
}

/* ------------------------- utilities ------------------------- */

fn build_edge_copies(prog: &ExprProgram) -> HashMap<(usize, usize), Vec<(VarId, VarId)>> {
    let mut m: HashMap<(usize, usize), Vec<(VarId, VarId)>> = HashMap::new();
    for b in &prog.blocks {
        for phi in &b.phi {
            for (pred, v) in &phi.args {
                m.entry((*pred, b.id))
                    .or_default()
                    .push((phi.result, *v));
            }
        }
    }
    m
}

fn compute_reachable(prog: &ExprProgram, entry: usize) -> HashSet<usize> {
    let mut seen = HashSet::new();
    let mut stack = vec![entry];
    while let Some(n) = stack.pop() {
        if !seen.insert(n) {
            continue;
        }
        for &s in &prog.blocks[n].succ {
            stack.push(s);
        }
    }
    seen
}

fn compute_dominators(
    prog: &ExprProgram,
    entry: usize,
    reachable: &HashSet<usize>,
) -> Vec<HashSet<usize>> {
    let n = prog.blocks.len();
    let all: HashSet<usize> = (0..n).filter(|x| reachable.contains(x)).collect();

    let mut dom = vec![HashSet::new(); n];
    for b in 0..n {
        if !reachable.contains(&b) {
            continue;
        }
        if b == entry {
            dom[b].insert(entry);
        } else {
            dom[b] = all.clone();
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for b in 0..n {
            if !reachable.contains(&b) || b == entry {
                continue;
            }
            let preds = &prog.blocks[b].pred;
            if preds.is_empty() {
                continue;
            }
            let mut nd = all.clone();
            for &p in preds {
                if !reachable.contains(&p) {
                    continue;
                }
                nd = nd
                    .intersection(&dom[p])
                    .copied()
                    .collect::<HashSet<usize>>();
            }
            nd.insert(b);
            if nd != dom[b] {
                dom[b] = nd;
                changed = true;
            }
        }
    }
    dom
}

fn compute_postdominators(prog: &ExprProgram, reachable: &HashSet<usize>) -> Vec<HashSet<usize>> {
    let n = prog.blocks.len();
    let all: HashSet<usize> = (0..n).filter(|x| reachable.contains(x)).collect();

    let exits: HashSet<usize> = (0..n)
        .filter(|b| {
            if !reachable.contains(b) {
                return false;
            }
            matches!(
                prog.blocks[*b].term,
                Terminator::Ret | Terminator::Throw(_) // Exit/Fallthrough with no succ also treated later
            ) || prog.blocks[*b].succ.is_empty()
        })
        .collect();

    let mut pdom = vec![HashSet::new(); n];
    for b in 0..n {
        if !reachable.contains(&b) {
            continue;
        }
        if exits.contains(&b) {
            pdom[b].insert(b);
        } else {
            pdom[b] = all.clone();
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for b in 0..n {
            if !reachable.contains(&b) || exits.contains(&b) {
                continue;
            }
            let succs = &prog.blocks[b].succ;
            if succs.is_empty() {
                continue;
            }
            let mut nd = all.clone();
            for &s in succs {
                if !reachable.contains(&s) {
                    continue;
                }
                nd = nd
                    .intersection(&pdom[s])
                    .copied()
                    .collect::<HashSet<usize>>();
            }
            nd.insert(b);
            if nd != pdom[b] {
                pdom[b] = nd;
                changed = true;
            }
        }
    }
    pdom
}

fn compute_ipdom(pdom: &[HashSet<usize>]) -> Vec<Option<usize>> {
    let n = pdom.len();
    let mut ip = vec![None; n];
    for b in 0..n {
        let mut cand: Vec<usize> = pdom[b].iter().copied().collect();
        cand.retain(|x| *x != b);
        if cand.is_empty() {
            continue;
        }
        // pick c such that no other candidate post-dominates c
        let mut picked = None;
        'outer: for &c in &cand {
            for &d in &cand {
                if d == c {
                    continue;
                }
                if pdom[d].contains(&c) {
                    continue 'outer;
                }
            }
            picked = Some(c);
            break;
        }
        ip[b] = picked;
    }
    ip
}

fn compute_natural_loops(
    prog: &ExprProgram,
    dom: &[HashSet<usize>],
    reachable: &HashSet<usize>,
) -> HashMap<usize, HashSet<usize>> {
    let mut loops: HashMap<usize, HashSet<usize>> = HashMap::new();
    for u in 0..prog.blocks.len() {
        if !reachable.contains(&u) {
            continue;
        }
        for &v in &prog.blocks[u].succ {
            if !reachable.contains(&v) {
                continue;
            }
            // back edge u -> v if v dominates u
            if dom[u].contains(&v) {
                let mut set = HashSet::new();
                set.insert(v);
                set.insert(u);
                let mut stack = vec![u];
                while let Some(x) = stack.pop() {
                    for &p in &prog.blocks[x].pred {
                        if !reachable.contains(&p) {
                            continue;
                        }
                        if set.insert(p) {
                            stack.push(p);
                        }
                    }
                }
                loops
                    .entry(v)
                    .and_modify(|s| {
                        for n in &set {
                            s.insert(*n);
                        }
                    })
                    .or_insert(set);
            }
        }
    }
    loops
}

fn to_compound_assign(op: BinOp) -> Option<BinOp> {
    Some(match op {
        BinOp::Add => BinOp::AddAssign,
        BinOp::Sub => BinOp::SubAssign,
        BinOp::Mul => BinOp::MulAssign,
        BinOp::Div => BinOp::DivAssign,
        BinOp::Mod => BinOp::ModAssign,
        BinOp::Shl => BinOp::ShlAssign,
        BinOp::Shr => BinOp::ShrAssign,
        BinOp::UShr => BinOp::UShrAssign,
        BinOp::BitAnd => BinOp::AndAssign,
        BinOp::BitOr => BinOp::OrAssign,
        BinOp::BitXor => BinOp::XorAssign,
        _ => return None,
    })
}

fn is_control_op(op: &str) -> bool {
    op.eq_ignore_ascii_case("JMP")
        || op.eq_ignore_ascii_case("JF")
        || op.eq_ignore_ascii_case("JNF")
        || op.eq_ignore_ascii_case("RET")
        || op.eq_ignore_ascii_case("THROW")
        || op.eq_ignore_ascii_case("ENTRY")
        || op.eq_ignore_ascii_case("EXTRY")
}

fn infer_arg_regs(prog: &ExprProgram) -> Vec<i32> {
    let vars = collect_vars(prog);
    let mut neg_regs: Vec<i32> = vars
        .iter()
        .filter_map(|v| match v.var {
            Var::Reg(r) if r <= -3 => Some(r),
            _ => None,
        })
        .collect();
    neg_regs.sort();
    neg_regs.dedup();

    // Only keep the conventional arg window: r-3, r-4, ...
    // If none, return empty.
    if neg_regs.is_empty() {
        return vec![];
    }

    // Find the minimum negative register observed (e.g., -7)
    let min_r = *neg_regs.first().unwrap();

    // We always start at -3 as args base. If min_r is -1/-2, ignore them (usually special regs).
    let start = -3;
    if min_r > start {
        return vec![]; // no conventional args seen
    }

    // return [-3, -4, ..., min_r]
    (min_r..=start).rev().collect()
}

fn arg_name_for_reg(r: i32) -> String {
    // r-3 -> a0, r-4 -> a1 ...
    let idx = (-3 - r) as usize;
    format!("a{}_1", idx)
}

fn emit_var_decls(
    out: &mut String,
    prog: &ExprProgram,
    fmt_var: &dyn Fn(VarId) -> String,
) -> Result<()> {
    let mut vars: Vec<VarId> = collect_vars(prog);
    vars.sort_by_key(|v| (var_key(v), v.ver));
    vars.retain(|v| match v.var {
        Var::Reg(r) => r >= 0,
        _ => true,
    });
    if vars.is_empty() {
        writeln!(out, "  // no SSA vars")?;
        return Ok(());
    }

    // emit in chunks
    let mut i = 0usize;
    while i < vars.len() {
        let end = (i + 12).min(vars.len());
        write!(out, "  var ")?;
        for j in i..end {
            if j != i {
                write!(out, ", ")?;
            }
            write!(out, "{}", fmt_var(vars[j]))?;
        }
        writeln!(out, ";")?;
        i = end;
    }
    Ok(())
}

fn collect_vars(prog: &ExprProgram) -> Vec<VarId> {
    let mut s: HashSet<VarId> = HashSet::new();

    for b in &prog.blocks {
        for p in &b.phi {
            s.insert(p.result);
            for (_pred, v) in &p.args {
                s.insert(*v);
            }
        }
        for st in &b.stmts {
            collect_vars_stmt(st, &mut s);
        }
        collect_vars_term(&b.term, &mut s);
    }

    s.into_iter().collect()
}

fn collect_vars_stmt(st: &Stmt, s: &mut HashSet<VarId>) {
    match st {
        Stmt::Assign { dst, expr } => {
            s.insert(*dst);
            collect_vars_expr(expr, s);
        }
        Stmt::Store { target, value } => {
            collect_vars_expr(target, s);
            collect_vars_expr(value, s);
        }
        Stmt::Update { dst, target, rhs, .. } => {
            if let Some(d) = dst {
                s.insert(*d);
            }
            collect_vars_expr(target, s);
            collect_vars_expr(rhs, s);
        }
        Stmt::Expr(e) => collect_vars_expr(e, s),
        Stmt::Opaque { args, defs, .. } => {
            for d in defs {
                s.insert(*d);
            }
            for a in args {
                collect_vars_expr(a, s);
            }
        }
    }
}

fn collect_vars_term(t: &Terminator, s: &mut HashSet<VarId>) {
    match t {
        Terminator::Br { cond, .. } => collect_vars_expr(cond, s),
        Terminator::Throw(e) => collect_vars_expr(e, s),
        _ => {}
    }
}

fn collect_vars_expr(e: &Expr, s: &mut HashSet<VarId>) {
    match e {
        Expr::SsaVar(v) => {
            s.insert(*v);
        }
        Expr::Unary(_, a) => collect_vars_expr(a, s),
        Expr::Deref(a) => collect_vars_expr(a, s),
        Expr::Binary(_, a, b) => {
            collect_vars_expr(a, s);
            collect_vars_expr(b, s);
        }
        Expr::Call(f, args) | Expr::New(f, args) => {
            collect_vars_expr(f, s);
            for a in args {
                collect_vars_expr(a, s);
            }
        }
        Expr::Index(a, b) => {
            collect_vars_expr(a, s);
            collect_vars_expr(b, s);
        }
        Expr::Member(a, _) => collect_vars_expr(a, s),
        Expr::MethodCall { base, args, .. } => {
            collect_vars_expr(base, s);
            for a in args {
                collect_vars_expr(a, s);
            }
        }
        Expr::Opaque(_, args) => {
            for a in args {
                collect_vars_expr(a, s);
            }
        }
        _ => {}
    }
}

fn var_key(v: &VarId) -> (u8, i32) {
    match v.var {
        Var::Reg(r) => (0, r),
        Var::Flag => (1, 0),
        Var::Exception => (2, 0),
    }
}

fn fmt_vid_tjs(vid: VarId) -> String {
    match vid.var {
        Var::Reg(r) => {
            // format!("r{}_{}", r, vid.ver)
            if r >= 0 {
                format!("r{}_{}", r, vid.ver)
            } else {
                format!("a{}_{}", -3 - r, vid.ver)
            }
        },
        Var::Flag => format!("flag_{}", vid.ver),
        Var::Exception => format!("exc_{}", vid.ver),
    }
}

fn obj_lhs(index: usize, name: Option<&str>) -> String {
    if let Some(n) = name {
        let parts: Vec<&str> = n.split('.').collect();
        if !parts.is_empty() && parts.iter().all(|p| is_identifier(p)) {
            return parts.join(".");
        }
    }
    format!("obj{}", index)
}

fn is_identifier(s: &str) -> bool {
    let mut it = s.chars();
    let Some(c0) = it.next() else { return false; };
    if !(c0 == '_' || c0.is_ascii_alphabetic()) {
        return false;
    }
    it.all(|c| c == '_' || c.is_ascii_alphanumeric())
}
