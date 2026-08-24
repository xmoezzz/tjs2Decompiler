use anyhow::{Result, bail};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;

use crate::{Tjs2File, Tjs2Object, Variant};
use crate::vmcodes::vm;

use super::cfg::Cfg;
use super::decode::decode_object;
use super::expr::{BinOp, Expr, UnOp};
use super::expr_build::{ExprProgram, Stmt, Terminator};
use super::ssa::{SsaProgram, Var, VarId};

fn vm_binop(op: &str) -> Option<BinOp> {
    match op {
        "VM_ADD" | "ADD" => Some(BinOp::Add),
        "VM_SUB" | "SUB" => Some(BinOp::Sub),
        "VM_MUL" | "MUL" => Some(BinOp::Mul),
        "VM_DIV" | "DIV" => Some(BinOp::Div),
        "VM_IDIV" | "IDIV" => Some(BinOp::IDiv),
        "VM_MOD" | "MOD" => Some(BinOp::Mod),

        "VM_SAL" | "SHL" => Some(BinOp::Shl),
        "VM_SAR" | "SHR" => Some(BinOp::Shr),
        "VM_SR" | "USHR" => Some(BinOp::UShr),

        "VM_BAND" | "BAND" => Some(BinOp::BitAnd),
        "VM_BXOR" | "BXOR" => Some(BinOp::BitXor),
        "VM_BOR" | "BOR" => Some(BinOp::BitOr),

        "VM_LAND" | "LAND" => Some(BinOp::LogAnd),
        "VM_LOR" | "LOR" => Some(BinOp::LogOr),

        "VM_EQ" | "EQ" => Some(BinOp::Eq),
        "VM_NE" | "NE" => Some(BinOp::Ne),
        "VM_DEQ" | "DEQ" => Some(BinOp::StrictEq),
        "VM_DNE" | "DNE" => Some(BinOp::StrictNe),

        "VM_LT" | "LT" => Some(BinOp::Lt),
        "VM_LE" | "LE" => Some(BinOp::Le),
        "VM_GT" | "GT" => Some(BinOp::Gt),
        "VM_GE" | "GE" => Some(BinOp::Ge),

        "VM_IN" | "IN" => Some(BinOp::In),
        "VM_CHKINS" | "CHKINS" => Some(BinOp::InstanceOf),

        _ => None,
    }
}

fn vm_unop(op: &str) -> Option<UnOp> {
    match op {
        "VM_CHS" | "CHS" => Some(UnOp::Neg),
        "VM_LNOT" | "LNOT" => Some(UnOp::Not),
        "VM_BNOT" | "BNOT" => Some(UnOp::BitNot),
        "VM_NUM" | "NUM" => Some(UnOp::Num),
        "VM_ASC" | "ASC" => Some(UnOp::CharCode),
        "VM_CHR" | "CHR" => Some(UnOp::CharFromCode),
        "VM_TYPEOF" | "TYPEOF" => Some(UnOp::Typeof),
        "VM_DELETE" | "DELETE" => Some(UnOp::Delete),
        _ => None,
    }
}

fn fmt_octet_literal(bytes: &[u8]) -> String {
    let mut s = String::from("<%");
    for b in bytes {
        s.push_str(&format!(" {:02x}", b));
    }
    if !bytes.is_empty() { s.push(' '); }
    s.push_str("%>");
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

/// Returns true if obj or any of its ancestors (via parent chain) is a class (context_type=6),
/// stopping at context_type=0 (global). Used to decide if `%-2` (scope) maps to `this`.
fn scope_is_class(file: &Tjs2File, obj: &Tjs2Object) -> bool {
    let mut cur = obj.parent;
    loop {
        if cur < 0 || cur as usize >= file.objects.len() {
            return false;
        }
        let p = &file.objects[cur as usize];
        match p.context_type {
            0 => return false,
            6 => return true,
            _ => cur = p.parent,
        }
    }
}

/// Build a fmt_var closure appropriate for the given object's context.
/// - r >= 0: r{r}_{ver}
/// - r == -1: "this"
/// - r == -2: "this" if in a class scope, else "global"
/// - r <= -3 and frame_idx < arg_count: "a{frame_idx}" (declared parameter)
/// - r <= -3 and frame_idx >= arg_count: "_fr{frame_idx - arg_count}" (local frame slot)
fn make_fmt_var(_in_class: bool, arg_count: usize, collapse_base: i32) -> impl Fn(VarId) -> String {
    move |vid: VarId| -> String {
        match vid.var {
            Var::Reg(r) if r >= 0 => format!("r{}_{}", r, vid.ver),
            Var::Reg(-1) => "this".to_string(),
            // %-2 has no standalone source-level spelling.  expr_build lowers
            // every genuine use to Expr::ScopeProxy before formatting.  If a
            // raw SSA value reaches here, fail the later semantic audit rather
            // than silently changing it to this/global.
            Var::Reg(-2) => "__tjs2dec_unrepresentable_scope_proxy".to_string(),
            Var::Reg(r) => {
                let frame_idx = (-3 - r) as usize;
                if frame_idx < arg_count {
                    format!("a{}", frame_idx)
                } else if collapse_base >= 0 && frame_idx == collapse_base as usize {
                    "__tjs2dec_args".to_string()
                } else {
                    let collapse_shift = usize::from(collapse_base >= 0 && frame_idx > collapse_base as usize);
                    format!("_fr{}", frame_idx.saturating_sub(arg_count + collapse_shift))
                }
            }
            Var::Flag => format!("flag_{}", vid.ver),
            Var::Result => format!("__tjs2dec_retval_{}", vid.ver),
            Var::Exception => format!("exc_{}", vid.ver),
        }
    }
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

fn const_propagate_intrablock(prog: &mut ExprProgram) {
    // Despite the historical name, this is now a whole-function SSA value
    // propagation pass.  Only semantically inert values are propagated, so a
    // rewrite can never duplicate/reorder a getter, conversion, allocation,
    // call, exception, or other observable operation.
    let mut env: HashMap<VarId, Expr> = HashMap::new();
    env.insert(
        VarId { var: Var::Reg(0), ver: 0 },
        Expr::Void,
    );
    env.insert(
        VarId { var: Var::Result, ver: 0 },
        Expr::Void,
    );

    // SSA definitions are unique. Re-scan to a fixed point because aliases may
    // be discovered in an order different from block layout.
    loop {
        let mut changed = false;
        for b in &prog.blocks {
            for st in &b.stmts {
                if let Stmt::Assign { dst, expr } = st {
                    if let Some(v) = prop_value(expr, &env) {
                        let same = env.get(dst).map(|old| old.to_tjs() == v.to_tjs()).unwrap_or(false);
                        if !same {
                            env.insert(*dst, v);
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed { break; }
    }

    for b in &mut prog.blocks {
        for st in &mut b.stmts {
            rewrite_stmt(st, &env);
        }
        match &mut b.term {
            Terminator::Br { cond, .. } | Terminator::Ret(cond) | Terminator::Throw(cond) => {
                rewrite_expr(cond, &env);
            }
            _ => {}
        }
    }
}

fn rewrite_stmt(st: &mut Stmt, env: &HashMap<VarId, Expr>) {
    match st {
        Stmt::Assign { expr, .. } => rewrite_expr(expr, env),
        Stmt::Store { target, value } => {
            rewrite_expr(target, env);
            rewrite_expr(value, env);
        }
        Stmt::MemberDecl { value, .. } => rewrite_expr(value, env),
        Stmt::Update { target, rhs, .. } => {
            rewrite_expr(target, env);
            rewrite_expr(rhs, env);
        }
        Stmt::IncDec { target, .. } => rewrite_expr(target, env),
        Stmt::Expr(e) => rewrite_expr(e, env),
        Stmt::Opaque { args, .. } => {
            for a in args {
                rewrite_expr(a, env);
            }
        }
    }
}

fn rewrite_expr(e: &mut Expr, env: &HashMap<VarId, Expr>) {
    match e {
        Expr::SsaVar(v) => {
            if let Some(rep) = env.get(v).cloned() {
                *e = rep;
            }
        }
        Expr::Unary(_, expr) | Expr::ArgExpand(expr) => rewrite_expr(expr, env),
        Expr::Binary(_, lhs, rhs) => {
            rewrite_expr(lhs, env);
            rewrite_expr(rhs, env);
        }
        Expr::Conditional {
            cond,
            then_expr,
            else_expr,
        } => {
            rewrite_expr(cond, env);
            rewrite_expr(then_expr, env);
            rewrite_expr(else_expr, env);
        }
        Expr::Member(base, _) | Expr::Deref(base) => rewrite_expr(base, env),
        Expr::Index(base, index) => {
            rewrite_expr(base, env);
            rewrite_expr(index, env);
        }
        Expr::Call(callee, args) => {
            rewrite_expr(callee, env);
            for a in args {
                rewrite_expr(a, env);
            }
        }
        Expr::New(ctor, args) => {
            rewrite_expr(ctor, env);
            for a in args {
                rewrite_expr(a, env);
            }
        }
        Expr::MethodCall { base, args, .. } => {
            rewrite_expr(base, env);
            for a in args {
                rewrite_expr(a, env);
            }
        }
        Expr::ArrayLiteral(items) => {
            for item in items {
                rewrite_expr(item, env);
            }
        }
        Expr::DictionaryLiteral(items) => {
            for (key, value) in items {
                rewrite_expr(key, env);
                rewrite_expr(value, env);
            }
        }
        Expr::Opaque(_, args) => {
            for a in args {
                rewrite_expr(a, env);
            }
        }
        _ => {}
    }
}

/// Decide whether `rhs` is safe to propagate as a value.
/// Keep this deliberately strict. TJS member/index reads can invoke property
/// handlers, so moving a property read into a later expression can duplicate or
/// reorder observable behavior. Only literal values and register aliases are
/// propagated in executable code.
fn prop_value(rhs: &Expr, env: &HashMap<VarId, Expr>) -> Option<Expr> {
    let mut v = rhs.clone();
    rewrite_expr(&mut v, env);

    match &v {
        Expr::Void
        | Expr::Null
        | Expr::Bool(_)
        | Expr::Int(_)
        | Expr::Real(_)
        | Expr::Str(_)
        | Expr::Octet(_)
        | Expr::ObjectRef(_)
        | Expr::GeneratorRef(_)
        | Expr::ScopeProxy => Some(v),

        // A pure SSA alias is safe to move. Property reads are intentionally
        // excluded even when their base is global/this.
        Expr::SsaVar(_) => Some(v),

        // VM_GLOBAL is a stable value load, not an opaque operation.  Keep the
        // representation for formatting, but allow ordinary SSA propagation.
        Expr::Opaque(name, args) if name == "global" && args.is_empty() => Some(v),

        _ => None,
    }
}


fn emit_object_body(obj: &Tjs2Object, file: &Tjs2File, indent: usize) -> Result<(String, String)> {
    let mut out = String::new();

    let cfg = Cfg::build(obj)?;
    let ssa = SsaProgram::from_cfg(&cfg)?;
    let mut prog = ExprProgram::from_ssa(file, obj, &ssa)?;

    let params = build_params(obj);
    let arg_count = obj.func_decl_arg_count.max(0) as usize;

    let in_class = scope_is_class(file, obj);
    let fmt_var = make_fmt_var(in_class, arg_count, obj.func_decl_collapse_base);

    // RET now consumes the SSA version of the VM result slot directly.  This
    // replaces the old block-local "last SRV" guess and correctly carries the
    // return state through phi nodes, loops and ENTRY/EXTRY boundaries.
    let mut ret_expr: Vec<Option<Expr>> = prog
        .blocks
        .iter()
        .map(|b| match &b.term {
            Terminator::Ret(e) => Some(e.clone()),
            _ => None,
        })
        .collect();
    optimize_expr_program(&mut prog, &mut ret_expr, Some(&cfg.block_handler_stack));

    emit_var_decls(&mut out, &prog, &fmt_var, arg_count, obj.func_decl_collapse_base, indent)?;

    let mut s = Structurer::new(&cfg, &prog, &fmt_var, ret_expr);
    let lines = s.emit_function_body(prog.entry_block, indent);

    for l in lines {
        writeln!(out, "{}", l)?;
    }
    Ok((out, params))
}

fn object_uses_unnamed_arg_expand(obj: &Tjs2Object) -> bool {
    let Ok(insns) = decode_object(obj) else { return false; };
    for insn in insns {
        let header = match insn.op {
            x if x == vm::VM_CALL || x == vm::VM_NEW => 4usize,
            x if x == vm::VM_CALLD || x == vm::VM_CALLI => 5usize,
            _ => continue,
        };
        if insn.words.get(header - 1).copied() != Some(-2) { continue; }
        let count = insn.words.get(header).copied().unwrap_or(0).max(0) as usize;
        for i in 0..count {
            if insn.words.get(header + 1 + i * 2).copied() == Some(2) {
                return true;
            }
        }
    }
    false
}

/// Reconstruct the declaration-level argument contract.  Regular arguments
/// occupy %-3..; a named collapse argument occupies the frame slot at
/// FuncDeclCollapseBase but is not included in FuncDeclArgCount.  Anonymous
/// `*` has no local slot; it is needed in source only when the function uses
/// FAT_UNNAMED expansion (or metadata moved its base away from the default 0).
fn build_params(obj: &Tjs2Object) -> String {
    let n = obj.func_decl_arg_count.max(0) as usize;
    let mut params = (0..n).map(|i| format!("a{}", i)).collect::<Vec<_>>();
    if obj.func_decl_collapse_base >= 0 {
        params.push("__tjs2dec_args*".to_string());
    } else if obj.func_decl_unnamed_arg_array_base > 0 || object_uses_unnamed_arg_expand(obj) {
        params.push("*".to_string());
    }
    params.join(", ")
}

/// Propagate constant assignments into ret_expr for each block.
fn propagate_into_ret_expr(ret_expr: &mut Vec<Option<Expr>>, prog: &ExprProgram, allow_property_reads: bool) {
    for b in &prog.blocks {
        let Some(re) = ret_expr.get_mut(b.id) else {
            continue;
        };
        let Some(e) = re else {
            continue;
        };
        let mut env: HashMap<VarId, Expr> = HashMap::new();
        for st in &b.stmts {
            match st {
                Stmt::Assign { dst, expr } => {
                    let mut v = expr.clone();
                    rewrite_expr(&mut v, &env);
                    if let Some(pv) = prop_value_for_return_inference(&v, &env, allow_property_reads) {
                        env.insert(*dst, pv);
                    }
                }
                Stmt::Opaque { op, args, defs }
                    if (op.eq_ignore_ascii_case("VM_SRV") || op.eq_ignore_ascii_case("SRV"))
                        && !args.is_empty()
                        && !defs.is_empty() =>
                {
                    let mut v = args[0].clone();
                    rewrite_expr(&mut v, &env);
                    if let Some(pv) = prop_value_for_return_inference(&v, &env, allow_property_reads) {
                        env.insert(defs[0], pv);
                    }
                }
                _ => {}
            }
        }
        rewrite_expr(e, &env);
    }
}

fn prop_value_for_return_inference(
    rhs: &Expr,
    env: &HashMap<VarId, Expr>,
    allow_property_reads: bool,
) -> Option<Expr> {
    let mut v = rhs.clone();
    rewrite_expr(&mut v, env);
    if let Some(simple) = prop_value(&v, &HashMap::new()) {
        return Some(simple);
    }
    if allow_property_reads {
        match v {
            Expr::Member(..) | Expr::Index(..) | Expr::Deref(..) => return Some(v),
            _ => {}
        }
    }
    None
}

/// Eliminate phi nodes whose results are never truly used (i.e. only consumed by other dead
/// phis or by edge copies that feed dead phis).  After this pass, `build_edge_copies` will
/// not emit the now-removed phi copies, and a subsequent `remove_dead_assigns` will clean up
/// any statements that only computed values for those dead phi args.
fn remove_dead_phis(prog: &mut ExprProgram, ret_expr: &[Option<Expr>]) {
    // Phase 1 – seed: vars used in stmts / terminators / ret_expr (NOT phi args yet).
    let mut live: HashSet<VarId> = HashSet::new();
    for b in &prog.blocks {
        for st in &b.stmts {
            collect_uses_stmt(st, &mut live);
        }
        collect_vars_term(&b.term, &mut live);
    }
    for re in ret_expr {
        if let Some(e) = re {
            collect_vars_expr(e, &mut live);
        }
    }

    // Phase 2 – propagate: if a phi result is live, its args become live.
    let mut changed = true;
    while changed {
        changed = false;
        for b in &prog.blocks {
            for phi in &b.phi {
                if live.contains(&phi.result) {
                    for (_, v) in &phi.args {
                        if live.insert(*v) {
                            changed = true;
                        }
                    }
                }
            }
        }
    }

    // Phase 3 – prune: drop every phi whose result is not in the live set.
    for b in &mut prog.blocks {
        b.phi.retain(|phi| live.contains(&phi.result));
    }
}

/// Conservative semantic effect/taint summary.  `may_throw` is deliberately
/// independent from state writes: an otherwise unused computation that can
/// throw is observable and therefore cannot be eliminated.
#[derive(Debug, Clone, Copy, Default)]
struct SemanticEffects {
    reads_property: bool,
    writes_state: bool,
    calls: bool,
    allocates: bool,
    may_throw: bool,
    opaque: bool,
}

impl SemanticEffects {
    fn merge(mut self, other: Self) -> Self {
        self.reads_property |= other.reads_property;
        self.writes_state |= other.writes_state;
        self.calls |= other.calls;
        self.allocates |= other.allocates;
        self.may_throw |= other.may_throw;
        self.opaque |= other.opaque;
        self
    }
    fn erasable(self) -> bool {
        !(self.reads_property || self.writes_state || self.calls || self.allocates || self.may_throw || self.opaque)
    }
}

fn expr_effects(expr: &Expr) -> SemanticEffects {
    match expr {
        Expr::Reg(_) | Expr::Flag | Expr::ConstData(_) | Expr::SsaVar(_)
        | Expr::Void | Expr::Null | Expr::Bool(_) | Expr::Int(_) | Expr::Real(_)
        | Expr::Str(_) | Expr::Octet(_) | Expr::ObjectRef(_) | Expr::GeneratorRef(_)
        | Expr::ArgUnnamedExpand | Expr::ArgForwardAll => SemanticEffects::default(),

        // The proxy itself is a binding token; moving an alias of it does not
        // perform dispatch.  Escaping uses are rejected separately by the
        // source representability audit.
        Expr::ScopeProxy => SemanticEffects::default(),

        Expr::Member(base, _) => expr_effects(base).merge(SemanticEffects {
            reads_property: true, may_throw: true, ..Default::default()
        }),
        Expr::Index(base, key) => expr_effects(base).merge(expr_effects(key)).merge(SemanticEffects {
            reads_property: true, may_throw: true, ..Default::default()
        }),
        Expr::Deref(inner) => expr_effects(inner).merge(SemanticEffects {
            reads_property: true, may_throw: true, ..Default::default()
        }),
        Expr::Unary(op, inner) => {
            let mut eff = expr_effects(inner);
            // VM conversions, delete/invalidate, and substance access may all
            // raise through variant/object dispatch.  Keep them unless used.
            eff.may_throw = true;
            if matches!(op, UnOp::Delete | UnOp::Invalidate) { eff.writes_state = true; }
            if matches!(op, UnOp::IgnoreProp) { eff.reads_property = true; }
            eff
        }
        Expr::Binary(op, lhs, rhs) => {
            let mut eff = expr_effects(lhs).merge(expr_effects(rhs));
            eff.may_throw = true;
            if matches!(op, BinOp::Assign | BinOp::AddAssign | BinOp::SubAssign
                | BinOp::MulAssign | BinOp::DivAssign | BinOp::IDivAssign | BinOp::ModAssign
                | BinOp::ShlAssign | BinOp::ShrAssign | BinOp::UShrAssign
                | BinOp::AndAssign | BinOp::OrAssign | BinOp::XorAssign
                | BinOp::LogAndAssign | BinOp::LogOrAssign) {
                eff.writes_state = true;
            }
            eff
        }
        Expr::Conditional {
            cond,
            then_expr,
            else_expr,
        } => {
            // Only one arm executes, but a union is the correct conservative
            // taint summary for legality checks: moving/deleting the complete
            // conditional is unsafe if either possible arm is observable.
            expr_effects(cond)
                .merge(expr_effects(then_expr))
                .merge(expr_effects(else_expr))
        }
        Expr::Call(callee, args) => {
            let mut eff = expr_effects(callee);
            for a in args { eff = eff.merge(expr_effects(a)); }
            eff.calls = true; eff.may_throw = true; eff
        }
        Expr::MethodCall { base, args, .. } => {
            let mut eff = expr_effects(base);
            for a in args { eff = eff.merge(expr_effects(a)); }
            eff.reads_property = true; eff.calls = true; eff.may_throw = true; eff
        }
        Expr::New(ctor, args) => {
            let mut eff = expr_effects(ctor);
            for a in args { eff = eff.merge(expr_effects(a)); }
            eff.calls = true; eff.allocates = true; eff.may_throw = true; eff
        }
        Expr::ArrayLiteral(items) => {
            let mut eff = SemanticEffects { allocates: true, may_throw: true, ..Default::default() };
            for a in items { eff = eff.merge(expr_effects(a)); }
            eff
        }
        Expr::DictionaryLiteral(items) => {
            let mut eff = SemanticEffects { allocates: true, may_throw: true, ..Default::default() };
            for (k, v) in items { eff = eff.merge(expr_effects(k)).merge(expr_effects(v)); }
            eff
        }
        Expr::RegExpLiteral(_) => SemanticEffects {
            reads_property: true,
            calls: true,
            allocates: true,
            may_throw: true,
            ..Default::default()
        },
        Expr::ArgExpand(inner) => expr_effects(inner).merge(SemanticEffects { may_throw: true, ..Default::default() }),
        // `global` is emitted by VM_GLOBAL as a distinguished VM value.  It is
        // represented as Opaque only to avoid widening Expr further; reading
        // the value itself performs no dispatch and cannot throw.  Treating it
        // as a generic opaque operation prevents exact reconstruction of the
        // compiler's Array/Dictionary/RegExp templates.
        Expr::Opaque(name, args) if name == "global" && args.is_empty() => {
            SemanticEffects::default()
        }
        Expr::Opaque(_, args) => {
            let mut eff = SemanticEffects { opaque: true, may_throw: true, ..Default::default() };
            for a in args { eff = eff.merge(expr_effects(a)); }
            eff
        }
    }
}

/// Remove dead SSA assignments to a fixed point, but only when evaluating the
/// RHS is proven unobservable.  This is an exception-aware DCE, not a textual
/// temporary-variable cleanup.
fn remove_dead_assigns(prog: &mut ExprProgram, ret_expr: &[Option<Expr>]) {
    loop {
        let mut used: HashSet<VarId> = HashSet::new();
        for b in &prog.blocks {
            for phi in &b.phi {
                for (_, v) in &phi.args { used.insert(*v); }
            }
            for st in &b.stmts { collect_uses_stmt(st, &mut used); }
            collect_vars_term(&b.term, &mut used);
        }
        for re in ret_expr {
            if let Some(e) = re { collect_vars_expr(e, &mut used); }
        }

        let mut removed = false;
        for b in &mut prog.blocks {
            b.stmts.retain(|st| {
                if let Stmt::Assign { dst, expr } = st {
                    if !used.contains(dst) && expr_effects(expr).erasable() {
                        removed = true;
                        return false;
                    }
                }
                true
            });
        }
        if !removed { break; }
    }
}

/// Collect only the "use" side of a statement (not defs of Assign).
fn collect_uses_stmt(st: &Stmt, s: &mut HashSet<VarId>) {
    match st {
        Stmt::Assign { expr, .. } => collect_vars_expr(expr, s), // dst is a def, skip it
        Stmt::Store { target, value } => {
            collect_vars_expr(target, s);
            collect_vars_expr(value, s);
        }
        Stmt::MemberDecl { value, .. } => collect_vars_expr(value, s),
        Stmt::Update { target, rhs, .. } => {
            // `dst` is a definition of the value returned by the VM property
            // operation, not an input use.  Counting it as a use makes every
            // optional result artificially live forever.
            collect_vars_expr(target, s);
            collect_vars_expr(rhs, s);
        }
        Stmt::IncDec { target, .. } => {
            collect_vars_expr(target, s);
        }
        Stmt::Expr(e) => collect_vars_expr(e, s),
        Stmt::Opaque { args, .. } => {
            // Opaque defs are definitions too; only their operands seed
            // liveness.  The opaque statement itself is retained separately
            // because its effects are not proven erasable.
            for a in args {
                collect_vars_expr(a, s);
            }
        }
    }
}

/// Drop only the synthetic SSA destination of an observable property update
/// when that returned value is provably unused.  The property operation itself
/// remains in place, preserving dispatch, side effects, and exceptions.
fn clear_unused_mutation_results(prog: &mut ExprProgram, ret_expr: &[Option<Expr>]) -> bool {
    let mut used: HashSet<VarId> = HashSet::new();
    for b in &prog.blocks {
        for phi in &b.phi {
            for (_, v) in &phi.args { used.insert(*v); }
        }
        for st in &b.stmts { collect_uses_stmt(st, &mut used); }
        collect_vars_term(&b.term, &mut used);
    }
    for re in ret_expr {
        if let Some(e) = re { collect_vars_expr(e, &mut used); }
    }

    let mut changed = false;
    for b in &mut prog.blocks {
        for st in &mut b.stmts {
            match st {
                Stmt::Update { dst, .. } | Stmt::IncDec { dst, .. } => {
                    if dst.as_ref().is_some_and(|d| !used.contains(d)) {
                        *dst = None;
                        changed = true;
                    }
                }
                _ => {}
            }
        }
    }
    changed
}

fn is_internal_vm_value(v: VarId) -> bool {
    matches!(v.var, Var::Reg(r) if r >= 0) || matches!(v.var, Var::Flag | Var::Result)
}

fn is_control_stmt(st: &Stmt) -> bool {
    matches!(st, Stmt::Opaque { op, .. } if is_control_op(op))
}

#[derive(Debug, Clone)]
struct RegionExpr {
    expr: Expr,
    consumed: Vec<(usize, usize)>,
    consumed_defs: HashSet<VarId>,
}

/// Resolve a value through assignment-only SSA code in `blocks`.  This helper
/// is intentionally stricter than ordinary copy propagation: every observable
/// statement in an arm must contribute to the reconstructed value.  That is
/// what makes it safe to move the arm into a lazy `?:`, `&&`, or `||` source
/// expression without changing execution count/order.
fn extract_region_expr(
    prog: &ExprProgram,
    blocks: &[usize],
    seed: Expr,
    root_suffix: bool,
) -> Option<RegionExpr> {
    let mut flat = Vec::<(usize, usize)>::new();
    let mut region_defs = HashSet::<VarId>::new();
    for &bid in blocks {
        let block = prog.blocks.get(bid)?;
        for (idx, st) in block.stmts.iter().enumerate() {
            if let Stmt::Assign { dst, .. } = st {
                region_defs.insert(*dst);
            }
            if !is_control_stmt(st) {
                flat.push((bid, idx));
            }
        }
    }

    let mut needed = HashSet::<VarId>::new();
    collect_vars_expr(&seed, &mut needed);
    needed.retain(|v| region_defs.contains(v));

    let mut consumed = Vec::<(usize, usize)>::new();
    let mut consumed_defs = HashSet::<VarId>::new();
    let mut have_consumed = false;

    for &(bid, idx) in flat.iter().rev() {
        let st = &prog.blocks[bid].stmts[idx];
        match st {
            Stmt::Assign { dst, expr } if needed.contains(dst) => {
                needed.remove(dst);
                let mut deps = HashSet::new();
                collect_vars_expr(expr, &mut deps);
                for dep in deps {
                    if region_defs.contains(&dep) {
                        needed.insert(dep);
                    }
                }
                consumed.push((bid, idx));
                consumed_defs.insert(*dst);
                have_consumed = true;
            }
            Stmt::Assign { dst, expr } => {
                // For a branch arm, any leftover observable producer means the
                // arm is more than a value expression.  For a root block we
                // may stop at an earlier source statement, but only after the
                // complete condition suffix has been captured.
                if !expr_effects(expr).erasable() {
                    if root_suffix && have_consumed && needed.is_empty() {
                        break;
                    }
                    return None;
                }
                // A pure, unused assignment can be left for DCE.  If its value
                // is live outside the region, the branch cannot disappear.
                if count_var_uses(prog, *dst) != 0 {
                    if root_suffix && have_consumed && needed.is_empty() {
                        break;
                    }
                    return None;
                }
            }
            _ => {
                if root_suffix && have_consumed && needed.is_empty() {
                    break;
                }
                return None;
            }
        }
    }

    if !needed.is_empty() {
        return None;
    }

    consumed.reverse();
    let mut env = HashMap::<VarId, Expr>::new();
    for &(bid, idx) in &consumed {
        let Stmt::Assign { dst, expr } = &prog.blocks[bid].stmts[idx] else {
            return None;
        };
        let mut rhs = expr.clone();
        rewrite_expr(&mut rhs, &env);
        env.insert(*dst, rhs);
    }
    let mut expr = seed;
    rewrite_expr(&mut expr, &env);

    // No consumed synthetic value may survive in the reconstructed tree.
    let mut unresolved = HashSet::new();
    collect_vars_expr(&expr, &mut unresolved);
    if unresolved.iter().any(|v| consumed_defs.contains(v)) {
        return None;
    }

    Some(RegionExpr {
        expr,
        consumed,
        consumed_defs,
    })
}

fn linear_chain(prog: &ExprProgram, start: usize, limit: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut cur = start;
    for _ in 0..limit {
        if cur >= prog.blocks.len() || !seen.insert(cur) {
            break;
        }
        out.push(cur);
        match &prog.blocks[cur].term {
            Terminator::Jmp(t) => cur = *t,
            Terminator::Fallthrough | Terminator::Exit => {
                let succ = normal_successors_of_block(prog, cur);
                if succ.len() != 1 {
                    break;
                }
                cur = succ[0];
            }
            Terminator::Br { .. } | Terminator::Ret(_) | Terminator::Throw(_) => break,
        }
    }
    out
}

fn simple_branch_region(
    prog: &ExprProgram,
    root: usize,
) -> Option<(usize, Vec<usize>, Vec<usize>, Expr, usize, usize)> {
    let Terminator::Br { cond, if_true, if_false } = &prog.blocks.get(root)?.term else {
        return None;
    };
    let tc = linear_chain(prog, *if_true, 32);
    let fc = linear_chain(prog, *if_false, 32);
    let mut fpos = HashMap::new();
    for (i, &b) in fc.iter().enumerate() {
        fpos.insert(b, i);
    }
    let mut best: Option<(usize, usize, usize)> = None;
    for (ti, &b) in tc.iter().enumerate() {
        if let Some(&fi) = fpos.get(&b) {
            let score = ti + fi;
            if best.map_or(true, |(_, bt, bf)| score < bt + bf) {
                best = Some((b, ti, fi));
            }
        }
    }
    let (join, ti, fi) = best?;
    let tpath = tc[..ti].to_vec();
    let fpath = fc[..fi].to_vec();

    // Each arm block must be owned by this branch.  An external predecessor
    // means moving its computation into this branch expression would remove
    // behavior from another entry path (the MsgHack shared-failure shape is a
    // deliberate example and is handled by a separate chain recognizer).
    for (path, first) in [(&tpath, *if_true), (&fpath, *if_false)] {
        let mut expected_pred = root;
        for &bid in path {
            let preds = prog.blocks[bid]
                .pred
                .iter()
                .copied()
                .filter(|p| *p < prog.blocks.len())
                .collect::<HashSet<_>>();
            if preds.len() != 1 || !preds.contains(&expected_pred) {
                return None;
            }
            expected_pred = bid;
        }
        let _ = first;
    }

    let tpred = tpath.last().copied().unwrap_or(root);
    let fpred = fpath.last().copied().unwrap_or(root);
    Some((join, tpath, fpath, cond.clone(), tpred, fpred))
}

fn remove_consumed_statements(prog: &mut ExprProgram, consumed: &[(usize, usize)]) {
    let mut by_block: HashMap<usize, Vec<usize>> = HashMap::new();
    for &(bid, idx) in consumed {
        by_block.entry(bid).or_default().push(idx);
    }
    for (bid, mut idxs) in by_block {
        idxs.sort_unstable();
        idxs.dedup();
        for idx in idxs.into_iter().rev() {
            if idx < prog.blocks[bid].stmts.len() {
                prog.blocks[bid].stmts.remove(idx);
            }
        }
    }
}

/// Return the sole phi at `join` whose result escapes into executable code.
/// Real TJS bytecode often carries collateral register phis across a value
/// diamond even though only one merged value is subsequently observed.  Those
/// dead phis must not prevent source `?:`/short-circuit recovery, but multiple
/// *live* merged values would require a statement region and are left intact.
fn sole_live_join_phi(prog: &ExprProgram, join: usize) -> Option<super::ssa::Phi> {
    let block = prog.blocks.get(join)?;
    let mut live = block
        .phi
        .iter()
        .filter(|phi| count_var_uses(prog, phi.result) != 0)
        .cloned();
    let one = live.next()?;
    if live.next().is_some() {
        return None;
    }
    Some(one)
}

fn phi_arg_for_pred(phi: &super::ssa::Phi, pred: usize) -> Option<VarId> {
    phi.args
        .iter()
        .find_map(|(p, v)| if *p == pred { Some(*v) } else { None })
}

fn branch_cond_var(cond: &Expr) -> Option<(VarId, bool)> {
    match cond {
        Expr::SsaVar(v) => Some((*v, false)),
        Expr::Unary(UnOp::Not, inner) => match inner.as_ref() {
            Expr::SsaVar(v) => Some((*v, true)),
            _ => None,
        },
        _ => None,
    }
}

fn blocks_share_handler_stack(
    handler_stacks: Option<&[Vec<usize>]>,
    blocks: impl IntoIterator<Item = usize>,
) -> bool {
    let Some(stacks) = handler_stacks else {
        // Unit tests and callers without exception metadata may only use this
        // when they deliberately opt out of exception-aware folding.
        return true;
    };
    let mut it = blocks.into_iter();
    let Some(first) = it.next() else { return true; };
    let Some(reference) = stacks.get(first) else { return false; };
    it.all(|bid| stacks.get(bid).is_some_and(|stack| stack == reference))
}

/// Collapse a compiler-generated value diamond into a typed source expression.
/// The transform is transactional: it is first applied to a clone, and every
/// consumed SSA definition is checked for surviving uses before committing.
/// This prevents a convenient-looking `?:` from stealing a value needed by a
/// different path.
fn fold_simple_phi_branches(
    prog: &mut ExprProgram,
    handler_stacks: Option<&[Vec<usize>]>,
) -> bool {
    let mut any = false;
    loop {
        let mut committed = false;
        for root in 0..prog.blocks.len() {
            let Some((join, tpath, fpath, cond, tpred, fpred)) =
                simple_branch_region(prog, root)
            else {
                continue;
            };
            if join == root
                || tpath.contains(&root)
                || fpath.contains(&root)
                || join >= prog.blocks.len()
            {
                continue;
            }
            let region_blocks = std::iter::once(root)
                .chain(tpath.iter().copied())
                .chain(fpath.iter().copied())
                .chain(std::iter::once(join));
            if !blocks_share_handler_stack(handler_stacks, region_blocks) {
                continue;
            }
            let Some(phi) = sole_live_join_phi(prog, join) else { continue; };
            let phi_preds = phi.args.iter().map(|(p, _)| *p).collect::<HashSet<_>>();
            let expected_phi_preds = [tpred, fpred].into_iter().collect::<HashSet<_>>();
            if phi_preds != expected_phi_preds {
                continue;
            }
            let Some(tv) = phi_arg_for_pred(&phi, tpred) else { continue; };
            let Some(fv) = phi_arg_for_pred(&phi, fpred) else { continue; };

            let mut all_consumed = Vec::new();
            let mut all_defs = HashSet::new();

            // Short-circuit is the important direct-join case.  Reconstructing
            // it as `cond ? left : rhs` would evaluate a property-bearing left
            // operand twice on the direct arm.  Match the original flag value
            // and emit `&&`/`||` so the left operand is evaluated exactly once.
            let folded = if tpath.is_empty() ^ fpath.is_empty() {
                let direct_true = tpath.is_empty();
                let direct_v = if direct_true { tv } else { fv };
                let other_v = if direct_true { fv } else { tv };
                let other_path = if direct_true { &fpath } else { &tpath };
                let Some((cond_v, cond_is_not)) = branch_cond_var(&cond) else {
                    continue;
                };
                if direct_v != cond_v {
                    continue;
                }
                let Some(left) = extract_region_expr(
                    prog,
                    &[root],
                    Expr::SsaVar(cond_v),
                    true,
                ) else { continue; };
                let Some(right) = extract_region_expr(
                    prog,
                    other_path,
                    Expr::SsaVar(other_v),
                    false,
                ) else { continue; };

                all_consumed.extend(left.consumed.iter().copied());
                all_consumed.extend(right.consumed.iter().copied());
                all_defs.extend(left.consumed_defs.iter().copied());
                all_defs.extend(right.consumed_defs.iter().copied());

                let op = match (direct_true, cond_is_not) {
                    // if cond is true -> direct left; this is OR when cond is
                    // left, AND when cond is !left.
                    (true, false) => BinOp::LogOr,
                    (true, true) => BinOp::LogAnd,
                    // false edge direct: inverse of the cases above.
                    (false, false) => BinOp::LogAnd,
                    (false, true) => BinOp::LogOr,
                };
                Expr::Binary(op, Box::new(left.expr), Box::new(right.expr))
            } else {
                if tpath.is_empty() || fpath.is_empty() {
                    continue;
                }
                let Some(c) = extract_region_expr(prog, &[root], cond, true) else {
                    continue;
                };
                let Some(t) = extract_region_expr(
                    prog,
                    &tpath,
                    Expr::SsaVar(tv),
                    false,
                ) else { continue; };
                let Some(f) = extract_region_expr(
                    prog,
                    &fpath,
                    Expr::SsaVar(fv),
                    false,
                ) else { continue; };
                for x in [&c, &t, &f] {
                    all_consumed.extend(x.consumed.iter().copied());
                    all_defs.extend(x.consumed_defs.iter().copied());
                }
                Expr::Conditional {
                    cond: Box::new(c.expr),
                    then_expr: Box::new(t.expr),
                    else_expr: Box::new(f.expr),
                }
            };

            let mut candidate = prog.clone();
            remove_consumed_statements(&mut candidate, &all_consumed);
            // Arm blocks are owned exclusively by this branch (proved above)
            // and their live computations have been absorbed into `folded`.
            // Disconnect them so stale SSA/control uses cannot leak into later
            // liveness or source-local checks.
            for &bid in tpath.iter().chain(fpath.iter()) {
                candidate.blocks[bid].stmts.clear();
                candidate.blocks[bid].phi.clear();
                candidate.blocks[bid].term = Terminator::Fallthrough;
                candidate.blocks[bid].pred.clear();
                candidate.blocks[bid].succ.clear();
            }
            candidate.blocks[join].phi.clear();
            candidate.blocks[join].stmts.insert(
                0,
                Stmt::Assign {
                    dst: phi.result,
                    expr: folded,
                },
            );

            // The source conditional now lives in the expression assigned at
            // the join, so the raw CFG branch must be bypassed.  Keep the
            // adjacency metadata consistent because dominator/postdominator
            // construction intentionally uses `pred`/`succ`, not just terms.
            candidate.blocks[root].term = Terminator::Jmp(join);
            candidate.blocks[root].succ = vec![join];
            candidate.blocks[join]
                .pred
                .retain(|p| *p != tpred && *p != fpred && *p != root);
            candidate.blocks[join].pred.push(root);
            candidate.blocks[join].pred.sort_unstable();
            candidate.blocks[join].pred.dedup();

            // Every consumed definition must have disappeared from the use
            // graph.  Otherwise the region is not a closed expression.
            if all_defs.iter().any(|v| count_var_uses(&candidate, *v) != 0) {
                continue;
            }

            *prog = candidate;
            committed = true;
            any = true;
            break;
        }
        if !committed {
            break;
        }
    }
    any
}


/// Collapse a chain of short-circuit predicates that all share one failure
/// block, followed by a two-value phi.  Canonical compiler shape:
///
///   c1 --fail--> F
///    |           |
///   c2 --fail--> F --> J(phi)
///    |           ^
///   c3 --fail----|
///    |
///    S ----------> J
///
/// becomes `(p1 && p2 && p3) ? S_value : F_value`.  Each `pi` is the
/// condition for *continuing* to the next predicate, so the short-circuit
/// order is identical to the VM branch ladder.
fn fold_shared_failure_predicate_ladders(
    prog: &mut ExprProgram,
    handler_stacks: Option<&[Vec<usize>]>,
) -> bool {
    let mut any = false;
    loop {
        let mut committed = false;
        'roots: for root in 0..prog.blocks.len() {
            let Terminator::Br { if_true: root_t, if_false: root_f, .. } =
                prog.blocks[root].term.clone()
            else {
                continue;
            };

            'fails: for fail in [root_t, root_f] {
                let mut cond_blocks = vec![root];
                let mut cur = root;
                let mut success_start = if fail == root_t { root_f } else { root_t };

                // Extend while the continuation is another branch with the
                // same failure destination and a unique predecessor from the
                // preceding predicate.
                loop {
                    let next = success_start;
                    if next >= prog.blocks.len() { break; }
                    let preds = prog.blocks[next].pred.iter().copied().collect::<HashSet<_>>();
                    if preds != [cur].into_iter().collect::<HashSet<_>>() {
                        break;
                    }
                    let Terminator::Br { if_true, if_false, .. } = prog.blocks[next].term.clone() else {
                        break;
                    };
                    let other = if if_true == fail {
                        if_false
                    } else if if_false == fail {
                        if_true
                    } else {
                        break;
                    };
                    cond_blocks.push(next);
                    cur = next;
                    success_start = other;
                }

                if cond_blocks.len() < 2 || success_start == fail {
                    continue;
                }

                let fc = linear_chain(prog, fail, 32);
                let sc = linear_chain(prog, success_start, 32);
                let mut spos = HashMap::new();
                for (i, &b) in sc.iter().enumerate() { spos.insert(b, i); }
                let mut best = None;
                for (fi, &b) in fc.iter().enumerate() {
                    if let Some(&si) = spos.get(&b) {
                        let score = fi + si;
                        if best.map_or(true, |(_, bf, bs)| score < bf + bs) {
                            best = Some((b, fi, si));
                        }
                    }
                }
                let Some((join, fi, si)) = best else { continue; };
                let fail_path = fc[..fi].to_vec();
                let success_path = sc[..si].to_vec();
                if fail_path.is_empty()
                    || success_path.is_empty()
                    || join == root
                    || cond_blocks.contains(&join)
                    || fail_path.iter().any(|b| cond_blocks.contains(b))
                    || success_path.iter().any(|b| cond_blocks.contains(b))
                {
                    continue;
                }
                let region_blocks = cond_blocks
                    .iter()
                    .copied()
                    .chain(fail_path.iter().copied())
                    .chain(success_path.iter().copied())
                    .chain(std::iter::once(join));
                if !blocks_share_handler_stack(handler_stacks, region_blocks) {
                    continue;
                }

                // The shared failure block may have one predecessor from each
                // predicate, but no unrelated entry.  The success arm is owned
                // by the final predicate.
                let expected_fail_preds = cond_blocks.iter().copied().collect::<HashSet<_>>();
                let actual_fail_preds = prog.blocks[fail_path[0]]
                    .pred
                    .iter()
                    .copied()
                    .collect::<HashSet<_>>();
                if actual_fail_preds != expected_fail_preds {
                    continue;
                }
                let mut prev = fail_path[0];
                for &bid in fail_path.iter().skip(1) {
                    let preds = prog.blocks[bid].pred.iter().copied().collect::<HashSet<_>>();
                    if preds != [prev].into_iter().collect::<HashSet<_>>() {
                        continue 'fails;
                    }
                    prev = bid;
                }
                let last_cond = *cond_blocks.last().unwrap();
                let spreds = prog.blocks[success_path[0]].pred.iter().copied().collect::<HashSet<_>>();
                if spreds != [last_cond].into_iter().collect::<HashSet<_>>() {
                    continue;
                }
                prev = success_path[0];
                for &bid in success_path.iter().skip(1) {
                    let preds = prog.blocks[bid].pred.iter().copied().collect::<HashSet<_>>();
                    if preds != [prev].into_iter().collect::<HashSet<_>>() {
                        continue 'fails;
                    }
                    prev = bid;
                }

                if join >= prog.blocks.len() {
                    continue;
                }
                let Some(phi) = sole_live_join_phi(prog, join) else { continue; };
                let fpred = *fail_path.last().unwrap();
                let spred = *success_path.last().unwrap();
                let phi_preds = phi.args.iter().map(|(p, _)| *p).collect::<HashSet<_>>();
                if phi_preds != [fpred, spred].into_iter().collect::<HashSet<_>>() {
                    continue;
                }
                let Some(fv) = phi_arg_for_pred(&phi, fpred) else { continue; };
                let Some(sv) = phi_arg_for_pred(&phi, spred) else { continue; };

                let mut all_consumed = Vec::new();
                let mut all_defs = HashSet::new();
                let mut predicate: Option<Expr> = None;
                for (i, &bid) in cond_blocks.iter().enumerate() {
                    let Terminator::Br { cond, if_true, if_false } = prog.blocks[bid].term.clone() else {
                        continue 'fails;
                    };
                    let continue_expr = if if_true == fail {
                        Expr::Unary(UnOp::Not, Box::new(cond))
                    } else if if_false == fail {
                        cond
                    } else {
                        continue 'fails;
                    };
                    let Some(extracted) = extract_region_expr(
                        prog,
                        &[bid],
                        continue_expr,
                        i == 0,
                    ) else {
                        continue 'fails;
                    };
                    all_consumed.extend(extracted.consumed.iter().copied());
                    all_defs.extend(extracted.consumed_defs.iter().copied());
                    predicate = Some(match predicate {
                        None => extracted.expr,
                        Some(prev) => Expr::Binary(
                            BinOp::LogAnd,
                            Box::new(prev),
                            Box::new(extracted.expr),
                        ),
                    });
                }
                let Some(pred_expr) = predicate else { continue; };
                let Some(fexpr) = extract_region_expr(
                    prog,
                    &fail_path,
                    Expr::SsaVar(fv),
                    false,
                ) else { continue; };
                let Some(sexpr) = extract_region_expr(
                    prog,
                    &success_path,
                    Expr::SsaVar(sv),
                    false,
                ) else { continue; };
                for x in [&fexpr, &sexpr] {
                    all_consumed.extend(x.consumed.iter().copied());
                    all_defs.extend(x.consumed_defs.iter().copied());
                }

                let folded = Expr::Conditional {
                    cond: Box::new(pred_expr),
                    then_expr: Box::new(sexpr.expr),
                    else_expr: Box::new(fexpr.expr),
                };

                let mut candidate = prog.clone();
                remove_consumed_statements(&mut candidate, &all_consumed);
                candidate.blocks[join].phi.clear();
                candidate.blocks[join].stmts.insert(
                    0,
                    Stmt::Assign { dst: phi.result, expr: folded },
                );

                let mut bypassed = HashSet::new();
                bypassed.extend(cond_blocks.iter().skip(1).copied());
                bypassed.extend(fail_path.iter().copied());
                bypassed.extend(success_path.iter().copied());
                bypassed.remove(&join);
                for bid in bypassed {
                    candidate.blocks[bid].stmts.clear();
                    candidate.blocks[bid].phi.clear();
                    candidate.blocks[bid].term = Terminator::Fallthrough;
                    candidate.blocks[bid].pred.clear();
                    candidate.blocks[bid].succ.clear();
                }
                candidate.blocks[root].term = Terminator::Jmp(join);
                candidate.blocks[root].succ = vec![join];
                candidate.blocks[join].pred.clear();
                candidate.blocks[join].pred.push(root);

                if all_defs.iter().any(|v| count_var_uses(&candidate, *v) != 0) {
                    continue;
                }

                *prog = candidate;
                any = true;
                committed = true;
                break 'roots;
            }
        }
        if !committed { break; }
    }
    any
}

/// An unused positive VM register/flag/result is not a source variable.  If
/// its producer is observable, preserve the producer as an expression
/// statement instead of inventing a source local merely to hold a dead result.
/// Pure producers are handled by ordinary DCE.
fn discard_unused_internal_results(prog: &mut ExprProgram, ret_expr: &[Option<Expr>]) -> bool {
    let mut used: HashSet<VarId> = HashSet::new();
    for b in &prog.blocks {
        for phi in &b.phi {
            for (_, v) in &phi.args {
                used.insert(*v);
            }
        }
        for st in &b.stmts {
            collect_uses_stmt(st, &mut used);
        }
        collect_vars_term(&b.term, &mut used);
    }
    for re in ret_expr {
        if let Some(e) = re {
            collect_vars_expr(e, &mut used);
        }
    }

    let mut changed = false;
    for b in &mut prog.blocks {
        for st in &mut b.stmts {
            let replacement = match st {
                Stmt::Assign { dst, expr }
                    if is_internal_vm_value(*dst)
                        && !used.contains(dst)
                        && !expr_effects(expr).erasable() =>
                {
                    Some(Stmt::Expr(expr.clone()))
                }
                _ => None,
            };
            if let Some(new_st) = replacement {
                *st = new_st;
                changed = true;
            }
        }
    }
    changed
}

fn rewrite_term(term: &mut Terminator, env: &HashMap<VarId, Expr>) {
    match term {
        Terminator::Br { cond, .. } | Terminator::Ret(cond) | Terminator::Throw(cond) => {
            rewrite_expr(cond, env)
        }
        _ => {}
    }
}

/// Sink a single-use assignment into the immediately following terminator.
/// This is especially important for class initializers: VM comparison/TT
/// temporaries belong to the expression tree feeding JF/JNF and must not turn
/// into class members just because the CFG boundary separated them.
fn inline_trailing_single_use_into_terminators(prog: &mut ExprProgram) {
    loop {
        let mut changed = false;
        'blocks: for bid in 0..prog.blocks.len() {
            let Some(Stmt::Assign { dst, expr }) = prog.blocks[bid].stmts.last().cloned() else {
                continue;
            };
            if count_var_uses(prog, dst) != 1 || count_var_in_term(&prog.blocks[bid].term, dst) != 1 {
                continue;
            }

            let can_sink = if expr_effects(&expr).erasable() {
                true
            } else {
                match &prog.blocks[bid].term {
                    Terminator::Br { cond, .. }
                    | Terminator::Ret(cond)
                    | Terminator::Throw(cond) => use_is_first_observable_in_expr(cond, dst),
                    _ => false,
                }
            };
            if !can_sink {
                continue;
            }

            let mut env = HashMap::new();
            env.insert(dst, expr);
            rewrite_term(&mut prog.blocks[bid].term, &env);
            prog.blocks[bid].stmts.pop();
            changed = true;
            break 'blocks;
        }
        if !changed {
            break;
        }
    }
}

fn infer_single_return_expr(file: &Tjs2File, getter_obj: &Tjs2Object) -> Option<String> {
    let cfg = Cfg::build(getter_obj).ok()?;
    let ssa = SsaProgram::from_cfg(&cfg).ok()?;
    let mut prog = ExprProgram::from_ssa(file, getter_obj, &ssa).ok()?;
    const_propagate_intrablock(&mut prog);

    let in_class = scope_is_class(file, getter_obj);
    let arg_count = getter_obj.func_decl_arg_count.max(0) as usize;
    let fmt_var = make_fmt_var(
        in_class,
        arg_count,
        getter_obj.func_decl_collapse_base,
    );

    // Return values come from the SSA result slot consumed by RET.
    let mut ret_expr: Vec<Option<Expr>> = prog
        .blocks
        .iter()
        .map(|b| match &b.term {
            Terminator::Ret(e) => Some(e.clone()),
            _ => None,
        })
        .collect();
    propagate_into_ret_expr(&mut ret_expr, &prog, true);

    let mut unique_ret: Option<String> = None;
    for re in &ret_expr {
        if let Some(e) = re {
            let s = e.to_tjs_with(&fmt_var);
            if let Some(prev) = &unique_ret {
                if *prev != s {
                    return None;
                }
            } else {
                unique_ret = Some(s);
            }
        }
    }
    unique_ret
}


/// Return the source-level declaration name recorded by the bytecode exporter.
/// For declarations whose parent is a function/class, RegisterFunction stores a
/// `(name, object)` pair on the child object; the bytecode loader later applies
/// that pair to the parent object.  Prefer this metadata over guessing from the
/// parent/child tree.
fn registered_decl_name(file: &Tjs2File, obj: &Tjs2Object) -> Option<String> {
    for &(name_idx, object_idx) in &obj.properties {
        if object_idx != obj.index as i32 || name_idx < 0 {
            continue;
        }
        let name = file.const_pools.strings.get(name_idx as usize)?;
        if is_identifier(name) {
            return Some(name.clone());
        }
    }
    obj.name
        .as_ref()
        .filter(|n| n.as_str() != "(anonymous)" && is_identifier(n))
        .cloned()
}


fn qualified_decl_symbol(file: &Tjs2File, obj_idx: usize) -> Option<String> {
    fn walk(file: &Tjs2File, idx: usize, seen: &mut HashSet<usize>) -> Option<String> {
        if idx >= file.objects.len() || !seen.insert(idx) {
            return None;
        }
        let obj = &file.objects[idx];
        let leaf = registered_decl_name(file, obj)?;
        let parent = obj.parent;
        if parent < 0 || parent as usize == file.toplevel.max(0) as usize {
            return Some(leaf);
        }
        let pidx = parent as usize;
        let pobj = file.objects.get(pidx)?;
        if matches!(pobj.context_type, 1 | 6) {
            if let Some(prefix) = walk(file, pidx, seen) {
                return Some(format!("{}.{}", prefix, leaf));
            }
        }
        Some(leaf)
    }

    walk(file, obj_idx, &mut HashSet::new())
}

/// Split a class VM object at the compiler-inserted REGMEMBER instruction.
/// Everything through REGMEMBER is class-construction scaffold (ADDCI,
/// superclass setup, member registration).  The remaining code is the source
/// class-body execution that creates/initializes instance member variables.
fn class_initializer_object(obj: &Tjs2Object) -> Result<Option<Tjs2Object>> {
    if obj.context_type != 6 {
        return Ok(None);
    }
    let insns = decode_object(obj)?;
    let addci_count = insns.iter().filter(|i| i.op == vm::VM_ADDCI).count();
    let regmembers = insns
        .iter()
        .filter(|i| i.op == vm::VM_REGMEMBER)
        .collect::<Vec<_>>();
    if addci_count != 1 || regmembers.len() != 1 {
        return Ok(None);
    }

    let start = regmembers[0].pc + regmembers[0].size;
    let mut end = obj.code.len();

    // Commit() always appends `srv %0; ret` to ctClass.  This is VM context
    // plumbing, not a source-level `return` in the class body.
    if insns.len() >= 2 {
        let a = &insns[insns.len() - 2];
        let b = &insns[insns.len() - 1];
        if a.op == vm::VM_SRV
            && a.operands().first().copied() == Some(0)
            && b.op == vm::VM_RET
            && a.pc >= start
        {
            end = a.pc;
        }
    }
    if start > end || end > obj.code.len() {
        return Ok(None);
    }

    let mut sliced = obj.clone();
    sliced.code = obj.code[start..end].to_vec();
    sliced.scgetterps.clear();
    // The slice is a synthetic analysis view, not an independently registered
    // bytecode object.
    sliced.properties.clear();
    Ok(Some(sliced))
}

fn slice_code_object(obj: &Tjs2Object, start: usize, end: usize) -> Option<Tjs2Object> {
    if start >= end || end > obj.code.len() {
        return None;
    }
    let mut sliced = obj.clone();
    sliced.code = obj.code[start..end].to_vec();
    sliced.scgetterps.clear();
    sliced.properties.clear();
    Some(sliced)
}


fn fallback_executable_object(obj: &Tjs2Object) -> Result<Tjs2Object> {
    if obj.context_type == 6 {
        if let Some(mut sliced) = class_initializer_object(obj)? {
            // Fallback is wrapped in a helper function.  Lower SPDS as the
            // original `this.member = value` operation there, not as a source
            // class `var`, while retaining class-scope register formatting via
            // the original parent chain.
            sliced.context_type = 1;
            return Ok(sliced);
        }
    }
    Ok(obj.clone())
}

/// Recover every `extends` expression recorded by the superclass getter proxy.
/// CreateExtendsExprProxyCode records the start PC of each proxy expression in
/// SuperClassGetterPointer, so this also handles TJS2 multiple inheritance.
fn infer_superclass_exprs(file: &Tjs2File, getter_obj: &Tjs2Object) -> Vec<String> {
    let mut out = Vec::new();
    if getter_obj.scgetterps.is_empty() {
        if let Some(e) = infer_single_return_expr(file, getter_obj) {
            out.push(e);
        }
        return out;
    }

    let mut starts = getter_obj
        .scgetterps
        .iter()
        .copied()
        .filter(|p| *p >= 0)
        .map(|p| p as usize)
        .filter(|p| *p < getter_obj.code.len())
        .collect::<Vec<_>>();
    starts.sort_unstable();
    starts.dedup();
    for (i, start) in starts.iter().copied().enumerate() {
        let end = starts.get(i + 1).copied().unwrap_or(getter_obj.code.len());
        let Some(piece) = slice_code_object(getter_obj, start, end) else {
            continue;
        };
        if let Some(e) = infer_single_return_expr(file, &piece) {
            out.push(e);
        }
    }
    out
}

fn count_var_in_expr(expr: &Expr, needle: VarId) -> usize {
    match expr {
        Expr::SsaVar(v) => usize::from(*v == needle),
        Expr::Unary(_, e) | Expr::Deref(e) | Expr::ArgExpand(e) => count_var_in_expr(e, needle),
        Expr::Binary(_, a, b) | Expr::Index(a, b) => {
            count_var_in_expr(a, needle) + count_var_in_expr(b, needle)
        }
        Expr::Conditional {
            cond,
            then_expr,
            else_expr,
        } => {
            count_var_in_expr(cond, needle)
                + count_var_in_expr(then_expr, needle)
                + count_var_in_expr(else_expr, needle)
        }
        Expr::Call(c, args) | Expr::New(c, args) => {
            count_var_in_expr(c, needle)
                + args.iter().map(|a| count_var_in_expr(a, needle)).sum::<usize>()
        }
        Expr::MethodCall { base, args, .. } => {
            count_var_in_expr(base, needle)
                + args.iter().map(|a| count_var_in_expr(a, needle)).sum::<usize>()
        }
        Expr::ArrayLiteral(items) => {
            items.iter().map(|a| count_var_in_expr(a, needle)).sum()
        }
        Expr::DictionaryLiteral(items) => items
            .iter()
            .map(|(k, v)| count_var_in_expr(k, needle) + count_var_in_expr(v, needle))
            .sum(),
        Expr::Opaque(_, args) => args.iter().map(|a| count_var_in_expr(a, needle)).sum(),
        Expr::Member(base, _) => count_var_in_expr(base, needle),
        _ => 0,
    }
}

fn count_var_in_stmt(st: &Stmt, needle: VarId) -> usize {
    match st {
        Stmt::Assign { expr, .. } => count_var_in_expr(expr, needle),
        Stmt::Store { target, value } => {
            count_var_in_expr(target, needle) + count_var_in_expr(value, needle)
        }
        Stmt::MemberDecl { value, .. } => count_var_in_expr(value, needle),
        Stmt::Update { target, rhs, .. } => {
            count_var_in_expr(target, needle) + count_var_in_expr(rhs, needle)
        }
        Stmt::IncDec { target, .. } => count_var_in_expr(target, needle),
        Stmt::Expr(e) => count_var_in_expr(e, needle),
        Stmt::Opaque { args, .. } => args.iter().map(|a| count_var_in_expr(a, needle)).sum(),
    }
}

fn count_var_in_term(term: &Terminator, needle: VarId) -> usize {
    match term {
        Terminator::Br { cond, .. } | Terminator::Ret(cond) | Terminator::Throw(cond) => {
            count_var_in_expr(cond, needle)
        }
        _ => 0,
    }
}

fn count_var_uses(prog: &ExprProgram, needle: VarId) -> usize {
    let mut n = 0usize;
    for b in &prog.blocks {
        for p in &b.phi {
            n += p.args.iter().filter(|(_, v)| *v == needle).count();
        }
        n += b.stmts.iter().map(|st| count_var_in_stmt(st, needle)).sum::<usize>();
        n += count_var_in_term(&b.term, needle);
    }
    n
}

/// Return whether replacing `needle` in `expr` would keep the producer at the
/// first potentially observable evaluation position.  The producer originally
/// executes as a separate VM instruction immediately before this statement;
/// moving it past a getter/call/conversion would change exception/side-effect
/// ordering.
fn use_is_first_observable_in_expr(expr: &Expr, needle: VarId) -> bool {
    if count_var_in_expr(expr, needle) == 0 { return false; }
    match expr {
        Expr::SsaVar(v) => *v == needle,
        Expr::Unary(_, e) | Expr::Deref(e) | Expr::ArgExpand(e) | Expr::Member(e, _) => {
            use_is_first_observable_in_expr(e, needle)
        }
        Expr::Binary(_, lhs, rhs) | Expr::Index(lhs, rhs) => {
            if count_var_in_expr(lhs, needle) != 0 {
                use_is_first_observable_in_expr(lhs, needle)
            } else {
                expr_effects(lhs).erasable() && use_is_first_observable_in_expr(rhs, needle)
            }
        }
        Expr::Conditional {
            cond,
            then_expr,
            else_expr,
        } => {
            if count_var_in_expr(cond, needle) != 0 {
                use_is_first_observable_in_expr(cond, needle)
            } else if !expr_effects(cond).erasable() {
                false
            } else {
                // A producer that originally ran before the conditional may
                // not be sunk into just one arm: that would make its execution
                // conditional.  It is safe only if both arms use the value,
                // which would duplicate it, so no arm sinking is allowed here.
                let _ = (then_expr, else_expr);
                false
            }
        }
        Expr::Call(callee, args) | Expr::New(callee, args) => {
            if count_var_in_expr(callee, needle) != 0 {
                return use_is_first_observable_in_expr(callee, needle);
            }
            if !expr_effects(callee).erasable() { return false; }
            for a in args {
                if count_var_in_expr(a, needle) != 0 {
                    return use_is_first_observable_in_expr(a, needle);
                }
                if !expr_effects(a).erasable() { return false; }
            }
            false
        }
        Expr::MethodCall { base, args, .. } => {
            if count_var_in_expr(base, needle) != 0 {
                return use_is_first_observable_in_expr(base, needle);
            }
            // Resolving a non-proxy method member can dispatch a property
            // getter before arguments are evaluated.
            if !matches!(base.as_ref(), Expr::ScopeProxy) { return false; }
            for a in args {
                if count_var_in_expr(a, needle) != 0 {
                    return use_is_first_observable_in_expr(a, needle);
                }
                if !expr_effects(a).erasable() { return false; }
            }
            false
        }
        Expr::ArrayLiteral(items) => {
            for a in items {
                if count_var_in_expr(a, needle) != 0 { return use_is_first_observable_in_expr(a, needle); }
                if !expr_effects(a).erasable() { return false; }
            }
            false
        }
        Expr::DictionaryLiteral(items) => {
            for (k, v) in items {
                for e in [k, v] {
                    if count_var_in_expr(e, needle) != 0 { return use_is_first_observable_in_expr(e, needle); }
                    if !expr_effects(e).erasable() { return false; }
                }
            }
            false
        }
        Expr::Opaque(_, _) => false,
        _ => false,
    }
}

/// Equivalent of `use_is_first_observable_in_expr` for an lvalue *address*.
/// A property lvalue does not perform its final getter/setter dispatch while
/// its base/key are being evaluated, so the final Member/Index/Deref node must
/// not be treated as an earlier property read.  This distinction is required
/// for preserving TJS's RHS-before-LHS assignment evaluation order.
fn use_is_first_observable_in_lvalue(expr: &Expr, needle: VarId) -> bool {
    if count_var_in_expr(expr, needle) == 0 { return false; }
    match expr {
        Expr::SsaVar(v) => *v == needle,
        Expr::ScopeProxy => false,
        Expr::Member(base, _) | Expr::Deref(base) => {
            use_is_first_observable_in_expr(base, needle)
        }
        Expr::Index(base, key) => {
            if count_var_in_expr(base, needle) != 0 {
                use_is_first_observable_in_expr(base, needle)
            } else {
                expr_effects(base).erasable()
                    && use_is_first_observable_in_expr(key, needle)
            }
        }
        // IgnoreProp changes the final property operation, not address
        // evaluation.  Other unary forms are not valid exact lvalues here.
        Expr::Unary(UnOp::IgnoreProp, inner) => {
            use_is_first_observable_in_lvalue(inner, needle)
        }
        _ => false,
    }
}

fn use_is_first_observable_in_stmt(st: &Stmt, needle: VarId) -> bool {
    match st {
        Stmt::Assign { expr, .. } | Stmt::Expr(expr) | Stmt::MemberDecl { value: expr, .. } => {
            use_is_first_observable_in_expr(expr, needle)
        }
        Stmt::Store { target, value } => {
            // TJS compiles `lhs = rhs` by evaluating rhs first, then lhs.
            // Therefore an immediately preceding producer may be sunk into
            // rhs without crossing lhs dispatch/address evaluation.
            if count_var_in_expr(value, needle) != 0 {
                use_is_first_observable_in_expr(value, needle)
            } else if count_var_in_expr(target, needle) != 0 {
                expr_effects(value).erasable()
                    && use_is_first_observable_in_lvalue(target, needle)
            } else {
                false
            }
        }
        Stmt::Update { target, rhs, .. } => {
            // The compiler uses the same RHS-first order for compound
            // assignment, then performs the lvalue read-modify-write once.
            if count_var_in_expr(rhs, needle) != 0 {
                use_is_first_observable_in_expr(rhs, needle)
            } else if count_var_in_expr(target, needle) != 0 {
                expr_effects(rhs).erasable()
                    && use_is_first_observable_in_lvalue(target, needle)
            } else {
                false
            }
        }
        Stmt::IncDec { target, .. } => {
            use_is_first_observable_in_lvalue(target, needle)
        }
        Stmt::Opaque { .. } => false,
    }
}

/// SSA single-use inlining guarded by semantic-effect taint.  Pure/no-throw
/// values may be freely substituted into the immediately following statement;
/// an observable producer is substituted only when it remains the very first
/// observable evaluation in that statement.
fn inline_adjacent_single_use_assignments(prog: &mut ExprProgram) {
    loop {
        let mut changed = false;
        'blocks: for bid in 0..prog.blocks.len() {
            let len = prog.blocks[bid].stmts.len();
            if len < 2 { continue; }
            for i in 0..(len - 1) {
                let (dst, expr) = match &prog.blocks[bid].stmts[i] {
                    Stmt::Assign { dst, expr } => (*dst, expr.clone()),
                    _ => continue,
                };
                if count_var_uses(prog, dst) != 1
                    || count_var_in_stmt(&prog.blocks[bid].stmts[i + 1], dst) != 1 {
                    continue;
                }
                let pure = expr_effects(&expr).erasable();
                if !pure && !use_is_first_observable_in_stmt(&prog.blocks[bid].stmts[i + 1], dst) {
                    continue;
                }
                let mut env = HashMap::new();
                env.insert(dst, expr);
                rewrite_stmt(&mut prog.blocks[bid].stmts[i + 1], &env);
                prog.blocks[bid].stmts.remove(i);
                changed = true;
                break 'blocks;
            }
        }
        if !changed { break; }
    }
}


/// Source lvalues that can participate in an ordinary chained assignment.
/// IgnoreProp/opaque VM stores are deliberately excluded: their dispatch flags
/// cannot be reproduced by a plain `=` nested inside another expression.
fn is_chainable_assignment_lvalue(expr: &Expr) -> bool {
    match expr {
        Expr::Member(_, _) | Expr::Index(_, _) | Expr::Deref(_) => true,
        _ => false,
    }
}

/// Recover a compiler temporary whose single computed value is written to two
/// or more ordinary lvalues consecutively.  Duplicating an observable producer
/// (notably a property getter) would be wrong, while keeping the positive SSA
/// register would invent a source local.  TJS assignment is RHS-first and an
/// assignment expression returns the assigned value, so
///
///   tmp = E; A = tmp; B = tmp;
///
/// is exactly `B = A = E`: E executes once, then A, then B.
fn fold_consecutive_shared_value_stores(prog: &mut ExprProgram) {
    loop {
        let mut changed = false;
        'blocks: for bid in 0..prog.blocks.len() {
            let len = prog.blocks[bid].stmts.len();
            if len < 3 { continue; }
            for i in 0..(len - 2) {
                let (dst, producer) = match &prog.blocks[bid].stmts[i] {
                    Stmt::Assign { dst, expr } => (*dst, expr.clone()),
                    _ => continue,
                };
                if !is_internal_vm_value(dst) {
                    continue;
                }

                let mut targets = Vec::<Expr>::new();
                let mut j = i + 1;
                while j < prog.blocks[bid].stmts.len() {
                    match &prog.blocks[bid].stmts[j] {
                        Stmt::Store { target, value }
                            if matches!(value, Expr::SsaVar(v) if *v == dst)
                                && count_var_in_expr(target, dst) == 0
                                && is_chainable_assignment_lvalue(target) =>
                        {
                            targets.push(target.clone());
                            j += 1;
                        }
                        _ => break,
                    }
                }
                if targets.len() < 2 || count_var_uses(prog, dst) != targets.len() {
                    continue;
                }

                let mut nested = producer;
                // Original execution is producer, target[0], target[1], ... .
                // Each newly wrapped assignment becomes the RHS of the next
                // outer store, preserving precisely that order under TJS's
                // RHS-before-LHS rule.
                for target in &targets[..targets.len() - 1] {
                    nested = Expr::Binary(
                        BinOp::Assign,
                        Box::new(target.clone()),
                        Box::new(nested),
                    );
                }
                let replacement = Stmt::Store {
                    target: targets.last().cloned().expect("two targets"),
                    value: nested,
                };

                let mut candidate = prog.clone();
                candidate.blocks[bid].stmts.splice(i..j, [replacement]);
                if count_var_uses(&candidate, dst) != 0 {
                    continue;
                }
                *prog = candidate;
                changed = true;
                break 'blocks;
            }
        }
        if !changed { break; }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InlineCollectionKind {
    Array,
    Dictionary,
}

fn is_global_builtin_member(expr: &Expr, member: &str) -> bool {
    let Expr::Member(base, name) = expr else {
        return false;
    };
    if name != member {
        return false;
    }
    match base.as_ref() {
        Expr::Opaque(name, args) => name == "global" && args.is_empty(),
        _ => false,
    }
}

fn inline_collection_kind(expr: &Expr) -> Option<InlineCollectionKind> {
    let Expr::New(ctor, args) = expr else {
        return None;
    };
    if !args.is_empty() {
        return None;
    }
    if is_global_builtin_member(ctor, "Array") {
        Some(InlineCollectionKind::Array)
    } else if is_global_builtin_member(ctor, "Dictionary") {
        Some(InlineCollectionKind::Dictionary)
    } else {
        None
    }
}

fn known_int_expr(expr: &Expr, known: &HashMap<VarId, i64>) -> Option<i64> {
    match expr {
        Expr::Int(v) => Some(*v),
        Expr::SsaVar(v) => known.get(v).copied(),
        Expr::Binary(BinOp::Add, lhs, rhs) => {
            Some(known_int_expr(lhs, known)? + known_int_expr(rhs, known)?)
        }
        Expr::Binary(BinOp::Sub, lhs, rhs) => {
            Some(known_int_expr(lhs, known)? - known_int_expr(rhs, known)?)
        }
        _ => None,
    }
}

fn builder_index_key<'a>(target: &'a Expr, builder: VarId) -> Option<&'a Expr> {
    // The compiler's literal templates initialize Array/Dictionary entries
    // with SPIS (IGNOREPROP).  Requiring that wrapper prevents accidentally
    // folding an ordinary user property store that merely happens to target a
    // freshly allocated Array/Dictionary.
    let Expr::Unary(UnOp::IgnoreProp, inner) = target else {
        return None;
    };
    let Expr::Index(base, key) = inner.as_ref() else {
        return None;
    };
    match base.as_ref() {
        Expr::SsaVar(v) if *v == builder => Some(key.as_ref()),
        _ => None,
    }
}

/// Compute the SSA definitions, inside one straight-line statement segment,
/// that are transitively required by `seed`.  Collection literal lowering is
/// useful here because the compiler materializes key/value expressions in VM
/// registers before the final SPIS; those register definitions are not source
/// locals and must be folded back into the literal expression.
fn segment_dependency_defs(
    stmts: &[Stmt],
    start: usize,
    end: usize,
    seed: &Expr,
) -> HashSet<VarId> {
    let mut defs = HashMap::<VarId, &Expr>::new();
    for st in &stmts[start..end] {
        if let Stmt::Assign { dst, expr } = st {
            defs.insert(*dst, expr);
        }
    }

    let mut needed = HashSet::<VarId>::new();
    let mut pending = HashSet::<VarId>::new();
    collect_vars_expr(seed, &mut pending);
    while let Some(v) = pending.iter().next().copied() {
        pending.remove(&v);
        let Some(expr) = defs.get(&v) else { continue; };
        if !needed.insert(v) { continue; }
        let mut deps = HashSet::new();
        collect_vars_expr(expr, &mut deps);
        for dep in deps {
            if defs.contains_key(&dep) && !needed.contains(&dep) {
                pending.insert(dep);
            }
        }
    }
    needed
}

/// Reconstruct one compiler-generated collection item from the assignments
/// between the preceding SPIS (or allocation) and this SPIS.  This is stricter
/// than generic SSA propagation:
///
/// * every observable statement in the segment must belong to the key/value;
/// * dictionary key effects must precede value effects, matching the compiler's
///   literal evaluation order;
/// * array index-register maintenance is accepted only when it is provably an
///   integer chain used by the compiler's sequential SPIS template;
/// * no consumed definition may have a use outside the region after the
///   transaction is committed.
///
fn reconstruct_collection_item_segment(
    prog: &ExprProgram,
    bid: usize,
    start: usize,
    end: usize,
    kind: InlineCollectionKind,
    key: &Expr,
    value: &Expr,
    known_ints: &HashMap<VarId, i64>,
) -> Option<(Expr, Expr, HashSet<VarId>)> {
    let stmts = &prog.blocks.get(bid)?.stmts;
    if start > end || end > stmts.len() { return None; }

    let key_defs = if kind == InlineCollectionKind::Dictionary {
        segment_dependency_defs(stmts, start, end, key)
    } else {
        HashSet::new()
    };
    let value_defs = segment_dependency_defs(stmts, start, end, value);
    let mut consumed_defs = key_defs.union(&value_defs).copied().collect::<HashSet<_>>();

    // Dictionary literal syntax evaluates `key => value` in that order.  A
    // later key-only observable producer after a value-only producer would be
    // reordered by source reconstruction, so reject such a segment.  A shared
    // observable producer would be duplicated if substituted into both trees.
    let mut saw_value_observable = false;
    for idx in start..end {
        let Stmt::Assign { dst, expr } = &stmts[idx] else {
            return None;
        };
        let in_key = key_defs.contains(dst);
        let in_value = value_defs.contains(dst);
        if in_key || in_value {
            let observable = !expr_effects(expr).erasable();
            if observable {
                if in_key && in_value {
                    return None;
                }
                if in_value {
                    saw_value_observable = true;
                } else if in_key && saw_value_observable {
                    return None;
                }
            }
            continue;
        }

        // Array literals carry a synthetic integer index register.  Its CONST
        // and INC/DEC SSA assignments are compiler scaffolding, not source
        // expressions.  Only accept a statement here when it is statically an
        // integer in the already-proven index environment.
        if kind == InlineCollectionKind::Array
            && known_int_expr(expr, known_ints).is_some()
        {
            consumed_defs.insert(*dst);
            continue;
        }

        // A completely dead, no-throw/no-effect assignment is harmless
        // optimizer residue and may disappear with the builder.  Anything
        // observable must remain at its original source position, therefore it
        // invalidates collection folding instead of being guessed into a
        // comma-expression or helper temporary.
        if expr_effects(expr).erasable() && count_var_uses(prog, *dst) == 0 {
            consumed_defs.insert(*dst);
            continue;
        }
        return None;
    }

    // Rebuild both source expressions in original instruction order.  SSA
    // definitions are unique; forward substitution therefore preserves each
    // dependency's relative position while eliminating VM-only registers.
    let mut env = HashMap::<VarId, Expr>::new();
    for idx in start..end {
        let Stmt::Assign { dst, expr } = &stmts[idx] else { return None; };
        if !consumed_defs.contains(dst) { continue; }
        let mut rhs = expr.clone();
        rewrite_expr(&mut rhs, &env);
        env.insert(*dst, rhs);
    }
    let mut out_key = key.clone();
    let mut out_value = value.clone();
    rewrite_expr(&mut out_key, &env);
    rewrite_expr(&mut out_value, &env);

    let mut unresolved = HashSet::new();
    collect_vars_expr(&out_key, &mut unresolved);
    collect_vars_expr(&out_value, &mut unresolved);
    if unresolved.iter().any(|v| consumed_defs.contains(v)) {
        return None;
    }

    Some((out_key, out_value, consumed_defs))
}

/// Invert the exact compiler template used for inline Array/Dictionary
/// literals: `new global.Array/Dictionary`, ordered SPIS stores, then one use
/// of the constructed object.
///
/// Unlike the older contiguous matcher, key/value expressions may contain
/// arbitrary SSA producer chains (property reads, calls, nested literals, ...)
/// between allocation and SPIS.  They are absorbed only when the complete
/// region is closed and its observable evaluation order is proven identical to
/// source literal evaluation.  This is what allows class initializers such as
///
///   `_itemTexts = %[IDOK => GetSystemLangMessage(...), ...];`
///
/// to eliminate every positive VM register without inventing class-scope
/// locals.
fn fold_inline_collection_builders(prog: &mut ExprProgram) {
    loop {
        let mut changed = false;

        'blocks: for bid in 0..prog.blocks.len() {
            let mut i = 0usize;
            while i < prog.blocks[bid].stmts.len() {
                let (builder, kind) = match &prog.blocks[bid].stmts[i] {
                    Stmt::Assign { dst, expr } => match inline_collection_kind(expr) {
                        Some(kind) => (*dst, kind),
                        None => {
                            i += 1;
                            continue;
                        }
                    },
                    _ => {
                        i += 1;
                        continue;
                    }
                };

                let mut known_ints: HashMap<VarId, i64> = HashMap::new();
                let mut dict_items: Vec<(Expr, Expr)> = Vec::new();
                let mut array_items: Vec<Expr> = Vec::new();
                let mut j = i + 1;
                let mut segment_start = j;
                let mut terminal: Option<usize> = None;
                let mut internal_uses = 0usize;
                let mut removed_defs = HashSet::<VarId>::new();
                removed_defs.insert(builder);
                let mut valid = true;

                while j < prog.blocks[bid].stmts.len() {
                    let st = &prog.blocks[bid].stmts[j];
                    let builder_uses = count_var_in_stmt(st, builder);

                    // Keep the compiler's Array index environment updated even
                    // while the assignment is also part of an item producer
                    // chain.  The value is only used as proof for SPIS order;
                    // it is never emitted as source.
                    if kind == InlineCollectionKind::Array {
                        if let Stmt::Assign { dst, expr } = st {
                            if let Some(value) = known_int_expr(expr, &known_ints) {
                                known_ints.insert(*dst, value);
                            }
                        }
                    }

                    if let Stmt::Store { target, value } = st {
                        if let Some(key) = builder_index_key(target, builder) {
                            if count_var_in_expr(value, builder) != 0
                                || count_var_in_expr(key, builder) != 0
                            {
                                valid = false;
                                break;
                            }

                            let Some((key, value, defs)) =
                                reconstruct_collection_item_segment(
                                    prog,
                                    bid,
                                    segment_start,
                                    j,
                                    kind,
                                    key,
                                    value,
                                    &known_ints,
                                )
                            else {
                                valid = false;
                                break;
                            };
                            removed_defs.extend(defs);

                            match kind {
                                InlineCollectionKind::Dictionary => {
                                    dict_items.push((key, value));
                                }
                                InlineCollectionKind::Array => {
                                    let Some(index) = known_int_expr(&key, &known_ints) else {
                                        valid = false;
                                        break;
                                    };
                                    if index < 0 || index as usize != array_items.len() {
                                        valid = false;
                                        break;
                                    }
                                    array_items.push(value);
                                }
                            }
                            internal_uses += 1;
                            segment_start = j + 1;
                            j += 1;
                            continue;
                        }

                        // A nested collection's terminal is itself a Store on
                        // the *outer* builder: `outer[key] = inner`.  Check for
                        // a use of the current builder before classifying an
                        // unrelated Store as an intervening side effect.  The
                        // old order rejected exactly this valid terminal and
                        // prevented bottom-up fixed-point folding of nested
                        // Dictionary literals.
                        if builder_uses != 0 {
                            if builder_uses == 1 {
                                terminal = Some(j);
                            } else {
                                valid = false;
                            }
                            break;
                        }

                        // A store to some genuinely unrelated object inside
                        // this interval is observable.  Leave the outer
                        // candidate untouched; if this is an inner builder's
                        // own SPIS, the fixed-point loop will fold that builder
                        // independently and retry the outer candidate.
                        valid = false;
                        break;
                    }

                    if builder_uses != 0 {
                        if builder_uses == 1 {
                            terminal = Some(j);
                        } else {
                            valid = false;
                        }
                        break;
                    }

                    // Producers are allowed to accumulate until the next SPIS.
                    // The per-item reconstruction above will prove that every
                    // observable one contributes to the item.  Non-assignment
                    // statements cannot be represented as part of a literal by
                    // the current typed expression IR, so leave them alone.
                    if !matches!(st, Stmt::Assign { .. }) {
                        valid = false;
                        break;
                    }
                    j += 1;
                }

                let Some(t) = terminal else {
                    i += 1;
                    continue;
                };
                if !valid {
                    i += 1;
                    continue;
                }

                // Validate compiler scaffolding after the final item (Array
                // emits a final INC and empty Array emits its initial index
                // CONST).  Dictionary literals have no such trailing state.
                for idx in segment_start..t {
                    let Stmt::Assign { dst, expr } = &prog.blocks[bid].stmts[idx] else {
                        valid = false;
                        break;
                    };
                    if kind == InlineCollectionKind::Array
                        && known_int_expr(expr, &known_ints).is_some()
                    {
                        removed_defs.insert(*dst);
                        continue;
                    }
                    if expr_effects(expr).erasable() && count_var_uses(prog, *dst) == 0 {
                        removed_defs.insert(*dst);
                        continue;
                    }
                    valid = false;
                    break;
                }
                if !valid || count_var_uses(prog, builder) != internal_uses + 1 {
                    i += 1;
                    continue;
                }

                let literal = match kind {
                    InlineCollectionKind::Array => Expr::ArrayLiteral(array_items),
                    InlineCollectionKind::Dictionary => Expr::DictionaryLiteral(dict_items),
                };
                let mut terminal_stmt = prog.blocks[bid].stmts[t].clone();

                // All producer effects from allocation through the final SPIS
                // are moving into the literal at the builder's terminal use.
                // The use must therefore be the first observable evaluation in
                // the terminal statement.  For class member assignment this is
                // exactly TJS's RHS-before-LHS evaluation order.
                if !use_is_first_observable_in_stmt(&terminal_stmt, builder) {
                    i += 1;
                    continue;
                }
                let mut env = HashMap::new();
                env.insert(builder, literal);
                rewrite_stmt(&mut terminal_stmt, &env);

                // Apply transactionally.  If any SSA definition removed with
                // the compiler template still has a use, this was not a closed
                // literal region and must remain explicit.
                let mut candidate = prog.clone();
                candidate.blocks[bid].stmts.splice(i..=t, [terminal_stmt]);
                if removed_defs
                    .iter()
                    .any(|v| count_var_uses(&candidate, *v) != 0)
                {
                    i += 1;
                    continue;
                }

                *prog = candidate;
                changed = true;
                break 'blocks;
            }
        }

        if !changed {
            break;
        }
    }
}

fn regexp_source_from_internal(internal: &str) -> Option<String> {
    let rest = internal.strip_prefix("//")?;
    let slash = rest.find('/')?;
    let flags = &rest[..slash];
    let pattern = &rest[slash + 1..];
    if !flags.chars().all(|c| c.is_ascii_lowercase()) {
        return None;
    }
    if pattern.contains('\n') || pattern.contains('\r') {
        return None;
    }
    // The source delimiter must still be escaped exactly as it was in the
    // original token.  Reject malformed/internal forms rather than inventing
    // escaping, because changing escapes can change the regexp pattern.
    let mut escaped = false;
    for ch in pattern.chars() {
        if escaped {
            escaped = false;
            continue;
        }
        if ch == '\\' {
            escaped = true;
        } else if ch == '/' {
            return None;
        }
    }
    if escaped {
        return None;
    }
    Some(format!("/{}/{}", pattern, flags))
}

fn is_global_regexp_new(expr: &Expr) -> bool {
    let Expr::New(ctor, args) = expr else { return false; };
    args.is_empty() && is_global_builtin_member(ctor, "RegExp")
}

/// Invert the exact TJS compiler RegExp-literal template after ordinary SSA
/// propagation has normalized it to:
///   r = new global.RegExp(); r._compile("//flags/pattern"); USE(r)
/// The replacement is a source RegExp token, which recompiles to that same
/// lookup/new/_compile sequence.  No arbitrary RegExp construction is folded.
fn fold_regexp_builders(prog: &mut ExprProgram) {
    loop {
        let mut changed = false;
        'blocks: for bid in 0..prog.blocks.len() {
            let len = prog.blocks[bid].stmts.len();
            if len < 3 { continue; }
            for i in 0..=(len - 3) {
                let builder = match &prog.blocks[bid].stmts[i] {
                    Stmt::Assign { dst, expr } if is_global_regexp_new(expr) => *dst,
                    _ => continue,
                };
                let internal = match &prog.blocks[bid].stmts[i + 1] {
                    Stmt::Expr(Expr::MethodCall { base, member, args })
                        if member == "_compile"
                            && matches!(base.as_ref(), Expr::SsaVar(v) if *v == builder)
                            && args.len() == 1 =>
                    {
                        match &args[0] {
                            Expr::Str(s) => s.clone(),
                            _ => continue,
                        }
                    }
                    _ => continue,
                };
                let Some(source) = regexp_source_from_internal(&internal) else { continue; };
                if count_var_uses(prog, builder) != 2
                    || count_var_in_stmt(&prog.blocks[bid].stmts[i + 2], builder) != 1
                {
                    continue;
                }
                let literal = Expr::RegExpLiteral(source);
                let mut terminal = prog.blocks[bid].stmts[i + 2].clone();
                if !use_is_first_observable_in_stmt(&terminal, builder) {
                    continue;
                }
                let mut env = HashMap::new();
                env.insert(builder, literal);
                rewrite_stmt(&mut terminal, &env);
                prog.blocks[bid].stmts.splice(i..=i + 2, [terminal]);
                changed = true;
                break 'blocks;
            }
        }
        if !changed { break; }
    }
}

/// Run only proof-preserving SSA/dataflow simplifications.  Every rewrite is
/// constrained by use count, effects/exception taint, and source evaluation
/// order; no string-level peephole participates in this pipeline.
fn optimize_expr_program(
    prog: &mut ExprProgram,
    ret_expr: &mut Vec<Option<Expr>>,
    handler_stacks: Option<&[Vec<usize>]>,
) {
    const_propagate_intrablock(prog);
    propagate_into_ret_expr(ret_expr, prog, false);
    remove_dead_phis(prog, ret_expr);

    // A fold can expose another alias chain, and clearing an unused VM result
    // can in turn make an assignment dead.  The individual inliner/folder are
    // fixed-point passes; a few outer rounds are enough to saturate their
    // interaction without changing CFG structure.
    for _ in 0..6 {
        clear_unused_mutation_results(prog, ret_expr);
        discard_unused_internal_results(prog, ret_expr);
        remove_dead_assigns(prog, ret_expr);
        inline_adjacent_single_use_assignments(prog);
        inline_trailing_single_use_into_terminators(prog);
        // Prune collateral VM-register phis before trying to recover source
        // value regions. Real compiler diamonds commonly merge every touched
        // register even though only one merged value escapes. Leaving those
        // dead phis until the end of the round makes an otherwise exact
        // `?:`/short-circuit region look multi-valued.
        remove_dead_phis(prog, ret_expr);
        fold_shared_failure_predicate_ladders(prog, handler_stacks);
        fold_simple_phi_branches(prog, handler_stacks);
        fold_regexp_builders(prog);
        fold_consecutive_shared_value_stores(prog);
        fold_inline_collection_builders(prog);
        const_propagate_intrablock(prog);
        propagate_into_ret_expr(ret_expr, prog, false);
        remove_dead_phis(prog, ret_expr);
    }
    clear_unused_mutation_results(prog, ret_expr);
    discard_unused_internal_results(prog, ret_expr);
    remove_dead_assigns(prog, ret_expr);
    inline_trailing_single_use_into_terminators(prog);
}

fn is_frame_local(v: VarId, arg_count: usize, collapse_base: i32) -> bool {
    let Var::Reg(r) = v.var else { return false; };
    if r > -3 { return false; }
    let frame_idx = (-3 - r) as usize;
    frame_idx >= arg_count
        && !(collapse_base >= 0 && frame_idx == collapse_base as usize)
}

fn frame_local_decl_defs(prog: &ExprProgram, arg_count: usize, collapse_base: i32) -> HashSet<VarId> {
    let mut first_def = HashMap::<i32, VarId>::new();
    let mut first_assign = HashMap::<i32, VarId>::new();

    let mut record = |map: &mut HashMap<i32, VarId>, v: VarId| {
        if !is_frame_local(v, arg_count, collapse_base) || v.ver == 0 {
            return;
        }
        let Var::Reg(r) = v.var else { return; };
        map.entry(r)
            .and_modify(|cur| {
                if v.ver < cur.ver { *cur = v; }
            })
            .or_insert(v);
    };

    for block in &prog.blocks {
        for p in &block.phi {
            record(&mut first_def, p.result);
        }
        for st in &block.stmts {
            match st {
                Stmt::Assign { dst, .. } => {
                    record(&mut first_def, *dst);
                    record(&mut first_assign, *dst);
                }
                Stmt::Update { dst: Some(dst), .. } | Stmt::IncDec { dst: Some(dst), .. } => {
                    record(&mut first_def, *dst);
                }
                Stmt::Opaque { defs, .. } => {
                    for &d in defs { record(&mut first_def, d); }
                }
                _ => {}
            }
        }
    }

    first_def
        .into_iter()
        .filter_map(|(slot, def)| {
            (first_assign.get(&slot).copied() == Some(def)).then_some(def)
        })
        .collect()
}

fn live_frame_slots(prog: &ExprProgram, arg_count: usize, collapse_base: i32) -> HashSet<i32> {
    collect_vars(prog)
        .into_iter()
        .filter(|v| is_frame_local(*v, arg_count, collapse_base))
        .filter_map(|v| match v.var { Var::Reg(r) => Some(r), _ => None })
        .collect()
}

fn is_internal_class_scaffold_var(v: VarId) -> bool {
    match v.var {
        Var::Reg(r) if r >= 0 => !(r == 0 && v.ver == 0),
        Var::Flag => true,
        Var::Result => v.ver != 0,
        _ => false,
    }
}

/// Formatter used only inside the lexical ctClass VM scaffold. SSA versions of
/// one physical VM slot deliberately collapse back to the same source local.
/// This preserves register overwrite/lifetime behavior instead of keeping every
/// SSA version alive until the end of the block.
fn make_class_scaffold_fmt_var(
    arg_count: usize,
    collapse_base: i32,
) -> impl Fn(VarId) -> String {
    let ordinary = make_fmt_var(true, arg_count, collapse_base);
    move |vid: VarId| match vid.var {
        Var::Reg(r) if r >= 0 => format!("__tjs2dec_vm_r{}", r),
        Var::Flag => "__tjs2dec_vm_flag".to_string(),
        Var::Result => "__tjs2dec_vm_result".to_string(),
        _ => ordinary(vid),
    }
}

fn expr_contains_dynamic_eval(expr: &Expr) -> bool {
    match expr {
        Expr::Unary(_, a) | Expr::Deref(a) | Expr::ArgExpand(a) | Expr::Member(a, _) => {
            expr_contains_dynamic_eval(a)
        }
        Expr::Binary(_, a, b) | Expr::Index(a, b) => {
            expr_contains_dynamic_eval(a) || expr_contains_dynamic_eval(b)
        }
        Expr::Conditional { cond, then_expr, else_expr } => {
            expr_contains_dynamic_eval(cond)
                || expr_contains_dynamic_eval(then_expr)
                || expr_contains_dynamic_eval(else_expr)
        }
        Expr::Call(callee, args) | Expr::New(callee, args) => {
            expr_contains_dynamic_eval(callee)
                || args.iter().any(expr_contains_dynamic_eval)
        }
        Expr::MethodCall { base, args, .. } => {
            expr_contains_dynamic_eval(base) || args.iter().any(expr_contains_dynamic_eval)
        }
        Expr::ArrayLiteral(items) => items.iter().any(expr_contains_dynamic_eval),
        Expr::DictionaryLiteral(items) => items
            .iter()
            .any(|(k, v)| expr_contains_dynamic_eval(k) || expr_contains_dynamic_eval(v)),
        Expr::Opaque(name, args) => {
            matches!(name.as_str(), "VM_EVAL" | "EVAL" | "VM_EEXP" | "EEXP")
                || args.iter().any(expr_contains_dynamic_eval)
        }
        _ => false,
    }
}

fn class_initializer_has_dynamic_eval(prog: &ExprProgram) -> bool {
    for block in &prog.blocks {
        for st in &block.stmts {
            let hit = match st {
                Stmt::Assign { expr, .. } | Stmt::Expr(expr) | Stmt::MemberDecl { value: expr, .. } => {
                    expr_contains_dynamic_eval(expr)
                }
                Stmt::Store { target, value } => {
                    expr_contains_dynamic_eval(target) || expr_contains_dynamic_eval(value)
                }
                Stmt::Update { target, rhs, .. } => {
                    expr_contains_dynamic_eval(target) || expr_contains_dynamic_eval(rhs)
                }
                Stmt::IncDec { target, .. } => expr_contains_dynamic_eval(target),
                Stmt::Opaque { op, args, .. } => {
                    matches!(*op, "VM_EVAL" | "EVAL" | "VM_EEXP" | "EEXP")
                        || args.iter().any(expr_contains_dynamic_eval)
                }
            };
            if hit {
                return true;
            }
        }
        let term_hit = match &block.term {
            Terminator::Br { cond, .. } | Terminator::Ret(cond) | Terminator::Throw(cond) => {
                expr_contains_dynamic_eval(cond)
            }
            _ => false,
        };
        if term_hit {
            return true;
        }
    }
    false
}

fn internal_class_scaffold_decl_line(
    prog: &ExprProgram,
    fmt_var: &dyn Fn(VarId) -> String,
    indent: usize,
) -> Option<String> {
    let mut vars = collect_vars(prog)
        .into_iter()
        .filter(|v| is_internal_class_scaffold_var(*v))
        .collect::<Vec<_>>();
    vars.sort_by_key(|v| (var_key(v), v.ver));
    vars.dedup_by_key(|v| fmt_var(*v));
    if vars.is_empty() {
        return None;
    }
    Some(format!(
        "{}var {};",
        " ".repeat(indent),
        vars.into_iter().map(|v| fmt_var(v)).collect::<Vec<_>>().join(", ")
    ))
}

/// Render the post-REGMEMBER class initializer with two semantics-preserving
/// source forms.  Fully reconstructed code stays directly at ctClass scope.
/// When compiler VM temporaries are still required by a structured statement
/// CFG, place them in an explicit nested lexical block so they cannot become
/// observable class members. Dynamic eval remains fail-closed because it can
/// observe newly introduced lexical bindings.
fn emit_class_initializer_body(
    original: &Tjs2Object,
    file: &Tjs2File,
    indent: usize,
) -> Result<Option<String>> {
    let Some(obj) = class_initializer_object(original)? else {
        return Ok(None);
    };
    if obj.code.is_empty() {
        return Ok(Some(String::new()));
    }

    let cfg = Cfg::build(&obj)?;
    let ssa = SsaProgram::from_cfg(&cfg)?;
    let mut prog = ExprProgram::from_ssa(file, &obj, &ssa)?;

    let mut ret_expr: Vec<Option<Expr>> = prog
        .blocks
        .iter()
        .map(|b| match &b.term {
            Terminator::Ret(e) => Some(e.clone()),
            _ => None,
        })
        .collect();
    optimize_expr_program(&mut prog, &mut ret_expr, Some(&cfg.block_handler_stack));

    for b in &prog.blocks {
        for st in &b.stmts {
            if let Stmt::MemberDecl { name, .. } = st {
                if !is_identifier(name) {
                    return Ok(None);
                }
            }
        }
    }

    let arg_count = 0usize;
    let collapse_base = -1;
    let vars = collect_vars(&prog);
    let has_internal_scaffold = vars
        .iter()
        .copied()
        .any(is_internal_class_scaffold_var);

    // Negative frame registers can be genuine lexical locals in nested class
    // namespaces. They are only safe when SSA proves an ordinary assignment
    // that can act as their source declaration point. A phi/opaque first
    // definition remains fail-closed.
    let live_frames = live_frame_slots(&prog, arg_count, collapse_base);
    let decl_defs = frame_local_decl_defs(&prog, arg_count, collapse_base);
    let declared_slots = decl_defs
        .iter()
        .filter_map(|v| match v.var { Var::Reg(r) => Some(r), _ => None })
        .collect::<HashSet<_>>();
    if !live_frames.is_subset(&declared_slots) {
        return Ok(None);
    }

    let fmt_var = make_fmt_var(true, arg_count, collapse_base);

    // First try the clean class-scope form. It is preferable because SPDS can
    // be reconstructed with the natural source `var member = ...` spelling and
    // no synthetic lexical namespace is introduced. This mode is only viable
    // when no positive VM register/flag/result survives optimization.
    if !has_internal_scaffold && live_frames.is_empty() {
        let mut structurer = Structurer::new(&cfg, &prog, &fmt_var, ret_expr.clone());
        structurer.set_terminal_fallthrough_returns(false);
        structurer.set_class_initializer_scope(indent, decl_defs.clone());
        let lines = structurer.emit_function_body(prog.entry_block, indent);
        let has_class_local_marker = lines
            .iter()
            .any(|l| l.contains("__tjs2dec_unrepresentable_class_local"));
        let has_guard = lines.iter().any(|l| l.contains("__tjs2dec_guard_"));
        let has_return = lines
            .iter()
            .any(|l| l.trim_start().starts_with("return"));
        if !has_class_local_marker && !has_guard && !has_return {
            let mut out = String::new();
            for line in lines {
                writeln!(out, "{}", line)?;
            }
            return Ok(Some(out));
        }
    }

    // Some ctClass initializers are intrinsically statement-shaped: ordinary
    // if/else regions, loops, or guarded shared CFGs can require VM temporaries
    // even after all safe SSA expression folding. A source `var r...` at the
    // class root would create an observable class member, so place *only* such
    // compiler scaffolding in an explicit nested lexical block instead.
    //
    // This is deliberately disabled in the presence of dynamic eval: adding
    // lexical bindings could then alter runtime name resolution. Bare scope-
    // proxy identifiers are separately audited against every generated name,
    // so ordinary source lookup cannot be captured by these locals.
    if class_initializer_has_dynamic_eval(&prog) {
        return Ok(None);
    }

    let body_indent = indent + 2;
    let scaffold_fmt_var = make_class_scaffold_fmt_var(arg_count, collapse_base);
    let mut structurer = Structurer::new(&cfg, &prog, &scaffold_fmt_var, ret_expr);
    structurer.set_terminal_fallthrough_returns(false);
    structurer.set_class_initializer_scope(indent, decl_defs);
    let mut body = structurer.emit_function_body(prog.entry_block, body_indent);
    if body
        .iter()
        .any(|l| l.contains("__tjs2dec_unrepresentable_class_local"))
    {
        return Ok(None);
    }
    if body
        .iter()
        .any(|l| l.trim_start().starts_with("return"))
    {
        return Ok(None);
    }

    let mut lines = Vec::new();
    lines.push(format!("{}{{", " ".repeat(indent)));
    if let Some(decl) = internal_class_scaffold_decl_line(&prog, &scaffold_fmt_var, body_indent) {
        lines.push(decl);
    }
    lines.append(&mut body);
    lines.push(format!("{}}}", " ".repeat(indent)));

    let mut out = String::new();
    for line in lines {
        writeln!(out, "{}", line)?;
    }
    Ok(Some(out))
}



fn emit_property_decl(
    out: &mut String,
    file: &Tjs2File,
    prop_idx: usize,
    indent: usize,
    children_of: &HashMap<usize, Vec<usize>>,
    emitted: &mut HashSet<usize>,
    body_emitted: &mut HashSet<usize>,
) -> Result<()> {
    if prop_idx >= file.objects.len() || emitted.contains(&prop_idx) {
        return Ok(());
    }
    let pobj = &file.objects[prop_idx];
    if pobj.context_type != 3 {
        return Ok(());
    }
    emitted.insert(prop_idx);
    let prop_name = registered_decl_name(file, pobj)
        .unwrap_or_else(|| format!("__prop_{}", prop_idx));
    let pad = " ".repeat(indent);
    writeln!(out, "{}property {} {{", pad, prop_name)?;

    if pobj.prop_getter >= 0 {
        let gi = pobj.prop_getter as usize;
        if gi < file.objects.len() && !emitted.contains(&gi) {
            let (body, _params) = emit_object_body(&file.objects[gi], file, indent + 4)?;
            writeln!(out, "{}getter {{", " ".repeat(indent + 2))?;
            write!(out, "{body}")?;
            writeln!(out, "{}}}", " ".repeat(indent + 2))?;
            emitted.insert(gi);
            body_emitted.insert(gi);
        }
    }
    if pobj.prop_setter >= 0 {
        let si = pobj.prop_setter as usize;
        if si < file.objects.len() && !emitted.contains(&si) {
            let (body, params) = emit_object_body(&file.objects[si], file, indent + 4)?;
            writeln!(out, "{}setter({}) {{", " ".repeat(indent + 2), params)?;
            write!(out, "{body}")?;
            writeln!(out, "{}}}", " ".repeat(indent + 2))?;
            emitted.insert(si);
            body_emitted.insert(si);
        }
    }
    if let Some(prop_children) = children_of.get(&prop_idx) {
        for &ci in prop_children {
            if ci < file.objects.len() && matches!(file.objects[ci].context_type, 4 | 5) {
                emitted.insert(ci);
            }
        }
    }
    writeln!(out, "{}}}", pad)?;
    Ok(())
}

fn emit_function_decl(
    out: &mut String,
    file: &Tjs2File,
    fn_idx: usize,
    indent: usize,
    children_of: &HashMap<usize, Vec<usize>>,
    emitted: &mut HashSet<usize>,
    body_emitted: &mut HashSet<usize>,
    object_symbols: &mut HashMap<usize, String>,
) -> Result<()> {
    if fn_idx >= file.objects.len() || emitted.contains(&fn_idx) {
        return Ok(());
    }
    let fobj = &file.objects[fn_idx];
    if fobj.context_type != 1 {
        return Ok(());
    }
    emitted.insert(fn_idx);
    let name = registered_decl_name(file, fobj)
        .unwrap_or_else(|| format!("__func_{}", fn_idx));
    object_symbols.insert(
        fn_idx,
        qualified_decl_symbol(file, fn_idx).unwrap_or_else(|| name.clone()),
    );

    if let Some(children) = children_of.get(&fn_idx) {
        for &ci in children {
            if ci < file.objects.len() && file.objects[ci].context_type == 2 {
                // Anonymous expression closures are not declarations. Their
                // executable bodies remain visible through the fallback until
                // function-expression reconstruction consumes them.
                emitted.insert(ci);
            }
        }
    }

    let pad = " ".repeat(indent);
    if fobj.code.is_empty() {
        writeln!(out, "{}function {}() {{}}", pad, name)?;
        return Ok(());
    }

    let (body, params) = emit_object_body(fobj, file, indent + 2)?;
    writeln!(out, "{}function {}({}) {{", pad, name, params)?;

    // RegisterFunction stores named function/property/class declarations as
    // children of the owning function object. Recreate that declaration graph
    // recursively instead of leaving all parent=function objects in fallback.
    let mut wrote_decl = false;
    if let Some(children) = children_of.get(&fn_idx).cloned() {
        for ci in children {
            if ci >= file.objects.len() || emitted.contains(&ci) {
                continue;
            }
            match file.objects[ci].context_type {
                1 => {
                    if wrote_decl { writeln!(out)?; }
                    emit_function_decl(
                        out, file, ci, indent + 2, children_of,
                        emitted, body_emitted, object_symbols,
                    )?;
                    wrote_decl = true;
                }
                3 => {
                    if wrote_decl { writeln!(out)?; }
                    emit_property_decl(
                        out, file, ci, indent + 2, children_of,
                        emitted, body_emitted,
                    )?;
                    wrote_decl = true;
                }
                6 => {
                    if wrote_decl { writeln!(out)?; }
                    emit_class_decl(
                        out, file, ci, indent + 2, children_of,
                        emitted, body_emitted, object_symbols,
                    )?;
                    wrote_decl = true;
                }
                _ => {}
            }
        }
    }
    if wrote_decl && !body.is_empty() {
        writeln!(out)?;
    }
    write!(out, "{body}")?;
    writeln!(out, "{}}}", pad)?;
    body_emitted.insert(fn_idx);
    Ok(())
}

fn emit_class_decl(
    out: &mut String,
    file: &Tjs2File,
    cls_idx: usize,
    indent: usize,
    children_of: &HashMap<usize, Vec<usize>>,
    emitted: &mut HashSet<usize>,
    body_emitted: &mut HashSet<usize>,
    object_symbols: &mut HashMap<usize, String>,
) -> Result<()> {
    if cls_idx >= file.objects.len() || emitted.contains(&cls_idx) {
        return Ok(());
    }
    let cls_obj = &file.objects[cls_idx];
    if cls_obj.context_type != 6 {
        return Ok(());
    }
    let cls_name = registered_decl_name(file, cls_obj)
        .unwrap_or_else(|| format!("__class_{}", cls_idx));
    emitted.insert(cls_idx);
    object_symbols.insert(
        cls_idx,
        qualified_decl_symbol(file, cls_idx).unwrap_or_else(|| cls_name.clone()),
    );

    let mut extends = Vec::new();
    let sg_idx = if cls_obj.super_class_getter >= 0 {
        Some(cls_obj.super_class_getter as usize)
    } else {
        children_of.get(&cls_idx).and_then(|ch| {
            ch.iter()
                .copied()
                .find(|&ci| file.objects.get(ci).map(|o| o.context_type == 7).unwrap_or(false))
        })
    };
    if let Some(sg) = sg_idx {
        if sg < file.objects.len() {
            emitted.insert(sg);
            extends = infer_superclass_exprs(file, &file.objects[sg]);
            if !extends.is_empty() {
                body_emitted.insert(sg);
            }
        }
    }

    let pad = " ".repeat(indent);
    if extends.is_empty() {
        writeln!(out, "{}class {} {{", pad, cls_name)?;
    } else {
        writeln!(out, "{}class {} extends {} {{", pad, cls_name, extends.join(", "))?;
    }

    let member_indent = indent + 2;
    let mut wrote_member = false;

    // ctClass executable code after REGMEMBER is the source member-variable
    // creation/initialization phase.  Render it only when doing so does not
    // require synthetic class-scope locals.
    if let Some(init_body) = emit_class_initializer_body(cls_obj, file, member_indent)? {
        if !init_body.is_empty() {
            write!(out, "{}", init_body)?;
            wrote_member = true;
        }
        body_emitted.insert(cls_idx);
    }

    let children = children_of.get(&cls_idx).cloned().unwrap_or_default();
    for ci in children {
        if emitted.contains(&ci) || ci >= file.objects.len() {
            continue;
        }
        let mobj = &file.objects[ci];
        match mobj.context_type {
            7 => {
                emitted.insert(ci);
            }
            2 => {
                // Expression closures are referenced from executable code; keep
                // their bodies for the fallback until closure reconstruction is
                // implemented, but do not mistake them for class declarations.
                emitted.insert(ci);
            }
            6 => {
                if wrote_member {
                    writeln!(out)?;
                }
                emit_class_decl(
                    out,
                    file,
                    ci,
                    member_indent,
                    children_of,
                    emitted,
                    body_emitted,
                    object_symbols,
                )?;
                wrote_member = true;
            }
            3 => {
                if wrote_member {
                    writeln!(out)?;
                }
                emit_property_decl(
                    out, file, ci, member_indent, children_of, emitted, body_emitted,
                )?;
                wrote_member = true;
            }
            1 => {
                if wrote_member {
                    writeln!(out)?;
                }
                emit_function_decl(
                    out, file, ci, member_indent, children_of,
                    emitted, body_emitted, object_symbols,
                )?;
                wrote_member = true;
            }
            _ => {
                emitted.insert(ci);
            }
        }
    }

    writeln!(out, "{}}}", pad)?;
    Ok(())
}

pub fn dump_src_file(file: &Tjs2File) -> Result<String> {
    let mut out = String::new();
    writeln!(out, "// Decompiled by tjs2Decompiler (high)")?;
    writeln!(
        out,
        "// objects={}, toplevel={}",
        file.objects.len(),
        file.toplevel
    )?;
    writeln!(out)?;

    let toplevel = file.toplevel.max(0) as usize;

    // Build parent -> children index (ordered by object index)
    let mut children_of: HashMap<usize, Vec<usize>> = HashMap::new();
    for obj in &file.objects {
        if obj.parent >= 0 {
            children_of
                .entry(obj.parent as usize)
                .or_default()
                .push(obj.index);
        }
    }

    // `emitted` tracks objects consumed by the structural pretty-printer.
    // `body_emitted` is deliberately separate: an object can be recognized as
    // structural metadata while its executable bytecode body is still omitted.
    // The fallback stage uses `body_emitted` so no executable body disappears.
    let mut emitted: HashSet<usize> = HashSet::new();
    let mut body_emitted: HashSet<usize> = HashSet::new();
    let mut object_symbols: HashMap<usize, String> = HashMap::new();
    emitted.insert(toplevel);

    // === Emit classes rooted at the top level. Nested classes are emitted
    // recursively from their owning class/function using bytecode declaration
    // metadata rather than being left as VM-object fallbacks.
    let classes: Vec<usize> = file
        .objects
        .iter()
        .filter(|o| o.context_type == 6 && o.parent == toplevel as i32)
        .map(|o| o.index)
        .collect();

    for cls_idx in classes {
        emit_class_decl(
            &mut out,
            file,
            cls_idx,
            0,
            &children_of,
            &mut emitted,
            &mut body_emitted,
            &mut object_symbols,
        )?;
        writeln!(out)?;
    }

    // === Emit top-level named declarations.  Child declarations are
    // recursively emitted from their owning function/class contexts.
    let top_properties: Vec<usize> = file
        .objects
        .iter()
        .filter(|o| o.context_type == 3 && o.parent == toplevel as i32)
        .map(|o| o.index)
        .collect();
    for prop_idx in top_properties {
        if emitted.contains(&prop_idx) {
            continue;
        }
        emit_property_decl(
            &mut out,
            file,
            prop_idx,
            0,
            &children_of,
            &mut emitted,
            &mut body_emitted,
        )?;
        writeln!(out)?;
    }

    let top_functions: Vec<usize> = file
        .objects
        .iter()
        .filter(|o| o.context_type == 1 && o.parent == toplevel as i32)
        .map(|o| o.index)
        .collect();
    for fn_idx in top_functions {
        if emitted.contains(&fn_idx) {
            continue;
        }
        emit_function_decl(
            &mut out,
            file,
            fn_idx,
            0,
            &children_of,
            &mut emitted,
            &mut body_emitted,
            &mut object_symbols,
        )?;
        writeln!(out)?;
    }

    // === Bytecode-object fallback ===
    // Never silently discard executable object bodies. Pretty reconstruction above
    // handles only structures we understand. Any body not actually rendered, the
    // top-level body, and every InterObject/InterGenerator target is made visible
    // below. The top-level fallback is emitted directly; non-top-level helpers
    // preserve auditability and do not claim that compiler-generated object
    // initialization has already been restructured to source form.
    let mut fallback_indices: HashSet<usize> = HashSet::new();
    if !body_emitted.contains(&toplevel) {
        fallback_indices.insert(toplevel);
    }
    let mut generator_refs: HashSet<usize> = HashSet::new();
    for owner in &file.objects {
        for v in &owner.data {
            match *v {
                Variant::InterObject(idx) if idx >= 0 => {
                    fallback_indices.insert(idx as usize);
                }
                Variant::InterGenerator(idx) if idx >= 0 => {
                    fallback_indices.insert(idx as usize);
                    generator_refs.insert(idx as usize);
                }
                _ => {}
            }
        }
        if !owner.code.is_empty() && !body_emitted.contains(&owner.index) {
            fallback_indices.insert(owner.index);
        }
    }

    let emit_toplevel_fallback = fallback_indices.contains(&toplevel)
        && !file.objects[toplevel].code.is_empty()
        && !body_emitted.contains(&toplevel);

    let mut fallback_indices = fallback_indices.into_iter().collect::<Vec<_>>();
    fallback_indices.sort_unstable();
    if !fallback_indices.is_empty() {
        writeln!(out, "// === Bytecode object fallbacks (unstructured but not omitted) ===")?;
        writeln!(out)?;
    }

    // Define every helper before the executable script body.  TJS executes the
    // top-level object immediately, so placing it before __tjs2dec_obj_N aliases
    // makes otherwise valid InterObject references observe undefined helpers.
    for idx in fallback_indices {
        if idx == toplevel {
            continue;
        }
        if idx >= file.objects.len() {
            writeln!(out, "// invalid InterObject reference: {}", idx)?;
            continue;
        }

        let obj = &file.objects[idx];

        // When a real source-level symbol exists, ObjectRef expressions should
        // resolve to that symbol. If its compiler-generated body was not rendered,
        // keep the body separately as an audit helper rather than replacing the
        // object reference with the helper function.
        if idx != toplevel {
            if let Some(symbol) = object_symbols.get(&idx) {
                writeln!(out, "var __tjs2dec_obj_{} = {};", idx, symbol)?;
                if generator_refs.contains(&idx) {
                    writeln!(out, "var __tjs2dec_gen_{} = __tjs2dec_obj_{};", idx, idx)?;
                }
                if !obj.code.is_empty() && !body_emitted.contains(&idx) {
                    let fallback_obj = fallback_executable_object(obj)?;
                    if !fallback_obj.code.is_empty() {
                        bail!(
                            "semantic decompilation incomplete: declared object {} ({:?}, context_type={}) still has executable bytecode that was not integrated into its source construct",
                            idx, obj.name, obj.context_type
                        );
                    }
                }
                writeln!(out)?;
                continue;
            }
        }

        if obj.code.is_empty() {
            writeln!(
                out,
                "var __tjs2dec_obj_{} = void; // metadata-only object: context_type={}, name={:?}",
                idx, obj.context_type, obj.name
            )?;
            if generator_refs.contains(&idx) {
                writeln!(out, "var __tjs2dec_gen_{} = __tjs2dec_obj_{};", idx, idx)?;
            }
            writeln!(out)?;
            continue;
        }

        writeln!(
            out,
            "// object {}: context_type={}, parent={}, name={:?}",
            idx, obj.context_type, obj.parent, obj.name
        )?;
        let fallback_obj = fallback_executable_object(obj)?;
        let (body, params) = emit_object_body(&fallback_obj, file, 2)?;
        writeln!(out, "function __tjs2dec_obj_{}({}) {{", idx, params)?;
        write!(out, "{body}")?;
        writeln!(out, "}}")?;
        if generator_refs.contains(&idx) {
            writeln!(out, "var __tjs2dec_gen_{} = __tjs2dec_obj_{};", idx, idx)?;
        }
        writeln!(out)?;
    }

    if emit_toplevel_fallback {
        writeln!(out, "// === top-level executable body ===")?;
        let obj = &file.objects[toplevel];
        let (mut body, _) = emit_object_body(obj, file, 0)?;
        if body.ends_with("return;\n") {
            body.truncate(body.len() - "return;\n".len());
        } else if body.ends_with("return __tjs2dec_retval;\n") {
            body.truncate(body.len() - "return __tjs2dec_retval;\n".len());
        }
        write!(out, "{body}")?;
        writeln!(out)?;
    }

    if out.contains("__tjs2dec_unrepresentable_scope_proxy")
        || out.contains("__tjs2dec_hidden_member_store")
        || out.contains("__tjs2dec_missing_arg")
        || out.contains("__tjs2dec_bad_fat_")
        || out.contains("__tjs2dec_unrepresentable_direct_property")
        || out.contains("__tjs2dec_unrepresentable_direct_call")
        || out.contains("__tjs2dec_unrepresentable_store_flags")
        || out.contains("__tjs2dec_unrepresentable_opaque_")
        || out.contains("__tjs2dec_unrepresentable_real_literal")
    {
        bail!("semantic decompilation refused: generated source still contains an unrepresentable VM semantic marker");
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

#[derive(Clone, Copy, Debug)]
struct StructuredTry {
    start_block: usize,
    catch_block: usize,
    /// Post-try continuation. None means the normal protected path terminates
    /// (for example `SRV; EXTRY; RET`) instead of jumping to a join block.
    join_block: Option<usize>,
}

#[derive(Clone, Debug)]
struct BranchIntercept {
    target_block: usize,
    guard_name: String,
}

#[derive(Clone, Debug)]
struct GuardedDagPlan {
    /// Region blocks in topological order. The branch root and an optional
    /// ordinary post-dominator are intentionally excluded.
    topo: Vec<usize>,
    /// Whether at least one ordinary edge in the region reaches the join.
    reaches_join: bool,
    /// Terminal blocks may be shared by ordinary control flow outside the
    /// current branch (for example a common function `return;` block). They
    /// are safe to render inside this guarded region, but must not be marked
    /// globally emitted or an unrelated path would lose its terminal action.
    externally_shared_terminals: HashSet<usize>,
}

struct Structurer<'a> {
    cfg: &'a Cfg,
    prog: &'a ExprProgram,
    fmt_var: &'a dyn Fn(VarId) -> String,

    // (pred, succ) -> list of (phi_result, incoming_value)
    edge_copies: HashMap<(usize, usize), Vec<(VarId, VarId)>>,

    // Semantic reachability from the function entry.  This includes
    // exceptional edges so catch handlers remain live, but excludes compiler
    // padding / dead jump blocks.  Source structuring must use the same
    // reachability universe as SSA/dominators; otherwise dead bytecode can
    // masquerade as an external predecessor and prevent valid shared-region
    // recovery.
    reachable: HashSet<usize>,

    // dominators / postdominators on reachable blocks
    dom: Vec<HashSet<usize>>,
    pdom: Vec<HashSet<usize>>,
    ipdom: Vec<Option<usize>>,

    // loop header -> natural loop node set
    loops: HashMap<usize, HashSet<usize>>,

    // Structured exception regions keyed by the first protected block.
    try_by_start: HashMap<usize, StructuredTry>,
    active_try_starts: HashSet<usize>,

    // A branch can conditionally converge on a shared block before its ordinary
    // post-dominator.  Rather than rendering that shared subgraph separately in
    // each arm, intercept entry into the shared block and record it in a local
    // boolean guard.  The shared block is emitted exactly once afterwards.
    branch_intercepts: Vec<BranchIntercept>,
    next_guard_id: usize,

    emitted: HashSet<usize>,

    // return expression per block (from scalar SSA result slot)
    ret_expr: Vec<Option<Expr>>,
    /// Ordinary functions require an explicit source return at a terminal
    /// synthetic CFG exit. Class-initializer slices end naturally at the class
    /// body boundary and must not manufacture a source `return`.
    terminal_fallthrough_returns: bool,
    /// When structuring a ctClass initializer, a negative frame register is a
    /// genuine lexical local only below the class body's root Namespace level.
    /// `class_scope_base_indent` lets statement emission distinguish that from
    /// a top-level class `var`, which would create a member instead.
    class_scope_base_indent: Option<usize>,
    frame_local_decl_defs: HashSet<VarId>,
}

fn normal_successors_of_block(prog: &ExprProgram, bid: usize) -> Vec<usize> {
    let blk = &prog.blocks[bid];
    match &blk.term {
        Terminator::Jmp(t) => vec![*t],
        Terminator::Br {
            if_true,
            if_false,
            ..
        } => vec![*if_true, *if_false],
        Terminator::Fallthrough | Terminator::Exit => {
            blk.succ.first().copied().into_iter().collect()
        }
        Terminator::Ret(_) | Terminator::Throw(_) => Vec::new(),
    }
}

fn all_normal_paths_terminate(
    prog: &ExprProgram,
    start: usize,
    visiting: &mut HashSet<usize>,
    memo: &mut HashMap<usize, bool>,
) -> bool {
    if let Some(v) = memo.get(&start) {
        return *v;
    }
    if !visiting.insert(start) {
        // A cycle in a catch path is not safe to classify as a terminal handler.
        return false;
    }

    let result = match &prog.blocks[start].term {
        Terminator::Ret(_) | Terminator::Throw(_) => true,
        Terminator::Jmp(_) | Terminator::Br { .. } | Terminator::Fallthrough | Terminator::Exit => {
            let succ = normal_successors_of_block(prog, start);
            !succ.is_empty()
                && succ
                    .into_iter()
                    .all(|s| all_normal_paths_terminate(prog, s, visiting, memo))
        }
    };

    visiting.remove(&start);
    memo.insert(start, result);
    result
}

fn normalize_try_exit_target(prog: &ExprProgram, start: usize) -> Option<usize> {
    let mut cur = start;
    let mut seen = HashSet::new();

    for _ in 0..16 {
        if !seen.insert(cur) {
            return Some(cur);
        }
        let blk = &prog.blocks[cur];
        let has_real_stmts = blk.stmts.iter().any(|st| {
            !matches!(st, Stmt::Opaque { op, .. } if is_control_op(op))
        });
        if has_real_stmts {
            return Some(cur);
        }

        match &blk.term {
            Terminator::Ret(_) | Terminator::Throw(_) => return None,
            Terminator::Jmp(t) => cur = *t,
            Terminator::Fallthrough | Terminator::Exit => {
                let Some(next) = normal_successors_of_block(prog, cur).first().copied() else {
                    return None;
                };
                cur = next;
            }
            Terminator::Br { .. } => return Some(cur),
        }
    }

    Some(cur)
}

fn normally_reaches(prog: &ExprProgram, start: usize, target: usize) -> bool {
    if start == target {
        return true;
    }
    let mut stack = vec![start];
    let mut seen = HashSet::new();
    while let Some(bid) = stack.pop() {
        if !seen.insert(bid) {
            continue;
        }
        for succ in normal_successors_of_block(prog, bid) {
            if succ == target {
                return true;
            }
            stack.push(succ);
        }
    }
    false
}

fn build_structured_try_map(cfg: &Cfg, prog: &ExprProgram) -> HashMap<usize, StructuredTry> {
    let mut out = HashMap::new();

    for region in &cfg.try_regions {
        let Some(&start_block) = cfg.pc_to_block.get(&region.start_pc) else {
            continue;
        };
        let Some(&catch_block) = cfg.pc_to_block.get(&region.catch_pc) else {
            continue;
        };

        // `normal_exit_edges` comes from handler-stack dataflow, not from a
        // guessed linear end_pc.  Every edge is an actually reachable EXTRY
        // that popped this exact handler, so return/break/continue/fallthrough
        // exits can coexist without losing the region identity.
        let mut nonterminal_targets = region
            .normal_exit_edges
            .iter()
            .filter_map(|&(_from, to)| normalize_try_exit_target(prog, to))
            .collect::<Vec<_>>();
        nonterminal_targets.sort_unstable();
        nonterminal_targets.dedup();

        let join = if nonterminal_targets.len() == 1 {
            Some(nonterminal_targets[0])
        } else if nonterminal_targets.len() > 1 {
            // Abrupt EXTRY exits (break/continue) may target unrelated loop
            // blocks.  The lexical post-try continuation is the unique exit
            // target also reachable from the catch body when such a target
            // exists.  This handles mixed shapes such as
            // `try { if (...) return x; } catch (...) { ... }` inside a loop.
            let catch_reachable = nonterminal_targets
                .iter()
                .copied()
                .filter(|&t| normally_reaches(prog, catch_block, t))
                .collect::<Vec<_>>();
            if catch_reachable.len() == 1 {
                Some(catch_reachable[0])
            } else {
                // If one exit is downstream of all the others, it is also a
                // valid convergence point.  Otherwise the try has genuinely
                // multiple nonterminal continuations and cannot be represented
                // by the current single-join source region without guessing.
                let converged = nonterminal_targets
                    .iter()
                    .copied()
                    .filter(|&candidate| {
                        nonterminal_targets
                            .iter()
                            .copied()
                            .all(|other| other == candidate || normally_reaches(prog, other, candidate))
                    })
                    .collect::<Vec<_>>();
                if converged.len() == 1 {
                    Some(converged[0])
                } else {
                    continue;
                }
            }
        } else {
            None
        };

        if join == Some(start_block) {
            continue;
        }

        if join == Some(catch_block)
            && block_has_live_exception_materialization(&prog.blocks[catch_block])
        {
            // Normal and exceptional entry would observe different exception
            // register state in the same source block.  Keep this conservative
            // until that edge is explicitly split.
            continue;
        }

        if join.is_none() {
            // With no nonterminal normal EXTRY target, the protected side is
            // terminal.  The catch side may itself continue to later code; in
            // that case emitting that continuation as part of the catch is
            // behaviorally equivalent because the normal protected side cannot
            // reach it.  Still reject cyclic catch paths that the source
            // structurer cannot safely delimit.
            let mut visiting = HashSet::new();
            let mut memo = HashMap::new();
            if !all_normal_paths_terminate(prog, catch_block, &mut visiting, &mut memo) {
                // A nonterminal catch with no reachable normal protected exit
                // is uncommon; keep the region unstructured rather than absorb
                // an unrelated continuation into the catch by accident.
                continue;
            }
        }

        let shape = StructuredTry {
            start_block,
            catch_block,
            join_block: join,
        };

        out.insert(start_block, shape);
    }

    out
}

fn block_has_live_exception_materialization(block: &super::expr_build::ExprBlock) -> bool {
    let Some(exc) = block.exception_in else {
        return false;
    };

    // EXCDEF can disappear after copy propagation while uses of the exception
    // remain (for example `r = exc#1; x = r.message` -> `x = exc#1.message`).
    // Judge liveness from the optimized uses, not from the presence of the
    // materialization assignment itself.
    let mut uses = HashSet::new();
    for st in &block.stmts {
        collect_uses_stmt(st, &mut uses);
    }
    collect_vars_term(&block.term, &mut uses);
    uses.contains(&exc)
}

fn catch_exception_var(block: &super::expr_build::ExprBlock) -> Option<VarId> {
    // The Exception SSA definition belongs to handler entry itself.  Do not
    // recover it by looking for an EXCDEF-shaped assignment in the optimized
    // statement list: propagation can legally turn
    //
    //     r1 = exc#1; r2 = r1.message
    //
    // into `r2 = exc#1.message`, deleting the assignment that the old lookup
    // relied on.  `exception_in` is captured from EXCIN before those rewrites.
    block.exception_in
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
        let try_by_start = build_structured_try_map(cfg, prog);



        Self {
            cfg,
            prog,
            fmt_var,
            edge_copies,
            reachable,
            dom,
            pdom,
            ipdom,
            loops,
            try_by_start,
            active_try_starts: HashSet::new(),
            branch_intercepts: Vec::new(),
            next_guard_id: 0,
            emitted: HashSet::new(),
            ret_expr,
            terminal_fallthrough_returns: true,
            class_scope_base_indent: None,
            frame_local_decl_defs: HashSet::new(),
        }
    }

    fn set_terminal_fallthrough_returns(&mut self, value: bool) {
        self.terminal_fallthrough_returns = value;
    }

    fn set_class_initializer_scope(&mut self, base_indent: usize, decl_defs: HashSet<VarId>) {
        self.class_scope_base_indent = Some(base_indent);
        self.frame_local_decl_defs = decl_defs;
    }

    fn emit_function_body(&mut self, entry: usize, indent: usize) -> Vec<String> {
        let mut lines = Vec::new();
        let _ = self.emit_seq(entry, None, indent, None, &mut lines);
        // Unreachable blocks are silently omitted — no goto/state-machine fallback.
        simplify_empty_if_then(&mut lines);
        lines
    }

    fn emit_try_region(
        &mut self,
        shape: StructuredTry,
        indent: usize,
        loop_ctx: Option<LoopCtx>,
        out: &mut Vec<String>,
    ) -> RegionOutcome {
        self.active_try_starts.insert(shape.start_block);

        // Both arms stop before the post-try join, so they do not need private
        // visited-state snapshots.  Sharing snapshots here can recursively
        // duplicate nested diamonds in malformed or unusual exception CFGs.
        out.push(format!("{}try {{", " ".repeat(indent)));
        let try_oc = self.emit_seq(
            shape.start_block,
            shape.join_block,
            indent + 2,
            loop_ctx.clone(),
            out,
        );
        out.push(format!("{}}}", " ".repeat(indent)));

        // Each handler has its own Exception SSA version.  Bind the generated
        // catch parameter to the exact version consumed by EXCDEF.
        let catch_name = catch_exception_var(&self.prog.blocks[shape.catch_block])
            .map(|v| (self.fmt_var)(v))
            .unwrap_or_else(|| "__tjs2dec_exc".to_string());
        out.push(format!(
            "{}catch ({}) {{",
            " ".repeat(indent),
            catch_name
        ));
        let catch_oc = if shape.join_block == Some(shape.catch_block) {
            // The handler has no exclusive body; both normal and exceptional
            // execution continue at the same block after the catch.
            RegionOutcome { falls_through: true }
        } else {
            self.emit_seq(
                shape.catch_block,
                shape.join_block,
                indent + 2,
                loop_ctx,
                out,
            )
        };
        out.push(format!("{}}}", " ".repeat(indent)));

        self.active_try_starts.remove(&shape.start_block);

        if shape.join_block.is_none() {
            RegionOutcome { falls_through: false }
        } else {
            RegionOutcome {
                falls_through: try_oc.falls_through || catch_oc.falls_through,
            }
        }
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

            // Intercepts are checked before the global emitted set.  The same
            // shared target may be reached from multiple arms; every such path
            // must set the guard even though the shared block itself is emitted
            // only once after the branch.
            if let Some(intercept) = self
                .branch_intercepts
                .iter()
                .rev()
                .find(|i| i.target_block == cur)
            {
                out.push(format!(
                    "{}{} = true;",
                    " ".repeat(indent),
                    intercept.guard_name
                ));
                return RegionOutcome {
                    falls_through: true,
                };
            }

            if self.emitted.contains(&cur) {
                return RegionOutcome {
                    falls_through: true,
                };
            }

            if let Some(shape) = self.try_by_start.get(&cur).copied() {
                if !self.active_try_starts.contains(&cur) && stop != Some(cur) {
                    let oc = self.emit_try_region(shape, indent, loop_ctx.clone(), out);
                    if oc.falls_through {
                        if let Some(join_block) = shape.join_block {
                            cur = join_block;
                            continue;
                        }
                    }
                    return oc;
                }
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
                Terminator::Ret(term_expr) => {
                    let e = self
                        .ret_expr
                        .get(cur)
                        .and_then(|x| x.clone())
                        .unwrap_or(term_expr);
                    let s = self.expr_to_tjs(&e);
                    if s == "void" || s == "r0_0" || s == "__tjs2dec_retval_0" {
                        out.push(format!("{}return;", " ".repeat(indent)));
                    } else {
                        out.push(format!("{}return {};", " ".repeat(indent), s));
                    }
                    return RegionOutcome {
                        falls_through: false,
                    };
                }
                Terminator::Throw(e) => {
                    out.push(format!(
                        "{}throw {};",
                        " ".repeat(indent),
                        self.expr_to_tjs(&e)
                    ));
                    return RegionOutcome {
                        falls_through: false,
                    };
                }
                Terminator::Exit | Terminator::Fallthrough => {
                    if let Some(n) = blk.succ.get(0).copied() {
                        self.emit_edge_copies(cur, n, indent, out);
                        cur = n;
                        continue;
                    }
                    if self.terminal_fallthrough_returns {
                        out.push(format!("{}return;", " ".repeat(indent)));
                        return RegionOutcome { falls_through: false };
                    }
                    return RegionOutcome { falls_through: true };
                }
                Terminator::Jmp(t) => {
                    if let Some(ctx) = loop_ctx.clone() {
                        if t == ctx.header {
                            self.emit_edge_copies(cur, t, indent, out);
                            out.push(format!("{}continue;", " ".repeat(indent)));
                            return RegionOutcome {
                                falls_through: false,
                            };
                        }
                        if ctx.exit == Some(t) {
                            self.emit_edge_copies(cur, t, indent, out);
                            out.push(format!("{}break;", " ".repeat(indent)));
                            return RegionOutcome {
                                falls_through: false,
                            };
                        }
                    }
                    if stop == Some(t) {
                        self.emit_edge_copies(cur, t, indent, out);
                        return RegionOutcome {
                            falls_through: true,
                        };
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
                        if if_true == ctx.header
                            || if_false == ctx.header
                            || ctx.exit == Some(if_true)
                            || ctx.exit == Some(if_false)
                        {
                            let oc = self.emit_branch_in_loop(
                                cur, &cond, if_true, if_false, indent, ctx, out,
                            );
                            return oc;
                        }
                    }

                    // Source joins are computed over ordinary VM control-flow
                    // only, even inside loops. The global post-dominator tree
                    // contains synthetic exception edges and can therefore
                    // miss a local join inside ENTRY/EXTRY or a loop body.
                    let join = self
                        .normal_ipdom_from(cur, stop)
                        .or_else(|| self.ipdom.get(cur).and_then(|x| *x))
                        .or(stop);

                    // If both arms are genuinely empty up to the same join,
                    // there is no source-level branch to preserve. This is a
                    // common artifact after dead SSA assignments disappear.
                    // `branch_is_trivially_empty` has already checked phi edge
                    // copies, so dropping the shell cannot lose dataflow.
                    if join.is_some()
                        && self.branch_is_trivially_empty(cur, if_true, join)
                        && self.branch_is_trivially_empty(cur, if_false, join)
                    {
                        self.mark_chain_emitted(if_true, join);
                        self.mark_chain_emitted(if_false, join);
                        if let Some(j) = join {
                            cur = j;
                            continue;
                        }
                    }

                    // Some compiler-generated short-circuit regions have more
                    // than one convergence point before the ordinary join, or
                    // converge on a shared return while the other path reaches
                    // a different return. A single shared-target guard cannot
                    // represent those shapes. For a closed acyclic region,
                    // linearize each block once with runtime reachability guards.
                    if let Some(plan) = self.plan_guarded_dag_branch(
                        cur,
                        if_true,
                        if_false,
                        join,
                        loop_ctx.as_ref(),
                    ) {
                        let oc = self.emit_guarded_dag_branch(
                            cur,
                            &cond,
                            if_true,
                            if_false,
                            join,
                            plan,
                            indent,
                            out,
                        );
                        if oc.falls_through {
                            if let Some(j) = join {
                                cur = j;
                                continue;
                            }
                        }
                        return oc;
                    }

                    // If the then-branch is trivially empty but else is not, negate and swap
                    // to avoid emitting `if (cond) { } else { ... }`.
                    let (cond_emitted, first_succ, second_succ) = if self
                        .branch_is_trivially_empty(cur, if_true, join)
                        && !self.branch_is_trivially_empty(cur, if_false, join)
                    {
                        (Expr::Unary(UnOp::Not, Box::new(cond)), if_false, if_true)
                    } else {
                        (cond, if_true, if_false)
                    };

                    // A post-dominator is not always the first shared block.  TJS2
                    // short-circuit code commonly has this shape:
                    //
                    //   A true  -> BODY
                    //   A false -> B -> BODY / JOIN
                    //
                    // Rendering BODY independently from each arm is correct but can
                    // become exponential when diamonds are nested.  Instead, locate a
                    // single-entry shared subgraph before JOIN, intercept entry into
                    // it from both arms, and emit it once under a synthetic guard.
                    let shared_target = join.and_then(|j| {
                        self.find_single_entry_shared_target(
                            cur,
                            first_succ,
                            second_succ,
                            j,
                            loop_ctx.as_ref(),
                        )
                    });
                    let guard_name = shared_target.map(|_| self.alloc_branch_guard());
                    if let (Some(target), Some(name)) = (shared_target, guard_name.as_ref()) {
                        out.push(format!(
                            "{}var {} = false;",
                            " ".repeat(indent),
                            name
                        ));
                        self.branch_intercepts.push(BranchIntercept {
                            target_block: target,
                            guard_name: name.clone(),
                        });
                    }

                    out.push(format!(
                        "{}if ({}) {{",
                        " ".repeat(indent),
                        self.expr_to_tjs(&cond_emitted)
                    ));

                    // then (primary branch)
                    self.emit_edge_copies(cur, first_succ, indent + 2, out);
                    let then_oc =
                        self.emit_seq(first_succ, join, indent + 2, loop_ctx.clone(), out);
                    out.push(format!("{}}}", " ".repeat(indent)));

                    // else (secondary branch) — omit the else block when trivially empty.
                    let second_is_empty = self.branch_is_trivially_empty(cur, second_succ, join);
                    let else_oc = if second_is_empty {
                        self.mark_chain_emitted(second_succ, join);
                        RegionOutcome {
                            falls_through: true,
                        }
                    } else {
                        out.push(format!("{}else {{", " ".repeat(indent)));
                        self.emit_edge_copies(cur, second_succ, indent + 2, out);
                        let oc = self.emit_seq(second_succ, join, indent + 2, loop_ctx.clone(), out);
                        out.push(format!("{}}}", " ".repeat(indent)));
                        oc
                    };

                    if let (Some(target), Some(name)) = (shared_target, guard_name.as_ref()) {
                        let popped = self.branch_intercepts.pop();
                        debug_assert!(matches!(
                            popped,
                            Some(BranchIntercept { target_block, .. }) if target_block == target
                        ));

                        out.push(format!(
                            "{}if ({}) {{",
                            " ".repeat(indent),
                            name
                        ));
                        let _ = self.emit_seq(
                            target,
                            join,
                            indent + 2,
                            loop_ctx.clone(),
                            out,
                        );
                        out.push(format!("{}}}", " ".repeat(indent)));
                    }

                    if let Some(j) = join {
                        if then_oc.falls_through || else_oc.falls_through {
                            cur = j;
                            continue;
                        }
                        return RegionOutcome {
                            falls_through: false,
                        };
                    }
                    return RegionOutcome {
                        falls_through: then_oc.falls_through || else_oc.falls_through,
                    };
                }
            }
        }

        RegionOutcome {
            falls_through: true,
        }
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
        // but allow branches to be break/continue.  Never clone `emitted` here:
        // loop bodies amplify branch-local snapshots especially quickly.
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

        RegionOutcome {
            falls_through: then_oc.falls_through || else_oc.falls_through,
        }
    }

    fn alloc_branch_guard(&mut self) -> String {
        let id = self.next_guard_id;
        self.next_guard_id += 1;
        format!("__tjs2dec_guard_{}", id)
    }

    /// Return the ordinary successors that participate in guarded-region
    /// planning.  A nested natural loop is already a structured source node, so
    /// treat the entire loop as one atom instead of rejecting the enclosing
    /// region merely because its raw CFG contains a back-edge.
    fn guarded_region_successors(
        &self,
        bid: usize,
        loop_ctx: Option<&LoopCtx>,
    ) -> Option<Vec<usize>> {
        if self.is_loop_header(bid) {
            // The current loop header is a boundary of the caller's region, not
            // a nested atom.  Re-entering it here would turn the planned DAG
            // cyclic again.
            if loop_ctx.map(|ctx| ctx.header) == Some(bid) {
                return None;
            }

            let body = self.loops.get(&bid)?;
            let primary_exit = self.loop_exit(bid);
            let mut exits = HashSet::new();
            for &node in body {
                for succ in self.normal_successors(node) {
                    if !body.contains(&succ) {
                        exits.insert(succ);
                    }
                }
            }

            // `emit_loop` currently models one ordinary loop exit.  Only use
            // the loop as an atom when the raw CFG agrees with that model.
            match (primary_exit, exits.len()) {
                (None, 0) => Some(Vec::new()),
                (Some(exit), 1) if exits.contains(&exit) => Some(vec![exit]),
                _ => None,
            }
        } else {
            Some(self.normal_successors(bid))
        }
    }

    /// Back-edges inside a loop atom and edges from its body to the unique loop
    /// exit are internal to that structured node.  They must not be mistaken
    /// for external entries into the enclosing guarded region.
    fn guarded_pred_owned_by_loop_atom(
        &self,
        pred: usize,
        bid: usize,
        loop_atoms: &[(usize, HashSet<usize>, Option<usize>)],
    ) -> bool {
        loop_atoms.iter().any(|(header, body, exit)| {
            body.contains(&pred) && (bid == *header || Some(bid) == *exit)
        })
    }

    /// Plan a guarded, single-emission linearization for an acyclic conditional
    /// region with more than one early convergence point.  This is the
    /// correctness fallback for shapes such as:
    ///
    ///     A ----> X ----> ... ----> J
    ///      \      ^
    ///       \-> B-+----> Y ----> J
    ///
    /// A single shared-target guard cannot represent both X and Y without
    /// either duplicating a subgraph or allowing the global `emitted` set to
    /// eat one path.  For a DAG we can instead emit every basic block exactly
    /// once and carry runtime reachability with synthetic booleans.
    fn plan_guarded_dag_branch(
        &self,
        branch_root: usize,
        if_true: usize,
        if_false: usize,
        join: Option<usize>,
        loop_ctx: Option<&LoopCtx>,
    ) -> Option<GuardedDagPlan> {
        const MAX_GUARDED_DAG_BLOCKS: usize = 256;

        let collect = |start: usize| -> Option<HashSet<usize>> {
            let mut seen = HashSet::new();
            let mut stack = Vec::new();
            if Some(start) != join {
                stack.push(start);
            }

            while let Some(bid) = stack.pop() {
                if Some(bid) == join || bid == branch_root || !seen.insert(bid) {
                    continue;
                }
                if seen.len() > MAX_GUARDED_DAG_BLOCKS
                    || (self.emitted.contains(&bid)
                        && !self.normal_successors(bid).is_empty())
                    || self.try_by_start.contains_key(&bid)
                    || self
                        .branch_intercepts
                        .iter()
                        .any(|i| i.target_block == bid)
                {
                    return None;
                }

                // Guarded DAG recovery is allowed inside a loop only while the
                // region remains local to the current iteration.  A nested loop
                // is treated as one structured atom; only the caller's own
                // header/exit remain hard boundaries.
                if let Some(ctx) = loop_ctx {
                    if bid == ctx.header || ctx.exit == Some(bid) {
                        return None;
                    }
                }

                let succs = self.guarded_region_successors(bid, loop_ctx)?;
                for succ in succs {
                    if Some(succ) == join || succ == branch_root {
                        continue;
                    }
                    if let Some(ctx) = loop_ctx {
                        if succ == ctx.header || ctx.exit == Some(succ) {
                            return None;
                        }
                    }
                    stack.push(succ);
                }
            }
            Some(seen)
        };

        let true_nodes = collect(if_true)?;
        let false_nodes = collect(if_false)?;
        if true_nodes.is_disjoint(&false_nodes) {
            return None;
        }

        let nodes = true_nodes
            .union(&false_nodes)
            .copied()
            .collect::<HashSet<_>>();
        if nodes.is_empty() || nodes.len() > MAX_GUARDED_DAG_BLOCKS {
            return None;
        }

        // The guarded region normally has one ordinary entry at branch_root.
        // A terminal block is the one safe exception: compilers commonly share
        // a single `return;` block among several otherwise unrelated branches.
        // We may render that terminal action locally, but must not mark it
        // globally emitted afterwards.
        let loop_atoms = nodes
            .iter()
            .copied()
            .filter_map(|header| {
                let body = self.loops.get(&header)?.clone();
                Some((header, body, self.loop_exit(header)))
            })
            .collect::<Vec<_>>();

        let mut externally_shared_terminals = HashSet::new();
        for &bid in &nodes {
            let mut has_external_pred = false;
            for pred in 0..self.prog.blocks.len() {
                // Dead compiler padding is not a semantic predecessor.  SSA and
                // dominators already exclude it; source structuring must do the
                // same or dead JMP stubs can veto a valid shared region.
                if !self.reachable.contains(&pred)
                    || pred == branch_root
                    || nodes.contains(&pred)
                    || self.guarded_pred_owned_by_loop_atom(pred, bid, &loop_atoms)
                {
                    continue;
                }
                if self.normal_successors(pred).contains(&bid) {
                    has_external_pred = true;
                    break;
                }
            }
            if has_external_pred || self.emitted.contains(&bid) {
                if self.normal_successors(bid).is_empty() {
                    externally_shared_terminals.insert(bid);
                } else {
                    return None;
                }
            }
        }

        // Every ordinary successor must stay inside the region, terminate, or
        // reach the optional ordinary join. Anything else means this is not a
        // closed conditional DAG and the normal structurer should handle it.
        let mut reaches_join = false;
        let mut indegree = nodes
            .iter()
            .copied()
            .map(|b| (b, 0usize))
            .collect::<HashMap<_, _>>();
        for &bid in &nodes {
            for succ in self.guarded_region_successors(bid, loop_ctx)? {
                if Some(succ) == join {
                    reaches_join = true;
                } else if nodes.contains(&succ) {
                    *indegree.get_mut(&succ)? += 1;
                } else {
                    return None;
                }
            }
        }
        if Some(if_true) == join || Some(if_false) == join {
            reaches_join = true;
        }

        // Kahn topological order also acts as the cycle check. Basic-block ids
        // follow bytecode order, so BTreeSet makes generated source stable.
        let mut ready = BTreeSet::new();
        for (&bid, &deg) in &indegree {
            if deg == 0 {
                ready.insert(bid);
            }
        }
        let mut topo = Vec::with_capacity(nodes.len());
        let mut indegree_work = indegree;
        while let Some(&bid) = ready.iter().next() {
            ready.remove(&bid);
            topo.push(bid);
            for succ in self.guarded_region_successors(bid, loop_ctx)? {
                if !nodes.contains(&succ) {
                    continue;
                }
                let deg = indegree_work.get_mut(&succ)?;
                *deg = deg.saturating_sub(1);
                if *deg == 0 {
                    ready.insert(succ);
                }
            }
        }
        if topo.len() != nodes.len() {
            return None;
        }

        Some(GuardedDagPlan {
            topo,
            reaches_join,
            externally_shared_terminals,
        })
    }

    fn emit_guarded_dag_edge(
        &mut self,
        pred: usize,
        succ: usize,
        join: Option<usize>,
        guards: &HashMap<usize, String>,
        indent: usize,
        out: &mut Vec<String>,
    ) {
        self.emit_edge_copies(pred, succ, indent, out);
        if Some(succ) == join {
            return;
        }
        if let Some(name) = guards.get(&succ) {
            out.push(format!("{}{} = true;", " ".repeat(indent), name));
        }
    }

    fn guarded_dag_edge_has_effect(
        &self,
        pred: usize,
        succ: usize,
        join: Option<usize>,
    ) -> bool {
        Some(succ) != join
            || self
                .edge_copies
                .get(&(pred, succ))
                .map_or(false, |copies| !copies.is_empty())
    }

    fn emit_guarded_dag_conditional(
        &mut self,
        pred: usize,
        cond: &Expr,
        if_true: usize,
        if_false: usize,
        join: Option<usize>,
        guards: &HashMap<usize, String>,
        indent: usize,
        out: &mut Vec<String>,
    ) {
        let true_effect = self.guarded_dag_edge_has_effect(pred, if_true, join);
        let false_effect = self.guarded_dag_edge_has_effect(pred, if_false, join);
        let cond_s = self.expr_to_tjs(cond);

        match (true_effect, false_effect) {
            (true, true) => {
                out.push(format!("{}if ({}) {{", " ".repeat(indent), cond_s));
                self.emit_guarded_dag_edge(
                    pred,
                    if_true,
                    join,
                    guards,
                    indent + 2,
                    out,
                );
                out.push(format!("{}}}", " ".repeat(indent)));
                out.push(format!("{}else {{", " ".repeat(indent)));
                self.emit_guarded_dag_edge(
                    pred,
                    if_false,
                    join,
                    guards,
                    indent + 2,
                    out,
                );
                out.push(format!("{}}}", " ".repeat(indent)));
            }
            (true, false) => {
                out.push(format!("{}if ({}) {{", " ".repeat(indent), cond_s));
                self.emit_guarded_dag_edge(
                    pred,
                    if_true,
                    join,
                    guards,
                    indent + 2,
                    out,
                );
                out.push(format!("{}}}", " ".repeat(indent)));
            }
            (false, true) => {
                out.push(format!("{}if (!({})) {{", " ".repeat(indent), cond_s));
                self.emit_guarded_dag_edge(
                    pred,
                    if_false,
                    join,
                    guards,
                    indent + 2,
                    out,
                );
                out.push(format!("{}}}", " ".repeat(indent)));
            }
            (false, false) => {}
        }
    }

    /// Emit a previously planned acyclic region.  The branch root has already
    /// emitted its statements; this function emits its terminator and every
    /// descendant block once, guarded by runtime reachability.
    fn emit_guarded_dag_branch(
        &mut self,
        branch_root: usize,
        cond: &Expr,
        if_true: usize,
        if_false: usize,
        join: Option<usize>,
        plan: GuardedDagPlan,
        indent: usize,
        out: &mut Vec<String>,
    ) -> RegionOutcome {
        let GuardedDagPlan {
            topo,
            reaches_join,
            externally_shared_terminals,
        } = plan;

        let mut guards = HashMap::new();
        for &bid in &topo {
            let name = self.alloc_branch_guard();
            out.push(format!("{}var {} = false;", " ".repeat(indent), name));
            guards.insert(bid, name);
        }

        self.emit_guarded_dag_conditional(
            branch_root,
            cond,
            if_true,
            if_false,
            join,
            &guards,
            indent,
            out,
        );

        for bid in topo {
            let guard = guards
                .get(&bid)
                .expect("guarded DAG block must have a guard")
                .clone();

            // Nested loops are structural atoms in the plan.  Let the normal
            // loop structurer render the loop body exactly once, then propagate
            // reachability to its unique ordinary exit.  Do not pre-mark the
            // header emitted: `emit_loop` owns the whole natural-loop node set.
            if self.is_loop_header(bid) {
                out.push(format!("{}if ({}) {{", " ".repeat(indent), guard));
                let oc = self.emit_loop(bid, indent + 2, out);
                if oc.falls_through {
                    if let Some(exit) = self
                        .guarded_region_successors(bid, None)
                        .and_then(|succs| succs.into_iter().next())
                    {
                        if Some(exit) != join {
                            if let Some(name) = guards.get(&exit) {
                                out.push(format!(
                                    "{}{} = true;",
                                    " ".repeat(indent + 2),
                                    name
                                ));
                            }
                        }
                    }
                }
                out.push(format!("{}}}", " ".repeat(indent)));
                continue;
            }

            if !externally_shared_terminals.contains(&bid) {
                self.emitted.insert(bid);
            }
            out.push(format!("{}if ({}) {{", " ".repeat(indent), guard));
            self.emit_block_stmts(bid, indent + 2, out);

            match self.prog.blocks[bid].term.clone() {
                Terminator::Ret(term_expr) => {
                    let e = self
                        .ret_expr
                        .get(bid)
                        .and_then(|x| x.clone())
                        .unwrap_or(term_expr);
                    let s = self.expr_to_tjs(&e);
                    if s == "void" || s == "r0_0" || s == "__tjs2dec_retval_0" {
                        out.push(format!("{}return;", " ".repeat(indent + 2)));
                    } else {
                        out.push(format!("{}return {};", " ".repeat(indent + 2), s));
                    }
                }
                Terminator::Throw(e) => out.push(format!(
                    "{}throw {};",
                    " ".repeat(indent + 2),
                    self.expr_to_tjs(&e)
                )),
                Terminator::Jmp(t) => self.emit_guarded_dag_edge(
                    bid,
                    t,
                    join,
                    &guards,
                    indent + 2,
                    out,
                ),
                Terminator::Br {
                    cond,
                    if_true,
                    if_false,
                } => self.emit_guarded_dag_conditional(
                    bid,
                    &cond,
                    if_true,
                    if_false,
                    join,
                    &guards,
                    indent + 2,
                    out,
                ),
                Terminator::Fallthrough | Terminator::Exit => {
                    if let Some(next) = self.normal_successors(bid).first().copied() {
                        self.emit_guarded_dag_edge(
                            bid,
                            next,
                            join,
                            &guards,
                            indent + 2,
                            out,
                        );
                    }
                }
            }
            out.push(format!("{}}}", " ".repeat(indent)));
        }

        RegionOutcome {
            falls_through: reaches_join,
        }
    }

    fn normal_successors(&self, bid: usize) -> Vec<usize> {
        let blk = &self.prog.blocks[bid];
        match &blk.term {
            Terminator::Jmp(t) => vec![*t],
            Terminator::Br {
                if_true,
                if_false,
                ..
            } => vec![*if_true, *if_false],
            Terminator::Fallthrough | Terminator::Exit => {
                blk.succ.first().copied().into_iter().collect()
            }
            Terminator::Ret(_) | Terminator::Throw(_) => Vec::new(),
        }
    }

    /// Compute the immediate post-dominator for source structuring using only
    /// ordinary VM control-flow edges.  `ExprBlock::succ` deliberately keeps
    /// synthetic exceptional edges for SSA, so the global post-dominator tree
    /// is not a reliable source join inside an ENTRY region.
    fn normal_ipdom_from(&self, root: usize, stop: Option<usize>) -> Option<usize> {
        let mut nodes = HashSet::new();
        let mut stack = vec![root];
        while let Some(bid) = stack.pop() {
            if !nodes.insert(bid) {
                continue;
            }
            if nodes.len() > 512 {
                return None;
            }
            if stop == Some(bid) {
                continue;
            }
            for succ in self.normal_successors(bid) {
                if succ < self.prog.blocks.len() {
                    stack.push(succ);
                }
            }
        }

        if nodes.len() <= 1 {
            return None;
        }
        let all = nodes.clone();
        let exits = nodes
            .iter()
            .copied()
            .filter(|&bid| {
                if stop == Some(bid) {
                    return true;
                }
                self.normal_successors(bid)
                    .into_iter()
                    .all(|s| !nodes.contains(&s))
            })
            .collect::<HashSet<_>>();
        if exits.is_empty() {
            return None;
        }

        let mut pdom = HashMap::<usize, HashSet<usize>>::new();
        for &bid in &nodes {
            if exits.contains(&bid) {
                let mut only = HashSet::new();
                only.insert(bid);
                pdom.insert(bid, only);
            } else {
                pdom.insert(bid, all.clone());
            }
        }

        let mut changed = true;
        let mut rounds = 0usize;
        while changed {
            changed = false;
            rounds += 1;
            if rounds > nodes.len().saturating_mul(4).max(8) {
                return None;
            }
            for &bid in &nodes {
                if exits.contains(&bid) {
                    continue;
                }
                let succ = self
                    .normal_successors(bid)
                    .into_iter()
                    .filter(|s| nodes.contains(s))
                    .collect::<Vec<_>>();
                if succ.is_empty() {
                    continue;
                }
                let mut next = all.clone();
                for sid in succ {
                    let sp = pdom.get(&sid)?;
                    next = next.intersection(sp).copied().collect();
                }
                next.insert(bid);
                if pdom.get(&bid) != Some(&next) {
                    pdom.insert(bid, next);
                    changed = true;
                }
            }
        }

        let root_pdom = pdom.get(&root)?;
        let candidates = root_pdom
            .iter()
            .copied()
            .filter(|&b| b != root)
            .collect::<Vec<_>>();
        for &candidate in &candidates {
            let immediate = candidates.iter().copied().all(|other| {
                other == candidate
                    || !pdom
                        .get(&other)
                        .map_or(false, |set| set.contains(&candidate))
            });
            if immediate {
                return Some(candidate);
            }
        }
        None
    }

    fn reachable_distances_before(
        &self,
        start: usize,
        stop: usize,
        branch_root: usize,
        loop_ctx: Option<&LoopCtx>,
    ) -> HashMap<usize, usize> {
        use std::collections::VecDeque;

        let mut dist = HashMap::new();
        let mut q = VecDeque::new();
        if start != stop && start != branch_root {
            dist.insert(start, 0);
            q.push_back(start);
        }

        while let Some(cur) = q.pop_front() {
            let d = dist[&cur];
            for next in self.normal_successors(cur) {
                if next == stop || next == branch_root {
                    continue;
                }
                if let Some(ctx) = loop_ctx {
                    if next == ctx.header || ctx.exit == Some(next) {
                        continue;
                    }
                    if let Some(body) = self.loops.get(&ctx.header) {
                        if !body.contains(&next) {
                            continue;
                        }
                    }
                }
                if self.emitted.contains(&next) || dist.contains_key(&next) {
                    continue;
                }
                dist.insert(next, d + 1);
                q.push_back(next);
            }
        }

        dist
    }

    /// Find a shared block strictly before the ordinary post-dominator that can
    /// be emitted once after both branch arms.  We only accept a candidate that
    /// dominates every other common block, giving the overlap a single entry.
    /// This is intentionally conservative: ambiguous multi-entry overlaps keep
    /// the ordinary non-duplicating structuring path instead of guessing.
    fn find_single_entry_shared_target(
        &self,
        branch_root: usize,
        if_true: usize,
        if_false: usize,
        join: usize,
        loop_ctx: Option<&LoopCtx>,
    ) -> Option<usize> {
        let td = self.reachable_distances_before(if_true, join, branch_root, loop_ctx);
        let fd = self.reachable_distances_before(if_false, join, branch_root, loop_ctx);

        let common = td
            .keys()
            .copied()
            .filter(|b| fd.contains_key(b))
            .filter(|&b| b != join && b != branch_root)
            // A shared block inside the region should be dominated by the
            // conditional itself; this rejects back-edges to enclosing CFG.
            .filter(|&b| self.dom.get(b).map_or(false, |d| d.contains(&branch_root)))
            .collect::<Vec<_>>();

        if common.is_empty() {
            return None;
        }

        let mut candidates = common
            .iter()
            .copied()
            .filter(|&candidate| {
                common.iter().all(|&other| {
                    candidate == other
                        || self
                            .dom
                            .get(other)
                            .map_or(false, |d| d.contains(&candidate))
                })
            })
            .collect::<Vec<_>>();

        candidates.sort_by_key(|b| {
            let a = td.get(b).copied().unwrap_or(usize::MAX / 4);
            let c = fd.get(b).copied().unwrap_or(usize::MAX / 4);
            (a.max(c), a.saturating_add(c), *b)
        });
        candidates.into_iter().next()
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
            None => {
                return RegionOutcome {
                    falls_through: true,
                };
            }
        };

        // Choose loop exit as header successor not in loop set.
        let exit = self.loop_exit(header);

        out.push(format!("{}while (true) {{", " ".repeat(indent)));

        // Emit header statements inside loop.
        self.emit_block_stmts(header, indent + 2, out);

        // Handle header terminator as loop guard / dispatch.
        let blk = &self.prog.blocks[header];
        match blk.term.clone() {
            Terminator::Br {
                cond,
                if_true,
                if_false,
            } => {
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
            Terminator::Ret(term_expr) => {
                let e = self
                    .ret_expr
                    .get(header)
                    .and_then(|x| x.clone())
                    .unwrap_or(term_expr);
                let s = self.expr_to_tjs(&e);
                if s == "void" || s == "r0_0" || s == "__tjs2dec_retval_0" {
                    out.push(format!("{}return;", " ".repeat(indent + 2)));
                } else {
                    out.push(format!("{}return {};", " ".repeat(indent + 2), s));
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

        RegionOutcome {
            falls_through: exit.is_some(),
        }
    }

    /// Returns true when branching from `pred` to `succ` (with `stop` as the region limit)
    /// would emit zero lines: no non-trivial edge copies, no block statements, and every block
    /// in the single-successor chain eventually falls to `stop` (follows Jmp/Fallthrough/Exit
    /// only, up to `depth` hops, with cycle detection).
    fn branch_is_trivially_empty(&self, pred: usize, succ: usize, stop: Option<usize>) -> bool {
        let mut visited = HashSet::new();
        self.chain_is_empty(pred, succ, stop, &mut visited, 16)
    }

    fn chain_is_empty(
        &self,
        pred: usize,
        succ: usize,
        stop: Option<usize>,
        visited: &mut HashSet<usize>,
        depth: usize,
    ) -> bool {
        // Always check edge copies from pred→succ first (including when succ==stop),
        // so that live phi edge copies on the final hop are not silently skipped.
        if let Some(xs) = self.edge_copies.get(&(pred, succ)) {
            for (d, s) in xs {
                if (self.fmt_var)(*d) != (self.fmt_var)(*s) {
                    return false;
                }
            }
        }
        if Some(succ) == stop {
            return true;
        }
        if depth == 0 || !visited.insert(succ) {
            return false;
        }
        let blk = &self.prog.blocks[succ];
        // Any non-control stmt → not empty.
        for st in &blk.stmts {
            if !matches!(st, Stmt::Opaque { op, .. } if is_control_op(op)) {
                return false;
            }
        }
        // Follow single-successor terminators only.
        match &blk.term {
            Terminator::Jmp(t) => self.chain_is_empty(succ, *t, stop, visited, depth - 1),
            Terminator::Fallthrough | Terminator::Exit => match blk.succ.get(0).copied() {
                Some(t) => self.chain_is_empty(succ, t, stop, visited, depth - 1),
                None => stop.is_none(),
            },
            _ => false,
        }
    }

    /// Mark all blocks in the single-successor chain from `succ` up to (but not including)
    /// `stop` as emitted.  Called when we skip an empty branch entirely.
    fn mark_chain_emitted(&mut self, succ: usize, stop: Option<usize>) {
        let mut cur = succ;
        loop {
            if Some(cur) == stop || !self.emitted.insert(cur) {
                break;
            }
            let blk = &self.prog.blocks[cur];
            match &blk.term {
                Terminator::Jmp(t) => cur = *t,
                Terminator::Fallthrough | Terminator::Exit => match blk.succ.get(0).copied() {
                    Some(t) => cur = t,
                    None => break,
                },
                _ => break,
            }
        }
    }

    fn emit_block_stmts(&self, bid: usize, indent: usize, out: &mut Vec<String>) {
        let blk = &self.prog.blocks[bid];
        for st in &blk.stmts {
            if let Stmt::Opaque { op, .. } = st {
                if is_control_op(op) {
                    continue;
                }
            }
            let s = self.stmt_to_tjs(st, indent);
            if s.is_empty() || s == "// (control op omitted)" {
                continue;
            }
            out.push(format!("{}{}", " ".repeat(indent), s));
        }
    }

    fn emit_edge_copies(&self, pred: usize, succ: usize, indent: usize, out: &mut Vec<String>) {
        if let Some(xs) = self.edge_copies.get(&(pred, succ)) {
            for (dst, src) in xs {
                let d = (self.fmt_var)(*dst);
                // Both r0#0 and Result#0 are VM live-ins whose initial value is void.
                let s = if (src.var == Var::Reg(0) || src.var == Var::Result) && src.ver == 0 {
                    "void".to_string()
                } else {
                    (self.fmt_var)(*src)
                };
                if d == s {
                    continue; // skip self-assignments
                }
                out.push(format!("{}{} = {};", " ".repeat(indent), d, s));
            }
        }
    }

    fn stmt_to_tjs(&self, st: &Stmt, indent: usize) -> String {
        match st {
            Stmt::Assign { dst, expr } => {
                if self.frame_local_decl_defs.contains(dst) {
                    let Some(base_indent) = self.class_scope_base_indent else {
                        return format!(
                            "{} = {};",
                            (self.fmt_var)(*dst),
                            self.expr_to_tjs(expr)
                        );
                    };
                    if indent <= base_indent {
                        // At ctClass root, `var` creates a member. A frame local
                        // must therefore be declared in a nested lexical block.
                        return "__tjs2dec_unrepresentable_class_local();".to_string();
                    }
                    if matches!(expr, Expr::Void) {
                        format!("var {};", (self.fmt_var)(*dst))
                    } else {
                        format!(
                            "var {} = {};",
                            (self.fmt_var)(*dst),
                            self.expr_to_tjs(expr)
                        )
                    }
                } else {
                    format!("{} = {};", (self.fmt_var)(*dst), self.expr_to_tjs(expr))
                }
            }
            Stmt::Store { target, value } => {
                format!(
                    "{} = {};",
                    self.expr_to_tjs(target),
                    self.expr_to_tjs(value)
                )
            }
            Stmt::MemberDecl { name, value } => {
                if let Some(base_indent) = self.class_scope_base_indent {
                    if indent > base_indent {
                        // At ctClass root, `var name = value` is the source
                        // spelling of SPDS and creates/initializes a class
                        // member.  Inside an explicit nested lexical block,
                        // however, `var` would create a local instead.  Keep
                        // the original VM target (`%-1`, the class object) and
                        // IGNOREPROP semantics with the source `&` lvalue.
                        let target = format!("&(this.{})", name);
                        return format!("{} = {};", target, self.expr_to_tjs(value));
                    }
                }
                if matches!(value, Expr::Void) {
                    format!("var {};", name)
                } else {
                    format!("var {} = {};", name, self.expr_to_tjs(value))
                }
            }
            Stmt::Update {
                dst,
                target,
                op,
                rhs,
            } => {
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
            Stmt::IncDec {
                dst,
                target,
                increment,
            } => {
                let op = if *increment { "++" } else { "--" };
                if let Some(d) = dst {
                    format!(
                        "{} = {}{};",
                        (self.fmt_var)(*d),
                        op,
                        self.expr_to_tjs(target)
                    )
                } else {
                    format!("{}{};", op, self.expr_to_tjs(target))
                }
            }
            Stmt::Expr(e) => format!("{};", self.expr_to_tjs(e)),
            Stmt::Opaque { op, args, defs } => {
                match op.to_string().as_str() {
                    "JF" | "JNF" | "JMP" | "RET" | "THROW" | "ENTRY" | "EXTRY" | "VM_JF"
                    | "VM_JNF" | "VM_JMP" | "VM_RET" | "VM_THROW" | "VM_ENTRY" | "VM_EXTRY" => {
                        return "// (control op omitted)".to_string();
                    }
                    _ => {}
                }
                let op_name = op.to_string();
                if (op_name == "VM_TYPEOFD"
                    || op_name == "TYPEOFD"
                    || op_name == "VM_TYPEOF"
                    || op_name == "TYPEOF")
                    && args.len() == 1
                {
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

                if (op_name == "VM_NUM" || op_name == "NUM") && args.len() == 1 {
                    let x = args[0].to_tjs_with(self.fmt_var);

                    let expr = format!("(+{})", x);

                    if defs.len() == 1 {
                        return format!("{} = {};", (self.fmt_var)(defs[0]), expr);
                    } else {
                        return format!("{};", expr);
                    }
                }

                if (op_name.starts_with("VM_STR") || op_name == "STR") && args.len() == 1 {
                    let x = args[0].to_tjs_with(self.fmt_var);
                    let expr = format!("(string {})", x);

                    if defs.len() == 1 {
                        return format!("{} = {};", (self.fmt_var)(defs[0]), expr);
                    } else {
                        return format!("{};", expr);
                    }
                }

                if matches!(
                    op_name.as_str(),
                    "VM_EVAL" | "EVAL" | "VM_EEXP" | "EEXP"
                ) && args.len() == 1
                {
                    let x = args[0].to_tjs_with(self.fmt_var);
                    // TJS' eval operator is postfix `!`. EVAL stores the result
                    // back to the operand register; EEXP executes only for side
                    // effects and therefore has no SSA definition.
                    let eval_expr = format!("({})!", x);
                    if op_name == "VM_EVAL" || op_name == "EVAL" {
                        if defs.len() == 1 {
                            return format!("{} = {};", (self.fmt_var)(defs[0]), eval_expr);
                        }
                    }
                    return format!("{};", eval_expr);
                }

                if op_name == "VM_CHGTHIS" || op_name == "CHGTHIS" {
                    if args.len() == 2 {
                        let dest = args[0].to_tjs_with(self.fmt_var);
                        let src = args[1].to_tjs_with(self.fmt_var);
                        if defs.len() == 1 {
                            return format!(
                                "{} = ({} incontextof {});",
                                (self.fmt_var)(defs[0]), dest, src
                            );
                        }
                        return format!("{} incontextof {};", dest, src);
                    }
                    return "// malformed chgthis".to_string();
                }

                if op_name == "VM_ADDCI" || op_name == "ADDCI" {
                    // Compiler-generated class-instance metadata bookkeeping. The
                    // surrounding structural class reconstruction is the source-level
                    // representation; do not invent a callable VM_ADDCI pseudo API.
                    return "__tjs2dec_unrepresentable_opaque_ADDCI();".to_string();
                }

                if op_name == "VM_REGMEMBER" || op_name == "REGMEMBER" {
                    // Internal member registration/copy with closure rebinding. It has
                    // no direct ordinary-TJS statement equivalent. Keep it visible as
                    // an audit marker rather than emitting false assignment syntax.
                    return "__tjs2dec_unrepresentable_opaque_REGMEMBER();".to_string();
                }

                if op_name == "VM_NOP" || op_name == "NOP" {
                    return String::new();
                }
                if op_name == "VM_DEBUGGER" || op_name == "DEBUGGER" {
                    return "debugger;".to_string();
                }

                // Every remaining opaque opcode is a semantic hole.  Older
                // code guessed a source operator from the mnemonic here, which
                // is unsafe for property-operation variants and unknown VM
                // extensions. Keep a marker that the final audit refuses.
                if !(op_name == "VM_EVAL" || op_name == "EVAL" || op_name == "VM_EEXP" || op_name == "EEXP") {
                    let safe_name = op_name
                        .chars()
                        .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
                        .collect::<String>();
                    return format!("__tjs2dec_unrepresentable_opaque_{}();", safe_name);
                }

                if op_name.starts_with("VM_INV") && args.len() >= 2 {
                    let recv = args[0].to_tjs_with(self.fmt_var);
                    let method = args[1].to_tjs_with(self.fmt_var);
                    let call_args = args
                        .iter()
                        .skip(2)
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
                        if opname.starts_with("VM_ADD") {
                            format!("({} + {})", x, y)
                        } else if opname.starts_with("VM_SUB") {
                            format!("({} - {})", x, y)
                        } else if opname.starts_with("VM_MUL") {
                            format!("({} * {})", x, y)
                        } else if opname.starts_with("VM_DIV") {
                            format!("({} / {})", x, y)
                        } else if opname.starts_with("VM_IDIV") {
                            format!("({} \\ {})", x, y)
                        } else if opname.starts_with("VM_MOD") {
                            format!("({} % {})", x, y)
                        } else if opname.starts_with("VM_SAL") {
                            format!("({} << {})", x, y)
                        } else if opname.starts_with("VM_SAR") {
                            format!("({} >> {})", x, y)
                        } else if opname.starts_with("VM_SR") {
                            format!("({} >>> {})", x, y)
                        } else if opname.starts_with("VM_BAND") {
                            format!("({} & {})", x, y)
                        } else if opname.starts_with("VM_BXOR") {
                            format!("({} ^ {})", x, y)
                        } else if opname.starts_with("VM_BOR") {
                            format!("({} | {})", x, y)
                        } else if opname.starts_with("VM_LAND") {
                            format!("({} && {})", x, y)
                        } else if opname.starts_with("VM_LOR") {
                            format!("({} || {})", x, y)
                        } else if opname.starts_with("VM_EQ") {
                            format!("({} == {})", x, y)
                        } else if opname.starts_with("VM_NE") {
                            format!("({} != {})", x, y)
                        } else if opname.starts_with("VM_DEQ") {
                            format!("({} === {})", x, y)
                        } else if opname.starts_with("VM_DNE") {
                            format!("({} !== {})", x, y)
                        } else if opname.starts_with("VM_LT") {
                            format!("({} < {})", x, y)
                        } else if opname.starts_with("VM_LE") {
                            format!("({} <= {})", x, y)
                        } else if opname.starts_with("VM_GT") {
                            format!("({} > {})", x, y)
                        } else if opname.starts_with("VM_GE") {
                            format!("({} >= {})", x, y)
                        } else if opname.to_string() == "CHKINS" || opname.starts_with("VM_IN") {
                            format!("({} in {})", x, y)
                        } else {
                            // fallback to original call form
                            let mut s = String::new();
                            s.push_str(op);
                            s.push('(');
                            for (i, a) in args.iter().enumerate() {
                                if i != 0 {
                                    s.push_str(", ");
                                }
                                s.push_str(&a.to_tjs_with(self.fmt_var));
                            }
                            s.push(')');
                            s
                        }
                    } else if let Some(x) = a0.as_deref() {
                        // unary families (also cover variants)
                        if opname.starts_with("VM_CHS") {
                            format!("(-{})", x)
                        } else if opname.starts_with("VM_LNOT") {
                            format!("(!{})", x)
                        } else if opname.starts_with("VM_BNOT") {
                            format!("(~{})", x)
                        } else if opname.starts_with("VM_TYPEOF") {
                            format!("(typeof {})", x)
                        } else if opname.starts_with("VM_DELETE") {
                            format!("(delete {})", x)
                        } else if opname.starts_with("VM_INC") {
                            format!("({} + 1)", x)
                        } else if opname.starts_with("VM_DEC") {
                            format!("({} - 1)", x)
                        } else {
                            // fallback
                            let mut s = String::new();
                            s.push_str(op);
                            s.push('(');
                            for (i, a) in args.iter().enumerate() {
                                if i != 0 {
                                    s.push_str(", ");
                                }
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
                        let _ = write!(&mut s, "{} = __t[{}]; ", (self.fmt_var)(*d), i);
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
                m.entry((*pred, b.id)).or_default().push((phi.result, *v));
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
                Terminator::Ret(_) | Terminator::Throw(_) // Exit/Fallthrough with no succ also treated later
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
        BinOp::IDiv => BinOp::IDivAssign,
        BinOp::Mod => BinOp::ModAssign,
        BinOp::Shl => BinOp::ShlAssign,
        BinOp::Shr => BinOp::ShrAssign,
        BinOp::UShr => BinOp::UShrAssign,
        BinOp::BitAnd => BinOp::AndAssign,
        BinOp::BitOr => BinOp::OrAssign,
        BinOp::BitXor => BinOp::XorAssign,
        BinOp::LogAnd => BinOp::LogAndAssign,
        BinOp::LogOr => BinOp::LogOrAssign,
        _ => return None,
    })
}

fn is_control_op(op: &str) -> bool {
    let bare = op.strip_prefix("VM_").unwrap_or(op);
    bare.eq_ignore_ascii_case("JMP")
        || bare.eq_ignore_ascii_case("JF")
        || bare.eq_ignore_ascii_case("JNF")
        || bare.eq_ignore_ascii_case("RET")
        || bare.eq_ignore_ascii_case("THROW")
        || bare.eq_ignore_ascii_case("ENTRY")
        || bare.eq_ignore_ascii_case("EXTRY")
}

fn emit_var_decls(
    out: &mut String,
    prog: &ExprProgram,
    fmt_var: &dyn Fn(VarId) -> String,
    arg_count: usize,
    collapse_base: i32,
    indent: usize,
) -> Result<()> {
    let mut vars: Vec<VarId> = collect_vars(prog);
    vars.sort_by_key(|v| (var_key(v), v.ver));
    // Declare positive registers, frame locals (_fr*), and special vars.
    // Do NOT declare declared params (a0..a{n-1}) or special regs (-1=this, -2=global/this).
    // Also skip r0_0 (ver=0 of reg 0) — it's always void and never declared.
    vars.retain(|v| match v.var {
        Var::Reg(r) if r >= 0 => !(r == 0 && v.ver == 0), // skip r0_0
        Var::Reg(r) if r <= -3 => {
            let frame_idx = (-3 - r) as usize;
            frame_idx >= arg_count && !(collapse_base >= 0 && frame_idx == collapse_base as usize)
        }, // frame locals only, not args/collapse parameter
        Var::Flag => true,
        // Exception SSA values are catch parameters, not function locals.
        Var::Exception => false,
        Var::Result => v.ver != 0,
        _ => false,
    });
    vars.dedup_by_key(|v| fmt_var(*v));
    if vars.is_empty() {
        return Ok(());
    }

    let pad = " ".repeat(indent);
    let mut i = 0usize;
    while i < vars.len() {
        let end = (i + 12).min(vars.len());
        write!(out, "{}var ", pad)?;
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
        Stmt::MemberDecl { value, .. } => collect_vars_expr(value, s),
        Stmt::Update {
            dst, target, rhs, ..
        } => {
            if let Some(d) = dst {
                s.insert(*d);
            }
            collect_vars_expr(target, s);
            collect_vars_expr(rhs, s);
        }
        Stmt::IncDec { dst, target, .. } => {
            if let Some(d) = dst {
                s.insert(*d);
            }
            collect_vars_expr(target, s);
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
        Terminator::Ret(e) | Terminator::Throw(e) => collect_vars_expr(e, s),
        _ => {}
    }
}

fn collect_vars_expr(e: &Expr, s: &mut HashSet<VarId>) {
    match e {
        Expr::SsaVar(v) => {
            s.insert(*v);
        }
        Expr::Unary(_, a) | Expr::ArgExpand(a) => collect_vars_expr(a, s),
        Expr::Deref(a) => collect_vars_expr(a, s),
        Expr::Binary(_, a, b) => {
            collect_vars_expr(a, s);
            collect_vars_expr(b, s);
        }
        Expr::Conditional {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_vars_expr(cond, s);
            collect_vars_expr(then_expr, s);
            collect_vars_expr(else_expr, s);
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
        Expr::ArrayLiteral(items) => {
            for a in items {
                collect_vars_expr(a, s);
            }
        }
        Expr::DictionaryLiteral(items) => {
            for (k, v) in items {
                collect_vars_expr(k, s);
                collect_vars_expr(v, s);
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
        Var::Result => (2, 0),
        Var::Exception => (3, 0),
    }
}

fn fmt_vid_tjs(vid: VarId) -> String {
    match vid.var {
        Var::Reg(r) if r >= 0 => format!("r{}_{}", r, vid.ver),
        Var::Reg(-1) => "this".to_string(),
        Var::Reg(-2) => "global".to_string(),
        Var::Reg(r) => format!("a{}", (-3 - r) as usize),
        Var::Flag => format!("flag_{}", vid.ver),
        Var::Result => format!("__tjs2dec_retval_{}", vid.ver),
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

/// Post-processing pass: collapse `if (cond) { } else { ... }` into `if (!cond) { ... }`.
/// Operates on a flat list of lines with consistent indentation.
fn simplify_empty_if_then(lines: &mut Vec<String>) {
    let mut i = 0;
    while i + 2 < lines.len() {
        let ind0 = leading_spaces(&lines[i]);
        let ind1 = leading_spaces(&lines[i + 1]);
        let ind2 = leading_spaces(&lines[i + 2]);
        let ln0 = lines[i][ind0..].trim_end();
        let ln1 = lines[i + 1][ind1..].trim_end();
        let ln2 = lines[i + 2][ind2..].trim_end();

        if ind0 == ind1
            && ind0 == ind2
            && ln0.starts_with("if (")
            && ln0.ends_with(") {")
            && ln1 == "}"
            && ln2 == "else {"
        {
            let cond = &ln0["if (".len()..ln0.len() - ") {".len()];
            let ncond = negate_str_cond(cond);
            let spaces = " ".repeat(ind0);
            lines[i] = format!("{}if ({}) {{", spaces, ncond);
            lines.remove(i + 2); // "else {"
            lines.remove(i + 1); // "}"
        // Don't increment — recheck this line in case of further nesting.
        } else {
            i += 1;
        }
    }
}

fn leading_spaces(s: &str) -> usize {
    s.len() - s.trim_start().len()
}

/// Negate a condition string syntactically:
/// - `"!expr"` / `"!(inner)"` → strip outer negation
/// - simple identifier → `"!ident"`
/// - anything else → `"!(cond)"`
fn negate_str_cond(cond: &str) -> String {
    if let Some(rest) = cond.strip_prefix('!') {
        if rest.starts_with('(') && rest.ends_with(')') {
            rest[1..rest.len() - 1].to_string()
        } else {
            rest.to_string()
        }
    } else if cond.chars().all(|c| c.is_alphanumeric() || c == '_') {
        format!("!{}", cond)
    } else {
        format!("!({})", cond)
    }
}

fn is_identifier(s: &str) -> bool {
    let mut it = s.chars();
    let Some(c0) = it.next() else {
        return false;
    };
    if !(c0 == '_' || c0.is_ascii_alphabetic()) {
        return false;
    }
    it.all(|c| c == '_' || c.is_ascii_alphanumeric())
}

#[cfg(test)]
mod semantic_optimizer_tests {
    use super::*;

    fn v(reg: i32, ver: u32) -> VarId {
        VarId { var: Var::Reg(reg), ver }
    }

    fn one_block(stmts: Vec<Stmt>) -> ExprProgram {
        ExprProgram {
            obj_index: 0,
            entry_block: 0,
            blocks: vec![super::super::expr_build::ExprBlock {
                id: 0,
                start_pc: 0,
                pred: vec![],
                succ: vec![],
                phi: vec![],
                exception_in: None,
                stmts,
                term: Terminator::Fallthrough,
            }],
        }
    }

    #[test]
    fn class_scaffold_reuses_physical_vm_slots_across_ssa_versions() {
        let fmt = make_class_scaffold_fmt_var(0, -1);
        assert_eq!(fmt(v(1, 1)), "__tjs2dec_vm_r1");
        assert_eq!(fmt(v(1, 9)), "__tjs2dec_vm_r1");
        assert_eq!(
            fmt(VarId { var: Var::Flag, ver: 1 }),
            "__tjs2dec_vm_flag"
        );
        assert_eq!(
            fmt(VarId { var: Var::Flag, ver: 7 }),
            "__tjs2dec_vm_flag"
        );
    }

    #[test]
    fn class_scaffold_is_refused_when_dynamic_eval_is_present() {
        let prog = one_block(vec![Stmt::Opaque {
            op: "VM_EVAL",
            args: vec![Expr::Str("x".into())],
            defs: vec![v(1, 1)],
        }]);
        assert!(class_initializer_has_dynamic_eval(&prog));
    }

    #[test]
    fn global_value_is_inert_for_dataflow() {
        assert!(expr_effects(&Expr::Opaque("global".into(), vec![])).erasable());
        assert!(!expr_effects(&Expr::Opaque("VM_UNKNOWN".into(), vec![])).erasable());
    }

    #[test]
    fn rhs_first_store_reconstructs_scope_property_chain() {
        let r1 = v(1, 1);
        let r2 = v(2, 1);
        let mut prog = one_block(vec![
            Stmt::Assign {
                dst: r1,
                expr: Expr::Member(Box::new(Expr::ScopeProxy), "SystemAction".into()),
            },
            Stmt::Assign {
                dst: r2,
                expr: Expr::Member(Box::new(Expr::SsaVar(r1)), "qsaveBookmarkNumber".into()),
            },
            Stmt::Store {
                target: Expr::Member(Box::new(Expr::ScopeProxy), "_dataOffset".into()),
                value: Expr::SsaVar(r2),
            },
        ]);
        let mut ret = vec![None];
        optimize_expr_program(&mut prog, &mut ret, None);

        assert_eq!(prog.blocks[0].stmts.len(), 1);
        match &prog.blocks[0].stmts[0] {
            Stmt::Store { target, value } => {
                assert_eq!(target.to_tjs(), "_dataOffset");
                assert_eq!(value.to_tjs(), "SystemAction.qsaveBookmarkNumber");
            }
            other => panic!("unexpected statement: {other:?}"),
        }
        assert!(collect_vars(&prog).is_empty());
    }

    fn block(
        id: usize,
        pred: Vec<usize>,
        succ: Vec<usize>,
        phi: Vec<super::super::ssa::Phi>,
        stmts: Vec<Stmt>,
        term: Terminator,
    ) -> super::super::expr_build::ExprBlock {
        super::super::expr_build::ExprBlock {
            id,
            start_pc: id,
            pred,
            succ,
            phi,
            exception_in: None,
            stmts,
            term,
        }
    }

    fn phi(result: VarId, args: Vec<(usize, VarId)>) -> super::super::ssa::Phi {
        super::super::ssa::Phi {
            result,
            var: result.var,
            args,
        }
    }

    #[test]
    fn folds_direct_join_phi_to_lazy_logical_or() {
        let left = v(1, 1);
        let right = v(2, 1);
        let merged = v(3, 1);
        let mut prog = ExprProgram {
            obj_index: 0,
            entry_block: 0,
            blocks: vec![
                block(
                    0,
                    vec![],
                    vec![2, 1],
                    vec![],
                    vec![Stmt::Assign {
                        dst: left,
                        expr: Expr::Member(Box::new(Expr::ScopeProxy), "left".into()),
                    }],
                    Terminator::Br {
                        cond: Expr::SsaVar(left),
                        if_true: 2,
                        if_false: 1,
                    },
                ),
                block(
                    1,
                    vec![0],
                    vec![2],
                    vec![],
                    vec![Stmt::Assign {
                        dst: right,
                        expr: Expr::Member(Box::new(Expr::ScopeProxy), "right".into()),
                    }],
                    Terminator::Jmp(2),
                ),
                block(
                    2,
                    vec![0, 1],
                    vec![],
                    vec![phi(merged, vec![(0, left), (1, right)])],
                    vec![Stmt::Store {
                        target: Expr::Member(Box::new(Expr::ScopeProxy), "value".into()),
                        value: Expr::SsaVar(merged),
                    }],
                    Terminator::Fallthrough,
                ),
            ],
        };
        let mut ret = vec![None; 3];
        optimize_expr_program(&mut prog, &mut ret, None);

        assert!(prog.blocks.iter().all(|b| b.phi.is_empty()));
        let stores = prog
            .blocks
            .iter()
            .flat_map(|b| b.stmts.iter())
            .filter_map(|st| match st {
                Stmt::Store { target, value } => Some((target, value)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(stores.len(), 1);
        assert_eq!(stores[0].0.to_tjs(), "value");
        assert_eq!(stores[0].1.to_tjs(), "left || right");
    }

    #[test]
    fn folds_closed_value_diamond_to_conditional() {
        let cond = v(1, 1);
        let tv = v(2, 1);
        let fv = v(2, 2);
        let merged = v(2, 3);
        let mut prog = ExprProgram {
            obj_index: 0,
            entry_block: 0,
            blocks: vec![
                block(
                    0,
                    vec![],
                    vec![1, 2],
                    vec![],
                    vec![Stmt::Assign {
                        dst: cond,
                        expr: Expr::Member(Box::new(Expr::ScopeProxy), "enabled".into()),
                    }],
                    Terminator::Br {
                        cond: Expr::SsaVar(cond),
                        if_true: 1,
                        if_false: 2,
                    },
                ),
                block(
                    1,
                    vec![0],
                    vec![3],
                    vec![],
                    vec![Stmt::Assign { dst: tv, expr: Expr::Int(10) }],
                    Terminator::Jmp(3),
                ),
                block(
                    2,
                    vec![0],
                    vec![3],
                    vec![],
                    vec![Stmt::Assign { dst: fv, expr: Expr::Int(20) }],
                    Terminator::Jmp(3),
                ),
                block(
                    3,
                    vec![1, 2],
                    vec![],
                    vec![phi(merged, vec![(1, tv), (2, fv)])],
                    vec![Stmt::Store {
                        target: Expr::Member(Box::new(Expr::ScopeProxy), "value".into()),
                        value: Expr::SsaVar(merged),
                    }],
                    Terminator::Fallthrough,
                ),
            ],
        };
        let mut ret = vec![None; 4];
        optimize_expr_program(&mut prog, &mut ret, None);

        assert!(prog.blocks.iter().all(|b| b.phi.is_empty()));
        let rendered = prog
            .blocks
            .iter()
            .flat_map(|b| b.stmts.iter())
            .find_map(|st| match st {
                Stmt::Store { value, .. } => Some(value.to_tjs()),
                _ => None,
            })
            .expect("store after fold");
        assert_eq!(rendered, "(enabled ? 10 : 20)");
    }

    #[test]
    fn does_not_fold_branch_across_exception_handler_boundary() {
        let cond = v(1, 1);
        let tv = v(2, 1);
        let fv = v(2, 2);
        let merged = v(2, 3);
        let mut prog = ExprProgram {
            obj_index: 0,
            entry_block: 0,
            blocks: vec![
                block(
                    0,
                    vec![],
                    vec![1, 2],
                    vec![],
                    vec![Stmt::Assign { dst: cond, expr: Expr::Bool(true) }],
                    Terminator::Br { cond: Expr::SsaVar(cond), if_true: 1, if_false: 2 },
                ),
                block(
                    1,
                    vec![0],
                    vec![3],
                    vec![],
                    vec![Stmt::Assign {
                        dst: tv,
                        expr: Expr::Member(Box::new(Expr::ScopeProxy), "mayThrow".into()),
                    }],
                    Terminator::Jmp(3),
                ),
                block(
                    2,
                    vec![0],
                    vec![3],
                    vec![],
                    vec![Stmt::Assign { dst: fv, expr: Expr::Int(0) }],
                    Terminator::Jmp(3),
                ),
                block(
                    3,
                    vec![1, 2],
                    vec![],
                    vec![phi(merged, vec![(1, tv), (2, fv)])],
                    vec![Stmt::Store {
                        target: Expr::Member(Box::new(Expr::ScopeProxy), "value".into()),
                        value: Expr::SsaVar(merged),
                    }],
                    Terminator::Fallthrough,
                ),
            ],
        };
        let mut ret = vec![None; 4];
        let handler_stacks = vec![vec![0], vec![0], vec![0], vec![]];
        optimize_expr_program(&mut prog, &mut ret, Some(&handler_stacks));

        // The may-throw property read must stay inside handler 0; sinking it to
        // bb3 would change which catch receives an exception.
        assert_eq!(prog.blocks[3].phi.len(), 1);
        assert!(matches!(prog.blocks[0].term, Terminator::Br { .. }));
    }

    #[test]
    fn does_not_fold_arm_with_unrelated_observable_statement() {
        let cond = v(1, 1);
        let tv = v(2, 1);
        let fv = v(2, 2);
        let merged = v(2, 3);
        let mut prog = ExprProgram {
            obj_index: 0,
            entry_block: 0,
            blocks: vec![
                block(
                    0,
                    vec![],
                    vec![1, 2],
                    vec![],
                    vec![Stmt::Assign { dst: cond, expr: Expr::Bool(true) }],
                    Terminator::Br { cond: Expr::SsaVar(cond), if_true: 1, if_false: 2 },
                ),
                block(
                    1,
                    vec![0],
                    vec![3],
                    vec![],
                    vec![
                        Stmt::Expr(Expr::Call(
                            Box::new(Expr::Member(Box::new(Expr::ScopeProxy), "sideEffect".into())),
                            vec![],
                        )),
                        Stmt::Assign { dst: tv, expr: Expr::Int(1) },
                    ],
                    Terminator::Jmp(3),
                ),
                block(
                    2,
                    vec![0],
                    vec![3],
                    vec![],
                    vec![Stmt::Assign { dst: fv, expr: Expr::Int(0) }],
                    Terminator::Jmp(3),
                ),
                block(
                    3,
                    vec![1, 2],
                    vec![],
                    vec![phi(merged, vec![(1, tv), (2, fv)])],
                    vec![Stmt::Store {
                        target: Expr::Member(Box::new(Expr::ScopeProxy), "value".into()),
                        value: Expr::SsaVar(merged),
                    }],
                    Terminator::Fallthrough,
                ),
            ],
        };
        let mut ret = vec![None; 4];
        optimize_expr_program(&mut prog, &mut ret, None);

        assert_eq!(prog.blocks[3].phi.len(), 1);
        assert!(prog.blocks[1].stmts.iter().any(|st| matches!(st, Stmt::Expr(Expr::Call(..)))));
    }

    #[test]
    fn folds_shared_failure_ladder_without_eager_predicates() {
        let c1 = v(1, 1);
        let c2 = v(2, 1);
        let sv = v(3, 1);
        let fv = v(3, 2);
        let merged = v(3, 3);
        let mut prog = ExprProgram {
            obj_index: 0,
            entry_block: 0,
            blocks: vec![
                block(
                    0,
                    vec![],
                    vec![1, 3],
                    vec![],
                    vec![Stmt::Assign {
                        dst: c1,
                        expr: Expr::Member(Box::new(Expr::ScopeProxy), "first".into()),
                    }],
                    Terminator::Br {
                        cond: Expr::SsaVar(c1),
                        if_true: 1,
                        if_false: 3,
                    },
                ),
                block(
                    1,
                    vec![0],
                    vec![2, 3],
                    vec![],
                    vec![Stmt::Assign {
                        dst: c2,
                        expr: Expr::Member(Box::new(Expr::ScopeProxy), "second".into()),
                    }],
                    Terminator::Br {
                        cond: Expr::SsaVar(c2),
                        if_true: 2,
                        if_false: 3,
                    },
                ),
                block(
                    2,
                    vec![1],
                    vec![4],
                    vec![],
                    vec![Stmt::Assign { dst: sv, expr: Expr::Int(1) }],
                    Terminator::Jmp(4),
                ),
                block(
                    3,
                    vec![0, 1],
                    vec![4],
                    vec![],
                    vec![Stmt::Assign { dst: fv, expr: Expr::Int(0) }],
                    Terminator::Jmp(4),
                ),
                block(
                    4,
                    vec![2, 3],
                    vec![],
                    vec![phi(merged, vec![(2, sv), (3, fv)])],
                    vec![Stmt::Store {
                        target: Expr::Member(Box::new(Expr::ScopeProxy), "value".into()),
                        value: Expr::SsaVar(merged),
                    }],
                    Terminator::Fallthrough,
                ),
            ],
        };
        let mut ret = vec![None; 5];
        optimize_expr_program(&mut prog, &mut ret, None);

        assert!(prog.blocks.iter().all(|b| b.phi.is_empty()));
        let rendered = prog
            .blocks
            .iter()
            .flat_map(|b| b.stmts.iter())
            .find_map(|st| match st {
                Stmt::Store { value, .. } => Some(value.to_tjs()),
                _ => None,
            })
            .expect("store after fold");
        assert_eq!(rendered, "(first && second ? 1 : 0)");
    }

    #[test]
    fn folds_real_class_style_diamond_with_prefix_side_effect_and_dead_phi() {
        let cond_base = v(1, 1);
        let cond = v(2, 1);
        let tbase = v(3, 1);
        let tv = v(4, 1);
        let fv_base = v(3, 2);
        let fv = v(4, 2);
        let dead = v(3, 3);
        let merged = v(4, 3);
        let mut prog = ExprProgram {
            obj_index: 0,
            entry_block: 0,
            blocks: vec![
                block(
                    0,
                    vec![],
                    vec![1, 2],
                    vec![],
                    vec![
                        // This is an earlier class-member initializer.  It is
                        // observable but independent of the later branch and
                        // therefore must remain in place, not block suffix
                        // extraction and not be absorbed into the conditional.
                        Stmt::Store {
                            target: Expr::Member(Box::new(Expr::ScopeProxy), "prefix".into()),
                            value: Expr::Int(1),
                        },
                        Stmt::Assign {
                            dst: cond_base,
                            expr: Expr::Member(Box::new(Expr::ScopeProxy), "settings".into()),
                        },
                        Stmt::Assign {
                            dst: cond,
                            expr: Expr::Member(Box::new(Expr::SsaVar(cond_base)), "enabled".into()),
                        },
                    ],
                    Terminator::Br {
                        cond: Expr::SsaVar(cond),
                        if_true: 1,
                        if_false: 2,
                    },
                ),
                block(
                    1,
                    vec![0],
                    vec![3],
                    vec![],
                    vec![
                        Stmt::Assign {
                            dst: tbase,
                            expr: Expr::Member(Box::new(Expr::ScopeProxy), "source".into()),
                        },
                        Stmt::Assign {
                            dst: tv,
                            expr: Expr::Member(Box::new(Expr::SsaVar(tbase)), "value".into()),
                        },
                    ],
                    Terminator::Jmp(3),
                ),
                block(
                    2,
                    vec![0],
                    vec![3],
                    vec![],
                    vec![
                        Stmt::Assign { dst: fv_base, expr: Expr::Int(0) },
                        Stmt::Assign { dst: fv, expr: Expr::SsaVar(fv_base) },
                    ],
                    Terminator::Jmp(3),
                ),
                block(
                    3,
                    vec![1, 2],
                    vec![],
                    vec![
                        phi(dead, vec![(1, tbase), (2, fv_base)]),
                        phi(merged, vec![(1, tv), (2, fv)]),
                    ],
                    vec![Stmt::Store {
                        target: Expr::Member(Box::new(Expr::ScopeProxy), "result".into()),
                        value: Expr::SsaVar(merged),
                    }],
                    Terminator::Fallthrough,
                ),
            ],
        };
        let mut ret = vec![None; 4];
        optimize_expr_program(&mut prog, &mut ret, None);

        assert!(prog.blocks.iter().all(|b| b.phi.is_empty()));
        let stores = prog
            .blocks
            .iter()
            .flat_map(|b| b.stmts.iter())
            .filter_map(|st| match st {
                Stmt::Store { target, value } => Some((target.to_tjs(), value.to_tjs())),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(stores.len(), 2);
        assert_eq!(stores[0], ("prefix".into(), "1".into()));
        assert_eq!(stores[1].0, "result");
        assert_eq!(stores[1].1, "(settings.enabled ? source.value : 0)");
    }

    #[test]
    fn folds_shared_failure_ladder_with_collateral_dead_phis() {
        let c1 = v(1, 1);
        let c2 = v(2, 1);
        let success = v(11, 1);
        let failure = v(11, 2);
        let merged = v(11, 3);
        let dead_a = v(4, 1);
        let dead_b = v(4, 2);
        let dead_join = v(4, 3);
        let mut prog = ExprProgram {
            obj_index: 0,
            entry_block: 0,
            blocks: vec![
                block(
                    0,
                    vec![],
                    vec![1, 3],
                    vec![],
                    vec![
                        Stmt::Store {
                            target: Expr::Member(Box::new(Expr::ScopeProxy), "prefix".into()),
                            value: Expr::Int(1),
                        },
                        Stmt::Assign {
                            dst: c1,
                            expr: Expr::Member(Box::new(Expr::ScopeProxy), "first".into()),
                        },
                    ],
                    Terminator::Br { cond: Expr::SsaVar(c1), if_true: 1, if_false: 3 },
                ),
                block(
                    1,
                    vec![0],
                    vec![2, 3],
                    vec![],
                    vec![Stmt::Assign {
                        dst: c2,
                        expr: Expr::Member(Box::new(Expr::ScopeProxy), "second".into()),
                    }],
                    Terminator::Br { cond: Expr::SsaVar(c2), if_true: 2, if_false: 3 },
                ),
                block(
                    2,
                    vec![1],
                    vec![4],
                    vec![],
                    vec![
                        Stmt::Assign { dst: dead_a, expr: Expr::Int(99) },
                        Stmt::Assign {
                            dst: success,
                            expr: Expr::New(
                                Box::new(Expr::Member(Box::new(Expr::ScopeProxy), "Rect".into())),
                                vec![],
                            ),
                        },
                    ],
                    Terminator::Jmp(4),
                ),
                block(
                    3,
                    vec![0, 1],
                    vec![4],
                    vec![],
                    vec![
                        Stmt::Assign { dst: dead_b, expr: Expr::Int(0) },
                        Stmt::Assign { dst: failure, expr: Expr::Void },
                    ],
                    Terminator::Jmp(4),
                ),
                block(
                    4,
                    vec![2, 3],
                    vec![],
                    vec![
                        phi(dead_join, vec![(2, dead_a), (3, dead_b)]),
                        phi(merged, vec![(2, success), (3, failure)]),
                    ],
                    vec![Stmt::Store {
                        target: Expr::Member(Box::new(Expr::ScopeProxy), "rect".into()),
                        value: Expr::SsaVar(merged),
                    }],
                    Terminator::Fallthrough,
                ),
            ],
        };
        let mut ret = vec![None; 5];
        optimize_expr_program(&mut prog, &mut ret, None);

        assert!(prog.blocks.iter().all(|b| b.phi.is_empty()));
        let rendered = prog
            .blocks
            .iter()
            .flat_map(|b| b.stmts.iter())
            .find_map(|st| match st {
                Stmt::Store { target, value } if target.to_tjs() == "rect" => Some(value.to_tjs()),
                _ => None,
            })
            .expect("rect store after fold");
        assert_eq!(rendered, "(first && second ? new Rect() : void)");
    }

    #[test]
    fn reconstructs_exact_regexp_compiler_template() {
        let builder = v(1, 1);
        let mut prog = one_block(vec![
            Stmt::Assign {
                dst: builder,
                expr: Expr::New(
                    Box::new(Expr::Member(
                        Box::new(Expr::Opaque("global".into(), vec![])),
                        "RegExp".into(),
                    )),
                    vec![],
                ),
            },
            Stmt::Expr(Expr::MethodCall {
                base: Box::new(Expr::SsaVar(builder)),
                member: "_compile".into(),
                args: vec![Expr::Str(r"//g/(\\n|\n)".into())],
            }),
            Stmt::MemberDecl {
                name: "_cutLF".into(),
                value: Expr::SsaVar(builder),
            },
        ]);
        let mut ret = vec![None];
        optimize_expr_program(&mut prog, &mut ret, None);

        assert_eq!(prog.blocks[0].stmts.len(), 1);
        match &prog.blocks[0].stmts[0] {
            Stmt::MemberDecl { name, value } => {
                assert_eq!(name, "_cutLF");
                assert_eq!(value.to_tjs(), r"/(\\n|\n)/g");
            }
            other => panic!("unexpected statement: {other:?}"),
        }
    }

    #[test]
    fn folds_shared_observable_value_into_rhs_first_assignment_chain() {
        let tmp = v(2, 1);
        let mut prog = one_block(vec![
            Stmt::Assign {
                dst: tmp,
                expr: Expr::Member(
                    Box::new(Expr::Member(Box::new(Expr::ScopeProxy), "SystemConfig".into())),
                    "voiceClipPopupTextMap".into(),
                ),
            },
            Stmt::Store {
                target: Expr::Member(Box::new(Expr::ScopeProxy), "_detailTextMap".into()),
                value: Expr::SsaVar(tmp),
            },
            Stmt::Store {
                target: Expr::Member(Box::new(Expr::ScopeProxy), "_genericDrawTextMap".into()),
                value: Expr::SsaVar(tmp),
            },
        ]);
        let mut ret = vec![None];
        optimize_expr_program(&mut prog, &mut ret, None);

        assert_eq!(prog.blocks[0].stmts.len(), 1);
        match &prog.blocks[0].stmts[0] {
            Stmt::Store { target, value } => {
                assert_eq!(target.to_tjs(), "_genericDrawTextMap");
                assert_eq!(
                    value.to_tjs(),
                    "_detailTextMap = SystemConfig.voiceClipPopupTextMap"
                );
            }
            other => panic!("unexpected statement: {other:?}"),
        }
        assert!(collect_vars(&prog).is_empty());
    }

    #[test]
    fn folds_nested_dictionary_when_inner_terminal_is_outer_spis() {
        let outer = v(1, 1);
        let inner = v(2, 1);
        let dict_ctor = || {
            Expr::Member(
                Box::new(Expr::Opaque("global".into(), vec![])),
                "Dictionary".into(),
            )
        };
        let spis = |builder: VarId, key: &str, value: Expr| Stmt::Store {
            target: Expr::Unary(
                UnOp::IgnoreProp,
                Box::new(Expr::Index(
                    Box::new(Expr::SsaVar(builder)),
                    Box::new(Expr::Str(key.into())),
                )),
            ),
            value,
        };
        let mut prog = one_block(vec![
            Stmt::Assign {
                dst: outer,
                expr: Expr::New(Box::new(dict_ctor()), vec![]),
            },
            Stmt::Assign {
                dst: inner,
                expr: Expr::New(Box::new(dict_ctor()), vec![]),
            },
            spis(inner, "a", Expr::Int(1)),
            // This is the inner builder's terminal use. It is also a Store on
            // the outer builder and used to be rejected before terminal-use
            // detection, breaking every nested Dictionary fixed point.
            spis(outer, "foo", Expr::SsaVar(inner)),
            Stmt::MemberDecl {
                name: "items".into(),
                value: Expr::SsaVar(outer),
            },
        ]);
        let mut ret = vec![None];
        optimize_expr_program(&mut prog, &mut ret, None);

        assert_eq!(prog.blocks[0].stmts.len(), 1);
        match &prog.blocks[0].stmts[0] {
            Stmt::MemberDecl { name, value } => {
                assert_eq!(name, "items");
                assert_eq!(value.to_tjs(), "%[\"foo\" => %[\"a\" => 1]]");
            }
            other => panic!("unexpected statement: {other:?}"),
        }
        assert!(collect_vars(&prog).is_empty());
    }

    #[test]
    fn folds_dictionary_builder_with_effectful_key_then_value_producers() {
        let builder = v(1, 1);
        let key = v(2, 1);
        let value = v(5, 1);
        let dict_ctor = Expr::Member(
            Box::new(Expr::Opaque("global".into(), vec![])),
            "Dictionary".into(),
        );
        let mut prog = one_block(vec![
            Stmt::Assign {
                dst: builder,
                expr: Expr::New(Box::new(dict_ctor), vec![]),
            },
            // Scope-proxy member lookup is observable and must remain before
            // the value call when reconstructed as `%[key => value]`.
            Stmt::Assign {
                dst: key,
                expr: Expr::Member(Box::new(Expr::ScopeProxy), "IDOK".into()),
            },
            Stmt::Assign {
                dst: value,
                expr: Expr::Call(
                    Box::new(Expr::Member(
                        Box::new(Expr::ScopeProxy),
                        "GetSystemLangMessage".into(),
                    )),
                    vec![Expr::Str("DialogOK".into()), Expr::Str("決定".into())],
                ),
            },
            Stmt::Store {
                target: Expr::Unary(
                    UnOp::IgnoreProp,
                    Box::new(Expr::Index(
                        Box::new(Expr::SsaVar(builder)),
                        Box::new(Expr::SsaVar(key)),
                    )),
                ),
                value: Expr::SsaVar(value),
            },
            Stmt::MemberDecl {
                name: "_itemTexts".into(),
                value: Expr::SsaVar(builder),
            },
        ]);
        let mut ret = vec![None];
        optimize_expr_program(&mut prog, &mut ret, None);

        assert_eq!(prog.blocks[0].stmts.len(), 1);
        match &prog.blocks[0].stmts[0] {
            Stmt::MemberDecl { name, value } => {
                assert_eq!(name, "_itemTexts");
                assert_eq!(
                    value.to_tjs(),
                    "%[IDOK => GetSystemLangMessage(\"DialogOK\", \"決定\")]"
                );
            }
            other => panic!("unexpected statement: {other:?}"),
        }
    }

    #[test]
    fn does_not_fold_dictionary_when_value_effect_precedes_key_effect() {
        let builder = v(1, 1);
        let key = v(2, 1);
        let value = v(5, 1);
        let dict_ctor = Expr::Member(
            Box::new(Expr::Opaque("global".into(), vec![])),
            "Dictionary".into(),
        );
        let mut prog = one_block(vec![
            Stmt::Assign {
                dst: builder,
                expr: Expr::New(Box::new(dict_ctor), vec![]),
            },
            // This order cannot come from a normal `%[key => value]` literal:
            // folding would reorder the two observable operations.
            Stmt::Assign {
                dst: value,
                expr: Expr::Call(
                    Box::new(Expr::Member(Box::new(Expr::ScopeProxy), "valueFn".into())),
                    vec![],
                ),
            },
            Stmt::Assign {
                dst: key,
                expr: Expr::Member(Box::new(Expr::ScopeProxy), "keyProp".into()),
            },
            Stmt::Store {
                target: Expr::Unary(
                    UnOp::IgnoreProp,
                    Box::new(Expr::Index(
                        Box::new(Expr::SsaVar(builder)),
                        Box::new(Expr::SsaVar(key)),
                    )),
                ),
                value: Expr::SsaVar(value),
            },
            Stmt::MemberDecl {
                name: "items".into(),
                value: Expr::SsaVar(builder),
            },
        ]);
        fold_inline_collection_builders(&mut prog);

        assert!(prog.blocks[0].stmts.len() > 1);
        assert!(matches!(prog.blocks[0].stmts[0], Stmt::Assign { .. }));
    }

    #[test]
    fn folds_empty_array_and_removes_index_scaffold() {
        let builder = v(1, 1);
        let idx0 = v(2, 1);
        let array_ctor = Expr::Member(
            Box::new(Expr::Opaque("global".into(), vec![])),
            "Array".into(),
        );
        let mut prog = one_block(vec![
            Stmt::Assign {
                dst: builder,
                expr: Expr::New(Box::new(array_ctor), vec![]),
            },
            Stmt::Assign { dst: idx0, expr: Expr::Int(0) },
            Stmt::MemberDecl {
                name: "items".into(),
                value: Expr::SsaVar(builder),
            },
        ]);
        let mut ret = vec![None];
        optimize_expr_program(&mut prog, &mut ret, None);

        assert_eq!(prog.blocks[0].stmts.len(), 1);
        match &prog.blocks[0].stmts[0] {
            Stmt::MemberDecl { value, .. } => assert_eq!(value.to_tjs(), "[]"),
            other => panic!("unexpected statement: {other:?}"),
        }
    }

    #[test]
    fn folds_only_ignoreprop_collection_builder_template() {
        let builder = v(1, 1);
        let idx0 = v(2, 1);
        let idx1 = v(2, 2);
        let array_ctor = Expr::Member(
            Box::new(Expr::Opaque("global".into(), vec![])),
            "Array".into(),
        );
        let spis = |index: Expr, value: Expr| Stmt::Store {
            target: Expr::Unary(
                UnOp::IgnoreProp,
                Box::new(Expr::Index(Box::new(Expr::SsaVar(builder)), Box::new(index))),
            ),
            value,
        };
        let mut prog = one_block(vec![
            Stmt::Assign {
                dst: builder,
                expr: Expr::New(Box::new(array_ctor), vec![]),
            },
            Stmt::Assign { dst: idx0, expr: Expr::Int(0) },
            spis(Expr::SsaVar(idx0), Expr::Str("a".into())),
            Stmt::Assign {
                dst: idx1,
                expr: Expr::Binary(
                    BinOp::Add,
                    Box::new(Expr::SsaVar(idx0)),
                    Box::new(Expr::Int(1)),
                ),
            },
            spis(Expr::SsaVar(idx1), Expr::Str("b".into())),
            Stmt::Store {
                target: Expr::Member(Box::new(Expr::ScopeProxy), "items".into()),
                value: Expr::SsaVar(builder),
            },
        ]);
        let mut ret = vec![None];
        optimize_expr_program(&mut prog, &mut ret, None);

        assert_eq!(prog.blocks[0].stmts.len(), 1);
        match &prog.blocks[0].stmts[0] {
            Stmt::Store { target, value } => {
                assert_eq!(target.to_tjs(), "items");
                assert_eq!(value.to_tjs(), "[\"a\", \"b\"]");
            }
            other => panic!("unexpected statement: {other:?}"),
        }
    }
}
