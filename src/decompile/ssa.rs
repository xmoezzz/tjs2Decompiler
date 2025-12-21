use std::collections::{BTreeSet, HashMap, HashSet};

use anyhow::Result;

use crate::vmcodes::vm;

use super::cfg::{BasicBlock, Cfg};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Var {
    Reg(i32),
    Flag,
    Exception,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId {
    pub var: Var,
    pub ver: u32,
}

#[derive(Debug, Clone)]
pub struct Phi {
    pub result: VarId,
    pub var: Var,
    pub args: Vec<(usize, VarId)>, // (pred_block_id, value)
}

#[derive(Debug, Clone)]
pub struct SsaInsn {
    pub pc: usize,
    pub op: i32,
    pub mnemonic: &'static str,
    pub raw_ops: Vec<i32>,
    pub uses: Vec<VarId>,
    pub defs: Vec<VarId>,
}

#[derive(Debug, Clone)]
pub struct SsaBlock {
    pub id: usize,
    pub start_pc: usize,
    pub pred: Vec<usize>,
    pub succ: Vec<usize>,
    pub phi: Vec<Phi>,
    pub insns: Vec<SsaInsn>,
}

#[derive(Debug, Clone)]
pub struct SsaProgram {
    pub obj_index: usize,
    pub blocks: Vec<SsaBlock>,
    pub entry_block: usize,
}

impl SsaProgram {
    pub fn from_cfg(cfg: &Cfg) -> Result<Self> {
        let dom = DomInfo::compute(&cfg.blocks, cfg.entry_block);
        let mut phi_sites = place_phi(&cfg.blocks, &dom);
        let mut ssa_blocks = cfg
            .blocks
            .iter()
            .map(|b| SsaBlock {
                id: b.id,
                start_pc: b.start_pc,
                pred: b.pred.clone(),
                succ: b.succ.clone(),
                phi: Vec::new(),
                insns: Vec::new(),
            })
            .collect::<Vec<_>>();

        // Materialize phi nodes.
        for (bid, vars) in phi_sites.drain() {
            for v in vars {
                ssa_blocks[bid].phi.push(Phi {
                    result: VarId { var: v, ver: 0 }, // filled during renaming
                    var: v,
                    args: Vec::new(),
                });
            }
            ssa_blocks[bid].phi.sort_by_key(|p| p.var);
        }

        rename(cfg, &dom, &mut ssa_blocks);
        Ok(Self {
            obj_index: cfg.obj_index,
            blocks: ssa_blocks,
            entry_block: cfg.entry_block,
        })
    }

    pub fn dump(&self) -> String {
        let mut out = String::new();
        for b in &self.blocks {
            out.push_str(&format!("-- bb{} @{} (pred={:?}, succ={:?})\n", b.id, b.start_pc, b.pred, b.succ));
            for p in &b.phi {
                out.push_str(&format!("  {} = phi {}", fmt_varid(p.result), fmt_var(p.var)));
                if !p.args.is_empty() {
                    out.push_str(" [");
                    for (i, (pred, v)) in p.args.iter().enumerate() {
                        if i != 0 {
                            out.push_str(", ");
                        }
                        out.push_str(&format!("bb{}: {}", pred, fmt_varid(*v)));
                    }
                    out.push(']');
                }
                out.push('\n');
            }
            for insn in &b.insns {
                out.push_str(&format!("  {:04} {}", insn.pc, insn.mnemonic));
                if !insn.raw_ops.is_empty() {
                    out.push(' ');
                    for (i, w) in insn.raw_ops.iter().enumerate() {
                        if i != 0 {
                            out.push_str(", ");
                        }
                        out.push_str(&format!("{}", w));
                    }
                }
                if !insn.defs.is_empty() {
                    out.push_str("\t; def=");
                    for (i, d) in insn.defs.iter().enumerate() {
                        if i != 0 {
                            out.push_str(",");
                        }
                        out.push_str(&fmt_varid(*d));
                    }
                }
                if !insn.uses.is_empty() {
                    out.push_str("\t; use=");
                    for (i, u) in insn.uses.iter().enumerate() {
                        if i != 0 {
                            out.push_str(",");
                        }
                        out.push_str(&fmt_varid(*u));
                    }
                }
                out.push('\n');
            }
        }
        out
    }
}

fn fmt_var(v: Var) -> &'static str {
    match v {
        Var::Reg(_) => "reg",
        Var::Flag => "flag",
        Var::Exception => "exception",
    }
}

fn fmt_varid(id: VarId) -> String {
    match id.var {
        Var::Reg(r) => format!("r{}#{}", r, id.ver),
        Var::Flag => format!("flag#{}", id.ver),
        Var::Exception => format!("exc#{}", id.ver),
    }
}

#[derive(Debug, Clone)]
struct DomInfo {
    idom: Vec<usize>,
    children: Vec<Vec<usize>>,
    df: Vec<HashSet<usize>>,
}

impl DomInfo {
    fn compute(blocks: &[BasicBlock], entry: usize) -> Self {
        let n = blocks.len();
        let mut dom: Vec<HashSet<usize>> = vec![HashSet::new(); n];
        for i in 0..n {
            if i == entry {
                dom[i].insert(i);
            } else {
                dom[i] = (0..n).collect();
            }
        }

        let mut changed = true;
        while changed {
            changed = false;
            for b in 0..n {
                if b == entry {
                    continue;
                }
                let preds = &blocks[b].pred;
                if preds.is_empty() {
                    continue;
                }
                let mut new_dom = dom[preds[0]].clone();
                for &p in &preds[1..] {
                    new_dom = new_dom
                        .intersection(&dom[p])
                        .copied()
                        .collect::<HashSet<_>>();
                }
                new_dom.insert(b);
                if new_dom != dom[b] {
                    dom[b] = new_dom;
                    changed = true;
                }
            }
        }

        // idom: pick the strict dominator with the largest dominator set (closest to b).
        let mut idom = vec![entry; n];
        for b in 0..n {
            if b == entry {
                idom[b] = entry;
                continue;
            }
            let mut best = entry;
            let mut best_len = 0usize;
            for &c in dom[b].iter() {
                if c == b {
                    continue;
                }
                let l = dom[c].len();
                if l > best_len {
                    best = c;
                    best_len = l;
                }
            }
            idom[b] = best;
        }

        // children
        let mut children = vec![Vec::new(); n];
        for b in 0..n {
            if b == entry {
                continue;
            }
            children[idom[b]].push(b);
        }

        // dominance frontier
        let mut df: Vec<HashSet<usize>> = vec![HashSet::new(); n];
        for b in 0..n {
            for &s in &blocks[b].succ {
                if idom[s] != b {
                    df[b].insert(s);
                }
            }
        }
        // postorder traversal over dom tree
        let mut order = Vec::new();
        fn post(u: usize, ch: &[Vec<usize>], out: &mut Vec<usize>) {
            for &v in &ch[u] {
                post(v, ch, out);
            }
            out.push(u);
        }
        post(entry, &children, &mut order);
        for &b in &order {
            for &c in &children[b] {
                let cdf: Vec<usize> = df[c].iter().copied().collect();
                for w in cdf {
                    if idom[w] != b {
                        df[b].insert(w);
                    }
                }
            }
        }

        Self { idom, children, df }
    }
}

fn collect_vars(blocks: &[BasicBlock]) -> BTreeSet<Var> {
    let mut vars = BTreeSet::new();
    vars.insert(Var::Flag);

    for b in blocks {
        for insn in &b.insns {
            let (defs, uses) = effects_of(insn.op, insn.words.as_slice());
            for r in defs {
                vars.insert(r);
            }
            for r in uses {
                vars.insert(r);
            }
        }
    }
    vars
}

fn place_phi(blocks: &[BasicBlock], dom: &DomInfo) -> HashMap<usize, BTreeSet<Var>> {
    let vars = collect_vars(blocks);
    let mut def_sites: HashMap<Var, HashSet<usize>> = HashMap::new();
    for v in vars.iter().copied() {
        def_sites.insert(v, HashSet::new());
    }
    for b in blocks {
        for insn in &b.insns {
            let (defs, _uses) = effects_of(insn.op, insn.words.as_slice());
            for v in defs {
                def_sites.entry(v).or_default().insert(b.id);
            }
        }
    }

    let mut phi: HashMap<usize, BTreeSet<Var>> = HashMap::new();
    for (v, defs) in def_sites {
        let mut work: Vec<usize> = defs.iter().copied().collect();
        let mut has_phi: HashSet<usize> = HashSet::new();
        while let Some(n) = work.pop() {
            for &y in &dom.df[n] {
                if !has_phi.contains(&y) {
                    has_phi.insert(y);
                    phi.entry(y).or_default().insert(v);
                    if !defs.contains(&y) {
                        work.push(y);
                    }
                }
            }
        }
    }
    phi
}

fn rename(cfg: &Cfg, dom: &DomInfo, blocks: &mut [SsaBlock]) {
    let mut counters: HashMap<Var, u32> = HashMap::new();
    let mut stacks: HashMap<Var, Vec<VarId>> = HashMap::new();

    // Initialize with version 0 for each observed variable; this avoids special-casing
    // "use before def" (it becomes rX#0).
    for b in &cfg.blocks {
        for insn in &b.insns {
            let (defs, uses) = effects_of(insn.op, insn.words.as_slice());
            for v in defs.into_iter().chain(uses.into_iter()) {
                counters.entry(v).or_insert(0);
                stacks.entry(v).or_default();
            }
        }
    }
    counters.entry(Var::Flag).or_insert(0);
    stacks.entry(Var::Flag).or_default();
    // Exception is a pseudo source; version 0 is fine.
    counters.entry(Var::Exception).or_insert(0);
    stacks.entry(Var::Exception).or_default();

    for (&v, st) in stacks.iter_mut() {
        st.push(VarId { var: v, ver: 0 });
    }

    fn new_ver(v: Var, counters: &mut HashMap<Var, u32>, stacks: &mut HashMap<Var, Vec<VarId>>) -> VarId {
        let c = counters.entry(v).or_insert(0);
        *c += 1;
        let id = VarId { var: v, ver: *c };
        stacks.entry(v).or_default().push(id);
        id
    }

    fn cur(v: Var, stacks: &HashMap<Var, Vec<VarId>>) -> VarId {
        stacks.get(&v).and_then(|s| s.last().copied()).unwrap_or(VarId { var: v, ver: 0 })
    }

    fn dfs(
        bid: usize,
        cfg: &Cfg,
        dom: &DomInfo,
        blocks: &mut [SsaBlock],
        counters: &mut HashMap<Var, u32>,
        stacks: &mut HashMap<Var, Vec<VarId>>,
    ) {
        let mut pushed: Vec<Var> = Vec::new();

        // Rename phi results.
        for p in blocks[bid].phi.iter_mut() {
            let id = new_ver(p.var, counters, stacks);
            p.result = id;
            pushed.push(p.var);
        }

        // Insert a pseudo "exception store" at catch entries: rEx = exc.
        if let Some(&ex_reg) = cfg.catch_sites.get(&blocks[bid].start_pc) {
            let dst = Var::Reg(ex_reg);
            let src = Var::Exception;
            let dst_id = new_ver(dst, counters, stacks);
            pushed.push(dst);
            let src_id = cur(src, stacks);
            blocks[bid].insns.push(SsaInsn {
                pc: blocks[bid].start_pc,
                op: -1,
                mnemonic: "EXCDEF",
                raw_ops: vec![ex_reg],
                uses: vec![src_id],
                defs: vec![dst_id],
            });
        }

        // Rename normal instructions.
        for insn in &cfg.blocks[bid].insns {
            let (defs, uses) = effects_of(insn.op, insn.words.as_slice());
            let mut use_ids = Vec::new();
            for v in uses {
                use_ids.push(cur(v, stacks));
            }

            let mut def_ids = Vec::new();
            for v in defs {
                let id = new_ver(v, counters, stacks);
                def_ids.push(id);
                pushed.push(v);
            }

            blocks[bid].insns.push(SsaInsn {
                pc: insn.pc,
                op: insn.op,
                mnemonic: insn.mnemonic(),
                raw_ops: insn.operands().to_vec(),
                uses: use_ids,
                defs: def_ids,
            });
        }

        // Populate phi arguments for successors.
        let end_state: HashMap<Var, VarId> = stacks.iter().map(|(&v, s)| (v, *s.last().unwrap())).collect();
        for &succ in blocks[bid].succ.iter() {
            for p in blocks[succ].phi.iter_mut() {
                let val = *end_state.get(&p.var).unwrap_or(&VarId { var: p.var, ver: 0 });
                p.args.push((bid, val));
            }
        }

        // Recurse.
        for &c in &dom.children[bid] {
            dfs(c, cfg, dom, blocks, counters, stacks);
        }

        // Pop everything we pushed in this block.
        for v in pushed.into_iter().rev() {
            if let Some(st) = stacks.get_mut(&v) {
                let _ = st.pop();
            }
        }
    }

    dfs(cfg.entry_block, cfg, dom, blocks, &mut counters, &mut stacks);
}

fn effects_of(op: i32, words: &[i32]) -> (Vec<Var>, Vec<Var>) {
    // Return (defs, uses). Conservatively treats most arithmetic as read-modify-write.
    // This function is the single place to refine semantics as we progress.
    if words.is_empty() {
        return (Vec::new(), Vec::new());
    }
    let ops = &words[1..];

    // Helpers
    let r = |i: usize| -> Var { Var::Reg(ops.get(i).copied().unwrap_or(0)) };
    let def_r0 = |reg: i32| -> Vec<Var> {
        if reg == 0 {
            Vec::new()
        } else {
            vec![Var::Reg(reg)]
        }
    };

    // Opcodes that define/consume the flag.
    // Note: SETF/SETNF are constant-set-to-register, not flag operations.
    if matches!(op, vm::VM_CEQ | vm::VM_CDEQ | vm::VM_CLT | vm::VM_CGT | vm::VM_CHKINS | vm::VM_TT | vm::VM_TF | vm::VM_NF){
        let mut uses = Vec::new();
        match op {
            x if x == vm::VM_TT || x == vm::VM_TF => {
                uses.push(r(0));
            }
            x if x == vm::VM_CEQ || x == vm::VM_CDEQ || x == vm::VM_CLT || x == vm::VM_CGT || x == vm::VM_CHKINS => {
                uses.push(r(0));
                uses.push(r(1));
            }
            x if x == vm::VM_NF => {
                uses.push(Var::Flag);
            }
            _ => {}
        }
        let defs = vec![Var::Flag];
        return (defs, uses);
    }

    // Branch uses flag.
    if op == vm::VM_JF || op == vm::VM_JNF {
        return (Vec::new(), vec![Var::Flag]);
    }

    // SETF/SETNF: dst := true/false (does NOT define Flag)
    if op == vm::VM_SETF || op == vm::VM_SETNF {
        let dst = ops.get(0).copied().unwrap_or(0);
        return (vec![Var::Reg(dst)], Vec::new());
    }

    // CONST: dst := data[*]
    if op == vm::VM_CONST {
        let dst = ops.get(0).copied().unwrap_or(0);
        return (def_r0(dst), Vec::new());
    }

    // CP: dst := src
    if op == vm::VM_CP {
        let dst = ops.get(0).copied().unwrap_or(0);
        let src = ops.get(1).copied().unwrap_or(0);
        return (def_r0(dst), vec![Var::Reg(src)]);
    }

    // CL: dst := void
    if op == vm::VM_CL {
        let dst = ops.get(0).copied().unwrap_or(0);
        return (def_r0(dst), Vec::new());
    }

    // CCL: cl %r0-%rN
    if op == vm::VM_CCL {
        let r0 = ops.get(0).copied().unwrap_or(0);
        let cnt = ops.get(1).copied().unwrap_or(0);
        let mut defs = Vec::new();
        for k in 0..cnt {
            let rr = r0 + k;
            if rr != 0 {
                defs.push(Var::Reg(rr));
            }
        }
        return (defs, Vec::new());
    }

    // Global: dst := GlobalObject
    if op == vm::VM_GLOBAL {
        let dst = ops.get(0).copied().unwrap_or(0);
        return (def_r0(dst), Vec::new());
    }

    // SRV: set return value (uses r)
    if op == vm::VM_SRV {
        return (Vec::new(), vec![r(0)]);
    }

    // RET / NOP / REGMEMBER / DEBUGGER / EXTRY / ENTRY: no register effects here.
    if matches!(op, vm::VM_RET | vm::VM_NOP | vm::VM_REGMEMBER | vm::VM_DEBUGGER | vm::VM_EXTRY | vm::VM_ENTRY) {
        return (Vec::new(), Vec::new());
    }

    // THROW reads operand.
    if op == vm::VM_THROW {
        return (Vec::new(), vec![r(0)]);
    }

    // SETP/GETP (property accessor register binding) uses regs.
    if op == vm::VM_SETP {
        // setp %obj, %prop
        return (Vec::new(), vec![r(0), r(1)]);
    }
    if op == vm::VM_GETP {
        // getp %dst, %prop
        let dst = ops.get(0).copied().unwrap_or(0);
        return (def_r0(dst), vec![r(1)]);
    }

    // GPD/GPDS: dst := obj[member_data]
    if op == vm::VM_GPD || op == vm::VM_GPDS {
        let dst = ops.get(0).copied().unwrap_or(0);
        let obj = ops.get(1).copied().unwrap_or(0);
        return (def_r0(dst), vec![Var::Reg(obj)]);
    }
    // GPI/GPIS: dst := obj[member_reg]
    if op == vm::VM_GPI || op == vm::VM_GPIS {
        let dst = ops.get(0).copied().unwrap_or(0);
        let obj = ops.get(1).copied().unwrap_or(0);
        let key = ops.get(2).copied().unwrap_or(0);
        return (def_r0(dst), vec![Var::Reg(obj), Var::Reg(key)]);
    }
    // SPD/SPDE/SPDEH/SPDS: obj[member_data] := value
    if matches!(op, vm::VM_SPD | vm::VM_SPDE | vm::VM_SPDEH | vm::VM_SPDS) {
        let obj = ops.get(0).copied().unwrap_or(0);
        let val = ops.get(2).copied().unwrap_or(0);
        return (Vec::new(), vec![Var::Reg(obj), Var::Reg(val)]);
    }
    // SPI/SPIE/SPIS: obj[member_reg] := value
    if op == vm::VM_SPI || op == vm::VM_SPIE || op == vm::VM_SPIS {
        let obj = ops.get(0).copied().unwrap_or(0);
        let key = ops.get(1).copied().unwrap_or(0);
        let val = ops.get(2).copied().unwrap_or(0);
        return (Vec::new(), vec![Var::Reg(obj), Var::Reg(key), Var::Reg(val)]);
    }

    // DELD/DELI, TYPEOFD/TYPEOFI: affect object + key + dst (for typeof*)
    // DELD: dst := delete obj[member_data]
    if op == vm::VM_DELD {
        let dst = ops.get(0).copied().unwrap_or(0);
        let obj = ops.get(1).copied().unwrap_or(0);
        return (vec![Var::Reg(dst)], vec![Var::Reg(obj)]);
    }

    // DELI: dst := delete obj[key_reg]
    if op == vm::VM_DELI {
        let dst = ops.get(0).copied().unwrap_or(0);
        let obj = ops.get(1).copied().unwrap_or(0);
        let key = ops.get(2).copied().unwrap_or(0);
        return (vec![Var::Reg(dst)], vec![Var::Reg(obj), Var::Reg(key)]);
    }

    if op == vm::VM_TYPEOFD {
        let dst = ops.get(0).copied().unwrap_or(0);
        let base = ops.get(1).copied().unwrap_or(0);
        return (def_r0(dst), vec![Var::Reg(base)]);
    }
    if op == vm::VM_TYPEOFI {
        let dst = ops.get(0).copied().unwrap_or(0);
        let base = ops.get(1).copied().unwrap_or(0);
        let key = ops.get(2).copied().unwrap_or(0);
        return (def_r0(dst), vec![Var::Reg(base), Var::Reg(key)]);
    }

    // INC/DEC families
    if (vm::VM_INC..=vm::VM_INCP).contains(&op) {
        return effects_op1_prop(ops, vm::VM_INC, op, true);
    }
    if (vm::VM_DEC..=vm::VM_DECP).contains(&op) {
        return effects_op1_prop(ops, vm::VM_DEC, op, true);
    }

    // Binary families with property variants.
    if is_op2_prop(op) {
        return effects_op2_prop(ops, op);
    }

    // CALL/NEW families: define dst, use callee + args.
    if op == vm::VM_CALL || op == vm::VM_NEW {
        let dst = ops.get(0).copied().unwrap_or(0);
        let callee = ops.get(1).copied().unwrap_or(0);
        let argc = ops.get(2).copied().unwrap_or(0);
        let mut uses = vec![Var::Reg(callee)];
        uses.extend(call_arg_regs(argc, ops, 3));
        return (def_r0(dst), uses);
    }
    if op == vm::VM_CALLD {
        let dst = ops.get(0).copied().unwrap_or(0);
        let obj = ops.get(1).copied().unwrap_or(0);
        let tmp = ops.get(3).copied().unwrap_or(0); // tmp func reg
        let argc = ops.get(4).copied().unwrap_or(0);
        let mut defs = Vec::new();
        if dst != 0 { defs.push(Var::Reg(dst)); }
        if tmp != 0 { defs.push(Var::Reg(tmp)); }
        let mut uses = vec![Var::Reg(obj)];
        uses.extend(call_arg_regs(argc, ops, 5));
        return (defs, uses);
    }
    if op == vm::VM_CALLI {
        let dst = ops.get(0).copied().unwrap_or(0);
        let obj = ops.get(1).copied().unwrap_or(0);
        let member = ops.get(2).copied().unwrap_or(0);
        let tmp = ops.get(3).copied().unwrap_or(0); // tmp func reg
        let argc = ops.get(4).copied().unwrap_or(0);
        let mut defs = Vec::new();
        if dst != 0 { defs.push(Var::Reg(dst)); }
        if tmp != 0 { defs.push(Var::Reg(tmp)); }
        let mut uses = vec![Var::Reg(obj), Var::Reg(member)];
        uses.extend(call_arg_regs(argc, ops, 5));
        return (defs, uses);
    }

    // Unary RMW operations (conservative default): op %r => r := f(r)
    if ops.len() == 1 {
        let dst = ops.get(0).copied().unwrap_or(0);
        if dst == 0 {
            return (Vec::new(), Vec::new());
        }
        return (vec![Var::Reg(dst)], vec![Var::Reg(dst)]);
    }

    // Binary RMW operations (conservative default): op %a,%b => a := f(a,b)
    if ops.len() == 2 {
        let a = ops.get(0).copied().unwrap_or(0);
        let b = ops.get(1).copied().unwrap_or(0);
        let defs = def_r0(a);
        let mut uses = Vec::new();
        uses.push(Var::Reg(a));
        uses.push(Var::Reg(b));
        return (defs, uses);
    }

    // Default: no register effects.
    (Vec::new(), Vec::new())
}

fn call_arg_regs(argc: i32, ops: &[i32], start: usize) -> Vec<Var> {
    // Mirror disasm formatting: argc >=0 => that many registers;
    // -1 => omitted args; -2 => FAT list.
    let mut uses = Vec::new();
    if argc == -1 {
        return uses;
    }
    if argc == -2 {
        let num = ops.get(start).copied().unwrap_or(0) as usize;
        // pairs: (ty, val)
        for j in 0..num {
            let ty = ops.get(start + 1 + j * 2).copied().unwrap_or(0);
            let val = ops.get(start + 1 + j * 2 + 1).copied().unwrap_or(0);
            // Only FAT_NORMAL / FAT_EXPAND consume a register.
            if ty == 0 || ty == 1 {
                uses.push(Var::Reg(val));
            }
        }
        return uses;
    }

    let n = argc.max(0) as usize;
    for j in 0..n {
        if let Some(&r) = ops.get(start + j) {
            uses.push(Var::Reg(r));
        }
    }
    uses
}

fn is_op2_prop(op: i32) -> bool {
    matches!(
        op,
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

fn op2_base(op: i32) -> i32 {
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

fn effects_op2_prop(ops: &[i32], op: i32) -> (Vec<Var>, Vec<Var>) {
    let base = op2_base(op);
    match op - base {
        0 => {
            // op %a, %b  => a := f(a,b)
            let a = ops.get(0).copied().unwrap_or(0);
            let b = ops.get(1).copied().unwrap_or(0);
            let defs = if a == 0 { Vec::new() } else { vec![Var::Reg(a)] };
            (defs, vec![Var::Reg(a), Var::Reg(b)])
        }
        1 => {
            // oppd %res, %obj.*data, %rhs
            let res = ops.get(0).copied().unwrap_or(0);
            let obj = ops.get(1).copied().unwrap_or(0);
            let rhs = ops.get(3).copied().unwrap_or(0);
            (if res == 0 { Vec::new() } else { vec![Var::Reg(res)] }, vec![Var::Reg(obj), Var::Reg(rhs)])
        }
        2 => {
            // oppi %res, %obj.%key, %rhs
            let res = ops.get(0).copied().unwrap_or(0);
            let obj = ops.get(1).copied().unwrap_or(0);
            let key = ops.get(2).copied().unwrap_or(0);
            let rhs = ops.get(3).copied().unwrap_or(0);
            (if res == 0 { Vec::new() } else { vec![Var::Reg(res)] }, vec![Var::Reg(obj), Var::Reg(key), Var::Reg(rhs)])
        }
        3 => {
            // opp %res, %obj, %rhs
            let res = ops.get(0).copied().unwrap_or(0);
            let obj = ops.get(1).copied().unwrap_or(0);
            let rhs = ops.get(2).copied().unwrap_or(0);
            (if res == 0 { Vec::new() } else { vec![Var::Reg(res)] }, vec![Var::Reg(obj), Var::Reg(rhs)])
        }
        _ => (Vec::new(), Vec::new()),
    }
}

fn effects_op1_prop(ops: &[i32], base: i32, op: i32, rmw: bool) -> (Vec<Var>, Vec<Var>) {
    match op - base {
        0 => {
            // inc/dec %r
            let r0 = ops.get(0).copied().unwrap_or(0);
            if r0 == 0 {
                return (Vec::new(), Vec::new());
            }
            if rmw {
                (vec![Var::Reg(r0)], vec![Var::Reg(r0)])
            } else {
                (vec![Var::Reg(r0)], Vec::new())
            }
        }
        1 => {
            // incpd %res, %obj.*data
            let res = ops.get(0).copied().unwrap_or(0);
            let obj = ops.get(1).copied().unwrap_or(0);
            (if res == 0 { Vec::new() } else { vec![Var::Reg(res)] }, vec![Var::Reg(obj)])
        }
        2 => {
            // incpi %res, %obj.%key
            let res = ops.get(0).copied().unwrap_or(0);
            let obj = ops.get(1).copied().unwrap_or(0);
            let key = ops.get(2).copied().unwrap_or(0);
            (if res == 0 { Vec::new() } else { vec![Var::Reg(res)] }, vec![Var::Reg(obj), Var::Reg(key)])
        }
        3 => {
            // incp %res, %obj
            let res = ops.get(0).copied().unwrap_or(0);
            let obj = ops.get(1).copied().unwrap_or(0);
            (if res == 0 { Vec::new() } else { vec![Var::Reg(res)] }, vec![Var::Reg(obj)])
        }
        _ => (Vec::new(), Vec::new()),
    }
}