use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use anyhow::{Result, bail};

use crate::model::Tjs2Object;
use crate::vmcodes::vm;

use super::decode::{Insn, decode_object};

#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub id: usize,
    pub start_pc: usize,
    pub insns: Vec<Insn>,
    pub succ: Vec<usize>, // successor block ids
    pub pred: Vec<usize>, // predecessor block ids
}

#[derive(Debug, Clone)]
pub struct Cfg {
    pub obj_index: usize,
    pub code_len: usize,
    pub blocks: Vec<BasicBlock>,
    pub pc_to_block: HashMap<usize, usize>,
    pub entry_block: usize,
    pub try_regions: Vec<TryRegion>,
    pub catch_sites: HashMap<usize, i32>, // catch_pc -> ex_reg
    /// Active exception-handler stack at basic-block entry, outermost first.
    /// Handler ids index `try_regions` only after `build_try_regions` preserves
    /// descriptor order.
    pub block_handler_stack: Vec<Vec<usize>>,
    /// Synthetic exceptional successor chosen from the innermost active
    /// handler.  Kept separate from ordinary control-flow semantics.
    pub exceptional_succ: HashMap<usize, usize>,
}

#[derive(Debug, Clone)]
pub struct TryRegion {
    pub id: usize,
    pub entry_pc: usize,
    pub start_pc: usize,
    pub catch_pc: usize,
    pub ex_reg: i32,
    pub depth: usize,
    /// Blocks executed while this handler is active.  Nested protected blocks
    /// are intentionally included; their exceptional edge still targets the
    /// innermost handler.
    pub protected_blocks: Vec<usize>,
    /// Ordinary CFG edges produced by an EXTRY that pops this handler.
    /// A single ENTRY may legitimately have many of these (return, break,
    /// continue, and ordinary fallthrough all compile this way).
    pub normal_exit_edges: Vec<(usize, usize)>,
}

#[derive(Debug, Clone)]
struct HandlerDesc {
    id: usize,
    entry_pc: usize,
    start_pc: usize,
    catch_pc: usize,
    ex_reg: i32,
}

#[derive(Debug)]
struct ExceptionFlow {
    block_stacks: Vec<Vec<usize>>,
    exceptional_succ: HashMap<usize, usize>,
    /// RET reached inside an ENTRY-created execution level returns the next
    /// bytecode address to the caller level; it is not a function return.
    execution_exit_succ: HashMap<usize, usize>,
    normal_exit_edges: HashMap<usize, Vec<(usize, usize)>>,
}

impl Cfg {
    pub fn build(obj: &Tjs2Object) -> Result<Self> {
        let insns = decode_object(obj)?;
        let code_len = obj.code.len();
        let (handlers, catch_sites) = parse_handlers(&insns, code_len)?;

        // Build the ordinary CFG first.  Exception protection is a dynamic
        // execution level in the official VM: ENTRY recursively executes the
        // protected code and any reached EXTRY returns from that level.  It is
        // therefore incorrect to infer protection from one linear [start,end)
        // interval.
        let leaders = compute_leaders(&insns, code_len, &handlers)?;
        let (mut blocks, pc_to_block) = build_blocks(obj.index, code_len, &insns, &leaders)?;
        connect_normal_edges(&mut blocks, &pc_to_block, code_len)?;
        let entry_block = *pc_to_block
            .get(&0)
            .ok_or_else(|| anyhow::anyhow!("missing entry block"))?;

        let flow = analyze_exception_flow(
            &blocks,
            &pc_to_block,
            entry_block,
            &handlers,
        )?;
        attach_exception_edges_and_rebuild_preds(
            &mut blocks,
            &flow.exceptional_succ,
            &flow.execution_exit_succ,
        );
        let try_regions = build_try_regions(&handlers, &flow, &pc_to_block)?;

        Ok(Self {
            obj_index: obj.index,
            code_len,
            blocks,
            pc_to_block,
            entry_block,
            try_regions,
            catch_sites,
            block_handler_stack: flow.block_stacks,
            exceptional_succ: flow.exceptional_succ,
        })
    }
}

fn parse_handlers(
    insns: &[Insn],
    code_len: usize,
) -> Result<(Vec<HandlerDesc>, HashMap<usize, i32>)> {
    let mut handlers = Vec::new();
    let mut catch_sites = HashMap::new();

    for insn in insns {
        if insn.op != vm::VM_ENTRY {
            continue;
        }
        if insn.size != 3 {
            bail!("ENTRY size mismatch at {}", insn.pc);
        }
        let catch_rel = insn.words[1];
        let catch_pc = (insn.pc as i32 + catch_rel) as isize;
        if catch_pc < 0 || catch_pc as usize >= code_len {
            bail!(
                "ENTRY catch target out of range: pc={} rel={}",
                insn.pc,
                catch_rel
            );
        }
        let catch_pc = catch_pc as usize;
        let ex_reg = insn.words[2];
        if let Some(prev) = catch_sites.insert(catch_pc, ex_reg) {
            if prev != ex_reg {
                bail!(
                    "conflicting exception registers for catch pc {}: {} vs {}",
                    catch_pc,
                    prev,
                    ex_reg
                );
            }
        }
        handlers.push(HandlerDesc {
            id: handlers.len(),
            entry_pc: insn.pc,
            start_pc: insn.pc + insn.size,
            catch_pc,
            ex_reg,
        });
    }

    Ok((handlers, catch_sites))
}

fn compute_leaders(
    insns: &[Insn],
    code_len: usize,
    handlers: &[HandlerDesc],
) -> Result<BTreeSet<usize>> {
    let mut leaders: BTreeSet<usize> = BTreeSet::new();
    leaders.insert(0);

    for insn in insns {
        let pc = insn.pc;
        let next = pc + insn.size;

        match insn.op {
            x if x == vm::VM_JMP => {
                let t = (pc as i32 + insn.words[1]) as isize;
                if t < 0 || t as usize >= code_len {
                    bail!("JMP target out of range at {}", pc);
                }
                leaders.insert(t as usize);
                if next < code_len {
                    leaders.insert(next);
                }
            }
            x if x == vm::VM_JF || x == vm::VM_JNF => {
                let t = (pc as i32 + insn.words[1]) as isize;
                if t < 0 || t as usize >= code_len {
                    bail!("JF/JNF target out of range at {}", pc);
                }
                leaders.insert(t as usize);
                if next < code_len {
                    leaders.insert(next);
                }
            }
            x if x == vm::VM_ENTRY || x == vm::VM_EXTRY => {
                // Keep handler-stack transitions at block boundaries.  ENTRY
                // pushes for the following block; EXTRY pops before its normal
                // successor executes.
                leaders.insert(pc);
                if next < code_len {
                    leaders.insert(next);
                }
            }
            x if x == vm::VM_RET || x == vm::VM_THROW => {
                if next < code_len {
                    leaders.insert(next);
                }
            }
            _ => {}
        }
    }

    for h in handlers {
        leaders.insert(h.entry_pc);
        if h.start_pc < code_len {
            leaders.insert(h.start_pc);
        }
        leaders.insert(h.catch_pc);
    }
    Ok(leaders)
}

fn build_blocks(
    obj_index: usize,
    code_len: usize,
    insns: &[Insn],
    leaders: &BTreeSet<usize>,
) -> Result<(Vec<BasicBlock>, HashMap<usize, usize>)> {
    // Map leader pc -> sequential id.
    let mut leader_list: Vec<usize> = leaders.iter().copied().collect();
    leader_list.sort();
    if leader_list.first().copied().unwrap_or(usize::MAX) != 0 {
        bail!("missing leader 0 in object {}", obj_index);
    }

    let mut pc_to_block: HashMap<usize, usize> = HashMap::new();
    for (id, &pc) in leader_list.iter().enumerate() {
        pc_to_block.insert(pc, id);
    }

    // Build pc->Insn lookup.
    let mut insn_at: BTreeMap<usize, Insn> = BTreeMap::new();
    for insn in insns {
        insn_at.insert(insn.pc, insn.clone());
    }

    let mut blocks: Vec<BasicBlock> = Vec::new();
    for (id, &start_pc) in leader_list.iter().enumerate() {
        let end_pc = leader_list.get(id + 1).copied().unwrap_or(code_len);
        let mut cur_pc = start_pc;
        let mut blk_insns = Vec::new();
        while cur_pc < end_pc {
            let insn = insn_at
                .get(&cur_pc)
                .cloned()
                .ok_or_else(|| anyhow::anyhow!("no instruction at pc {}", cur_pc))?;
            cur_pc += insn.size;
            blk_insns.push(insn);
        }
        blocks.push(BasicBlock {
            id,
            start_pc,
            insns: blk_insns,
            succ: Vec::new(),
            pred: Vec::new(),
        });
    }
    Ok((blocks, pc_to_block))
}

fn connect_normal_edges(
    blocks: &mut [BasicBlock],
    pc_to_block: &HashMap<usize, usize>,
    code_len: usize,
) -> Result<()> {
    for b in blocks.iter_mut() {
        if b.insns.is_empty() {
            b.succ.clear();
            continue;
        }
        let last = b.insns.last().unwrap();
        let pc = last.pc;
        let next = pc + last.size;
        let mut succ = Vec::new();

        match last.op {
            x if x == vm::VM_JMP => {
                let t = (pc as i32 + last.words[1]) as isize;
                if t < 0 || t as usize >= code_len {
                    bail!("JMP target out of range at {}", pc);
                }
                succ.push(
                    *pc_to_block
                        .get(&(t as usize))
                        .ok_or_else(|| anyhow::anyhow!("missing block for JMP target {}", t))?,
                );
            }
            x if x == vm::VM_JF || x == vm::VM_JNF => {
                let t = (pc as i32 + last.words[1]) as isize;
                if t < 0 || t as usize >= code_len {
                    bail!("JF/JNF target out of range at {}", pc);
                }
                succ.push(
                    *pc_to_block
                        .get(&(t as usize))
                        .ok_or_else(|| anyhow::anyhow!("missing block for JF/JNF target {}", t))?,
                );
                if next < code_len {
                    succ.push(*pc_to_block.get(&next).ok_or_else(|| {
                        anyhow::anyhow!("missing block for fallthrough {}", next)
                    })?);
                }
            }
            x if x == vm::VM_RET || x == vm::VM_THROW => {
                // no ordinary successors
            }
            _ => {
                if next < code_len {
                    if let Some(&nid) = pc_to_block.get(&next) {
                        succ.push(nid);
                    }
                }
            }
        }

        let mut seen = HashSet::new();
        succ.retain(|x| seen.insert(*x));
        b.succ = succ;
        b.pred.clear();
    }
    Ok(())
}

fn block_can_raise(block: &BasicBlock) -> bool {
    // ENTRY/EXTRY are VM execution-level control operators.  They do not
    // themselves execute user operations; treating their dedicated blocks as
    // throwing would create spurious handler edges.  Other instructions are
    // conservatively allowed to raise, including explicit THROW.
    block.insns.iter().any(|insn| {
        !matches!(
            insn.op,
            x if x == vm::VM_NOP
                || x == vm::VM_NF
                || x == vm::VM_JMP
                || x == vm::VM_JF
                || x == vm::VM_JNF
                || x == vm::VM_ENTRY
                || x == vm::VM_EXTRY
                || x == vm::VM_RET
        )
    })
}

fn merge_handler_state(
    states: &mut [Option<Vec<usize>>],
    bid: usize,
    incoming: &[usize],
    work: &mut VecDeque<usize>,
) -> Result<()> {
    match states[bid].clone() {
        None => {
            states[bid] = Some(incoming.to_vec());
            work.push_back(bid);
        }
        Some(existing) if existing.as_slice() == incoming => {}
        Some(existing) => {
            bail!(
                "inconsistent exception-handler stack at block {}: {:?} vs {:?}",
                bid,
                existing,
                incoming
            );
        }
    }
    Ok(())
}

fn analyze_exception_flow(
    blocks: &[BasicBlock],
    pc_to_block: &HashMap<usize, usize>,
    entry_block: usize,
    handlers: &[HandlerDesc],
) -> Result<ExceptionFlow> {
    let mut handler_at_entry_pc = HashMap::new();
    for h in handlers {
        handler_at_entry_pc.insert(h.entry_pc, h.id);
    }

    let mut states: Vec<Option<Vec<usize>>> = vec![None; blocks.len()];
    states[entry_block] = Some(Vec::new());
    let mut work = VecDeque::new();
    work.push_back(entry_block);
    let mut exceptional_succ = HashMap::new();
    let mut execution_exit_succ = HashMap::new();
    let mut normal_exit_edges: HashMap<usize, Vec<(usize, usize)>> = HashMap::new();

    while let Some(bid) = work.pop_front() {
        let in_stack = states[bid].clone().unwrap_or_default();
        let block = &blocks[bid];

        // An exception raised by an ordinary instruction is caught by the
        // innermost execution level that was active on block entry.  On the
        // exceptional transfer that level has unwound, so the handler itself
        // is popped before the catch block executes.
        if block_can_raise(block) {
            if let Some(&handler_id) = in_stack.last() {
                let h = &handlers[handler_id];
                let catch_block = *pc_to_block.get(&h.catch_pc).ok_or_else(|| {
                    anyhow::anyhow!("missing catch block for pc {}", h.catch_pc)
                })?;
                exceptional_succ.insert(bid, catch_block);
                let outer_stack = &in_stack[..in_stack.len() - 1];
                merge_handler_state(&mut states, catch_block, outer_stack, &mut work)?;
            }
        }

        let mut out_stack = in_stack.clone();
        let mut popped: Vec<usize> = Vec::new();
        for insn in &block.insns {
            if insn.op == vm::VM_ENTRY {
                let handler_id = *handler_at_entry_pc.get(&insn.pc).ok_or_else(|| {
                    anyhow::anyhow!("missing handler descriptor for ENTRY at {}", insn.pc)
                })?;
                out_stack.push(handler_id);
            } else if insn.op == vm::VM_EXTRY {
                let Some(handler_id) = out_stack.pop() else {
                    bail!("reachable EXTRY without active handler at pc {}", insn.pc);
                };
                popped.push(handler_id);
            }
        }

        // ExecuteCode() returns `RET + 1` to its caller.  At level zero that
        // means a real function return, but inside an ENTRY-created recursive
        // ExecuteCode level it pops exactly one handler and resumes the caller
        // at the following instruction.  Model that edge explicitly so CFG,
        // SSA and source structuring do not turn a protected RET into `return`.
        let protected_ret = block
            .insns
            .last()
            .filter(|insn| insn.op == vm::VM_RET && !in_stack.is_empty());
        if let Some(ret) = protected_ret {
            let handler_id = *in_stack.last().unwrap();
            let next_pc = ret.pc + ret.size;
            let succ = *pc_to_block.get(&next_pc).ok_or_else(|| {
                anyhow::anyhow!("missing block for protected RET continuation {}", next_pc)
            })?;
            let outer_stack = &in_stack[..in_stack.len() - 1];
            merge_handler_state(&mut states, succ, outer_stack, &mut work)?;
            execution_exit_succ.insert(bid, succ);
            normal_exit_edges
                .entry(handler_id)
                .or_default()
                .push((bid, succ));
            continue;
        }

        for &succ in &block.succ {
            merge_handler_state(&mut states, succ, &out_stack, &mut work)?;
            for &handler_id in &popped {
                normal_exit_edges
                    .entry(handler_id)
                    .or_default()
                    .push((bid, succ));
            }
        }
    }

    let block_stacks = states
        .into_iter()
        .map(|s| s.unwrap_or_default())
        .collect::<Vec<_>>();

    for edges in normal_exit_edges.values_mut() {
        edges.sort_unstable();
        edges.dedup();
    }

    Ok(ExceptionFlow {
        block_stacks,
        exceptional_succ,
        execution_exit_succ,
        normal_exit_edges,
    })
}

fn build_try_regions(
    handlers: &[HandlerDesc],
    flow: &ExceptionFlow,
    pc_to_block: &HashMap<usize, usize>,
) -> Result<Vec<TryRegion>> {
    let mut regions = Vec::with_capacity(handlers.len());

    for h in handlers {
        let start_block = *pc_to_block.get(&h.start_pc).ok_or_else(|| {
            anyhow::anyhow!("missing protected start block for pc {}", h.start_pc)
        })?;
        let start_stack = &flow.block_stacks[start_block];
        let depth = start_stack
            .iter()
            .position(|id| *id == h.id)
            .unwrap_or(start_stack.len().saturating_sub(1));

        let mut protected_blocks = flow
            .block_stacks
            .iter()
            .enumerate()
            .filter_map(|(bid, stack)| stack.contains(&h.id).then_some(bid))
            .collect::<Vec<_>>();
        protected_blocks.sort_unstable();

        regions.push(TryRegion {
            id: h.id,
            entry_pc: h.entry_pc,
            start_pc: h.start_pc,
            catch_pc: h.catch_pc,
            ex_reg: h.ex_reg,
            depth,
            protected_blocks,
            normal_exit_edges: flow
                .normal_exit_edges
                .get(&h.id)
                .cloned()
                .unwrap_or_default(),
        });
    }

    Ok(regions)
}

fn attach_exception_edges_and_rebuild_preds(
    blocks: &mut [BasicBlock],
    exceptional_succ: &HashMap<usize, usize>,
    execution_exit_succ: &HashMap<usize, usize>,
) {
    for b in blocks.iter_mut() {
        if let Some(&exit_block) = execution_exit_succ.get(&b.id) {
            if !b.succ.contains(&exit_block) {
                b.succ.push(exit_block);
            }
        }
        if let Some(&catch_block) = exceptional_succ.get(&b.id) {
            if !b.succ.contains(&catch_block) {
                b.succ.push(catch_block);
            }
        }
        b.pred.clear();
    }

    let mut preds = vec![Vec::new(); blocks.len()];
    for b in blocks.iter() {
        for &succ in &b.succ {
            preds[succ].push(b.id);
        }
    }
    for (bid, mut pred) in preds.into_iter().enumerate() {
        pred.sort_unstable();
        pred.dedup();
        blocks[bid].pred = pred;
    }
}
