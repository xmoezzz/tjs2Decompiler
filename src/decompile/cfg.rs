use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use anyhow::{bail, Result};

use crate::model::Tjs2Object;
use crate::vmcodes::vm;

use super::decode::{decode_object, Insn};

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
}

#[derive(Debug, Clone)]
pub struct TryRegion {
    pub start_pc: usize,
    pub end_pc: usize,   // exclusive
    pub catch_pc: usize,
    pub ex_reg: i32,
    pub depth: usize,
}

impl Cfg {
    pub fn build(obj: &Tjs2Object) -> Result<Self> {
        let insns = decode_object(obj)?;
        let code_len = obj.code.len();
        let (try_regions, catch_sites) = parse_try_regions(&insns, code_len)?;

        let leaders = compute_leaders(&insns, code_len, &try_regions)?;
        let (mut blocks, pc_to_block) = build_blocks(obj.index, code_len, &insns, &leaders)?;
        connect_edges(&mut blocks, &pc_to_block, code_len, &try_regions)?;
        let entry_block = *pc_to_block.get(&0).ok_or_else(|| anyhow::anyhow!("missing entry block"))?;

        Ok(Self {
            obj_index: obj.index,
            code_len,
            blocks,
            pc_to_block,
            entry_block,
            try_regions,
            catch_sites,
        })
    }
}

fn parse_try_regions(insns: &[Insn], code_len: usize) -> Result<(Vec<TryRegion>, HashMap<usize, i32>)> {
    // Model nesting based on ENTRY/EXTRY.
    // Range: from (entry_pc + 3) up to (extry_pc) exclusive.
    let mut stack: Vec<(usize, usize, i32)> = Vec::new(); // (start_pc, catch_pc, ex_reg)
    let mut regions: Vec<TryRegion> = Vec::new();
    let mut catch_sites: HashMap<usize, i32> = HashMap::new();

    for insn in insns {
        match insn.op {
            x if x == vm::VM_ENTRY => {
                if insn.size != 3 {
                    bail!("ENTRY size mismatch at {}", insn.pc);
                }
                let catch_rel = insn.words[1];
                let catch_pc = (insn.pc as i32 + catch_rel) as isize;
                if catch_pc < 0 || catch_pc as usize >= code_len {
                    bail!("ENTRY catch target out of range: pc={} rel={}", insn.pc, catch_rel);
                }
                let catch_pc = catch_pc as usize;
                let ex_reg = insn.words[2];
                let start_pc = insn.pc + insn.size;
                stack.push((start_pc, catch_pc, ex_reg));
                catch_sites.entry(catch_pc).or_insert(ex_reg);
            }
            x if x == vm::VM_EXTRY => {
                // NOTE: In real TJS2 bytecode, the compiler may emit multiple EXTRY instructions
                // for the same ENTRY (multi-exit try blocks). Linear matching therefore cannot
                // assume a strict 1:1 nesting in the instruction stream.
                if let Some((start_pc, catch_pc, ex_reg)) = stack.pop() {
                    let end_pc = insn.pc; // exclusive
                    let depth = stack.len();
                    regions.push(TryRegion {
                        start_pc,
                        end_pc,
                        catch_pc,
                        ex_reg,
                        depth,
                    });
                } else {
                    // Orphan EXTRY: ignore for region construction (do not fail CFG/SSA build).
                }
            }
            _ => {}
        }
    }
    // If there are unmatched ENTRYs, we still keep them as open regions up to end.
    while let Some((start_pc, catch_pc, ex_reg)) = stack.pop() {
        let depth = stack.len();
        regions.push(TryRegion {
            start_pc,
            end_pc: code_len,
            catch_pc,
            ex_reg,
            depth,
        });
    }
    regions.sort_by_key(|r| (r.start_pc, r.end_pc, r.depth));
    Ok((regions, catch_sites))
}

fn compute_leaders(insns: &[Insn], code_len: usize, try_regions: &[TryRegion]) -> Result<BTreeSet<usize>> {
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
            x if x == vm::VM_ENTRY => {
                // ENTRY's catch target is a leader.
                let t = (pc as i32 + insn.words[1]) as isize;
                if t >= 0 && (t as usize) < code_len {
                    leaders.insert(t as usize);
                }
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

    // Also mark catch entries as leaders (redundant but explicit).
    for r in try_regions {
        leaders.insert(r.catch_pc);
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
            let insn = insn_at.get(&cur_pc).cloned().ok_or_else(|| anyhow::anyhow!("no instruction at pc {}", cur_pc))?;
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

fn connect_edges(
    blocks: &mut [BasicBlock],
    pc_to_block: &HashMap<usize, usize>,
    code_len: usize,
    try_regions: &[TryRegion],
) -> Result<()> {
    // Precompute catch edges per block (conservative): if a block is inside a try region,
    // it may have an exceptional successor to the innermost handler.
    let mut exc_succ: HashMap<usize, usize> = HashMap::new(); // block_id -> catch_block_id
    for b in blocks.iter() {
        if let Some((catch_pc, _ex_reg)) = innermost_handler_for_pc(b.start_pc, try_regions) {
            if let Some(&cid) = pc_to_block.get(&catch_pc) {
                exc_succ.insert(b.id, cid);
            }
        }
    }

    for b in blocks.iter_mut() {
        if b.insns.is_empty() {
            b.succ = Vec::new();
            continue;
        }
        let last = b.insns.last().unwrap();
        let pc = last.pc;
        let next = pc + last.size;

        let mut succ: Vec<usize> = Vec::new();
        match last.op {
            x if x == vm::VM_JMP => {
                let t = (pc as i32 + last.words[1]) as usize;
                succ.push(*pc_to_block.get(&t).ok_or_else(|| anyhow::anyhow!("missing block for JMP target {}", t))?);
            }
            x if x == vm::VM_JF || x == vm::VM_JNF => {
                let t = (pc as i32 + last.words[1]) as usize;
                succ.push(*pc_to_block.get(&t).ok_or_else(|| anyhow::anyhow!("missing block for JF/JNF target {}", t))?);
                if next < code_len {
                    succ.push(*pc_to_block.get(&next).ok_or_else(|| anyhow::anyhow!("missing block for fallthrough {}", next))?);
                }
            }
            x if x == vm::VM_RET || x == vm::VM_THROW => {
                // no normal successors
            }
            _ => {
                if next < code_len {
                    if let Some(&nid) = pc_to_block.get(&next) {
                        succ.push(nid);
                    }
                }
            }
        }

        // Add an exceptional successor for blocks in a try region, conservatively.
        if let Some(&cid) = exc_succ.get(&b.id) {
            if !succ.contains(&cid) {
                succ.push(cid);
            }
        }

        // Dedup while preserving order.
        let mut seen: HashSet<usize> = HashSet::new();
        succ.retain(|x| seen.insert(*x));
        b.succ = succ;
    }

    // Fill predecessor lists.
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); blocks.len()];
    for b in blocks.iter() {
        for &s in &b.succ {
            preds[s].push(b.id);
        }
    }
    for (id, p) in preds.into_iter().enumerate() {
        blocks[id].pred = p;
    }
    Ok(())
}

fn innermost_handler_for_pc(pc: usize, try_regions: &[TryRegion]) -> Option<(usize, i32)> {
    // Pick the deepest (most nested) region that contains pc.
    let mut best: Option<&TryRegion> = None;
    for r in try_regions {
        if pc >= r.start_pc && pc < r.end_pc {
            match best {
                None => best = Some(r),
                Some(b) => {
                    if r.depth >= b.depth {
                        best = Some(r);
                    }
                }
            }
        }
    }
    best.map(|r| (r.catch_pc, r.ex_reg))
}
