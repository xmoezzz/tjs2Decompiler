// SPDX-License-Identifier: MIT
//
// Minimal CFG builder for the raw i32-word disassembler output.

use std::collections::{BTreeSet, HashMap};

use crate::opcode::Opcode;
use crate::raw_disasm::Instruction;

#[derive(Debug, Clone)]
pub struct Cfg {
    pub leaders: BTreeSet<usize>,          // instruction ip values
    pub edges: HashMap<usize, Vec<usize>>, // leader_ip -> successor leader_ip
}

fn is_terminator(op: &Opcode) -> bool {
    matches!(op, Opcode::Jmp | Opcode::Jf | Opcode::Jnf | Opcode::Ret | Opcode::Throw)
}

pub fn build_cfg(insns: &[Instruction]) -> Cfg {
    let mut leaders: BTreeSet<usize> = BTreeSet::new();
    let mut ip_to_idx: HashMap<usize, usize> = HashMap::new();

    for (idx, ins) in insns.iter().enumerate() {
        ip_to_idx.insert(ins.ip, idx);
    }

    if let Some(first) = insns.first() {
        leaders.insert(first.ip);
    }

    for (i, ins) in insns.iter().enumerate() {
        match ins.opcode {
            Opcode::Jmp | Opcode::Jf | Opcode::Jnf => {
                if let Some(t) = ins.operands.get(0).copied() {
                    if t >= 0 {
                        leaders.insert(t as usize);
                    }
                }
                if ins.opcode != Opcode::Jmp {
                    if let Some(next) = insns.get(i + 1) {
                        leaders.insert(next.ip);
                    }
                }
            }
            _ => {
                if is_terminator(&ins.opcode) {
                    if let Some(next) = insns.get(i + 1) {
                        leaders.insert(next.ip);
                    }
                }
            }
        }
    }

    let mut edges: HashMap<usize, Vec<usize>> = HashMap::new();
    let leader_list: Vec<usize> = leaders.iter().copied().collect();

    for (li, &l_ip) in leader_list.iter().enumerate() {
        let start_idx = match ip_to_idx.get(&l_ip) {
            Some(&v) => v,
            None => continue,
        };
        let end_ip = leader_list.get(li + 1).copied();

        let mut last = &insns[start_idx];
        for ins in &insns[start_idx..] {
            if let Some(eip) = end_ip {
                if ins.ip >= eip {
                    break;
                }
            }
            last = ins;
        }

        let mut succ = Vec::new();
        match last.opcode {
            Opcode::Jmp => {
                if let Some(t) = last.operands.get(0).copied() {
                    if t >= 0 {
                        succ.push(t as usize);
                    }
                }
            }
            Opcode::Jf | Opcode::Jnf => {
                if let Some(t) = last.operands.get(0).copied() {
                    if t >= 0 {
                        succ.push(t as usize);
                    }
                }
                if let Some(next) = leader_list.get(li + 1).copied() {
                    succ.push(next);
                }
            }
            Opcode::Ret | Opcode::Throw => {}
            _ => {
                if let Some(next) = leader_list.get(li + 1).copied() {
                    succ.push(next);
                }
            }
        }

        succ.sort_unstable();
        succ.dedup();
        edges.insert(l_ip, succ);
    }

    Cfg { leaders, edges }
}
