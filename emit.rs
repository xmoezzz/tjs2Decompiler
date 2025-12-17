// SPDX-License-Identifier: MIT
//
// Pseudo-code emitter for raw i32-word disassembly.
//
// This is intentionally unstructured. It prints labels at basic block leaders and dumps the raw
// instruction listing. This output is intended for reverse engineering and resynchronization.

use std::collections::HashMap;

use crate::cfg::Cfg;
use crate::raw_disasm::Instruction;

pub fn emit_pseudo(insns: &[Instruction], g: &Cfg) -> String {
    let mut label_of: HashMap<usize, String> = HashMap::new();
    let mut n = 0usize;
    for &l in &g.leaders {
        label_of.insert(l, format!("L{:04}", n));
        n += 1;
    }

    let mut out = String::new();
    out.push_str("// Pseudo TJS (unstructured)\n");
    out.push_str("// This output is intended for bootstrapping format reverse engineering.\n\n");

    for ins in insns {
        if let Some(lbl) = label_of.get(&ins.ip) {
            out.push_str(&format!("{lbl}:\n"));
        }
        out.push_str(&format!("  // {}\n", ins.format()));
    }

    out.push_str("\n// CFG edges (leader -> successors)\n");
    for (from, tos) in &g.edges {
        let lf = label_of.get(from).cloned().unwrap_or_else(|| format!("IP_{from}"));
        let succs = tos
            .iter()
            .map(|t| label_of.get(t).cloned().unwrap_or_else(|| format!("IP_{t}")))
            .collect::<Vec<_>>()
            .join(", ");
        out.push_str(&format!("// {lf} -> {succs}\n"));
    }

    out
}
