use anyhow::{Result, bail};

use std::collections::{HashSet, VecDeque};

use crate::model::{ConstPools, Tjs2File, Tjs2Object, Variant};
use crate::vmcodes::vm;

// This module emits a low-level, semantics-oriented TJS program that
// replays the VM code using an explicit instruction-pointer state machine.
//
// Design goal: produce *executable* TJS that is as close as possible to the
// original bytecode behavior, not human-readable source.

const FAT_NORMAL: i32 = 0;
const FAT_EXPAND: i32 = 1;
const FAT_UNNAMED_EXPAND: i32 = 2;

const CT_TOPLEVEL: i32 = 0;
const CT_FUNCTION: i32 = 1;
const CT_EXPR_FUNCTION: i32 = 2;
const CT_PROPERTY: i32 = 3;
const CT_PROPERTY_SETTER: i32 = 4;
const CT_PROPERTY_GETTER: i32 = 5;
const CT_CLASS: i32 = 6;
const CT_SUPER_GETTER: i32 = 7;

pub fn emit_executable_tjs(file: &Tjs2File) -> Result<String> {
    preflight_topology(file)?;

    let mut out = String::new();
    out.push_str("return (function(__tjs2dec_top_this) {\n");

    // Recreate native dispatch kinds first.  Accessor/super-getter contexts
    // are consumed by their property/class parent and therefore intentionally
    // do not get a fake standalone Function object.
    for obj in &file.objects {
        out.push_str(&emit_object_materializer(file, obj)?);
    }

    // Loader-time Properties[] registration occurs exactly once, before
    // InterObject replacement and before the top-level context is executed.
    for obj in &file.objects {
        for &(name_idx, child_idx) in &obj.properties {
            let parent = obj.parent;
            if parent < 0 {
                bail!("executable emit: object {} has loader property without parent", obj.index);
            }
            let name = pool_string(&file.const_pools, name_idx, obj.index)?;
            require_decl_identifier(name, obj.index, "loader member")?;
            if child_idx < 0 || child_idx as usize >= file.objects.len() {
                bail!("executable emit: object {} loader property references invalid child {}", obj.index, child_idx);
            }
            out.push_str(&format!(
                "  &(__tjs2dec_obj_{}.{} ) = (__tjs2dec_obj_{} incontextof null);\n",
                parent, name, child_idx
            ));
        }
    }

    // DATA octet entries are shared objects in the bytecode loader.  Create
    // each pool entry once, then let every DataArea slot reference it.
    for (i, bytes) in file.const_pools.octets.iter().enumerate() {
        let mut lit = String::from("<%");
        for b in bytes {
            lit.push_str(&format!(" {:02x}", b));
        }
        if !bytes.is_empty() {
            lit.push(' ');
        }
        lit.push_str("%>");
        out.push_str(&format!("  var __tjs2dec_octet_{} = {};\n", i, lit));
    }

    // Only now replace InterObject/InterGenerator DataArea entries.  The
    // original loader stores ObjThis=null closures here.
    for obj in &file.objects {
        out.push_str(&emit_object_data(obj, &file.const_pools)?);
    }

    out.push_str(&format!(
        "  return (__tjs2dec_obj_{} incontextof __tjs2dec_top_this)();\n",
        file.toplevel
    ));
    out.push_str("})(this);\n");

    if out.contains("__tjs2dec_unrepresentable_scope_proxy") {
        bail!("executable emit refused: bytecode uses VM %-2 scope proxy in a form with no exact ordinary-TJS spelling");
    }
    Ok(compact_generated_tjs(&out))
}

/// The executable emitter is a transport form, not a debugging disassembly.
/// Keep one statement per line for diagnostics, but strip indentation and blank
/// lines so large VM replays do not grow by another factor just from formatting.
fn compact_generated_tjs(source: &str) -> String {
    let mut out = String::with_capacity(source.len());
    for line in source.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        out.push_str(line);
        out.push('\n');
    }
    out
}

fn preflight_topology(file: &Tjs2File) -> Result<()> {
    if file.toplevel < 0 || file.toplevel as usize >= file.objects.len() {
        bail!("executable emit: invalid top-level object {}", file.toplevel);
    }
    if file.objects[file.toplevel as usize].context_type != CT_TOPLEVEL {
        bail!("executable emit: object {} is not ctTopLevel", file.toplevel);
    }

    let mut referenced = vec![0usize; file.objects.len()];
    for obj in &file.objects {
        for v in &obj.data {
            let target = match v {
                Variant::InterObject(i) | Variant::InterGenerator(i) => Some(*i),
                _ => None,
            };
            if let Some(i) = target {
                if i < 0 || i as usize >= file.objects.len() {
                    bail!("executable emit: object {} DataArea references invalid object {}", obj.index, i);
                }
                referenced[i as usize] += 1;
            }
        }
    }

    for (slot, obj) in file.objects.iter().enumerate() {
        if obj.index != slot {
            bail!("executable emit: object slot {} contains index {}", slot, obj.index);
        }
        if !(CT_TOPLEVEL..=CT_SUPER_GETTER).contains(&obj.context_type) {
            bail!("executable emit: object {} has unknown context_type {}", obj.index, obj.context_type);
        }
        if obj.parent >= 0 && obj.parent as usize >= file.objects.len() {
            bail!("executable emit: object {} has invalid parent {}", obj.index, obj.parent);
        }

        match obj.context_type {
            CT_TOPLEVEL => {
                if obj.index != file.toplevel as usize || obj.parent >= 0 {
                    bail!("executable emit: unexpected non-root/extra ctTopLevel object {}", obj.index);
                }
                if referenced[obj.index] != 0 {
                    bail!("executable emit: ctTopLevel object {} is directly referenced from DataArea", obj.index);
                }
            }
            CT_FUNCTION => {
                require_decl_identifier(obj.name.as_deref().unwrap_or(""), obj.index, "function")?;
            }
            CT_EXPR_FUNCTION => {}
            CT_PROPERTY => {
                require_decl_identifier(obj.name.as_deref().unwrap_or(""), obj.index, "property")?;
                if !obj.code.is_empty() {
                    bail!("executable emit: ctProperty object {} unexpectedly has executable code", obj.index);
                }
                validate_property_links(file, obj)?;
            }
            CT_PROPERTY_SETTER | CT_PROPERTY_GETTER => {
                if obj.parent < 0 {
                    bail!("executable emit: property accessor {} has no parent", obj.index);
                }
                let prop = &file.objects[obj.parent as usize];
                if prop.context_type != CT_PROPERTY {
                    bail!("executable emit: accessor {} parent {} is not ctProperty", obj.index, obj.parent);
                }
                let linked = if obj.context_type == CT_PROPERTY_SETTER { prop.prop_setter } else { prop.prop_getter };
                if linked != obj.index as i32 {
                    bail!("executable emit: accessor {} is not linked back from property {}", obj.index, prop.index);
                }
                if referenced[obj.index] != 0 {
                    bail!("executable emit: DataArea directly references property accessor object {}", obj.index);
                }
            }
            CT_CLASS => {
                require_decl_identifier(obj.name.as_deref().unwrap_or(""), obj.index, "class")?;
                let _ = class_emit_parts(file, obj)?;
            }
            CT_SUPER_GETTER => {
                if obj.parent < 0 || file.objects[obj.parent as usize].context_type != CT_CLASS {
                    bail!("executable emit: superclass getter {} has no ctClass parent", obj.index);
                }
                if referenced[obj.index] != 0 {
                    bail!("executable emit: DataArea directly references superclass getter object {}", obj.index);
                }
            }
            _ => unreachable!(),
        }

        for &(name_idx, child_idx) in &obj.properties {
            if obj.parent < 0 {
                bail!("executable emit: object {} has loader property without parent", obj.index);
            }
            if child_idx != obj.index as i32 {
                bail!("executable emit: object {} has non-canonical loader property target {}", obj.index, child_idx);
            }
            let name = pool_string(&file.const_pools, name_idx, obj.index)?;
            require_decl_identifier(name, obj.index, "loader member")?;
            if obj.name.as_deref() != Some(name) {
                bail!("executable emit: object {} loader name {:?} != object name {:?}", obj.index, name, obj.name);
            }
            if !matches!(obj.context_type, CT_FUNCTION | CT_PROPERTY | CT_CLASS) {
                bail!("executable emit: object {} context {} cannot be loader-registered child", obj.index, obj.context_type);
            }
            let parent_ct = file.objects[obj.parent as usize].context_type;
            if !matches!(parent_ct, CT_FUNCTION | CT_CLASS) {
                bail!(
                    "executable emit: object {} loader property parent {} has unsupported context {}",
                    obj.index,
                    obj.parent,
                    parent_ct
                );
            }
        }
    }
    Ok(())
}

fn validate_property_links(file: &Tjs2File, prop: &Tjs2Object) -> Result<()> {
    for (kind, idx, ct) in [
        ("setter", prop.prop_setter, CT_PROPERTY_SETTER),
        ("getter", prop.prop_getter, CT_PROPERTY_GETTER),
    ] {
        if idx < 0 { continue; }
        if idx as usize >= file.objects.len() {
            bail!("executable emit: property {} {} index {} out of range", prop.index, kind, idx);
        }
        let a = &file.objects[idx as usize];
        if a.context_type != ct || a.parent != prop.index as i32 {
            bail!("executable emit: property {} {} object {} has context {} parent {}", prop.index, kind, idx, a.context_type, a.parent);
        }
    }
    Ok(())
}

fn pool_string<'a>(pools: &'a ConstPools, idx: i32, obj_index: usize) -> Result<&'a str> {
    if idx < 0 {
        bail!("executable emit: negative string pool index {} in object {}", idx, obj_index);
    }
    pools.strings.get(idx as usize).map(|s| s.as_str()).ok_or_else(|| anyhow::anyhow!(
        "executable emit: string pool index {} out of range in object {}", idx, obj_index
    ))
}

fn require_decl_identifier(name: &str, obj_index: usize, kind: &str) -> Result<()> {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        bail!("executable emit: {} object {} has empty name", kind, obj_index);
    };
    if !(first == '_' || first.is_ascii_alphabetic())
        || !chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
        || is_tjs_keyword(name)
        || is_emit_reserved_ident(name)
    {
        bail!("executable emit: {} object {} name {:?} is not safely declarable", kind, obj_index, name);
    }
    Ok(())
}

fn emit_object_materializer(file: &Tjs2File, obj: &Tjs2Object) -> Result<String> {
    let mut out = String::new();
    match obj.context_type {
        CT_TOPLEVEL => {
            let params = emit_function_params(obj)?;
            out.push_str(&format!("  function __tjs2dec_obj_{}({}) {{\n", obj.index, params));
            out.push_str(&emit_vm_body(obj, &file.const_pools, "    ", false)?);
            out.push_str("  }\n");
        }
        CT_FUNCTION => {
            let name = obj.name.as_deref().unwrap_or("");
            let params = emit_function_params(obj)?;
            out.push_str(&format!("  function __tjs2dec_holder_{}() {{\n", obj.index));
            out.push_str(&format!("    function {}({}) {{\n", name, params));
            out.push_str(&emit_vm_body(obj, &file.const_pools, "      ", false)?);
            out.push_str("    }\n  }\n");
            out.push_str(&format!(
                "  var __tjs2dec_obj_{} = (__tjs2dec_holder_{}.{} incontextof null);\n",
                obj.index, obj.index, name
            ));
        }
        CT_EXPR_FUNCTION => {
            let params = emit_function_params(obj)?;
            out.push_str(&format!("  var __tjs2dec_obj_{} = (function({}) {{\n", obj.index, params));
            out.push_str(&emit_vm_body(obj, &file.const_pools, "    ", false)?);
            out.push_str("  } incontextof null);\n");
        }
        CT_PROPERTY => {
            let name = obj.name.as_deref().unwrap_or("");
            out.push_str(&format!("  function __tjs2dec_holder_{}() {{\n", obj.index));
            out.push_str(&format!("    property {} {{\n", name));
            if obj.prop_getter >= 0 {
                let getter = &file.objects[obj.prop_getter as usize];
                out.push_str("      getter {\n");
                out.push_str(&emit_vm_body(getter, &file.const_pools, "        ", false)?);
                out.push_str("      }\n");
            }
            if obj.prop_setter >= 0 {
                let setter = &file.objects[obj.prop_setter as usize];
                let params = emit_function_params(setter)?;
                out.push_str(&format!("      setter({}) {{\n", params));
                out.push_str(&emit_vm_body(setter, &file.const_pools, "        ", false)?);
                out.push_str("      }\n");
            }
            out.push_str("    }\n  }\n");
            out.push_str(&format!(
                "  var __tjs2dec_obj_{} = (&(__tjs2dec_holder_{}.{}) incontextof null);\n",
                obj.index, obj.index, name
            ));
        }
        CT_CLASS => {
            let name = obj.name.as_deref().unwrap_or("");
            let (bases, init) = class_emit_parts(file, obj)?;
            out.push_str(&format!("  function __tjs2dec_holder_{}() {{\n", obj.index));
            if bases.is_empty() {
                out.push_str(&format!("    class {} {{\n", name));
            } else {
                out.push_str(&format!("    class {} extends {} {{\n", name, bases.join(", ")));
            }
            if !init.code.is_empty() {
                // A function expression is deliberately used instead of local
                // `var` declarations in the class context: class-context var
                // declarations are instance members and would be observable.
                out.push_str("      (function() {\n");
                out.push_str(&emit_vm_body(&init, &file.const_pools, "        ", true)?);
                out.push_str("      } incontextof this)();\n");
            }
            out.push_str("    }\n  }\n");
            out.push_str(&format!(
                "  var __tjs2dec_obj_{} = (__tjs2dec_holder_{}.{} incontextof null);\n",
                obj.index, obj.index, name
            ));
        }
        CT_PROPERTY_SETTER | CT_PROPERTY_GETTER | CT_SUPER_GETTER => {}
        _ => unreachable!(),
    }
    Ok(out)
}

fn emit_object_data(obj: &Tjs2Object, pools: &ConstPools) -> Result<String> {
    let mut out = String::new();
    out.push_str(&format!("  var __tjs2dec_data_{} = [\n", obj.index));
    for (di, v) in obj.data.iter().enumerate() {
        out.push_str("    ");
        out.push_str(&variant_to_tjs(v, pools, obj.index)?);
        if di + 1 == obj.data.len() {
            out.push_str("\n");
        } else {
            out.push_str(",\n");
        }
    }
    out.push_str("  ];\n");
    Ok(out)
}

fn emit_vm_body(obj: &Tjs2Object, pools: &ConstPools, pad: &str, allow_end: bool) -> Result<String> {
    let mut out = String::new();
    let neg_reg_max = (obj.max_variable_count + obj.variable_reserve_count).max(2);
    let max_reg = obj.max_frame_count.max(0);
    let mut reg_names = Vec::new();
    for i in 0..=max_reg { reg_names.push(format!("r{}", i)); }
    for i in 1..=neg_reg_max {
        if i != 2 { reg_names.push(format!("rN{}", i)); }
    }
    for chunk in reg_names.chunks(16) {
        out.push_str(pad);
        out.push_str("var ");
        out.push_str(&chunk.join(", "));
        out.push_str(";\n");
    }
    out.push_str(pad);
    out.push_str("rN1 = this;\n");
    let argc = obj.func_decl_arg_count.max(0);
    for k in 3..=neg_reg_max {
        let frame = k - 3;
        out.push_str(pad);
        if frame < argc {
            out.push_str(&format!("rN{} = a{};\n", k, frame));
        } else if obj.func_decl_collapse_base >= 0 && frame == obj.func_decl_collapse_base {
            out.push_str(&format!("rN{} = __tjs2dec_args;\n", k));
        } else {
            out.push_str(&format!("rN{} = void;\n", k));
        }
    }
    out.push_str(pad);
    out.push_str(&format!("var __d = __tjs2dec_data_{};\n", obj.index));
    out.push_str(pad); out.push_str("var __rv = void;\n");
    out.push_str(pad); out.push_str("var __flag = false;\n");
    out.push_str(pad); out.push_str("var ip = 0;\n");
    out.push_str(pad); out.push_str("var __tjs2dec_internal_error = %[];\n");

    if obj.code.is_empty() {
        if allow_end {
            out.push_str(pad); out.push_str("return void;\n");
            return Ok(out);
        }
        bail!("executable emit: executable object {} has empty code", obj.index);
    }

    let cfg = crate::decompile::cfg::Cfg::build(obj)?;
    let root = Vec::<usize>::new();
    out.push_str(&emit_execution_level(obj, pools, &cfg, &root, None, pad, allow_end)?);
    Ok(out)
}

fn reachable_cfg_blocks(cfg: &crate::decompile::cfg::Cfg) -> HashSet<usize> {
    let mut reachable = HashSet::new();
    let mut queue = VecDeque::new();
    reachable.insert(cfg.entry_block);
    queue.push_back(cfg.entry_block);
    while let Some(bid) = queue.pop_front() {
        for &succ in &cfg.blocks[bid].succ {
            if reachable.insert(succ) {
                queue.push_back(succ);
            }
        }
    }
    reachable
}

fn emit_execution_level(
    obj: &Tjs2Object,
    pools: &ConstPools,
    cfg: &crate::decompile::cfg::Cfg,
    stack: &[usize],
    active_handler: Option<usize>,
    pad: &str,
    allow_end: bool,
) -> Result<String> {
    let mut out = String::new();
    let reachable = reachable_cfg_blocks(cfg);
    let active_name = active_handler.map(|h| format!("__tjs2dec_level_{}", h));
    if let Some(name) = &active_name {
        out.push_str(pad); out.push_str(&format!("var {} = true;\n", name));
    }
    out.push_str(pad);
    if let Some(name) = &active_name {
        out.push_str(&format!("while ({}) {{\n", name));
    } else {
        out.push_str("while (true) {\n");
    }
    let p1 = format!("{}  ", pad);
    let p2 = format!("{}    ", pad);
    out.push_str(&p1); out.push_str("switch (ip) {\n");

    let mut pc = 0usize;
    while pc < obj.code.len() {
        let bid = cfg.blocks.iter().find_map(|b| {
            b.insns.iter().any(|insn| insn.pc == pc).then_some(b.id)
        }).ok_or_else(|| anyhow::anyhow!(
            "executable emit: object {} pc {} is not in the CFG", obj.index, pc
        ))?;
        let bstack = &cfg.block_handler_stack[bid];
        let size = insn_len(&obj.code, pc)?;
        if reachable.contains(&bid) && bstack.as_slice() == stack {
            let op = obj.code[pc];
            if op == vm::VM_ENTRY {
                let region = cfg.try_regions.iter().find(|r| r.entry_pc == pc).ok_or_else(|| anyhow::anyhow!(
                    "executable emit: missing try-region descriptor for ENTRY at object {} pc {}", obj.index, pc
                ))?;
                let mut child_stack = stack.to_vec();
                child_stack.push(region.id);
                out.push_str(&p2); out.push_str(&format!("case {}:\n", pc));
                out.push_str(&p2); out.push_str(&format!("  ip = {};\n", pc + size));
                out.push_str(&p2); out.push_str("  try {\n");
                out.push_str(&emit_execution_level(obj, pools, cfg, &child_stack, Some(region.id), &format!("{}    ", p2), allow_end)?);
                out.push_str(&p2); out.push_str("  }\n");
                out.push_str(&p2); out.push_str("  catch (__e) {\n");
                out.push_str(&p2); out.push_str("    if (__e === __tjs2dec_internal_error) throw __e;\n");
                out.push_str(&p2); out.push_str(&format!("    {} = __e;\n", reg_name(region.ex_reg)));
                out.push_str(&p2); out.push_str(&format!("    ip = {};\n", region.catch_pc));
                out.push_str(&p2); out.push_str("  }\n");
                out.push_str(&p2); out.push_str("  continue;\n");
            } else if op == vm::VM_EXTRY || (op == vm::VM_RET && active_handler.is_some()) {
                let Some(name) = &active_name else {
                    bail!("executable emit: execution-level exit {} at object {} pc {} without active handler", vm::name(op), obj.index, pc);
                };
                out.push_str(&p2); out.push_str(&format!("case {}:\n", pc));
                out.push_str(&p2); out.push_str(&format!("  ip = {};\n", pc + size));
                out.push_str(&p2); out.push_str(&format!("  {} = false;\n", name));
                out.push_str(&p2); out.push_str("  continue;\n");
            } else {
                out.push_str(&emit_case(obj, pools, pc, size)?);
            }
        }
        pc += size;
    }

    if active_handler.is_none() && allow_end {
        out.push_str(&p2); out.push_str(&format!("case {}:\n", obj.code.len()));
        out.push_str(&p2); out.push_str("  return void;\n");
    }
    out.push_str(&p2); out.push_str("default:\n");
    out.push_str(&p2); out.push_str("  throw __tjs2dec_internal_error;\n");
    out.push_str(&p1); out.push_str("}\n");
    out.push_str(pad); out.push_str("}\n");
    Ok(out)
}

fn class_emit_parts(file: &Tjs2File, obj: &Tjs2Object) -> Result<(Vec<String>, Tjs2Object)> {
    let c = &obj.code;
    let mut pc = 0usize;
    ensure(c, pc, 3)?;
    if c[pc] != vm::VM_CONST {
        bail!("executable emit: class {} lacks canonical CONST prefix", obj.index);
    }
    let class_reg = c[pc + 1];
    let data_idx = c[pc + 2];
    if data_idx < 0 {
        bail!("executable emit: class {} has negative name data index {}", obj.index, data_idx);
    }
    let expected = obj.name.as_deref().unwrap_or("");
    let actual = match obj.data.get(data_idx as usize) {
        Some(Variant::String(si)) => file.const_pools.strings.get(*si as usize).map(|s| s.as_str()),
        _ => None,
    }.ok_or_else(|| anyhow::anyhow!("executable emit: class {} name CONST is not a string", obj.index))?;
    if actual != expected {
        bail!("executable emit: class {} prefix name {:?} != {:?}", obj.index, actual, expected);
    }
    pc += 3;
    ensure(c, pc, 3)?;
    if c[pc] != vm::VM_ADDCI || c[pc + 1] != -1 || c[pc + 2] != class_reg {
        bail!("executable emit: class {} has non-canonical ADDCI prefix", obj.index);
    }
    pc += 3;
    ensure(c, pc, 2)?;
    if c[pc] != vm::VM_CL || c[pc + 1] != class_reg {
        bail!("executable emit: class {} has non-canonical CL prefix", obj.index);
    }
    pc += 2;

    let mut bases = Vec::new();
    while pc < c.len() && c[pc] != vm::VM_REGMEMBER {
        let (base, fn_reg, next_pc) = if c[pc] == vm::VM_GPD {
            ensure(c, pc, 4)?;
            if c[pc + 2] != -2 {
                bail!("executable emit: class {} superclass GPD is not scope-proxy based at pc {}", obj.index, pc);
            }
            let name = direct_data_identifier(obj, &file.const_pools, c[pc + 3], pc)?;
            (name, c[pc + 1], pc + 4)
        } else if c[pc] == vm::VM_GLOBAL {
            ensure(c, pc, 2)?;
            let gr = c[pc + 1];
            let gp = pc + 2;
            ensure(c, gp, 4)?;
            if c[gp] != vm::VM_GPD || c[gp + 2] != gr {
                bail!("executable emit: class {} malformed global superclass lookup at pc {}", obj.index, pc);
            }
            let name = direct_data_identifier(obj, &file.const_pools, c[gp + 3], gp)?;
            (format!("(global).{}", name), c[gp + 1], gp + 4)
        } else {
            bail!("executable emit: class {} unexpected opcode {} before REGMEMBER at pc {}", obj.index, vm::name(c[pc]), pc);
        };
        pc = next_pc;
        ensure(c, pc, 3)?;
        if c[pc] != vm::VM_CHGTHIS || c[pc + 1] != fn_reg || c[pc + 2] != -1 {
            bail!("executable emit: class {} malformed superclass CHGTHIS at pc {}", obj.index, pc);
        }
        pc += 3;
        ensure(c, pc, 4)?;
        if c[pc] != vm::VM_CALL || c[pc + 1] != 0 || c[pc + 2] != fn_reg || c[pc + 3] != 0 || insn_len(c, pc)? != 4 {
            bail!("executable emit: class {} malformed superclass CALL at pc {}", obj.index, pc);
        }
        pc += 4;
        bases.push(base);
    }
    if pc >= c.len() || c[pc] != vm::VM_REGMEMBER {
        bail!("executable emit: class {} has no canonical REGMEMBER", obj.index);
    }
    pc += 1;

    let getter_bases = strict_super_getter_exprs(file, obj)?;
    if getter_bases != bases {
        bail!("executable emit: class {} prefix bases {:?} != superclass getter {:?}", obj.index, bases, getter_bases);
    }

    if c.len() < pc + 3 || c[c.len() - 3] != vm::VM_SRV || c[c.len() - 2] != 0 || c[c.len() - 1] != vm::VM_RET {
        bail!("executable emit: class {} lacks canonical final SRV %0; RET", obj.index);
    }
    let end = c.len() - 3;
    let mut q = pc;
    while q < end {
        let op = c[q];
        if matches!(op, x if x == vm::VM_RET || x == vm::VM_ADDCI || x == vm::VM_REGMEMBER) {
            bail!("executable emit: class {} initializer contains unexpected {} at pc {}", obj.index, vm::name(op), q);
        }
        q += insn_len(c, q)?;
    }
    if q != end {
        bail!("executable emit: class {} initializer does not end on instruction boundary", obj.index);
    }

    let mut init = obj.clone();
    init.code = c[pc..end].to_vec();
    init.scgetterps.clear();
    init.properties.clear();
    Ok((bases, init))
}

fn strict_super_getter_exprs(file: &Tjs2File, class: &Tjs2Object) -> Result<Vec<String>> {
    if class.super_class_getter < 0 { return Ok(Vec::new()); }
    let gi = class.super_class_getter as usize;
    if gi >= file.objects.len() {
        bail!("executable emit: class {} superclass getter {} out of range", class.index, gi);
    }
    let g = &file.objects[gi];
    if g.context_type != CT_SUPER_GETTER || g.parent != class.index as i32 {
        bail!("executable emit: class {} malformed superclass getter {}", class.index, gi);
    }
    if g.scgetterps.is_empty() {
        bail!("executable emit: superclass getter {} has no scgetterps", gi);
    }
    let starts: Vec<usize> = g.scgetterps.iter().map(|v| *v as usize).collect();
    if starts.iter().any(|p| *p >= g.code.len()) || starts.windows(2).any(|w| w[0] >= w[1]) {
        bail!("executable emit: superclass getter {} has invalid/non-increasing scgetterps {:?}", gi, g.scgetterps);
    }
    let mut out = Vec::new();
    for (n, &start) in starts.iter().enumerate() {
        let end = starts.get(n + 1).copied().unwrap_or(g.code.len());
        let c = &g.code[start..end];
        let mut pc = 0usize;
        let expr;
        if c.get(0).copied() == Some(vm::VM_GPD) {
            ensure(c, 0, 4)?;
            if c[2] != -2 { bail!("executable emit: superclass getter {} slice {} is not scope-proxy GPD", gi, n); }
            let dst = c[1];
            expr = direct_data_identifier(g, &file.const_pools, c[3], start)?;
            pc = 4;
            ensure(c, pc, 2)?;
            if c[pc] != vm::VM_SRV || c[pc + 1] != dst { bail!("executable emit: superclass getter {} slice {} malformed SRV", gi, n); }
            pc += 2;
        } else if c.get(0).copied() == Some(vm::VM_GLOBAL) {
            ensure(c, 0, 2)?;
            let gr = c[1];
            pc = 2;
            ensure(c, pc, 4)?;
            if c[pc] != vm::VM_GPD || c[pc + 2] != gr { bail!("executable emit: superclass getter {} slice {} malformed global GPD", gi, n); }
            let dst = c[pc + 1];
            let name = direct_data_identifier(g, &file.const_pools, c[pc + 3], start + pc)?;
            expr = format!("(global).{}", name);
            pc += 4;
            ensure(c, pc, 2)?;
            if c[pc] != vm::VM_SRV || c[pc + 1] != dst { bail!("executable emit: superclass getter {} slice {} malformed global SRV", gi, n); }
            pc += 2;
        } else {
            bail!("executable emit: superclass getter {} slice {} has unsupported prefix", gi, n);
        }
        ensure(c, pc, 1)?;
        if c[pc] != vm::VM_RET { bail!("executable emit: superclass getter {} slice {} lacks RET", gi, n); }
        pc += 1;
        if pc < c.len() && c[pc] == vm::VM_NOP { pc += 1; }
        if pc != c.len() { bail!("executable emit: superclass getter {} slice {} has trailing code", gi, n); }
        out.push(expr);
    }
    Ok(out)
}

fn direct_data_identifier(obj: &Tjs2Object, pools: &ConstPools, data_idx: i32, pc: usize) -> Result<String> {
    if data_idx < 0 {
        bail!("executable emit: object {} pc {} has negative data index {}", obj.index, pc, data_idx);
    }
    let Some(Variant::String(si)) = obj.data.get(data_idx as usize) else {
        bail!("executable emit: object {} pc {} direct member key is not a string", obj.index, pc);
    };
    let name = pools.strings.get(*si as usize).ok_or_else(|| anyhow::anyhow!(
        "executable emit: object {} pc {} string pool index {} out of range", obj.index, pc, si
    ))?;
    require_decl_identifier(name, obj.index, "member")?;
    Ok(name.clone())
}

fn emit_result_expr(out: &mut String, dst: i32, expr: &str) {
    if dst == 0 {
        out.push_str(&format!("          {};\n", expr));
    } else {
        out.push_str(&format!("          {} = {};\n", reg_name(dst), expr));
    }
}

fn data_ident<'a>(obj: &'a Tjs2Object, pools: &'a ConstPools, data_idx: i32) -> Option<&'a str> {
    let Variant::String(si) = obj.data.get(data_idx as usize)? else { return None; };
    let s = pools.strings.get(*si as usize)?.as_str();
    let mut chars = s.chars();
    let first = chars.next()?;
    if !(first == '_' || first.is_ascii_alphabetic()) { return None; }
    if !chars.all(|c| c == '_' || c.is_ascii_alphanumeric()) { return None; }
    Some(s)
}


/// Names introduced by the VM replayer are lexical bindings.  A scope-proxy
/// access must never be emitted as a bare identifier when that identifier
/// would resolve to one of these bindings instead of the original this/global
/// proxy lookup.
fn is_emit_reserved_ident(s: &str) -> bool {
    if s == "ip" || s.starts_with("__tjs2dec_") || s == "__d" || s == "__rv"
        || s == "__flag" || s == "__try" || s == "__get_reg" || s == "__set_reg"
        || s == "__this" || s == "__e" || s == "__h" || s == "__k" || s == "__t"
        || s == "__p" || s == "__a" || s == "__b" || s == "__tmp"
    {
        return true;
    }
    fn decimal_suffix(s: &str, prefix: &str) -> bool {
        let Some(rest) = s.strip_prefix(prefix) else { return false; };
        !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit())
    }
    decimal_suffix(s, "r") || decimal_suffix(s, "rN") || decimal_suffix(s, "a")
}

fn is_tjs_keyword(s: &str) -> bool {
    matches!(
        s,
        "break" | "continue" | "const" | "catch" | "class" | "case" | "debugger"
            | "default" | "delete" | "do" | "else" | "enum" | "export" | "extends" | "finally"
            | "for" | "function" | "global" | "if" | "import" | "in" | "incontextof"
            | "instanceof" | "int" | "invalidate" | "isvalid" | "new" | "octet"
            | "property" | "private" | "protected" | "public" | "real" | "return"
            | "goto" | "Infinity" | "NaN"
            | "static" | "string" | "super" | "switch" | "synchronized" | "this"
            | "throw" | "try" | "typeof" | "var" | "void" | "while" | "with"
            | "true" | "false" | "null"
    )
}

fn format_call_args(
    code: &[i32],
    pc: usize,
    start: usize,
    argc: i32,
    r: &impl Fn(i32) -> String,
) -> Result<String> {
    if argc == -1 { return Ok("...".to_string()); }
    if argc == -2 {
        let num = code.get(pc + start).copied().ok_or_else(|| anyhow::anyhow!("truncated FAT argument count at pc {}", pc))?.max(0) as usize;
        ensure(code, pc, start + 1 + num * 2)?;
        let mut args = Vec::with_capacity(num);
        for j in 0..num {
            let ty = code[pc + start + 1 + j * 2];
            let v = code[pc + start + 2 + j * 2];
            match ty {
                FAT_NORMAL => args.push(r(v)),
                FAT_EXPAND => args.push(format!("{}*", r(v))),
                FAT_UNNAMED_EXPAND => args.push("*".to_string()),
                _ => bail!("bad FAT argument type {} at pc {}", ty, pc),
            }
        }
        return Ok(args.join(", "));
    }
    if argc < 0 { bail!("unknown negative argc {} at pc {}", argc, pc); }
    let n = argc as usize;
    ensure(code, pc, start + n)?;
    Ok((0..n).map(|j| r(code[pc + start + j])).collect::<Vec<_>>().join(", "))
}

fn emit_function_params(obj: &Tjs2Object) -> Result<String> {
    let n = obj.func_decl_arg_count.max(0) as usize;
    let mut params = (0..n).map(|i| format!("a{}", i)).collect::<Vec<_>>();
    let mut uses_unnamed = obj.func_decl_unnamed_arg_array_base > 0;
    let mut pc = 0usize;
    while pc < obj.code.len() {
        let op = obj.code[pc];
        let size = insn_len(&obj.code, pc)?;
        if matches!(op, x if x == vm::VM_CALL || x == vm::VM_NEW || x == vm::VM_CALLD || x == vm::VM_CALLI) {
            let header = if op == vm::VM_CALL || op == vm::VM_NEW { 4usize } else { 5usize };
            if obj.code.get(pc + header - 1).copied() == Some(-2) {
                let count = obj.code.get(pc + header).copied().unwrap_or(0).max(0) as usize;
                for i in 0..count {
                    if obj.code.get(pc + header + 1 + i * 2).copied() == Some(FAT_UNNAMED_EXPAND) {
                        uses_unnamed = true;
                    }
                }
            }
        }
        pc += size;
    }
    if obj.func_decl_collapse_base >= 0 {
        if obj.func_decl_collapse_base as usize != n {
            bail!("executable emit: unexpected named collapse base {} != arg count {} in object {}", obj.func_decl_collapse_base, n, obj.index);
        }
        params.push("__tjs2dec_args*".to_string());
    } else if uses_unnamed {
        params.push("*".to_string());
    }
    Ok(params.join(", "))
}

fn emit_op2_prop(
    out: &mut String,
    obj: &Tjs2Object,
    pools: &ConstPools,
    code: &[i32],
    pc: usize,
    kind: i32,
    r: &impl Fn(i32) -> String,
    op: &str,
) -> Result<()> {
    match kind {
        0 => {
            ensure(code, pc, 3)?;
            let lhs = r(code[pc + 1]);
            let rhs = r(code[pc + 2]);
            out.push_str(&format!("          {lhs} {op}= {rhs};\n"));
        }
        1 => {
            ensure(code, pc, 5)?;
            let dst = code[pc + 1];
            let target = direct_property_target(obj, pools, code[pc + 2], code[pc + 3], r, pc)?;
            let rhs = r(code[pc + 4]);
            emit_result_expr(out, dst, &format!("({target} {op}= {rhs})"));
        }
        2 => {
            ensure(code, pc, 5)?;
            let dst = code[pc + 1];
            let objr = code[pc + 2];
            if objr == -2 {
                bail!("executable emit: dynamic compound operation through VM scope proxy is not exactly representable (object {} pc {})", obj.index, pc);
            }
            let target = format!("{}[{}]", r(objr), r(code[pc + 3]));
            let rhs = r(code[pc + 4]);
            emit_result_expr(out, dst, &format!("({target} {op}= {rhs})"));
        }
        3 => {
            ensure(code, pc, 4)?;
            let dst = code[pc + 1];
            let target = format!("*{}", r(code[pc + 2]));
            let rhs = r(code[pc + 3]);
            emit_result_expr(out, dst, &format!("({target} {op}= {rhs})"));
        }
        _ => bail!(
            "executable emit: unknown compound-operation opcode kind {} at object {} pc {}",
            kind,
            obj.index,
            pc
        ),
    }
    Ok(())
}

fn direct_property_target(
    obj: &Tjs2Object,
    pools: &ConstPools,
    objr: i32,
    key: i32,
    r: &impl Fn(i32) -> String,
    pc: usize,
) -> Result<String> {
    let name = data_ident(obj, pools, key).ok_or_else(|| anyhow::anyhow!(
        "executable emit: direct-property opcode at object {} pc {} has a member name that cannot be emitted as an exact direct TJS member access",
        obj.index,
        pc
    ))?;
    if objr == -2 {
        if is_emit_reserved_ident(name) || is_tjs_keyword(name) {
            bail!(
                "executable emit: scope-proxy member {:?} at object {} pc {} collides with generated/local TJS syntax",
                name,
                obj.index,
                pc
            );
        }
        Ok(name.to_string())
    } else {
        Ok(format!("{}.{}", r(objr), name))
    }
}

fn emit_incdec_prop(
    out: &mut String,
    obj: &Tjs2Object,
    pools: &ConstPools,
    code: &[i32],
    pc: usize,
    kind: i32,
    r: &impl Fn(i32) -> String,
    increment: bool,
) -> Result<()> {
    let prefix = if increment { "++" } else { "--" };
    match kind {
        0 => {
            ensure(code, pc, 2)?;
            out.push_str(&format!("          {prefix}{};\n", r(code[pc + 1])));
        }
        1 => {
            ensure(code, pc, 4)?;
            let dst = code[pc + 1];
            let target = direct_property_target(obj, pools, code[pc + 2], code[pc + 3], r, pc)?;
            emit_result_expr(out, dst, &format!("{prefix}{target}"));
        }
        2 => {
            ensure(code, pc, 4)?;
            let dst = code[pc + 1];
            let objr = code[pc + 2];
            if objr == -2 {
                bail!("executable emit: dynamic increment/decrement through VM scope proxy is not exactly representable (object {} pc {})", obj.index, pc);
            }
            let target = format!("{}[{}]", r(objr), r(code[pc + 3]));
            emit_result_expr(out, dst, &format!("{prefix}{target}"));
        }
        3 => {
            ensure(code, pc, 3)?;
            let dst = code[pc + 1];
            let target = format!("*{}", r(code[pc + 2]));
            emit_result_expr(out, dst, &format!("{prefix}{target}"));
        }
        _ => bail!(
            "executable emit: unknown increment/decrement opcode kind {} at object {} pc {}",
            kind,
            obj.index,
            pc
        ),
    }
    Ok(())
}

fn emit_case(
    obj: &Tjs2Object,
    pools: &ConstPools,
    pc: usize,
    size: usize,
) -> Result<String> {
    let code = &obj.code;
    let op = code[pc];

    let mut out = String::new();
    out.push_str(&format!("        case {}:\n", pc));

    // Helpers to format registers.
    let r = |idx: i32| -> String { reg_name(idx) };

    // Core opcodes.
    match op {
        x if x == vm::VM_NOP => {
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x == vm::VM_DEBUGGER => {
            out.push_str("          debugger;\n");
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }

        // Data/regs
        x if x == vm::VM_CONST => {
            ensure(code, pc, 3)?;
            let dst = code[pc + 1];
            let src = code[pc + 2];
            out.push_str(&format!("          {} = __d[{}];\n", r(dst), src));
            out.push_str("          ip += 3;\n          continue;\n");
        }
        x if x == vm::VM_CP => {
            ensure(code, pc, 3)?;
            let dst = code[pc + 1];
            let src = code[pc + 2];
            out.push_str(&format!("          {} = {};\n", r(dst), r(src)));
            out.push_str("          ip += 3;\n          continue;\n");
        }
        x if x == vm::VM_CL => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = void;\n", r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_CCL => {
            // CCL operands are compile-time register indices.  Emit each clear
            // directly; a synthetic dynamic register accessor is unnecessary
            // and would introduce extra observable helper behavior.
            ensure(code, pc, 3)?;
            let base = code[pc + 1];
            let count = code[pc + 2];
            if count < 0 {
                bail!("executable emit: negative CCL count {} in object {} pc {}", count, obj.index, pc);
            }
            for j in 0..count {
                let rr = base + j;
                if rr == -2 {
                    bail!("executable emit: CCL attempts to clear VM scope-proxy register in object {} pc {}", obj.index, pc);
                }
                out.push_str(&format!("          {} = void;\n", r(rr)));
            }
            out.push_str("          ip += 3;\n          continue;\n");
        }

        // Flag ops
        x if x == vm::VM_TT => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!(
                "          __flag = {} ? true : false;\n",
                r(rr)
            ));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_TF => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!(
                "          __flag = !({});\n",
                r(rr)
            ));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_NF => {
            ensure(code, pc, 1)?;
            out.push_str("          __flag = !__flag;\n");
            out.push_str("          ip += 1;\n          continue;\n");
        }
        x if x == vm::VM_SETF => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = __flag;\n", r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_SETNF => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = !__flag;\n", r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }

        // Comparisons -> __flag
        x if x == vm::VM_CEQ => {
            ensure(code, pc, 3)?;
            let a = code[pc + 1];
            let b = code[pc + 2];
            out.push_str(&format!("          __flag = ({} == {});\n", r(a), r(b)));
            out.push_str("          ip += 3;\n          continue;\n");
        }
        x if x == vm::VM_CDEQ => {
            ensure(code, pc, 3)?;
            let a = code[pc + 1];
            let b = code[pc + 2];
            out.push_str(&format!("          __flag = ({} === {});\n", r(a), r(b)));
            out.push_str("          ip += 3;\n          continue;\n");
        }
        x if x == vm::VM_CLT => {
            ensure(code, pc, 3)?;
            let a = code[pc + 1];
            let b = code[pc + 2];
            out.push_str(&format!("          __flag = ({} < {});\n", r(a), r(b)));
            out.push_str("          ip += 3;\n          continue;\n");
        }
        x if x == vm::VM_CGT => {
            ensure(code, pc, 3)?;
            let a = code[pc + 1];
            let b = code[pc + 2];
            out.push_str(&format!("          __flag = ({} > {});\n", r(a), r(b)));
            out.push_str("          ip += 3;\n          continue;\n");
        }
        x if x == vm::VM_CHKINS => {
            ensure(code, pc, 3)?;
            let value = code[pc + 1];
            let class = code[pc + 2];
            out.push_str(&format!(
                "          {} = ({} instanceof {});\n",
                r(value),
                r(value),
                r(class)
            ));
            out.push_str("          ip += 3;\n          continue;\n");
        }

        // Jumps
        x if x == vm::VM_JMP => {
            ensure(code, pc, 2)?;
            let tgt = pc as i32 + code[pc + 1];
            out.push_str(&format!("          ip = {};\n          continue;\n", tgt));
        }
        x if x == vm::VM_JF => {
            ensure(code, pc, 2)?;
            let tgt = pc as i32 + code[pc + 1];
            out.push_str(&format!(
                "          if (__flag) {{ ip = {}; }} else {{ ip += 2; }}\n          continue;\n",
                tgt
            ));
        }
        x if x == vm::VM_JNF => {
            ensure(code, pc, 2)?;
            let tgt = pc as i32 + code[pc + 1];
            out.push_str(&format!(
                "          if (!__flag) {{ ip = {}; }} else {{ ip += 2; }}\n          continue;\n",
                tgt
            ));
        }

        // Unary in-place
        x if x == vm::VM_LNOT => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!(
                "          {} = !({});\n",
                r(rr),
                r(rr)
            ));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_BNOT => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = ~({});\n", r(rr), r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_CHS => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = -({});\n", r(rr), r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_TYPEOF => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = typeof({});\n", r(rr), r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_EVAL => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = {}!;\n", r(rr), r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_EEXP => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            // EEXP is the no-result form of TJS' postfix expression-eval operator.
            // Executing it as a statement preserves the source register.
            out.push_str(&format!("          {}!;\n", r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_ASC => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = #{};\n", r(rr), r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_CHR => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = ${};\n", r(rr), r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_NUM => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = +{};\n", r(rr), r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_INV => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = (invalidate {});\n", r(rr), r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_CHKINV => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = (isvalid {});\n", r(rr), r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_INT => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = int {};\n", r(rr), r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_REAL => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = real {};\n", r(rr), r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_STR => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = string {};\n", r(rr), r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_OCTET => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = octet {};\n", r(rr), r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }

        // Increment/decrement opcodes are VM property operations, not a
        // decomposable get/add/set sequence.  Native pre-increment/decrement
        // compiles back to the same Operation(TJS_OP_INC/DEC) dispatch.
        x if x >= vm::VM_INC && x <= vm::VM_INCP => {
            emit_incdec_prop(&mut out, obj, pools, code, pc, x - vm::VM_INC, &r, true)?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x >= vm::VM_DEC && x <= vm::VM_DECP => {
            emit_incdec_prop(&mut out, obj, pools, code, pc, x - vm::VM_DEC, &r, false)?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }

        // VM_LOR/LAND are compound logical-assignment operations.  Do not
        // lower them to separate reads/writes; that changes property dispatch.
        x if x >= vm::VM_LOR && x <= vm::VM_LORP => {
            emit_op2_prop(&mut out, obj, pools, code, pc, x - vm::VM_LOR, &r, "||")?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x >= vm::VM_LAND && x <= vm::VM_LANDP => {
            emit_op2_prop(&mut out, obj, pools, code, pc, x - vm::VM_LAND, &r, "&&")?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }

        // Other op2_prop groups (P-variant remains special but executable)
        x if x >= vm::VM_BOR && x <= vm::VM_BORP => {
            emit_op2_prop(&mut out, obj, pools, code, pc, x - vm::VM_BOR, &r, "|")?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x >= vm::VM_BXOR && x <= vm::VM_BXORP => {
            emit_op2_prop(&mut out, obj, pools, code, pc, x - vm::VM_BXOR, &r, "^")?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x >= vm::VM_BAND && x <= vm::VM_BANDP => {
            emit_op2_prop(&mut out, obj, pools, code, pc, x - vm::VM_BAND, &r, "&")?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x >= vm::VM_SAR && x <= vm::VM_SARP => {
            emit_op2_prop(&mut out, obj, pools, code, pc, x - vm::VM_SAR, &r, ">>")?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x >= vm::VM_SAL && x <= vm::VM_SALP => {
            emit_op2_prop(&mut out, obj, pools, code, pc, x - vm::VM_SAL, &r, "<<")?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x >= vm::VM_SR && x <= vm::VM_SRP => {
            emit_op2_prop(&mut out, obj, pools, code, pc, x - vm::VM_SR, &r, ">>>")?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x >= vm::VM_ADD && x <= vm::VM_ADDP => {
            emit_op2_prop(&mut out, obj, pools, code, pc, x - vm::VM_ADD, &r, "+")?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x >= vm::VM_SUB && x <= vm::VM_SUBP => {
            emit_op2_prop(&mut out, obj, pools, code, pc, x - vm::VM_SUB, &r, "-")?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x >= vm::VM_MOD && x <= vm::VM_MODP => {
            emit_op2_prop(&mut out, obj, pools, code, pc, x - vm::VM_MOD, &r, "%")?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x >= vm::VM_DIV && x <= vm::VM_DIVP => {
            emit_op2_prop(&mut out, obj, pools, code, pc, x - vm::VM_DIV, &r, "/")?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x >= vm::VM_MUL && x <= vm::VM_MULP => {
            emit_op2_prop(&mut out, obj, pools, code, pc, x - vm::VM_MUL, &r, "*")?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x >= vm::VM_IDIV && x <= vm::VM_IDIVP => {
            emit_op2_prop(&mut out, obj, pools, code, pc, x - vm::VM_IDIV, &r, "\\")?;
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }

        // Delete/typeof member opcodes have dedicated VM dispatch.  Native
        // delete/typeof source expressions compile back to those opcodes; a
        // decomposed get/delete helper does not preserve missing-member and
        // custom-dispatch behavior.
        x if x == vm::VM_DELD || x == vm::VM_TYPEOFD => {
            ensure(code, pc, 4)?;
            let dst = code[pc + 1];
            let target = direct_property_target(obj, pools, code[pc + 2], code[pc + 3], &r, pc)?;
            let expr = if x == vm::VM_DELD {
                format!("delete {target}")
            } else {
                format!("typeof {target}")
            };
            emit_result_expr(&mut out, dst, &expr);
            out.push_str("          ip += 4;\n          continue;\n");
        }
        x if x == vm::VM_DELI || x == vm::VM_TYPEOFI => {
            ensure(code, pc, 4)?;
            let dst = code[pc + 1];
            let objr = code[pc + 2];
            if objr == -2 {
                bail!("executable emit: dynamic delete/typeof through VM scope proxy is not exactly representable (object {} pc {})", obj.index, pc);
            }
            let target = format!("{}[{}]", r(objr), r(code[pc + 3]));
            let expr = if x == vm::VM_DELI {
                format!("delete {target}")
            } else {
                format!("typeof {target}")
            };
            emit_result_expr(&mut out, dst, &expr);
            out.push_str("          ip += 4;\n          continue;\n");
        }

        // gpd/gpds, gpi/gpis. %-2 is the scope proxy; static access
        // through it is emitted as a bare identifier so TJS recreates the
        // this-then-global lookup. Dynamic proxy access has no exact source spelling.
        x if x == vm::VM_GPD || x == vm::VM_GPDS => {
            ensure(code, pc, 4)?;
            let dst = code[pc + 1];
            let objr = code[pc + 2];
            let key = code[pc + 3];
            let target = direct_property_target(obj, pools, objr, key, &r, pc)?;
            let expr = if x == vm::VM_GPDS {
                format!("&({target})")
            } else {
                target
            };
            emit_result_expr(&mut out, dst, &expr);
            out.push_str("          ip += 4;\n          continue;\n");
        }
        x if x == vm::VM_GPI || x == vm::VM_GPIS => {
            ensure(code, pc, 4)?;
            let dst = code[pc + 1];
            let objr = code[pc + 2];
            let keyr = code[pc + 3];
            if objr == -2 {
                bail!("executable emit: dynamic GPI/GPIS through VM scope proxy is not exactly representable (object {} pc {})", obj.index, pc);
            }
            let expr = if x == vm::VM_GPIS {
                format!("&({}[{}])", r(objr), r(keyr))
            } else {
                format!("{}[{}]", r(objr), r(keyr))
            };
            emit_result_expr(&mut out, dst, &expr);
            out.push_str("          ip += 4;\n          continue;\n");
        }

        // spd/spds/spde/spdeh, spi/spis/spie
        x if x == vm::VM_SPD || x == vm::VM_SPDS || x == vm::VM_SPDE || x == vm::VM_SPDEH => {
            ensure(code, pc, 4)?;
            let objr = code[pc + 1];
            let key = code[pc + 2];
            let valr = code[pc + 3];
            if x == vm::VM_SPDEH {
                bail!("executable emit: VM_SPDEH hidden-member semantics are not expressible as an ordinary TJS assignment (object {} pc {})", obj.index, pc);
            }
            if objr == -2 && x == vm::VM_SPDE {
                bail!("executable emit: VM_SPDE member-ensure on the scope proxy cannot be reproduced by a bare assignment (object {} pc {})", obj.index, pc);
            }
            if objr != -2 && x == vm::VM_SPD {
                bail!("executable emit: VM_SPD without MEMBERENSURE on a non-proxy object has no exact ordinary assignment spelling (object {} pc {})", obj.index, pc);
            }
            let target = direct_property_target(obj, pools, objr, key, &r, pc)?;
            if x == vm::VM_SPDS {
                out.push_str(&format!("          &({target}) = {};\n", r(valr)));
            } else {
                out.push_str(&format!("          {target} = {};\n", r(valr)));
            }
            out.push_str("          ip += 4;\n          continue;\n");
        }
        x if x == vm::VM_SPI || x == vm::VM_SPIS || x == vm::VM_SPIE => {
            ensure(code, pc, 4)?;
            let objr = code[pc + 1];
            let keyr = code[pc + 2];
            let valr = code[pc + 3];
            if objr == -2 {
                bail!("executable emit: dynamic SPI/SPIS/SPIE through VM scope proxy is not exactly representable (object {} pc {})", obj.index, pc);
            }
            if x == vm::VM_SPI {
                bail!("executable emit: VM_SPI without MEMBERENSURE on a non-proxy object has no exact ordinary assignment spelling (object {} pc {})", obj.index, pc);
            }
            if x == vm::VM_SPIS {
                out.push_str(&format!("          &({}[{}]) = {};\n", r(objr), r(keyr), r(valr)));
            } else {
                out.push_str(&format!("          {}[{}] = {};\n", r(objr), r(keyr), r(valr)));
            }
            out.push_str("          ip += 4;\n          continue;\n");
        }

        // call/callD/callI/new.  Preserve the VM's FAT argument forms in
        // native TJS syntax instead of rebuilding an Array and calling apply();
        // that old approximation changed array-expansion and closure ObjThis semantics.
        x if x == vm::VM_CALL || x == vm::VM_NEW => {
            ensure(code, pc, size)?;
            let dst = code[pc + 1];
            let func = code[pc + 2];
            let argc = code[pc + 3];
            let args = format_call_args(code, pc, 4, argc, &r)?;
            let expr = if x == vm::VM_NEW {
                format!("new {}({})", r(func), args)
            } else {
                format!("{}({})", r(func), args)
            };
            emit_result_expr(&mut out, dst, &expr);
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x == vm::VM_CALLD => {
            ensure(code, pc, size)?;
            let dst = code[pc + 1];
            let objr = code[pc + 2];
            let key = code[pc + 3];
            let argc = code[pc + 4];
            let args = format_call_args(code, pc, 5, argc, &r)?;
            let target = direct_property_target(obj, pools, objr, key, &r, pc)?;
            let expr = format!("{target}({args})");
            emit_result_expr(&mut out, dst, &expr);
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }
        x if x == vm::VM_CALLI => {
            ensure(code, pc, size)?;
            let dst = code[pc + 1];
            let objr = code[pc + 2];
            let keyr = code[pc + 3];
            if objr == -2 {
                bail!("executable emit: dynamic CALLI through VM scope proxy is not exactly representable (object {} pc {})", obj.index, pc);
            }
            let argc = code[pc + 4];
            let args = format_call_args(code, pc, 5, argc, &r)?;
            let expr = format!("{}[{}]({})", r(objr), r(keyr), args);
            emit_result_expr(&mut out, dst, &expr);
            out.push_str(&format!("          ip += {};\n          continue;\n", size));
        }

        // setp/getp: property handler (unary '*' operator)
        x if x == vm::VM_SETP || x == vm::VM_GETP => {
            ensure(code, pc, 3)?;
            let a = code[pc + 1];
            let b = code[pc + 2];
            if op == vm::VM_GETP {
                // getp %dst, %propobj  => dst = *propobj
                if a != 0 {
                    out.push_str(&format!(
                        "          {} = *{};
",
                        r(a),
                        r(b)
                    ));
                } else {
                    out.push_str(&format!(
                        "          var __tmp = *{};
",
                        r(b)
                    ));
                }
            } else {
                // setp %propobj, %src  => *propobj = src
                out.push_str(&format!(
                    "          *{} = {};
",
                    r(a),
                    r(b)
                ));
            }
            out.push_str(
                "          ip += 3;
          continue;
",
            );
        }

        // srv/global/throw
        x if x == vm::VM_SRV => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          __rv = {};\n", r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_GLOBAL => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          {} = global;\n", r(rr)));
            out.push_str("          ip += 2;\n          continue;\n");
        }
        x if x == vm::VM_THROW => {
            ensure(code, pc, 2)?;
            let rr = code[pc + 1];
            out.push_str(&format!("          throw {};\n", r(rr)));
        }

        // VM_ENTRY executes the protected bytecode recursively and converts a
        // caught host/TJS exception into the VM's exception object before
        // writing the handler register.  A source-level catch-stack emulator is
        // observably different, so refuse until the region is structurally
        // reconstructed as an exact TJS try/catch.
        x if x == vm::VM_ENTRY => {
            ensure(code, pc, 3)?;
            bail!("executable emit: VM_ENTRY exception-region semantics are not yet proven source-equivalent (object {} pc {})", obj.index, pc);
        }
        x if x == vm::VM_EXTRY => {
            ensure(code, pc, 1)?;
            bail!("executable emit: VM_EXTRY without proven structural try reconstruction (object {} pc {})", obj.index, pc);
        }

        // closure/class-instance bookkeeping
        x if x == vm::VM_CHGTHIS => {
            ensure(code, pc, 3)?;
            let dest = code[pc + 1];
            let src = code[pc + 2];
            // VM_CHGTHIS changes the closure's ObjThis; it does not switch the
            // currently executing function's `this`. TJS exposes the same
            // operation through the `incontextof` operator.
            out.push_str(&format!(
                "          {} = ({} incontextof {});\n",
                r(dest),
                r(dest),
                r(src)
            ));
            out.push_str("          ip += 3;\n          continue;\n");
        }
        x if x == vm::VM_ADDCI => {
            ensure(code, pc, 3)?;
            // ADDCI mutates the VM's internal class-instance metadata. There is no
            // faithful ordinary-TJS expression equivalent, so never silently skip
            // it in the executable emitter.
            bail!("executable emit: VM_ADDCI requires class-instance metadata semantics (object {} pc {})", obj.index, pc);
        }
        x if x == vm::VM_REGMEMBER => {
            ensure(code, pc, 1)?;
            // REGMEMBER copies/registers non-static members with closure rebinding
            // inside the VM. Silently treating it as a no-op changes class semantics.
            bail!("executable emit: VM_REGMEMBER requires class member registration/rebinding semantics (object {} pc {})", obj.index, pc);
        }

        // ret
        x if x == vm::VM_RET => {
            ensure(code, pc, 1)?;
            out.push_str("          return __rv;\n");
        }

        _ => {
            bail!("executable emit: unimplemented opcode {} ({}) at object {} pc {}", op, vm::name(op), obj.index, pc);
        }
    }

    Ok(out)
}

fn reg_name(idx: i32) -> String {
    if idx >= 0 {
        format!("r{}", idx)
    } else if idx == -2 {
        "__tjs2dec_unrepresentable_scope_proxy".to_string()
    } else {
        format!("rN{}", -idx)
    }
}

fn variant_to_tjs(v: &Variant, pools: &ConstPools, obj_index: usize) -> Result<String> {
    let text = match v {
        Variant::Void => "void".to_string(),
        Variant::NullObject => "null".to_string(),
        // TYPE_UNKNOWN/default is loader Clear(), i.e. void.
        Variant::Unknown => "void".to_string(),
        Variant::String(i) => {
            let s = pools.strings.get(*i as usize).ok_or_else(|| anyhow::anyhow!(
                "executable emit: string pool index {} out of range in object {}", i, obj_index
            ))?;
            quote_tjs_string(s)
        }
        Variant::Octet(i) => {
            if pools.octets.get(*i as usize).is_none() {
                bail!("executable emit: octet pool index {} out of range in object {}", i, obj_index);
            }
            format!("__tjs2dec_octet_{}", i)
        }
        Variant::Real(i) => {
            let value = pools.doubles.get(*i as usize).copied().ok_or_else(|| anyhow::anyhow!(
                "executable emit: double pool index {} out of range in object {}", i, obj_index
            ))?;
            real_to_tjs(value, obj_index)?
        },
        Variant::Byte(i) => pools.bytes.get(*i as usize).copied().ok_or_else(|| anyhow::anyhow!(
            "executable emit: byte pool index {} out of range in object {}", i, obj_index
        ))?.to_string(),
        Variant::Short(i) => pools.shorts.get(*i as usize).copied().ok_or_else(|| anyhow::anyhow!(
            "executable emit: short pool index {} out of range in object {}", i, obj_index
        ))?.to_string(),
        Variant::Integer(i) => pools.ints.get(*i as usize).copied().ok_or_else(|| anyhow::anyhow!(
            "executable emit: int pool index {} out of range in object {}", i, obj_index
        ))?.to_string(),
        Variant::Long(i) => pools.longs.get(*i as usize).copied().ok_or_else(|| anyhow::anyhow!(
            "executable emit: long pool index {} out of range in object {}", i, obj_index
        ))?.to_string(),
        Variant::InterObject(i) | Variant::InterGenerator(i) => {
            format!("(__tjs2dec_obj_{} incontextof null)", i)
        }
    };
    Ok(text)
}

fn real_to_tjs(value: f64, obj_index: usize) -> Result<String> {
    if value.is_infinite() {
        return Ok(if value.is_sign_negative() {
            "-Infinity".to_string()
        } else {
            "Infinity".to_string()
        });
    }
    if value.is_nan() {
        // TJS2 has a source-level NaN term.  Preserve exactness by accepting
        // only the canonical positive quiet-NaN representation emitted by the
        // reference compiler.  Payload/sign-bearing NaNs remain fail-closed.
        const TJS_CANONICAL_QNAN_BITS: u64 = 0x7ff8_0000_0000_0000;
        if value.to_bits() == TJS_CANONICAL_QNAN_BITS {
            return Ok("NaN".to_string());
        }
        bail!(
            "executable emit: NaN real constant bits=0x{:016x} in object {} are not the canonical TJS NaN representation",
            value.to_bits(),
            obj_index
        );
    }
    // Debug formatting is shortest-roundtrip and preserves the real type of
    // integral-valued doubles (`1.0`, not integer `1`).
    Ok(format!("{:?}", value))
}

fn quote_tjs_string(s: &str) -> String {
    let mut out = String::new();
    out.push('"');
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn ensure(code: &[i32], i: usize, need: usize) -> Result<()> {
    if i + need > code.len() {
        bail!(
            "truncated instruction at {}: need {}, code_len {}",
            i,
            need,
            code.len()
        );
    }
    Ok(())
}

fn insn_len(code: &[i32], pc: usize) -> Result<usize> {
    let op = code[pc];

    if op == vm::VM_CONST {
        return Ok(3);
    }
    for base in [
        vm::VM_CP,
        vm::VM_CEQ,
        vm::VM_CDEQ,
        vm::VM_CLT,
        vm::VM_CGT,
        vm::VM_CHKINS,
        vm::VM_ADDCI,
        vm::VM_CHGTHIS,
    ] {
        if op == base {
            return Ok(3);
        }
    }
    for base in [
        vm::VM_CL,
        vm::VM_SRV,
        vm::VM_GLOBAL,
        vm::VM_THROW,
        vm::VM_TT,
        vm::VM_TF,
        vm::VM_SETF,
        vm::VM_SETNF,
        vm::VM_LNOT,
        vm::VM_BNOT,
        vm::VM_ASC,
        vm::VM_CHR,
        vm::VM_NUM,
        vm::VM_CHS,
        vm::VM_INV,
        vm::VM_CHKINV,
        vm::VM_TYPEOF,
        vm::VM_EVAL,
        vm::VM_EEXP,
        vm::VM_INT,
        vm::VM_REAL,
        vm::VM_STR,
        vm::VM_OCTET,
    ] {
        if op == base {
            return Ok(2);
        }
    }
    if op == vm::VM_CCL {
        return Ok(3);
    }
    for base in [vm::VM_JF, vm::VM_JNF, vm::VM_JMP] {
        if op == base {
            return Ok(2);
        }
    }
    if op == vm::VM_ENTRY {
        return Ok(3);
    }
    for base in [
        vm::VM_RET,
        vm::VM_NOP,
        vm::VM_NF,
        vm::VM_EXTRY,
        vm::VM_REGMEMBER,
        vm::VM_DEBUGGER,
    ] {
        if op == base {
            return Ok(1);
        }
    }
    if op == vm::VM_SETP || op == vm::VM_GETP {
        return Ok(3);
    }
    if op == vm::VM_DELD || op == vm::VM_TYPEOFD {
        return Ok(4);
    }
    if op == vm::VM_DELI || op == vm::VM_TYPEOFI {
        return Ok(4);
    }
    if op == vm::VM_GPD || op == vm::VM_GPDS {
        return Ok(4);
    }
    if op == vm::VM_SPD || op == vm::VM_SPDE || op == vm::VM_SPDEH || op == vm::VM_SPDS {
        return Ok(4);
    }
    if op == vm::VM_GPI || op == vm::VM_GPIS {
        return Ok(4);
    }
    if op == vm::VM_SPI || op == vm::VM_SPIE || op == vm::VM_SPIS {
        return Ok(4);
    }

    // inc/dec variants
    for base in [vm::VM_INC, vm::VM_DEC] {
        if op == base {
            return Ok(2);
        }
        if op == base + 1 {
            return Ok(4);
        }
        if op == base + 2 {
            return Ok(4);
        }
        if op == base + 3 {
            return Ok(3);
        }
    }
    // binary op variants base..base+3
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
        if op == base {
            return Ok(3);
        }
        if op == base + 1 {
            return Ok(5);
        }
        if op == base + 2 {
            return Ok(5);
        }
        if op == base + 3 {
            return Ok(4);
        }
    }

    // call/new and their variable length
    if op == vm::VM_CALL || op == vm::VM_NEW {
        ensure(code, pc, 4)?;
        let argc = code[pc + 3];
        if argc >= 0 {
            return Ok(4 + argc as usize);
        }
        if argc == -1 {
            return Ok(4);
        }
        if argc == -2 {
            ensure(code, pc, 5)?;
            let num = code[pc + 4] as usize;
            return Ok(5 + num * 2);
        }
        return Ok(4);
    }
    if op == vm::VM_CALLD || op == vm::VM_CALLI {
        ensure(code, pc, 5)?;
        let argc = code[pc + 4];
        if argc >= 0 {
            return Ok(5 + argc as usize);
        }
        if argc == -1 {
            return Ok(5);
        }
        if argc == -2 {
            ensure(code, pc, 6)?;
            let num = code[pc + 5] as usize;
            return Ok(6 + num * 2);
        }
        return Ok(5);
    }

    Ok(1)
}

#[cfg(test)]
mod emit_literal_tests {
    use super::{compact_generated_tjs, real_to_tjs};

    #[test]
    fn real_nonfinite_terms_are_exact_and_fail_closed_for_payload_nan() {
        assert_eq!(real_to_tjs(f64::INFINITY, 0).unwrap(), "Infinity");
        assert_eq!(real_to_tjs(f64::NEG_INFINITY, 0).unwrap(), "-Infinity");
        assert_eq!(
            real_to_tjs(f64::from_bits(0x7ff8_0000_0000_0000), 0).unwrap(),
            "NaN"
        );
        assert!(real_to_tjs(f64::from_bits(0x7ff8_0000_0000_0001), 0).is_err());
        assert!(real_to_tjs(f64::from_bits(0xfff8_0000_0000_0000), 0).is_err());
    }

    #[test]
    fn compact_emit_removes_only_layout_whitespace() {
        let src = "  function f() {\n    var x = \" a b \";\n\n    return x;\n  }\n";
        assert_eq!(
            compact_generated_tjs(src),
            "function f() {\nvar x = \" a b \";\nreturn x;\n}\n"
        );
    }
}
