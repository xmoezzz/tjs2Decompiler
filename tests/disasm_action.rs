use std::path::Path;

use tjs2dec::{
    decompile::{dump_hlir_file, dump_ssa_file},
    disasm::disassemble_file,
    load_tjs2_bytecode,
};

#[test]
fn disasm_action_tjs_if_present() {
    let p = Path::new("testcase/Action.tjs");
    if !p.exists() {
        return;
    }
    let buf = std::fs::read(p).expect("read testcase/Action.tjs");
    let file = load_tjs2_bytecode(&buf).expect("parse structured TJS2 bytecode");
    println!("{:#?}", file.const_pools);
    let text = disassemble_file(&file).expect("disassemble");
    println!("{}", text);
    assert!(!text.is_empty());
}

#[test]
fn decompile_action_tjs_if_present() {
    let p = Path::new("testcase/Action.tjs");
    if !p.exists() {
        return;
    }
    let buf = std::fs::read(p).expect("read testcase/Action.tjs");
    let file = load_tjs2_bytecode(&buf).expect("parse structured TJS2 bytecode");

    let tjs = tjs2dec::emit_executable_tjs(&file).expect("emit executable TJS");
    println!("{}", tjs);

    assert!(!tjs.is_empty());
    assert!(tjs.contains("function __tjs2dec_obj_"));
    assert!(tjs.contains("var __tjs2dec_objs"));
}

#[test]
fn ssa_action_tjs_if_present() {
    let p = Path::new("testcase/Action.tjs");
    if !p.exists() {
        return;
    }
    let buf = std::fs::read(p).expect("read testcase/Action.tjs");
    let file = load_tjs2_bytecode(&buf).expect("parse structured TJS2 bytecode");
    let ssa = dump_ssa_file(&file).expect("build SSA");
    println!("{}", ssa);
    assert!(ssa.contains("== object"));

    let hlir = dump_hlir_file(&file).expect("build HLIR");
    println!("{}", hlir);
    assert!(hlir.contains("-- bb"));
}
