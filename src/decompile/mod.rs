pub mod cfg;
pub mod decode;
pub mod hlir;
pub mod ssa;

use anyhow::Result;

use crate::model::Tjs2File;

/// Build CFG + SSA for each object and return a text dump.
///
/// This is a parallel pipeline to the executable-emitter mode.
/// The dump is a developer-facing artifact intended for validation.
pub fn dump_ssa_file(file: &Tjs2File) -> Result<String> {
    let mut out = String::new();
    out.push_str(&format!("toplevel: {}\n", file.toplevel));
    out.push_str(&format!("objects: {}\n\n", file.objects.len()));

    for obj in &file.objects {
        out.push_str(&format!("== object {}: {} ==\n", obj.index, obj.name.as_deref().unwrap_or("<anonymous>")));
        if obj.code.is_empty() {
            out.push_str("  (empty code area; skipped)\n\n");
            continue;
        }
        let cfg = cfg::Cfg::build(obj)?;
        let ssa = ssa::SsaProgram::from_cfg(&cfg)?;
        out.push_str(&ssa.dump());
        out.push('\n');
    }
    Ok(out)
}

/// Build a basic HLIR representation (SSA-backed) and return a dump.
///
/// At this stage, HLIR is intentionally conservative: it keeps side-effects explicit
/// and avoids reordering across potential exception boundaries.
pub fn dump_hlir_file(file: &Tjs2File) -> Result<String> {
    let mut out = String::new();
    out.push_str(&format!("toplevel: {}\n", file.toplevel));
    out.push_str(&format!("objects: {}\n\n", file.objects.len()));

    for obj in &file.objects {
        out.push_str(&format!("== object {}: {} ==\n", obj.index, obj.name.as_deref().unwrap_or("<anonymous>")));
        let cfg = cfg::Cfg::build(obj)?;
        let ssa = ssa::SsaProgram::from_cfg(&cfg)?;
        let hlir = hlir::HlirProgram::from_ssa(&ssa)?;
        out.push_str(&hlir.dump());
        out.push('\n');
    }
    Ok(out)
}