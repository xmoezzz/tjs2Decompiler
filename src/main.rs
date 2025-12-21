use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use std::fs;

use tjs2dec::{
    decompile::srcgen_high::dump_src_file as dump_src_file_high,
    decompile::{dump_hlir_file, dump_ssa_file},
    disasm::disassemble_file,
    emit_executable_tjs, load_tjs2_bytecode,
};

#[derive(Parser)]
#[command(
    name = "tjs2dec",
    version,
    about = "TJS2 (krkrz) bytecode loader + disassembler"
)]
struct Cli {
    #[command(subcommand)]
    cmd: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Disassemble a compiled TJS2 bytecode file.
    Disasm {
        /// Path to a compiled script file (e.g., Action.tjs)
        path: String,
    },

    /// Emit a low-level, executable TJS program that replays the bytecode.
    EmitTjs {
        /// Path to a compiled script file (e.g., Action.tjs)
        path: String,
    },
    Ssa {
        /// Path to a compiled script file (e.g., Action.tjs)
        path: String,

        /// Emit HLIR instead of raw SSA.
        #[arg(long)]
        hlir: bool,
    },
    Tjs {
        /// Path to a compiled script file (e.g., Action.tjs)
        path: String,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.cmd {
        Command::Disasm { path } => {
            let buf = fs::read(&path).with_context(|| format!("read {}", path))?;
            let file = load_tjs2_bytecode(&buf).context("parse structured TJS2 bytecode")?;
            let text = disassemble_file(&file).context("disassemble")?;
            print!("{}", text);
        }
        Command::EmitTjs { path } => {
            let buf = fs::read(&path).with_context(|| format!("read {}", path))?;
            let file = load_tjs2_bytecode(&buf).context("parse structured TJS2 bytecode")?;
            let text = emit_executable_tjs(&file).context("emit executable TJS")?;
            print!("{}", text);
        }
        Command::Ssa { path, hlir } => {
            let buf = fs::read(&path).with_context(|| format!("read {}", path))?;
            let file = load_tjs2_bytecode(&buf).context("parse structured TJS2 bytecode")?;
            let text = if hlir {
                dump_hlir_file(&file).context("build HLIR")?
            } else {
                dump_ssa_file(&file).context("build SSA")?
            };
            print!("{}", text);
        }
        Command::Tjs { path } => {
            let buf = fs::read(&path).with_context(|| format!("read {}", path))?;
            let file = load_tjs2_bytecode(&buf).context("parse structured TJS2 bytecode")?;
            let text = dump_src_file_high(&file, Default::default()).context("build src")?;
            print!("{}", text);
        }
    }
    Ok(())
}
