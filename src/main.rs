// SPDX-License-Identifier: MIT
//
// tjs2dec
//
// A small tool to parse Kirikiri TJS2 compiled script images (TJS2/DATA/OBJS)
// and disassemble the VM code stream.
//
// This revision focuses on opcode restoration:
//  - Full opcode enumeration (128 VM opcodes)
//  - Instruction arity table (including variable-length CALL/NEW)
//  - Constant-pool (object CONST table -> DATA pools) resolution

mod disasm;
mod opcode;
mod reader;
mod tjs2;

use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "tjs2dec", version, about = "TJS2 bytecode parser and disassembler (Kirikiri)")]
struct Cli {
    #[command(subcommand)]
    cmd: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Parse a structured TJS2 bytecode file (TJS2/DATA/OBJS) and print a summary.
    Parse {
        file: PathBuf,
        /// Also dump raw code words for each object.
        #[arg(long)]
        dump_code: bool,
        /// Also dump constant tables for each object.
        #[arg(long)]
        dump_consts: bool,
    },

    /// Disassemble all objects (top-level context + subroutines) with labels.
    Disasm {
        file: PathBuf,
        /// Only disassemble a single object index.
        #[arg(long)]
        object: Option<usize>,
        /// Print resolved constants (strings, numbers) inline where possible.
        #[arg(long, default_value_t = true)]
        resolve_consts: bool,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.cmd {
        Command::Parse {
            file,
            dump_code,
            dump_consts,
        } => {
            let data = std::fs::read(&file).with_context(|| format!("read {:?}", file))?;
            let bc = tjs2::parse_tjs2_bytecode(&data).context("parse structured TJS2 bytecode")?;
            bc.dump_summary();
            if dump_consts {
                bc.dump_consts();
            }
            if dump_code {
                bc.dump_code_words();
            }
        }

        Command::Disasm {
            file,
            object,
            resolve_consts,
        } => {
            let data = std::fs::read(&file).with_context(|| format!("read {:?}", file))?;
            let bc = tjs2::parse_tjs2_bytecode(&data).context("parse structured TJS2 bytecode")?;
            if let Some(i) = object {
                disasm::disasm_object(&bc, i, resolve_consts)?;
            } else {
                disasm::disasm_all(&bc, resolve_consts)?;
            }
        }
    }
    Ok(())
}


#[cfg(test)]
mod tests {
    use anyhow::{Context, Result};
    use std::path::PathBuf;

    #[test]
    #[ignore]
    fn disasm_action_tjs() -> Result<()> {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("testcase")
            .join("Action.tjs");

        if !path.exists() {
            eprintln!("skip: file not found: {:?}", path);
            return Ok(());
        }

        let data = std::fs::read(&path).with_context(|| format!("read {:?}", path))?;
        let bc = crate::tjs2::parse_tjs2_bytecode(&data).context("parse structured TJS2 bytecode")?;

        // Resolve consts into comments, but keep official-style *idx formatting.
        crate::disasm::disasm_all(&bc, true)?;

        Ok(())
    }

    #[test]
    #[ignore]
    fn disasm_action_tjs_2() -> Result<()> {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("testcase")
            .join("Action.tjs");

        if !path.exists() {
            eprintln!("skip: file not found: {:?}", path);
            return Ok(());
        }

        let data = std::fs::read(&path).with_context(|| format!("read {:?}", path))?;
        let bc = crate::tjs2::parse_tjs2_bytecode(&data).context("parse structured TJS2 bytecode")?;

        // Resolve consts into comments, but keep official-style *idx formatting.
        crate::disasm::disasm_all(&bc, true)?;
        println!("{:#?}", bc);

        Ok(())
    }
}
