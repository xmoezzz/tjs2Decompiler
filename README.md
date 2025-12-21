# tjs2dec

A minimal, strict **TJS2 (Kirikiri2 / Kirikiri-Z)** bytecode loader and disassembler written in Rust. This tool allows you to inspect, analyze, and decompile compiled TJS2 script files (`.tjs`).

## Features

* **Disassemble**: Convert binary bytecode into human-readable assembly mnemonics.
* **SSA&HLIR**: Generate Static Single Assignment (SSA) form or High-Level Intermediate Representation (HLIR) for deep code analysis.
* **Decompilation**: Attempt to reconstruct high-level TJS2 source code.
* **TJS Emitting**: Generate an executable TJS script that replays the low-level bytecode logic.

---

## Installation

```bash
cargo build --release

```

The binary will be located at `./target/release/tjs2dec`.

---

## Usage

`tjs2dec` provides several subcommands depending on the level of detail you need.

### 1. Disassemble Bytecode

To see the raw instructions and constant pools:

```bash
tjs2dec disasm Action.tjs

```

### 2. High-Level Decompilation

To attempt to recover the original TJS2 source code:

```bash
tjs2dec tjs Action.tjs

```

### 3. SSA and HLIR Analysis

To dump the Static Single Assignment form (useful for understanding data flow):

```bash
tjs2dec ssa Action.tjs

```

To dump the High-Level IR (HLIR):

```bash
tjs2dec ssa --hlir Action.tjs

```

### 4. Emit Executable TJS

To create a low-level TJS program that mimics the behavior of the bytecode:

```bash
tjs2dec emit-tjs Action.tjs

```

---

## License

MPL-2.0 License

---