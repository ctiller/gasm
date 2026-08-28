# Project: AArch64 QEMU Support in gasm

## Architecture
- **Target Architecture**: 64-bit ARMv8-A / ARMv9-A little-endian.
- **Machine State**:
  - 64-bit general registers: `X0`–`X30`, dedicated zero register `XZR` (reads zero, writes discarded), stack pointer `SP`.
  - 32-bit sub-registers: `W0`–`W30` (writes zero-extend to 64 bits).
  - Condition flags: `PSTATE.NZCV` (N=negative, Z=zero, C=carry, V=overflow).
  - Sealed memory cell: `AArch64Memory` with checked read/write operations.
  - Addressing: `AArch64AddrMode` (immediate offset, pre-index writeback, post-index writeback, register offset with shift, PC-relative).
- **Instruction Surface**: Modular existential architecture mirroring x86-64: universe-polymorphic typeclass `class AArch64Instruction (ι : Type u)` in `Instructions/Base.lean`, open existential wrapper `structure AnyAArch64Instruction` (aliased as `AArch64Instr`), independent per-family submodules under `Instructions/<Family>.lean` (e.g. `Add.lean`, `Sub.lean`, `Logical.lean`, `Mov.lean`, `LoadStore.lean`, `Branch.lean`, `System.lean`, etc.), and import-only umbrella `Instructions.lean`.
- **Execution Harnesses**:
  - Bare Metal: Flat ELF64 loaded at `0x40000000`, PL011 UART MMIO (`0x09000000`), semihosting exit (`HLT #0xF000` with `SYS_EXIT = 0x18`, `0x20026`).
  - Linux: Static ELF64, `SVC #0` calling convention (`X8` syscall number, `X0`–`X5` arguments, `X0` return/exit), asm-generic syscall mapping.
  - QEMU Runner: `GASM_QEMU_AARCH64` (system) and `GASM_QEMU_USER_AARCH64` (user), fail-honest exit codes (0 = pass, 1 = fail, 2 = skip).
- **Spikes**: Spikes 1–5 with complete `Spec.lean`, `Program.lean`, `Equivalence.lean`, and test runner executables.
- **Testing & Fuzzing**: Differential encoding fuzzer vs `llvm-mc-19`, semantics fuzzer vs QEMU, stability fuzzer, and multi-tier E2E testing.

## Code Layout
- `docs/TARGETS/ARM64.md`: Authoritative in-tree AArch64 architecture and ABI specification.
- `references.json`: External ARM references registry.
- `scripts/check_references.py`: Reference registry validator.
- `Gasm/Targets/AArch64/`:
  - `Registers.lean`: Register definitions and accessors.
  - `Addressing.lean`: Addressing modes.
  - `MemoryCell.lean`: Sealed memory model.
  - `Machine.lean`: Machine state, flag evaluation, and step semantics.
  - `Instructions/`:
    - `Base.lean`: `AArch64Instruction` typeclass and `AnyAArch64Instruction` existential wrapper.
    - Individual family submodules (`Add.lean`, `Sub.lean`, `Logical.lean`, `Mov.lean`, `LoadStore.lean`, `Branch.lean`, `System.lean`).
  - `Instructions.lean`: Import-only umbrella module aggregating all instruction submodules.
  - `Decoder.lean`: 32-bit instruction decoder.
  - `Performance.lean`: Cortex-A53 performance profile.
  - `RoundtripGate/`: Round-trip theorems per instruction family and exhaustive dispatch.
  - `EncodingFuzzer.lean`: llvm-mc differential fuzzer.
  - `SemanticsFuzzer.lean`: QEMU trace differential fuzzer.
  - `StabilityFuzzer.lean`: Random bitstream stability fuzzer.
- `Gasm/Targets/BareMetal/`: AArch64 ELF emission, PL011 UART device, semihosting trap.
- `Gasm/Targets/Linux/`: AArch64 static ELF emission and asm-generic syscall table.
- `Gasm/Execution/QEMUAArch64.lean`: QEMU system and user runners.
- `Tools/CheckAArch64Obligations.lean`: Mechanical obligation validation tool.
- `Spikes/Spike1Hello/` .. `Spikes/Spike5Gzip/`: AArch64 spike implementations and test runners.
- `lakefile.toml`: Build targets and executable definitions.
- `scripts/run_gates.py`: CI gates and prerequisite verification.

## Feature Inventory
| # | Feature | Description | Milestone | Source |
|---|---------|-------------|-----------|--------|
| 1 | Reference Registration | Register ARM manuals in references.json | M1 | R1 |
| 2 | License Token | Extend check_references.py with arm-unmodified-only | M1 | R1 |
| 3 | Target Spec Docs | Expand docs/TARGETS/ARM64.md with architecture & ABI | M1 | R1 |
| 4 | Citation Discipline | 100% declaration citations and anchor verification | M1 | R1 |
| 5 | Registers & State | X0-X30, XZR, SP, PC, NZCV, AArch64Memory | M2 | R2 |
| 6 | Addressing Modes | AArch64AddrMode (imm, pre/post index, reg offset, literal) | M2 | R2 |
| 7 | Machine Semantics | Machine step, flag evaluation, TargetArch instance | M2 | R2 |
| 8 | Instruction Surface | 15 instruction families for Spikes 1-5 | M3 | R2 |
| 9 | 32-bit Codec | Binary encode & decode for all instruction families | M3 | R3 |
| 10 | Round-Trip Proofs | Machine-checked by decide proofs in RoundtripGate/*.lean | M3 | R3 |
| 11 | Registry Exhaustiveness | Compile-time run_cmd audit of instruction instances | M3 | R3 |
| 12 | Performance Model | Cortex-A53 dual-issue micro-op model | M3 | R4 |
| 13 | Obligation Enforcement | CheckAArch64Obligations validation tool & gate | M3 | R4 |
| 14 | Bare Metal Target | Flat ELF64, PL011 UART MMIO, semihosting exit | M4 | R5 |
| 15 | Linux Target | Static ELF64, SVC #0 calling convention, asm-generic syscalls | M4 | R5 |
| 16 | QEMU Runners | QEMUAArch64.lean system & user runners, fail-honest exits | M4 | R5 |
| 17 | Spike 1 Hello World | Bare Metal (PL011 + semihosting) and Linux ELF64 | M5 | R6 |
| 18 | Spike 2 Fibonacci | Control flow, UDIV/MSUB formatting on Linux | M5 | R6 |
| 19 | Spike 3 Sort Lines | SmolAlloc dynamic allocation, quicksort on Linux | M5 | R6 |
| 20 | Spike 4 HTTP Server | Socket syscalls, routing, request/response on Linux | M5 | R6 |
| 21 | Spike 5 GZIP | DEFLATE RFC 1951 / RFC 1952 streaming on Linux | M5 | R6 |
| 22 | Encoding Fuzzing | Differential fuzzer vs llvm-mc-19 | M6 | R7 |
| 23 | Semantics Fuzzing | Differential fuzzer vs QEMU traces | M6 | R7 |
| 24 | Stability Fuzzing | Parser crash-freedom and mutation fuzzer | M6 | R7 |
| 25 | Lakefile Integration | Add all AArch64 targets, libs, exes to lakefile.toml | M6 | R8 |
| 26 | CI Gate Integration | Add AArch64 gates to scripts/run_gates.py | M6 | R8 |
| 27 | E2E Test Suite Pass | Pass 100% of Tiers 1-4 tests published in TEST_READY.md | M7 | Acceptance |
| 28 | Adversarial Hardening | Tier 5 white-box challenger coverage hardening | M7 | Acceptance |

## Milestones
| # | Name | Scope | Dependencies | Status |
|---|------|-------|-------------|--------|
| M1 | Documentation & Citation Foundation | `references.json`, `scripts/check_references.py`, `docs/TARGETS/ARM64.md`, citation verification | none | DONE |
| M2 | Architectural State & Machine Model | `Registers.lean`, `MemoryCell.lean`, `Addressing.lean`, `Machine.lean` | M1 | DONE |
| M3 | Instruction Surface, Codec, Proofs & Obligations | 15 instruction families, `Decoder.lean`, `RoundtripGate/*.lean`, `Performance.lean`, `CheckAArch64Obligations.lean` | M2 | DONE |
| M4 | Execution Harnesses & QEMU Runner | Bare Metal (PL011 + semihosting), Linux (SVC #0), `QEMUAArch64.lean` | M3 | IN_PROGRESS |
| M5 | Vertical Spikes 1–5 | Spikes 1–5 (`Spec.lean`, `Program.lean`, `Equivalence.lean`, `Test.lean`) | M4 | PLANNED |
| M6 | Fuzzing & CI Gates | `EncodingFuzzer`, `SemanticsFuzzer`, `StabilityFuzzer`, `lakefile.toml`, `scripts/run_gates.py` | M5 | PLANNED |
| M7 | Final Acceptance & Adversarial Hardening | Phase 1: 100% E2E test pass (Tiers 1-4); Phase 2: Tier 5 adversarial hardening | M6, TEST_READY.md | PLANNED |

## Interface Contracts
### M1 ↔ M2 (Documentation to Machine Model)
- `docs/TARGETS/ARM64.md` anchors provide valid target URLs for all top-level Lean declaration citations in M2:
  - `#registers`: `X0`..`X30`, `XZR`, `SP`, `W0`..`W30`.
  - `#addressing-modes`: immediate, pre/post-index, register offset, literal.
  - `#machine-state`: `AArch64MachineState`, `NZCV`, step semantics.

### M2 ↔ M3 (Machine State to Instructions & Codec)
- `AArch64MachineState`: `pc : Address`, `gprs : Reg64 → UInt64`, `nzcv : UInt32`, `memory : AArch64Memory`, `fault : Option AArch64Fault`.
- `AArch64AddrMode`: addressing mode evaluation function `evalAddr : AArch64AddrMode → AArch64MachineState → Address × Option (Reg64 × Address)`.
- `TargetArch.stepPure : Instruction → MachineState → MachineState`.

### M3 ↔ M4 (Instructions to Execution Targets)
- `AArch64Instruction.encode : Instruction → ByteArray` (exactly 4 bytes, little-endian).
- `decodeAArch64Instr : ByteArray → Nat → Except String (AnyAArch64Instruction × Nat)`.
- Bare Metal entry point jumps to `0x40000000`. PL011 MMIO intercepts `0x09000000`–`0x09000018`.
- Linux entry point initializes stack at `0x7FFFFFFF0000`, routes `SVC #0` to syscall dispatcher.

### M4 ↔ M5 (Execution Targets to Spikes)
- Spikes emit static ELF64 binaries using `Gasm.Targets.BareMetal.Emitter` and `Gasm.Targets.Linux.Emitter`.
- Spikes invoke `Gasm.Execution.QEMUAArch64` runners returning exit code: 0 = pass, 1 = fail, 2 = skip.
- Spike equivalence proven via `by decide` comparing symbolic step execution against specification trace.

### M5 ↔ M6 (Spikes to Fuzzing & Gates)
- Fuzzers import instruction families from `Gasm.Targets.AArch64.Instructions`.
- CI runner `scripts/run_gates.py` defines gate prerequisites: `qemu_system_aarch64`, `qemu_aarch64`, `llvm_mc`.

### E2E Testing Track ↔ Implementation Track
- Interface: Opaque-box executable binaries emitted to disk and run via host CLI or QEMU runners.
- Signal: `TEST_READY.md` at repository root signals test suite availability and coverage metrics.
