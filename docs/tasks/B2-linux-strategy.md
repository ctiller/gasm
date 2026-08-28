---
id: B2
title: Linux target foundation & strategy — ABI, ELF64 linker, syscall semantics, and runner plan
status: design-review
blocked_on: ""
after: [TC4]
related: [TC6, N1]
bar: ""
track: build-scale
priority: 7.0
priority_set: 2026-08-27T23:20:00Z
design: "docs/TARGETS/LINUX.md"
design_review: ""
date: 2026-08-27
---

# B2: Linux target foundation & strategy — ABI, ELF64 linker, syscall semantics, and runner plan

## Context

`B2` encompasses both the **pure Lean Linux x86-64 target foundation** (ABI modeling, ELF64 binary emission/linking, unified syscall interception, and Spike 1 Hello World verification) and the **hardware/runner strategy** for multi-OS differential validation.

### Why it matters — the epistemology gap it closes

PLAN.md's gaps register names the reason this must happen, under "Single-machine/single-OS epistemology":

> **Single-machine/single-OS epistemology**: all hardware truth from one i9-13900H; whole oracle
> stack is Windows-only; zen4/skylake profiles unvalidatable; Linux target doc'd but absent from
> PLAN. Perf model must state "validated on exactly N microarchitectures"; Linux runner story
> eventually gates fleet-scale agents.

Closing this gap begins with establishing formal and mechanical foundations for Linux in Lean:
1. **Instruction Set**: Adding `SyscallOp` (`0F 05`) to `Gasm.Targets.X86_64`, passing decoder and roundtrip gate audits.
2. **Target ABIs**: Modeling System V AMD64 function call ABI and Linux Syscall register conventions in `Gasm.Targets.Linux.ABI`.
3. **ELF64 Format & Linker**: Pure Lean ELF64 serialization (`Elf64_Ehdr`, `Elf64_Phdr`, `Elf64_Shdr`) and freestanding static executable linking (`Gasm.Targets.Linux.Linker`).
4. **Syscall Semantics & Interception**: Unified system call effect interceptor mapping syscalls (`sys_write`, `sys_exit`, `sys_read`, `sys_mmap`) to typed `Effects` events.
5. **Spike 1 Verification**: Complete port of Spike 1 (`Spikes.Spike1Hello.Linux.*`) with `native_decide` trace equivalence proof against `helloWorldSpec`.
6. **Runner & Hardware Strategy**: Plan for Linux CI/differential testing runners to run generated ELF binaries and execute oracle fuzzers.

## Deliverables & acceptance criteria

- [x] **X86-64 `Syscall` Instruction**:
  - `Gasm/Targets/X86_64/Instructions/Syscall.lean`: `SyscallOp` instance with `0F 05` encoding, micro-op breakdown, NASM emission, and `canFuzzHardware := false`.
  - `Gasm/Targets/X86_64/Decoder.lean`: Decoder integration for `0x0F 0x05`.
  - `Gasm/Targets/X86_64/RoundtripGate/Syscall.lean` & `Registry.lean`: Gate shard and type registration ensuring `expectedInstructionTypes` audit passes.
- [x] **Linux Target Modules (`Gasm/Targets/Linux/`)**:
  - `ABI.lean`: `AbiDiscipline X86_64 SystemVAMD64` instance and `LinuxSyscallABI` register definitions.
  - `Syscall.lean`: Syscall number definitions (`SYS_write = 1`, `SYS_exit = 60`, etc.) and `LinuxSyscallInterceptor` producing typed domain events.
  - `ELFFormat.lean`: Structured ELF64 data structures and standard constants (`ET_EXEC`, `PT_LOAD`, `PF_R | PF_X`, etc.).
  - `Emitter.lean`: Pure Lean binary serialization for ELF64 headers and segments.
  - `Linker.lean`: `LinuxExecutable` representation and `linkLinuxProgramStatic` with configurable base VMA (default `0x400000`) and 4KB segment alignment.
- [x] **Spike 1 Linux Implementation & Verification (`Spikes/Spike1Hello/Linux/`)**:
  - `Program.lean`: `spike1SymbolicProgram` using `sys_write` and `sys_exit`.
  - `Emit.lean`: Assembles and links freestanding static ELF binary.
  - `Equivalence.lean`: Constructive proof `spike1_canonical_effect_trace_equivalence` using `native_decide` matching `helloWorldSpec`.
  - `Test.lean`: Executable test verifying generated ELF binary structure and execution trace.
- [ ] **Hardware / Runner Plan**:
  - Runner and differential oracle strategy document for executing Linux binaries in CI.

## Pointers

- Design specification: `docs/TARGETS/LINUX.md`.
- Windows target precedent: `Gasm/Targets/Windows/` (`ABI.lean`, `PEFormat.lean`, `Emitter.lean`, `Linker.lean`, `Win32API.lean`).
- Spike 1 precedent: `Spikes/Spike1Hello/Windows/` and `Spikes/Spike1Hello/Spec.lean`.
- `Gasm/Targets/X86_64/Registry.lean` and `Gasm/Targets/X86_64/RoundtripGate/`.

## Notes

- 2026-08-27: Repurposed and unblocked B2 per owner alignment via /grill-me session. Consolidated design in `docs/TARGETS/LINUX.md`. Scope expanded to cover the pure Lean Linux x86-64 target foundation, `syscall` instruction, ELF64 static linker, and Spike 1 equivalence proof alongside the runner plan.

