---
id: B4
title: Pre-index instruction byte offsets to eliminate O(M * N) re-encoding in simulator
status: ready
blocked_on: ""
after: [TC4]
related: [B1, TC18]
bar: ""
track: perf
priority: 7.5
priority_set: 2026-08-28T00:06:33Z
design: inline
design_review: waived-mechanical
date: 2026-08-28
---

# B4: Pre-index instruction byte offsets to eliminate O(M * N) re-encoding in simulator

## Context

Sourced from `MODEL_DEBT.md` **B6 (Self-modifying code unrepresentable; O(n²) perf wall)** and the 2026-08-28 comprehensive codebase security audit:

In `Gasm/Targets/X86_64/Semantics.lean:29-37`:
```lean
def instructionAtRip (instructions : List X86_64Instr) (rip : Address) : Option X86_64Instr :=
  let rec findInstr (curRip : Address) (remaining : List X86_64Instr) : Option X86_64Instr :=
    match remaining with
    | [] => none
    | i :: rest =>
      let len := (X86_64Instruction.encode i).size
      if curRip == rip then some i
      else findInstr (curRip + len.toUInt64) rest
  findInstr 0x401000 instructions
```

On every single execution step of the x86-64 machine simulator:
1. `instructionAtRip` is invoked with the current `rip`.
2. It walks `instructions : List X86_64Instr` from index 0.
3. For every instruction visited, it invokes `X86_64Instruction.encode i` to calculate its byte length on the fly (`let len := (X86_64Instruction.encode i).size`).

For an assembly routine containing $N$ instructions running for $M$ simulation steps:
- Total instruction encoding operations: $O(M \times N)$.
- Each encoding dynamically allocates a `ByteArray`, formats ModR/M and REX prefix bytes, and pattern matches opcode tables.

### Severe Impact on Lean Kernel Heartbeats
This quadratic interpreter overhead is the primary reason why:
- `Spikes.Spike2Fibonacci.Windows.Equivalence` consumes ~198 seconds of CPU time and requires `set_option maxHeartbeats 5000000`.
- `Spikes.Spike5Gzip.Equivalence` consumes ~135 seconds of CPU time and requires `set_option maxHeartbeats 4000000`.
- Whole-repository gate verification is bogged down in re-encoding identical instructions millions of times during elaboration.

## Deliverables & acceptance criteria

- **Pre-computed Instruction Map**:
  Introduce a pre-indexed instruction structure (e.g. `InstructionMap` backed by `Std.HashMap Address X86_64Instr` or a sorted `Array (Address × X86_64Instr)` with pre-calculated offsets computed once at program initialization time).
- **$O(1)$ / $O(\log N)$ Instruction Fetch**:
  Update `instructionAtRip` (or introduce `instructionAtRipIndexed`) to query the pre-computed map without performing any runtime `ByteArray` allocations or `encode` calls during execution steps.
- **Proof of Equivalence**:
  Prove lemma `instructionAtRipIndexed_eq_instructionAtRip` confirming that indexed lookup produces identical results to linear scanning for all valid program states.
- **Build Performance Benchmark**:
  Demonstrate substantial reduction in elaboration time and memory footprint for `Spikes.Spike2Fibonacci.Windows.Equivalence` and `Spikes.Spike5Gzip.Equivalence`.
- `lake build` and `scripts/run_gates.py --quick` pass cleanly.

## Pointers

- `Gasm/Targets/X86_64/Semantics.lean:25-45` (`instructionAtRip`, `stepProgram`).
- `Spikes/Spike2Fibonacci/Windows/Equivalence.lean` (heartbeat baseline).
- `Spikes/Spike5Gzip/Equivalence.lean` (heartbeat baseline).
- `MODEL_DEBT.md` §B6.

## Notes

- 2026-08-28: Task created following comprehensive codebase security audit identifying quadratic re-encoding in simulator fetch loop.
