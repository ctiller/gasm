---
id: MT1
title: "Atomic primitives: XCHG r64,[m64] with implicit LOCK, plus MFENCE"
status: blocked
blocked_on: "XM1 (TSO ordering vocabulary + machine, filed with docs/X86_MEMORY_MODEL.md §10) — per that design's §6 class 1, the first atomic form and XM1 are one indivisible landing; convert this to an after: [XM1] entry once XM1's task file is stably in-tree"
after: [MH1]
related: [B4, TC8]
bar: ""
track: concurrency
priority: 7.0
priority_set: 2026-08-28T00:00:00Z
design: "docs/SPIKES/SPIKE8_MULTITHREADING.md"
design_review: ""
date: 2026-08-28
---

# MT1: Atomic primitives — XCHG r64,[m64] (implicit LOCK) + MFENCE

## Context

Spike 8 (`docs/SPIKES/SPIKE8_MULTITHREADING.md` §5.1) needs exactly one atomic
read-modify-write and one full fence; today the tree has zero of either. The only XCHG
form is `XchgR64R64` (`Gasm/Targets/X86_64/Instructions/Xchg.lean`) — register-only,
honestly `memAccesses _ := []`, and now carrying the tripwire doc-comment gating any
memory-operand form on the memory model (`docs/X86_MEMORY_MODEL.md` §5). The ordering
semantics and the declaration vocabulary are **not this task's to design**: XM1 owns
`MemOrder` (`.plain`/`.locked`) on the MH1 `MemAccessSpec`, the `fenceEffect` field,
the TSO store-buffer machine, and the single-thread degeneration + `.locked` fidelity
theorems (`docs/X86_MEMORY_MODEL.md` §2.3). This task lands the two instruction forms
*through* that vocabulary — and per that design's §6 class 1, instruction, `.locked`
descriptors, and machine are one indivisible landing, so MT1 and XM1 ship together.

`MFENCE` arriving here (not earlier) follows that design's §6 class 2 and Q1 default:
a fence before the first threaded spike is a meaning-free no-op; Spike 8 *is* the
first threaded spike.

Sequenced `after: [MH1]` because the atomic RMW must ride the sealed memory hook: an
atomic access is `.locked` descriptor entries on one form, not a separate read plus
write that a scheduler could interleave between.

## Deliverables & acceptance criteria

- `XchgR64Mem64` (`87 /r`, memory destination): step semantics through the MH1 hook;
  `memAccesses` entries with `order := .locked`; implicit-LOCK behavior (atomic with
  or without the prefix) cited from the Intel SDM via the `intel_sdm` corpus and
  consistent with `docs/X86_MEMORY_MODEL.md` §2.1's locked-RMW rule.
- `Mfence` (`0F AE F0`): declares `fenceEffect := drainStoreBuffer`; single-threaded
  step is the identity and the existing 88-form step-lemma surface is unaffected.
- Full instruction contract for both: roundtrip/registry entries, `encoding_fuzzer`
  NASM differential, `x86_fuzzer` silicon coverage for the single-threaded semantics
  (a locked RMW on one thread must produce exactly the plain RMW's architectural
  result — `docs/X86_MEMORY_MODEL.md` §7 last bullet), sourced cost coefficients per
  D30 P4/P5.
- `writesWithin`/`readsWithin` frame lemmas for the XCHG memory form per the
  `RoundtripGate/*` shard convention, extended with XM1's atomicity fidelity
  obligation for the `.locked` entries.
- Explicit non-goals recorded in the module docstring: no general `LOCK` prefix, no
  `CMPXCHG`/`XADD`, no `SFENCE`/`LFENCE` — deferred until a spike demands CAS
  (`docs/X86_MEMORY_MODEL.md` §2.1: for WB memory, `SFENCE`/`LFENCE` add nothing over
  TSO).
- Optional (may be split out without blocking Spike 8): `Pause` (`F3 90`) as a
  semantic no-op with a real cost entry.
