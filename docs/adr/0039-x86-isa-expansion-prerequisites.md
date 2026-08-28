# 0039. x86 ISA Expansion Prerequisites

## Status

Accepted, 2026-08-28. (PLAN.md D30.)

## Context

The owner is considering having a team perform a large expansion of the x86-64 instruction
set, and asked what must be pinned down first. His starting hypothesis: "i think something
around the x86 round trip proofs, performance model debts would be baseline here."

The question matters more here than it would elsewhere. The predecessor project died of
exactly this: "we didn't get the instruction model right and built out too much of the isa
as code - so going back and fixing it was more expensive then rebuilding" (ADR-0008, Law 5).
Incomplete ISAs and spike-driven growth are the deliberate countermeasure, so a large
expansion is an eyes-open departure from that discipline and the prerequisites are the entire
safety argument for making it.

A planning pass produced `docs/X86_ISA_EXPANSION_PREREQUISITES.md`. Its verdict: not ready —
but not where the hypothesis pointed. The roundtrip proofs turned out to be the *healthiest*
part of the pipeline (kernel-checked `decide`, zero allowlist entries, registry enforcement
re-verified live by mutation). The real gaps are in the instruction model itself.

## Decision

The owner's rulings, in his words, on the planning document's ranked prerequisites:

- P1, machine-state schema: "machine state i expect to be expanded when we need them
  (spike/demand driven essentially)" — **not a prerequisite.**
- P2, memory contracts: "let's plan out a memory hook -- apis every instruction needs to go
  through to access memory, so we can do the perf and permissions in one place."
- P3, decoder modularization: "happy to make those tasks prereqs."
- P4 and P5: "p4/p5 are the same thing, let's build it now."

## Consequences

**P1 declined is Law 5 applied consistently, not an oversight.** The planner ranked it
BLOCKING and highest-stakes because SIMD instructions cannot be written against today's state
type — no XMM, no MXCSR, no fault taxonomy. That is true, and it is precisely why it is not a
prerequisite: those instructions are not being written yet. Building the schema before a spike
demands it is the wsc failure mode wearing a prerequisite's clothing. The expansion is
therefore shaped by model-readiness rather than by ISA coverage: GPR-only ALU forms first,
memory forms after the hook lands, SIMD only when something needs it.

**P2 unifies two concerns that would otherwise be re-implemented 88 times.** Routing every
memory access through one API means Law 11's capability check ("failing to assemble if that
proof doesn't carry") and the performance model's latency and cache accounting each get
implemented once. The chokepoint is also a proof chokepoint: one lemma set about the hook,
reused everywhere, instead of per-instruction memory reasoning.

**P4 and P5 being the same thing is the sharpest observation in this exchange.** They were
filed as separate prerequisites — mandatory validation, and calibration coefficients citing
sources — and they are one obligation: an instruction lands, the build goes green, and nothing
has established that what it claims is true. The evidence is symmetrical. A probe instruction
with identity semantics, empty uops, and zero fuzz states compiled cleanly. 50 of 88 forms
silently opt out of silicon validation. And `toUops` is mandatory, so every instruction *gets*
a cost number, while 0 of 88 coefficients cite any source — producing numbers that are
present, uniform, and unfalsifiable. Enforcing registration without enforcing meaning is the
same defect in both halves.

Building that gate runs into D29 (`0038-standards-are-earned-before-imposed.md`): all 88
existing forms fail the calibration obligation immediately. Grandfathering all of them would
make the gate 100% allowlisted and therefore enforce nothing, so the implementing task is
required to report honestly what fraction is real enforcement versus deferred debt, and what
fixing the 88 would actually cost.

**A coordinator error is corrected here for the record.** The coordinator framed ISA expansion
as multiplying oracle debt, and cited the Linux target's 24 new allowlist entries as evidence.
Measurement contradicts this: instructions add **zero** allowlist entries (`SyscallOp` added
none); the ~24 came from the *target*. The debt mint is the pointwise spike-equivalence
convention, not the ISA. An expansion is close to debt-neutral under the current conventions,
which materially weakens one of the arguments for delaying it.

## Provenance

Mixed. The four rulings in the Decision section are the owner's own words. The planning
document's findings and rankings are the planner's; the reasoning in Consequences — including
why declining P1 is consistent rather than risky, and why P4/P5 are one defect — is the
coordinator's elaboration of the owner's rulings, assented to but not stated by him.
