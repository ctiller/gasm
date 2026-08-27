---
id: PA2
title: step-lemma library + composition calculus design doc
status: ready
blocked_on: ""
after: [PA1]
related: []
bar: ""
track: proof-arch
priority: 8.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# PA2: step-lemma library + composition calculus design doc

## Context

This is the design doc that turns the modular-contracts architecture (`docs/VISION.md` §4, D2 in
PLAN.md) into something concrete enough to implement. `TASKS.md` sequences it `after: PA1
(learnings)` deliberately, not as a formality: PA1's own task file (`docs/tasks/PA1-crc32-pathfinder.md`)
was pulled forward out of its natural position specifically so that this design doc would be
informed by a real end-to-end proof rather than by guessing. PLAN.md's gaps register states the
rationale verbatim:

> **Pull the crc32 pathfinder FORWARD** (start when decoder lands, parallel to Phase 2 docs): the
> Phase 4 proof architecture is untested hypothesis until one routine goes
> contract→asm→kernel-proof→composition end-to-end; it will find what the design is missing
> faster than more design will.

Concretely: PA1's task file requires a written "composition sketch" as one of its acceptance
criteria — an explicit note on what a caller-composition proof would need, whether the pathfinder
proof had to hand-derive any per-instruction step lemma from scratch, and where the
`docs/EQUIVALENCE_PROOFS.md` §4 three-theorem template needed bending. That sketch is this task's
**primary input**. Note also that PA1 landing schedules BAR 2 (`TASKS.md`: "BAR 2 — after PA1:
fresh-agent review of the proof architecture against the pathfinder evidence") — but per
`docs/adr/0010-bar-triggered-deep-re-reviews.md`, BAR 2 is a full deep re-review of the *entire* codebase
from scratch, not a review scoped to the pathfinder or to this design doc; whatever findings it
produces about proof-architecture drift anywhere in the tree are additional input worth checking
against once available, but this task should not wait on or assume a narrowly-scoped verdict. Do
not start authoring this design doc from a blank slate against the theory alone — read PA1's
completion report and Notes first, and cite concretely what it found.

### What this design doc is, per D11

PLAN.md's Decision D11 is explicit about how to *frame* this work, not just what to build:

> **D11 — DSLs as the unit of proof leverage**: prove the language in total, apply to every
> inhabitant; DSLs compose (layered lemma libraries)... Operational consequences: Phase 4's
> step-lemma library + composition calculus ARE the total theorems of the assembly DSL (frame it
> that way in the design doc)...

`docs/VISION.md` §4 states the same idea in its own words, and this is the paragraph to build the
doc's spine around:

> **DSLs are the unit of proof leverage.** A lesson imported from prior projects: a DSL in Lean is
> a superpower for proofs, because theorems are proven about the *language in total* — once — and
> then apply to every program written in it. Well-designed DSLs compose, so lemma libraries stack:
> a bit-reader language inside an assembly language inside a syscall-effect language, each layer
> carrying its own total theorems... step lemmas and composition rules are total theorems about
> the assembly DSL; contracts are total theorems about the effect DSL; and proving languages
> instead of programs is precisely what makes proof cost sublinear in system size.

Concretely: a "step lemma" for, say, `add_r64_imm32` is a single theorem proven once — `∀` initial
machine state and `∀` operands — that characterizes exactly how that instruction transforms
registers/flags/memory. Every routine that uses that instruction cites the lemma instead of
re-deriving the transition. The composition calculus is the total theorems that let routine-level
contracts (the "local proofs" of `docs/VISION.md` §4 point 2) chain into whole-program theorems
(point 3) without re-proving anything about the underlying instructions.

### What PLAN.md already scoped for this doc

PLAN.md Phase 2 lists this exact deliverable and names its hardest sub-problem:

> **Step-lemma library + composition calculus design** (extends EQUIVALENCE_PROOFS.md): per-
> instruction step lemmas (simp-set); sequential/call/loop rules; capability tokens as frame
> conditions; trace algebra for event-emitting routines (the hard design item).

Four concrete pieces to design, in order of how PLAN.md itself signals difficulty:

1. **Per-instruction step lemmas as a simp-set.** For every `X86_64Instr` constructor, a lemma of
   the shape `step m (encode i) = m'` where `m'` is expressed compositionally in terms of `m` and
   `i`'s operands — registered so that a routine's proof can `simp` through a whole instruction
   sequence rather than hand-unfolding `step`. Consider whether this can be partly auto-derived
   from each instruction's own semantics definition (`Gasm/Targets/X86_64/Instructions/*.lean`) or
   must be proven per-family.
2. **Sequential/call/loop composition rules.** Given step-lemma-level facts about instruction I1
   then I2, a rule that composes them into a fact about "I1 then I2" without re-deriving the
   underlying steps; a call rule that plugs a callee's `docs/EQUIVALENCE_PROOFS.md` §4.2
   callability theorem into a caller's proof (register/stack preservation as a frame the caller's
   proof can assume); a loop rule that turns a per-iteration invariant plus a decreasing measure
   into a `docs/EQUIVALENCE_PROOFS.md` §3 total-correctness statement — this is precisely the
   shape `docs/REVIEW.md` Law 7 requires (induction over dynamic loop bounds, never a hardcoded
   jump table), and PA1's pathfinder is the first data point on what that induction actually
   looks like for the assembly DSL.
3. **Capability tokens as frame conditions.** `docs/VISION.md` §4's closing line: "Memory safety
   and proof modularity are the same feature: the capability tokens that make an unsafe access
   fail to assemble (Law 11) are also the frame conditions that let routine proofs compose without
   global reasoning." This design doc must specify *how* a `MemoryPerm`/`MemoryPermissions` token
   (`Gasm/Core/Permissions.lean:50`) attached to a routine's contract becomes the frame condition
   consumed by the composition rules above — this is the load-bearing link between this task and
   PA4 (capability adoption), and PA4 is explicitly sequenced `after: PA2` because PA4's migration
   plan needs this DSL framing as an input.
4. **Trace algebra for event-emitting routines** — PLAN.md's own words flag this as "the hard
   design item." A routine that emits observable events (not just transforms registers/memory)
   needs its step lemmas and composition rules to also compose *traces*, and that composition must
   already respect the coalescing/causality algebra `docs/SYSTEM_EFFECTS.md` §6 defines. Note the
   dependency direction carefully: PA5 (canonicalizeTrace) is scheduled `after: PA2` specifically
   because PA5 needs this design's trace-algebra sketch as a starting point, but this task should
   not attempt to fully resolve trace canonical forms itself — sketch the interface (what a
   routine's contract needs to expose about its emitted trace to compose), and leave the full
   causal-order machinery to PA5.

## Deliverables & acceptance criteria

- A design doc (new file — likely `docs/PROOF_ARCHITECTURE.md`, or a substantial new section
  appended to `docs/EQUIVALENCE_PROOFS.md` since PLAN.md phrases this task as extending that file;
  the implementing agent should judge which keeps the citation graph cleanest and state the choice)
  specifying, at minimum, the four pieces above: step-lemma shape, composition rules
  (sequential/call/loop), capability-token frame conditions, and the trace-algebra interface sketch.
- Explicit engagement with PA1's composition sketch and Notes: name what the pathfinder proof
  needed that this design must supply as reusable infrastructure, and what (if anything) in the §4
  template PA1 had to bend that this design should account for structurally rather than leaving as
  a one-off workaround.
- Explicit statement of what is in scope vs. deferred: this doc designs the calculus; PA3
  implements it; PA4 designs/executes the capability migration that supplies real tokens for the
  frame-condition rule; PA5 designs the full trace canonical form. Do not let this doc's scope
  creep into re-solving those.
- Since this is Law-5-class model/spec-shaping work (a wrong composition calculus is expensive to
  unwind once PA3/PA4/PA9 depend on it — see `docs/VISION.md` §4 and the graphics pre-build audit
  precedent for why paper review precedes code here), this task must NOT be marked done until a
  fresh-agent design review has evaluated the doc. Do not waive review on this track.
- Acceptance evidence for the design itself is the review verdict plus `scripts/check_refs.py`
  passing once the doc exists and is cited; there is no Lean code to kernel-check at this stage
  (that arrives with PA3), so the usual "zero sorry / clean axiom gate" bar applies to PA3, not
  here — but this doc's design choices are exactly what PA3's kernel-checked proofs will be judged
  against, so precision here is not optional.

## Pointers

- `docs/tasks/PA1-crc32-pathfinder.md` — read in full; its "composition sketch" deliverable and
  Notes section are this task's primary input, per the framing above.
- `docs/VISION.md` §4 ("Tractability: Modular Contracts, Composed Proofs") in full, especially the
  DSL paragraph quoted above.
- `docs/EQUIVALENCE_PROOFS.md` §4 (the three split theorems — §4.1 functional equivalence, §4.2
  callability/ABI, §4.3 memory safety) — the per-routine contract shape the composition calculus
  must chain together; §3 (total correctness formulation) — the shape loop composition must
  produce.
- `docs/SYSTEM_EFFECTS.md` §6 in full — the observation algebra the trace-algebra interface sketch
  must be compatible with (do not design a trace composition rule that could violate the
  coalescing/causality rules stated there).
- PLAN.md Phase 2, "Step-lemma library + composition calculus design" bullet (quoted above) and
  Decision D11 (quoted above); `docs/adr/0011-dsls-as-unit-of-proof-leverage.md` (the ratified ADR
  for D11 — the framing this whole doc must be written against) and
  `docs/adr/0003-universal-equivalence-via-modular-decomposition.md` (D2 — the modular-contracts
  architecture this design doc's composition calculus makes tractable).
- `docs/REVIEW.md` Law 7 (anti-jump-table, dynamic-loop-induction requirement for the loop
  composition rule), Law 11 (capability tokens as the authoring surface the frame-condition design
  must integrate with; `docs/adr/0004-adopt-core-capability-machinery-for-memory-safety.md`), Law
  9/10 (universal quantification and kernel-checked-proof requirements that every composition rule
  itself must satisfy — a composition rule is not exempt from Law 9 just because it is
  infrastructure; `docs/adr/0002-native-decide-restricted-to-exhaustive-finite-domains.md`).
- `Gasm/Core/State.lean:11` (`ComposedState`), `Gasm/Core/Permissions.lean:50`
  (`MemoryPermissions`), `Gasm/Core/Obligations.lean:8,14,27,52` (`IsObligation`,
  `ObligationToken`, `ArenaPageToken`, `ObligationLedger`), `Gasm/Core/BlockM.lean:9` (`BlockM`),
  `Gasm/Core/Callable.lean:16` (`Callable`) — the dormant Core machinery this design's
  capability-frame-condition piece must eventually connect to (PA4 does the migration; this task
  only needs to design the connection point).
- `Gasm/Targets/X86_64/Instructions/*.lean` — the per-instruction semantics definitions the
  step-lemma library will be proven about; survey a representative sample (not all ~79 registered
  instructions) when scoping the simp-set design.

## Notes

- 2026-08-27: priority 8.0 — step-lemma library design is directly informed by PA1's findings and unblocks PA3, PA4, F4, and N7 — high downstream fan-out once PA1 lands.

_(none yet — first entries append here as work begins; this is Law-5-class proof-architecture
work — consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch; do not waive review on this track.)_
