---
id: F4
title: Parametric cost functions (loop annotations to closed-form polynomials on contracts)
status: ready
blocked_on: ""
after: [F3, PA2]
related: []
bar: ""
track: perf
priority: 7.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# F4: Parametric cost functions (loop annotations to closed-form polynomials on contracts)

## Context

This task is one half of `docs/VISION.md` §5 made concrete — the half about *what a cost is
expressed as*, as opposed to F5's half (*how a cost is viewed/converted across devices*). Decision
D5 in PLAN.md states the end-state directly: "static model → agents optimize without executing;
needs its own differential validation ... End-state: parametric cost functions with concrete
coefficients (`5·N² + 3·N + 293` cycles under a named profile), never bare big-O. Cost functions
live on routine contracts, regression-gated." This task is the mechanism that turns that end-state
sentence into something buildable.

### VISION §5's thesis, quoted in full (the part this task makes concrete)

> **Parametric cost functions, not asymptotics.** The end-state for performance contracts is
> symbolic cost modeling with real coefficients baked in: a routine's cost is stated as a closed-form
> function of its input parameters — `5·N² + 3·N + 293` cycles under a named microarchitectural
> profile, not `O(N²)`. Asymptotic classes hide exactly the constant factors that agents are best
> positioned to optimize; concrete-coefficient cost functions make every optimization measurable,
> every regression mechanical, and cost composition (caller cost = Σ callee costs + glue, loop cost =
> trip count × body + overhead) ordinary polynomial arithmetic that Lean can check. Cost functions
> are part of a routine's contract, derived from the per-instruction uop/latency model plus
> loop-structure annotations, and regress like proofs do.
>
> The performance model is itself a model, and inherits the obligation of §3.2: it must be
> differentially validated against real hardware measurement. Static bounds do not need to be
> cycle-exact, but they must be **monotonically faithful** — when the model ranks variant A faster
> than variant B, real hardware must overwhelmingly agree, or the model is actively misleading the
> optimization search.

Three separate claims are packed into this passage; keep them distinct while designing:

1. **The cost *shape*** is a closed-form polynomial (or more generally, a symbolic expression) in the
   routine's input parameters, with concrete numeric coefficients — not an asymptotic class, and not
   a bare numeral (a fixed cycle count only works for input-independent routines; anything
   input-size-dependent, which is most of what the zlib epic (F6) will optimize, needs the polynomial
   form).
2. **The derivation path** is explicit: per-instruction uop/latency data (which is exactly what F3's
   staged calibration corrects) **plus loop-structure annotations** — i.e. this task needs a way to
   annotate a routine's loops (trip-count expression, whether the trip count is a function of an
   input parameter like buffer length) so that a per-basic-block cost can be lifted into a per-routine
   symbolic cost via the composition arithmetic VISION describes: "caller cost = Σ callee costs +
   glue, loop cost = trip count × body + overhead." This composition is explicitly claimed to be
   "ordinary polynomial arithmetic that Lean can check" — meaning the design should aim for something
   Lean's kernel can verify mechanically (regression-checking a stated cost bound against the
   composed derivation), not merely a documentation artifact.
3. **Cost functions live on the contract**, alongside the routine's functional-equivalence,
   callability/ABI, and memory-safety obligations (the "three split theorems" shape `PA1`'s crc32
   pathfinder is establishing for the correctness side — this task is the performance-side sibling of
   that same contract-authoring discipline) — and they **regress like proofs do**, meaning a change to
   a routine that increases its actual cost beyond its stated contract should fail a build gate the
   same way a broken correctness proof would.

### Why this depends on both F3 and PA2

`after: [F3, PA2]` in TASKS.md is doing real work, not just bookkeeping:

- **F3** is the prerequisite because a parametric cost function is only as good as the per-instruction
  uop/latency/dependency-chain/branch data it's built from — deriving a closed-form polynomial from an
  *uncalibrated* model (MODEL_DEBT §A1's missing dependency-chain cost, §A4's missing branch model,
  etc.) would produce cost functions that are precise-looking but wrong in exactly the ways F3 exists
  to fix. F4 should not begin deriving real cost functions before F3's stages have at least landed
  A8 (uop/latency) and A1 (dependency chains) — the two stages VISION's own composition formula
  ("trip count × body + overhead") most directly depends on getting right.
- **PA2** (step-lemma library + composition calculus design doc) is the prerequisite because VISION's
  cost-composition arithmetic ("caller cost = Σ callee costs + glue, loop cost = trip count × body +
  overhead") is structurally the *performance* analogue of PA2's *correctness* composition calculus —
  PA2 is designing how routine contracts compose for correctness (sequential/call/loop rules); this
  task needs the same shape of compositional reasoning for cost, and should reuse or mirror whatever
  loop/call/sequential composition structure PA2 settles on rather than inventing a parallel one. Per
  D11 ("DSLs are the unit of proof leverage"), if PA2's step-lemma library ends up being a genuine DSL
  over the assembly language with its own composition rules, this task's loop-annotation-to-polynomial
  derivation should be designed as riding on top of that same DSL structure, not a separate mechanism
  bolted on afterward.

## Deliverables & acceptance criteria

- A design doc (Law 5; Law-5-class performance-model work per the task-lifecycle convention) for a
  loop-annotation scheme: how a routine's `Program.lean` (or its symbolic-assembly authoring surface)
  states a loop's trip-count expression as a function of contract-level input parameters (e.g. "this
  loop runs `bufferLength` times"), and how that annotation is validated against the actual emitted
  control flow (an annotation that lies about trip count is worse than no annotation — this needs its
  own soundness argument, likely tied to the same loop-invariant machinery PA2/PA3 are building for
  correctness).
- A derivation mechanism: per-instruction uop/latency/dependency data (from the now-calibrated model,
  post-F3) plus loop annotations compose into a closed-form polynomial cost expression, following
  VISION's stated composition arithmetic (`caller cost = Σ callee costs + glue`,
  `loop cost = trip count × body + overhead`). State explicitly whether this composition is checked by
  Lean (kernel-checked arithmetic over the derived polynomial, matching VISION's "ordinary polynomial
  arithmetic that Lean can check" framing) or produced by an external/meta-level tool with Lean only
  checking the final stated bound — this is a real design decision, not a formality, and should be
  argued for explicitly.
- Cost functions attached to routine contracts as a new contract component, alongside (not replacing)
  the correctness-side three-split-theorem shape PA1 is establishing — coordinate with PA1/PA2's
  authors so the contract-shape additions are compatible rather than competing.
- **Regression gating**: a routine whose actual measured/derived cost exceeds its contract's stated
  cost function must fail a build gate, mirroring how a broken correctness proof already fails
  `lake build` — this is the mechanical enforcement VISION's "regress like proofs do" clause demands.
- **Differential validation is the acceptance bar for the derived cost functions themselves**, per
  VISION §5's explicit inheritance clause: "The performance model is itself a model, and inherits the
  obligation of §3.2: it must be differentially validated against real hardware measurement... they
  must be **monotonically faithful**." Concretely: pick at least one non-trivial parametric example
  (a loop whose trip count depends on an input parameter — ideally reusing a kernel already exercised
  by F1/F3's validation suite) and show the derived closed-form polynomial's rank-ordering of two or
  more variants agrees with real hardware measurement via F1's harness, not merely that the polynomial
  was mechanically derived without contradiction.
- Explicitly state in the design doc how this task's cost functions cite calibration data governed by
  F2 (every numeric coefficient inside a derived polynomial ultimately traces back to a calibration
  file, the same way F3's corrected `Uop.lean` constants do) — do not let coefficients re-enter the
  codebase as bare literals with no calibration citation, which would silently undo F2's governance
  mechanism at one remove.

## Pointers

- `docs/VISION.md` §5, in full (quoted above) — this task's direct thesis statement.
- PLAN.md, Decision D5 ("Performance modeling is strategic" — the `5·N² + 3·N + 293` example
  originates here) and Phase-2's "Parametric cost function design" bullet: "loop annotations → cost
  recurrences → closed-form polynomials on contracts."
- `docs/tasks/F3-staged-model-calibration.md` (the calibrated model this task's derivations are built
  from — do not begin real derivation before F3's A8/A1 stages land).
- `docs/tasks/PA2-step-lemma-composition-design.md` (the correctness-side composition calculus this
  task's cost-composition arithmetic should mirror or ride on top of).
- `docs/tasks/PA1-crc32-pathfinder.md` (the three-split-theorem contract shape this task's cost
  component attaches alongside — read its "What 'contract' means here" section for the pattern to
  extend, not replace).
- `Gasm/Targets/X86_64/Performance.lean:76-96` (`computeCycleBounds` — the per-instruction-sequence
  cost function this task lifts into per-routine, parameter-dependent closed forms).
- `Gasm/Targets/X86_64/Uop.lean:47-68` (the uop/latency model this task's polynomials are ultimately
  derived from, once F3 has calibrated it).
- `docs/EQUIVALENCE_PROOFS.md` §4 (the three-split-theorem template this task's cost component
  extends — read alongside PA1's pointers).
- `docs/adr/0006-performance-model-as-strategic-asset.md` (D5), `docs/adr/0011-dsls-as-unit-of-proof-leverage.md` (D11 — relevant if this task's loop-annotation scheme rides on PA2's DSL structure).

## Notes

- 2026-08-27: priority 7.0 — parametric cost functions turn F3's calibrated numbers into closed-form polynomials on PA2's contracts — gates F6.

_(none yet — first entries append here as work begins; this is Law-5-class performance-model work
— consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch.)_
