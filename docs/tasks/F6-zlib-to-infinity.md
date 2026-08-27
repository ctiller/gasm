---
id: F6
title: zlib-to-infinity epic — optimizing zlib against the state of the art
status: ready
blocked_on: ""
after: [PA8, PA4, F4, TC12]
related: []
bar: ""
track: perf
priority: 7.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# F6: zlib-to-infinity epic — optimizing zlib against the state of the art

## Context

This is the proving ground for the entire `gasm` thesis. It is the task where every other track's
work — universal correctness contracts (Proof Architecture), a calibrated performance model
(F1-F5), and demand-driven ISA growth (Law 5/D7) — gets asked to do its actual job at once, on a
real, externally-benchmarkable target. PLAN.md's "Candidate post-repair epic" section states this
directly and should be read in full, since it is short and is this task's entire mission statement:

> Take the zlib implementation and optimize it as far as it will go versus the best available today
> (zlib-ng, libdeflate, ISA-L class baselines). This is the proving ground for the whole thesis:
> universal contracts hold correctness fixed, the calibrated perf model ranks candidates without
> execution, agents run the superoptimization search = "world's foremost optimizing compiler" made
> concrete and benchmarkable against the state of the art. Prerequisites: Phase 4 pathfinder (crc32
> ∀-proof — conveniently also the first optimization target: table-driven/SIMD CRC vs current
> bitwise loop), perf fuzzer calibrated (Phase 3), capability migration of Zlib/Windows.lean (Phase
> 2/D3). Likely needs ISA growth on spike demand (SSE/PCLMULQDQ for CRC32, wider moves) — each
> increment differentially validated per D7. External benchmark harness vs real zlib-ng/libdeflate
> binaries would be the headline scoreboard.

### Unpacking the thesis statement

"Universal contracts hold correctness fixed, the calibrated perf model ranks candidates without
execution, agents run the superoptimization search" is not marketing language — it is a literal
description of the mechanism this task must actually operate:

1. **Correctness is held fixed by universal contracts** — every candidate optimized variant of a
   zlib routine (CRC32, adler32, LZ77 match search, Huffman encode/decode) must satisfy the *same*
   universally-quantified functional-equivalence contract PA1's crc32 pathfinder establishes the
   shape for (see `docs/tasks/PA1-crc32-pathfinder.md`'s "three split theorems" pattern), proven by
   kernel-checked structural proof (Law 10), never by a pointwise regression check (Law 9). A variant
   that is faster but not proven equivalent is not a candidate; it is a bug.
2. **The calibrated perf model ranks without execution** — this is the entire reason F1-F5 exist and
   are hard dependencies. F4's parametric cost functions give each candidate a closed-form,
   real-coefficient cost under a named profile; F1's containment/rank-order validation is what makes
   trusting that ranking (instead of just running every candidate on real hardware) defensible. Read
   this literally: F6 is unstartable as a *ranking* exercise until the model it ranks with has been
   shown, per `docs/VISION.md` §5, to be "monotonically faithful" — a model that gets absolute numbers
   wrong but ranks correctly is the thing F1-F5 exist to produce, and F6 is the first task that
   actually spends that asset.
3. **Agents run the superoptimization search** — the workflow this task enables is: an agent proposes
   an assembly variant, checks it against the correctness contract (mechanical, fast), evaluates its
   cost under the calibrated model (mechanical, fast, no execution needed), and only occasionally
   validates against real hardware (F1's harness) to keep the model honest — exactly the "optimization
   loops that run at model-evaluation speed rather than benchmark speed" VISION §5 promises.

### The prerequisite chain — why each one is a hard blocker, not just sequencing

TASKS.md lists `after: [PA8, PA4, F4, TC12]`. Each is load-bearing:

- **PA8** (Law 9 migration, Spike5-first): PLAN.md's own findings ledger records that "Spike5's
  `inductive GzipOp | compress` / `GunzipOp | decompress` are SINGLE-CONSTRUCTOR types, so `∀ op`
  quantifies over one element while spec ignores the parameter" — a domain-shrinking evasion of Law 9
  that currently makes Spike5's gzip "verification" vacuous. TASKS.md's PA8 line notes this fix
  "also unblocks zlib epic" explicitly. **This task cannot start against an honestly-verified zlib
  baseline until PA8's Spike5 fix lands** — optimizing a routine whose current "proof" of correctness
  is vacuous means F6 would be racing against a baseline that was never actually shown correct in the
  first place, defeating the entire "correctness held fixed" premise.
- **PA4** (capability adoption / Law 11 migration, Zlib/Windows.lean last): PLAN.md's findings ledger
  flags `Stdlib/Zlib/Windows.lean` directly: "4096-byte stack scratch with hand-computed offsets
  (+8-for-push corrections) in dynamic-Huffman path — most fragile code in repo; only guarded by
  external Python fuzzer. Fixed 8MB/8MB VirtualAlloc split, no bounds checks (→ Law 11)." Optimizing
  this code before it has capability-token memory-safety proofs means every proposed variant inherits
  an already-unrepresentable-as-safe risk profile; PA4 is what upgrades the frame condition PA1's
  pathfinder deliberately kept simple (per PA1's "same-file churn only" scope note) into a real Law-11
  capability obligation, which this epic needs before agent-generated variants can be trusted not to
  silently corrupt the fixed 8MB/8MB scratch split.
- **F4** (parametric cost functions): the direct performance-side prerequisite — see point 2 above.
  Without closed-form cost functions on routine contracts, there is no mechanical way to rank
  candidates without executing every one of them.
- **TC12** (connection-theorem linter + known twins): TASKS.md's own parenthetical on the F6 line
  reads "(bit-reader/Huffman mini-DSLs per D11 as part of this)" — meaning D11's mandate (quoted
  below) that the bit-reader and Huffman machinery become mini-DSLs with their own lemma libraries is
  itself part of *this* task's scope, not a separate prerequisite to wait for passively. TC12's
  connection-theorem tooling is the mechanism that would catch it if, mid-optimization, two encodings
  of the same Huffman/bit-reader fact (a table-driven form and a closed-form/SIMD form) end up
  unlinked — exactly the failure mode Law 12 exists to prevent, and exactly the situation a
  superoptimization search over many candidate encodings is likely to produce accidentally.

### D11's mini-DSL mandate for bit-reader/Huffman machinery, quoted

PLAN.md Decision D11 states:

> ...the registry gate is the closed-population exemplar; Zlib's bit-reader/Huffman machinery should
> become mini-DSLs with their own lemma libraries before the optimization epic (one language-level
> proof, many optimized inhabitants); every new subsystem design starts by asking "what is the
> language here?"...

Read this as a scoping instruction, not a footnote: before (or as the opening phase of) this epic,
the bit-reader and Huffman decode/encode machinery in `Stdlib/Zlib/Deflate.lean` /
`Stdlib/Zlib/Windows.lean` should be restructured as their own small DSLs — proven correct *in
total* once, so that every optimized variant (branchless vs branchy Huffman decode, different
bit-reader window strategies) is automatically an inhabitant of an already-proven language rather
than requiring its own from-scratch correctness proof. This is the direct DSL-composition mechanism
`docs/VISION.md` §4 describes ("a bit-reader language inside an assembly language inside a
syscall-effect language, each layer carrying its own total theorems") — do this restructuring before
generating many candidate variants, not after, or the superoptimization search will multiply proof
work instead of amortizing it.

### The ISA-growth caveat — demand-driven, not speculative

PLAN.md flags: "Likely needs ISA growth on spike demand (SSE/PCLMULQDQ for CRC32, wider moves) —
each increment differentially validated per D7." This directly invokes Decision D7 (the wsc lesson):

> **Demand-driven model growth (wsc lesson)**: the predecessor (wsc/Lasm) died by building out too
> much ISA as code before the instruction model was right — repair cost exceeded rebuild cost.
> Therefore: models stay deliberately incomplete, grow only on spike demand (Law 5), and every
> increment is differentially validated in the change that introduces it, before anything depends on
> it. Never bulk-import ISA surface.

Concretely: this task will very likely need `PCLMULQDQ` (carryless multiply, the standard SIMD
CRC32 acceleration instruction) and possibly wider `MOVDQU`-class moves once the CRC32/adler32
optimization work actually reaches for SIMD. MODEL_DEBT §B4 confirms the current model has **no
FPU/SSE/AVX state at all** ("No XMM registers, no MXCSR, no x87... Excludes: all SIMD
(`PCLMULQDQ` CRC32, vectorized adler32, wide `MOVDQU` copies — likely zlib-epic demands)") — this is
not a hypothetical, it is a named, already-flagged gap this exact task will hit. When it does: add
only the specific instructions the current optimization candidate demands (per Law 5/D7), with
differential validation (hardware fuzzing, per the same discipline `HardwareHarness.lean` already
applies to the rest of the ISA) landing in the *same change* that introduces the instruction — do
not bulk-import a general XMM/SSE model speculatively ahead of actual demand, per D7's explicit
prohibition and the wsc failure it's named for.

### The external-benchmark scoreboard

PLAN.md's closing sentence — "External benchmark harness vs real zlib-ng/libdeflate binaries would
be the headline scoreboard" — names the ambition level explicitly: this is not just an internal
self-consistency improvement, it is meant to produce a genuine, externally-checkable comparison
against the actual state-of-the-art C implementations the wider world already trusts. Treat building
that external comparison harness (invoking real zlib-ng/libdeflate binaries against the same
corpora, comparing wall-clock or cycle-level performance) as a real deliverable of this epic, not an
optional victory-lap — it is the only way this task's "ranks against the state of the art" claim
becomes falsifiable by someone outside this project.

## Deliverables & acceptance criteria

- Confirm all four prerequisites (PA8's Spike5 fix, PA4's Zlib/Windows.lean capability migration, F4's
  cost functions, TC12's connection-theorem tooling + D11 mini-DSL restructuring) have actually landed
  before beginning candidate generation — this task's own completion report should cite each one's
  landing evidence, not merely assume it from TASKS.md's `after:` list being marked done elsewhere.
- Bit-reader and Huffman machinery restructured as mini-DSLs (per D11) with language-level total
  theorems, ahead of or as the first phase of candidate generation — this is explicit in-scope work
  for this task per TASKS.md's own parenthetical, not something to treat as someone else's job.
- At least one genuine optimization pass on a real target — PA1's crc32 pathfinder is explicitly
  named as "conveniently also the first optimization target: table-driven/SIMD CRC vs current
  bitwise loop" — table-driven and/or SIMD (`PCLMULQDQ`) CRC32 variants, each proven functionally
  equivalent to the existing spec by kernel-checked structural proof (reusing/extending PA1's
  connection-theorem work between the table-driven Lean spec and the per-bit assembly realization),
  and ranked against each other and the baseline via F4's cost functions plus F1's containment
  criterion.
- Any new ISA surface (PCLMULQDQ, wider moves, etc.) added strictly on demand from an actual
  optimization candidate, each increment differentially validated (hardware-fuzzed) in the same
  change that introduces it — per D7, no speculative bulk ISA import.
- An external benchmark harness invoking real zlib-ng and/or libdeflate reference binaries against
  shared test corpora, producing a genuine head-to-head comparison — the "headline scoreboard" PLAN.md
  names as this epic's ambition.
- **Differential validation evidence at every level**, per `docs/VISION.md` §5: every optimized
  variant's correctness comes from a kernel-checked proof (not a benchmark), and every ranking claim
  ("variant A is faster than variant B") is backed by both the calibrated model's cost function
  *and* real-hardware agreement via F1's containment/rank-order criterion — a variant that wins on
  the model alone, without hardware confirmation via F1's harness on at least a representative
  sample, has not actually demonstrated the epic's central claim.
- Given the scale and ambition of this epic, expect it to be a multi-task epic in practice (this
  single file is the entry point / mission brief, not a single atomic unit of work) — the completion
  report for the first dispatch against this file should include a proposed decomposition into
  sub-tasks (mirroring how PA1→PA2→PA3 decomposed the proof-architecture track) rather than trying to
  swallow the whole epic in one pass.

## Pointers

- PLAN.md, "Candidate post-repair epic — 'zlib to infinity'" (quoted in full above) — this task's
  entire mission statement.
- PLAN.md, Decision D7 (demand-driven model growth, quoted above), Decision D11 (DSLs as the unit of
  proof leverage, mini-DSL mandate quoted above), findings ledger entries on Spike5's domain-shrinking
  (TIER 2) and `Stdlib/Zlib/Windows.lean`'s fragile hand-computed scratch offsets.
- `docs/VISION.md` §5 (parametric cost functions, monotonically faithful — the standard this epic's
  every ranking claim must meet), §4 (DSL composition — "a bit-reader language inside an assembly
  language inside a syscall-effect language").
- `MODEL_DEBT.md` §B4 (FPU/SSE/AVX absence — the ISA-growth gap this task will hit when it reaches for
  SIMD CRC32/adler32), §A1/§A4/§A0 (the dependency-chain/branch/hierarchy debt F3 must have already
  fixed for this task's rankings — CRC/adler accumulator-chain unrolling and branchy-vs-branchless
  Huffman decode are the exact examples MODEL_DEBT names as bitten by A1/A4 respectively).
- `Stdlib/Zlib/CRC32.lean:7-46` (`crc32Polynomial`, `mkCrcTableEntry`, `crc32Table`, `updateCrc32`,
  `crc32` — the table-driven spec side of the first optimization target).
- `Stdlib/Zlib/Windows.lean:36-119` (`crc32SymbolicProgram` — the existing bitwise-loop assembly
  realization this task's first optimization pass improves on; see PA1's pointers for exact current
  line numbers, confirmed by grep, since this file churns frequently — dynamic Huffman and LZ77
  compression landed the same day per git log).
- `docs/tasks/PA1-crc32-pathfinder.md` (the pathfinder this task's first optimization pass extends —
  read its "Three Split Theorems" and "composition sketch" sections for the contract/proof pattern to
  reuse), `docs/tasks/PA4-capability-adoption.md` and `docs/tasks/PA8-law9-migration.md` (hard
  prerequisites — confirm landed before starting), `docs/tasks/F4-parametric-cost-functions.md` (hard
  prerequisite — the cost-function mechanism this epic ranks candidates with), `docs/tasks/F1-rdtsc-harness.md`
  (the containment/rank-order criterion this epic's ranking claims must satisfy on real hardware).
- `docs/adr/0008-demand-driven-model-growth.md` (D7), `docs/adr/0011-dsls-as-unit-of-proof-leverage.md`
  (D11), `docs/adr/0006-performance-model-as-strategic-asset.md` (D5).

## Notes

- 2026-08-27: priority 7.0 — the zlib-to-infinity epic is the owner-named forcing function for nearly all of Section A's performance-model debt, but it sits behind four other tracks' prerequisites (PA8, PA4, F4, TC12).

_(none yet — first entries append here as work begins; this is Law-5-class performance-model work
— consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch.)_
