---
id: B3
title: Stage B decoder modularization (per-instruction tryDecode co-located with encode)
status: ready
blocked_on: ""
after: [TC4, B1]
related: []
bar: ""
track: build-scale
priority: 5.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# B3: Stage B decoder modularization (per-instruction tryDecode co-located with encode)

## Context

This task already has its design written — it is not a from-scratch design task, it is an
implementation task whose design was deliberately produced and locked in advance, as its own
protected phase, alongside the registry-gate work (TC4). PLAN.md's findings-ledger entry for the
instruction registry states this explicitly, under the heading "STAGE B," quoted in full because its
own wording establishes both the design and the sequencing rule this task must follow:

> **STAGE B** (design-doc'd now, implemented as separate reviewed change AFTER gate lands, protected
> by it): modularize the decoder — per-instruction `tryDecode` co-located with `encode`, local
> roundtrip proof in the same file (mostly rfl/decide, kernel-checked), global decoder = registry-
> driven dispatcher, per-family dispatch-reachability + in-bucket exclusivity lemmas. Result: editing
> one instruction rebuilds only its file + dispatcher + one lemma; other families' proofs stay
> cached. This is both the build-perf sharding win AND proof-architecture practice for Phase 4
> composition.

Read every clause of that literally — it is the whole design:

1. **"design-doc'd now, implemented as separate reviewed change AFTER gate lands, protected by it"**
   — this task's design already exists (in `docs/TARGETS/X86_64.md`'s design section, authored
   alongside TC4's dispatch, per PLAN.md's DESIGN note: "Law 5: design section authored in
   docs/TARGETS/X86_64.md inside the implementing branch"), and its sequencing is deliberate: it must
   land only *after* TC4's registry roundtrip gate is in place and green, because the gate is what
   protects this refactor — a decoder restructuring this large (moving decode logic that currently
   lives in one 700+-line file into 21+ per-instruction files) is exactly the kind of change that
   could silently reintroduce a decode gap or misdecode, and the registry gate's exhaustive
   per-instruction roundtrip theorem (`decode (encode i) = i`, discharged via `native_decide` over
   each family's finite `roundtripCases`) is what makes that class of regression build-failing rather
   than merely likely-to-be-caught. Do not attempt this restructuring against a tree where TC4's gate
   isn't live — that would remove the safety net the design explicitly relies on.
2. **"per-instruction `tryDecode` co-located with `encode`"** — today, `decode (encode i) = i` is
   proven, but the decode direction is monolithic: `Gasm/Targets/X86_64/Decoder.lean` (708 lines) is
   a single global `decodeX86_64Instr` function that pattern-matches on opcode bytes across every
   instruction family in one file, entirely separate from where each instruction's `encode` lives
   (co-located per-family in `Gasm/Targets/X86_64/Instructions/*.lean`). This task's core move is to
   give each instruction family its own `tryDecode` function living in the *same file* as its
   `encode` (mirroring how `Instructions/Add.lean` already owns `Add`'s encode logic end to end) —
   this is a real architectural inversion of where decode logic lives today, not a light refactor.
3. **"local roundtrip proof in the same file (mostly rfl/decide, kernel-checked)"** — once decode is
   co-located with encode per-family, the roundtrip proof for that family becomes a local, small,
   fast proof discharged by `rfl`/`decide` where possible (Law 10: exhaustive finite domains only),
   living in the same file rather than as a separate global proof. This is the direct build-perf
   payoff: a change to one instruction family's decode logic now only invalidates that family's own
   file plus whatever thin dispatcher/lemma depends on it, not a monolithic 708-line decoder file
   that every family's roundtrip check currently shares.
4. **"global decoder = registry-driven dispatcher"** — `Decoder.lean`'s current role (a single
   function owning every family's decode logic) shrinks to a thin dispatcher that reads the opcode
   byte(s) and routes to the appropriate family's `tryDecode`, driven by the same registry structure
   TC4 built (`Gasm/Targets/X86_64/Registry.lean`'s `allEncodableInstructions`/environment audit) —
   this task should investigate reusing that registry machinery for dispatch rather than building a
   second, parallel one.
5. **"per-family dispatch-reachability + in-bucket exclusivity lemmas"** — two new proof obligations
   this restructuring introduces that don't exist as such today: a **reachability** lemma per family
   (every instruction in this family's `roundtripCases` is actually reachable through the thin
   dispatcher's routing logic — i.e. the dispatcher doesn't accidentally shadow or misroute a case to
   the wrong family's `tryDecode`), and an **in-bucket exclusivity** lemma per family (within a single
   family's own decode logic, no two of its own byte patterns collide ambiguously). These are new,
   named proof deliverables this task must actually produce, not just restructure code and assume
   correctness carries over.

### The dual payoff this task claims — build-perf AND proof-architecture practice

PLAN.md's STAGE B note closes with: "This is both the build-perf sharding win AND proof-architecture
practice for Phase 4 composition." Take both halves seriously as acceptance criteria, not just the
build-perf one:

- **Build-perf sharding**: "editing one instruction rebuilds only its file + dispatcher + one lemma;
  other families' proofs stay cached" is a concrete, testable claim — this task's before/after
  build-timing evidence should specifically demonstrate that editing a single instruction family's
  file no longer triggers a rebuild of every other family's roundtrip proof, which is exactly the
  cascade B1 (Instructions.lean aggregator sharding, this task's other hard dependency) is separately
  fixing on the encode/import side. B1 and B3 attack the same underlying cascade from two directions
  — B1 fixes who-imports-what so consumers aren't forced through one umbrella file, B3 fixes
  where-decode-logic-lives so the roundtrip proof itself is no longer monolithic. **This task depends
  on B1 landing first** (TASKS.md: `after: [TC4, B1]`) because B3's per-family co-location plan
  assumes the module-import structure B1 leaves behind, not the current umbrella-import structure —
  attempting B3 against a pre-B1 tree risks fighting the same aggregator cascade B1 is designed to
  remove.
- **Proof-architecture practice for Phase 4 composition**: per `docs/VISION.md` §4 and Decision D11,
  the project's stated strategy for making proof cost sublinear at scale is per-module contracts with
  local proofs that compose (routine contracts, step lemmas, composition rules) rather than
  monolithic whole-program reasoning. This task is a small-scale rehearsal of exactly that pattern —
  local proofs (per-family roundtrip, reachability, exclusivity) that compose into a global guarantee
  (the dispatcher correctly routes every registered instruction) — for the decoder specifically,
  ahead of Phase 4's larger step-lemma/composition-calculus work (PA2/PA3) needing the same shape at
  a much larger scale. Treat any friction this task hits (does the reachability/exclusivity lemma
  shape actually compose cleanly? does the dispatcher pattern generalize?) as useful signal for
  PA2/PA3's design, similar in spirit to how PA1's crc32 pathfinder is explicitly asked to report
  friction for the correctness-composition track.

## Deliverables & acceptance criteria

- A short inline `## Design` section confirming/adapting the STAGE B design (quoted above, already
  written in `docs/TARGETS/X86_64.md` per PLAN.md's DESIGN note) to the actual state of the tree at
  implementation time — since this design predates its own dispatch by some time, confirm the
  registry/gate structure it assumes (TC4's `Registry.lean`, `RoundtripGate.lean` and the per-family
  `RoundtripGate/*.lean` shards) still matches what's described, and note any drift. Per the
  task-lifecycle convention this is mechanical work, so `design: "inline"` /
  `design_review: "waived-mechanical"` is appropriate once this section exists — but confirm the
  pre-existing STAGE B design doc content first rather than re-deriving from scratch.
- Per-instruction `tryDecode` functions added to each `Instructions/<Family>.lean` file, co-located
  with that family's existing `encode`.
- `Gasm/Targets/X86_64/Decoder.lean` reduced from its current monolithic ~708-line
  `decodeX86_64Instr` to a thin registry-driven dispatcher.
- Local roundtrip proofs, per family, living in the same file as that family's `tryDecode`/`encode`,
  discharged by `rfl`/`decide` where the domain is genuinely exhaustive-finite (Law 10) — reusing
  TC4's existing per-family `RoundtripGate/<Family>.lean` shards as the template/starting point where
  applicable, since that gate infrastructure already shards proofs one-per-instruction-family.
- New per-family **dispatch-reachability** and **in-bucket exclusivity** lemmas, as named in the
  STAGE B design — these are additional, currently-nonexistent proof obligations this task
  introduces, not a restatement of the existing roundtrip gate.
- The existing registry roundtrip gate (TC4's `decode (encode i) = i` exhaustive theorem) must
  continue to pass, unweakened, throughout this restructuring — this task modularizes *where* decode
  logic lives, it must not relax *what* is proven about it. Any temporary weakening during the
  restructuring must be flagged loudly in Notes, not silently carried to completion.
- **Before/after build-timing evidence, per `scripts/build_baseline.md`'s established convention**:
  demonstrate specifically that editing a single instruction family's file (e.g. touching only
  `Instructions/Add.lean`'s new `tryDecode`) no longer forces a rebuild of every other family's
  roundtrip proof — this is the literal, checkable form of PLAN.md's claim ("editing one instruction
  rebuilds only its file + dispatcher + one lemma; other families' proofs stay cached"). Compare
  against both iteration 1's original baseline (`scripts/build_baseline.md`) and B1's post-restructuring
  numbers, since B3 builds on B1's changes.
- `python scripts/check_refs.py` and `lake exe check_gates_axioms` must both continue to exit 0 —
  moving decode logic between files changes which declarations carry which `/- REF: ... -/`
  citations and which module owns which axiom dependency; verify explicitly.
- Completion report should note, for PA2/PA3's benefit per the "proof-architecture practice" framing
  above, whether the reachability/exclusivity lemma shapes generalize cleanly or needed
  hand-derivation specific to the decoder — this is useful input to Phase 4's larger composition
  work even though B3 itself is scoped to the decoder only.

## Pointers

- PLAN.md, findings-ledger entry on the instruction registry, "STAGE B" paragraph (quoted in full
  above) — this task's design, already written.
- PLAN.md, same entry's earlier "(3-REVISED per Craig 2026-08-27)" note: "gate proofs SHARDED
  one-per-instruction-family in separate modules + thin aggregator (parallel elaboration, failure
  names the family; prefer decide/rfl over native_decide per shard where fast enough)" — the sharding
  pattern TC4 already applied to the *gate* proofs, which this task extends to the *decode logic*
  itself.
- `Gasm/Targets/X86_64/Decoder.lean:37` (`decodeX86_64Instr`, the current 708-line monolithic global
  decoder this task modularizes) and its current import list (lines 1-27, importing every instruction
  submodule individually already — note this file does NOT currently go through the
  `Instructions.lean` umbrella, unlike most consumers, which may make it a useful precedent for B1's
  "import only what you use" pattern).
- `Gasm/Targets/X86_64/Registry.lean` (TC4's `allEncodableInstructions` registry and build-time
  environment audit — the structure this task's "registry-driven dispatcher" should reuse for
  routing, not duplicate).
- `Gasm/Targets/X86_64/RoundtripGate.lean` and `Gasm/Targets/X86_64/RoundtripGate/*.lean` (TC4's
  existing per-family gate shards — e.g. `Add.lean`, `And.lean`, `Call.lean`, `Cmov.lean`, `Cmp.lean`,
  `Common.lean`, `Div.lean`, `Imul.lean`, `Jcc.lean`, `Lea.lean`, and others — the template this task's
  local per-family roundtrip proofs should follow or directly extend).
- `Gasm/Targets/X86_64/Instructions/*.lean` (21 per-family files — the co-location target for the new
  `tryDecode` functions).
- `docs/TARGETS/X86_64.md` (where the STAGE B design section was authored per PLAN.md's own citation
  — read this directly for the design's exact stated form before implementing; this task file
  summarizes it but the doc is the primary source).
- `docs/tasks/TC4-decoder-registry-gate.md` if present, else TASKS.md's TC4 entry, and
  `docs/tasks/B1-build-perf-iteration2.md` (both hard dependencies — confirm both landed; B3's
  per-family co-location plan assumes B1's post-restructuring import layout, not the current one).
- `docs/VISION.md` §4 (modular contracts/composed proofs, DSL composition) and Decision D11 — the
  proof-architecture-practice framing this task's second payoff draws on.
- `scripts/build_baseline.md` (the before/after timing convention this task's evidence must follow).

## Notes

- 2026-08-27: priority 5.0 — Stage B decoder modularization is build-scale hygiene gated on B1; useful but not urgent relative to the trust-core/proof-arch/graphics/networking tracks.

_(none yet — first entries append here as work begins; mechanical build/refactoring task,
consolidate into an inline ## Design section before implementation, design_review:
waived-mechanical.)_

### 2026-08-27 — design constraint from the B1 review (coordinator)

The B1 reviewer analysed whether Stage B actually breaks the residual 32-job cascade and
found that **moving `tryDecode` into each instruction family file is necessary but NOT
sufficient**. 23 of the 32 residual jobs are the RoundtripGate shards plus `Common` and
the aggregator, all coupled through `RoundtripGate/Common.lean:4 → Decoder → all 21
families`. A global dispatcher must still *see* every family in order to dispatch, so
`Decoder.lean` keeps full fan-in, and any `Common.lean` that imports `Decoder` preserves
the 21-shard fanout unchanged.

So B3 must additionally: (a) make each family's gate shard verify against **its own**
`tryDecode`, not against the global decoder; and (b) isolate dispatch exhaustiveness into
one separate module that is *allowed* to have full fan-in, proving that the dispatcher
agrees with the per-family decoders. Only then does an instruction edit rebuild just that
file, the dispatcher, and one composition lemma.

Also from that review: the umbrella `Instructions.lean` is now down to two importers
(`Decoder.lean`, `Registry.lean`), and B3 removes one of them — leaving a manifest file
that nothing mechanically enforces. Before or with B3, add the ~10-line check that
`{Instructions/*.lean} \ {Base} == {imports in Instructions.lean}`, which also closes the
residual audit gap `Registry.lean`'s header documents (an unimported instruction module
is invisible to the environment audit). Do not let B3 land while the only thing keeping
the umbrella complete is convention.
