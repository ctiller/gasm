---
id: BR1
title: "Borrow index: elaboration-cost measurement, then the capability context and weaving DSL"
status: ready
blocked_on: ""
after: [MH1]
related: [MH3, PA2, PA4, MT1]
bar: ""
track: proof-arch
priority: 7.1
priority_set: 2026-08-28T00:00:00Z
design: "docs/BORROW_MODEL.md"
design_review: ""
date: 2026-08-28
---

# BR1: Borrow index — measurement first, then the context and the weaving DSL

## Context

Implements `docs/BORROW_MODEL.md` §2, §4, §5. The owner's demand trigger is stated
(`docs/BORROW_MODEL.md` §10.1, verbatim: *"isa scale up: we need multithreading and
borrowing resolved"*), so this is Law 5 demand-driven work, not banked design.

**This task leads with a measurement that can kill it.** `docs/BORROW_MODEL.md` §5.5
records exactly what the feasibility spike did and did not establish: the indexed-monad
weaving DSL was compiled at v4.33.1 and works, but the largest program measured is seven
steps over two literal-index regions. Elaboration cost of index normalization at realistic
program length is unmeasured, and if it is superlinear the approach is a redesign rather
than a fix. Building the DSL before measuring that is the facade risk `docs/REVIEW.md`
Law 8 exists to catch.

## Deliverables & acceptance criteria

- **Phase 0 — the kill criterion, delivered before anything else.** A synthetic
  elaboration-cost measurement: authored programs of increasing length (10, 50, 200, 1000
  steps) over increasing region counts, timed, with the growth curve reported. State the
  threshold up front and honour it: if elaboration is superlinear in program length at
  the scale `Stdlib/Zlib/X86_64.lean` (2,245 lines) would demand, STOP and report — the
  fallback design is `docs/BORROW_MODEL.md` §12's decidable posterior borrow-check pass,
  and choosing it is a success outcome for this task, not a failure.
- The capability context: the `Cap` state, the four operations of
  `docs/BORROW_MODEL.md` §2.1 (`lend`, `reclaim`, `donate`, and the initial `write`), and
  the two decidable authority predicates. Backed by, and connected to, the existing Core
  vocabulary (`Gasm/Core/Permissions.lean` — `PermissionShare`, `MemoryPerm`,
  `DisjointTokens`), so the dormant machinery gains semantically-invoked call sites
  (Law 8): the tokens must appear in the discharged obligations, not alongside them.
- The share-splitting primitive that does not exist today: `MemoryPerm.split`
  (`Gasm/Core/Permissions.lean:38-49`) is spatial only and carries the same `share` into
  both halves. The `Exclusive → ReadOnly ⊗ ReadOnly` direction, with the reclaim rule as
  its inverse, is this task's core addition, stated as lemmas about the index rather than
  as operations on values (`docs/BORROW_MODEL.md` §3.1 explains why the value-level form
  is unsound in a non-linear metatheory).
- The weaving DSL: a term-level syntax over Lean's own `doSeq` parser folding to indexed
  binds (`docs/BORROW_MODEL.md` §5.2 contains the measured 30-line shape). Must support
  statement sequencing, `let x ← e`, and an explicit per-step proof escape
  (`docs/BORROW_MODEL.md` §7.2).
- **Obligation dispatch, with both halves demonstrated** (`docs/BORROW_MODEL.md` §5.4):
  the automatic tactic closes literal-index cases silently, and a case it cannot close
  presents the author with the exact proposition at the failing step's source position.
  **Acceptance evidence (Law 13)**: a store-while-lent mutation must fail to elaborate
  with a goal naming the region's state; an opaque-context access must present its goal
  and then be closable by an author-supplied proof term. Demonstrated, then reverted.
- **Error-message quality is a deliverable, not a nicety.** `docs/BORROW_MODEL.md` §5.4's
  NEG-2 measurement — the most common author mistake, an undischarged loan — produced a
  goal mentioning a metavariable rather than naming the outstanding loan. An
  index-mismatch report that names the region and its loan count is required before this
  task counts as delivered; unusable errors mean an unused surface.
- Language-level theorems, not per-program ones (`docs/VISION.md` §4, and
  `docs/BORROW_MODEL.md` §10.5 for the checked version of that claim including its
  qualification): the authority-bookkeeping facts are proven once about the language.

## Pointers

- `docs/BORROW_MODEL.md` §2 (the model), §3 (why the index and not a value), §4 (what the
  index is and is not), §5 (the measured spike and its limits), §11 (what it cannot
  catch), §13 Q3 (the measurement-gate ruling this task implements).
- `Gasm/Core/BlockM.lean:25-52` — the indexed monad already in the tree, dormant since it
  was written, whose only tree-wide occurrence outside its own file is an import on
  `Gasm/Core/CFG.lean:20`. This task is its first consumer, or the evidence it should be
  deleted.
- `Gasm/Core/Permissions.lean` — the vocabulary being made real.
- `docs/API_STATE_MODELS.md` §2 — the ratified design `BlockM` implements.
- `docs/REVIEW.md` Law 8 (the facade risk this task's Phase 0 answers), Law 10 (the
  automatic path is `decide`, rung 2 — kernel-checked, no allowlist entry), Law 13.

## Notes

_(none yet)_
