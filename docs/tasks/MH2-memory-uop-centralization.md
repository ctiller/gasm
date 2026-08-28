---
id: MH2
title: Memory uop centralization — one provenance-marked cost table, derived per-form uops
status: ready
blocked_on: ""
after: [MH1]
related: [F1, F2, F3, PA4]
bar: ""
track: perf
priority: 7.0
priority_set: 2026-08-28T00:00:00Z
design: "docs/MEMORY_HOOK.md"
design_review: ""
date: 2026-08-28
---

# MH2: Memory uop centralization — one provenance-marked cost table, derived per-form uops

## Context

Implements `docs/MEMORY_HOOK.md` §5 (Layer P) — migration phase M2. Today every
memory-touching form hand-writes its load/store uops inline with invented
coefficients (flat `latencyCycles := 4` loads, duplicated
`MOV.storeAddr`/`MOV.storeData` literal blocks — a Law-12 unlinked-twin population),
and 0 of 88 forms cite any source (`MODEL_DEBT.md` §A8). The failure mode under the
planned ISA expansion is P5's: every new form *will* get a number (the field is
mandatory), and nothing marks whether it means anything.

This task changes the shape of the claim: memory cost becomes a single enumerable
table of ~8 named coefficients, each carrying Law-14 provenance
(`modelInternal` | `calibrated <artifact>`), from which every form's memory uops are
*derived* via its MH1 `memAccesses` descriptor. It supplies the enumerable surface
the per-instruction validation-and-calibration gate (dispatched concurrently with
this design) checks — see `docs/MEMORY_HOOK.md` §5.3 for the exact handoff list.

## Deliverables & acceptance criteria

- `MemCostModel` in its own leaf module (so cost edits and semantic-hook edits cascade
  independently — the B3 cascade note in `docs/MEMORY_HOOK.md` §7): every memory-cost
  coefficient as a `Cited` value with a `Provenance` mark. Initial values are today's
  de-facto numbers, all honestly `modelInternal`.
- `memUops : MemAccessSpec → MemCostModel → List X86_64Uop` as the only constructor of
  memory-class uops; the 14 memory forms' `toUops` rewritten to derive their memory
  uops from `memAccesses` via `memUops`. Constructing a `.load`/`.storeAddr`/
  `.storeData` uop outside the hook is closed off structurally (private cost tag) or,
  failing that, by a build-failing linter — state which was achieved and why.
- Per-coefficient measurement recipes documented on the table (the F1 microbenchmark
  shape that would refute each value) — named recipes, not performed measurements,
  until F1 lands.
- Gate output counts and prints "N of M memory coefficients calibrated / M-N
  model-internal" (Law 14 honesty-in-output) — wired into `scripts/run_gates.py`'s
  gate table, not just printed by an unwired script.
- Derivation-invariant check in the registry audit: for every form in
  `allEncodableInstructions`, the memory-class subset of its `toUops` equals
  `memAccesses` mapped through `memUops` — decidable over the witness population,
  build-failing on divergence. **Acceptance evidence (Law 13 negative control)**: a
  mutation giving one form a hand-written memory uop must fail the audit;
  demonstrated, then reverted.
- Do not perpetuate dead fields: `memUops` must not populate `reciprocalThroughput` or
  other zero-read-site fields (`MODEL_DEBT.md` §A3) — either the field is deleted in a
  coordinated change or this task records explicitly why it still exists.

## Pointers

- `docs/MEMORY_HOOK.md` §5 and §8 (M2 row) — the governing design; §5.3 for what the
  sibling calibration gate consumes.
- `docs/REVIEW.md` Law 14 (provenance, citation, honesty-in-output), Law 12 (the
  inline-literal twins this deletes).
- `MODEL_DEBT.md` §A0/§A3/§A8; `docs/X86_ISA_EXPANSION_PREREQUISITES.md` P5.
- `Gasm/Targets/X86_64/Uop.lean` (`X86_64Uop`, dead fields),
  `Gasm/Targets/X86_64/Instructions/Mov.lean:278-281,325-328,378-381,437-439` (the
  duplicated literal blocks to delete).
- `docs/tasks/F1-rdtsc-harness.md`, `docs/tasks/F2-calibration-data-governance.md` —
  the harness and governance mechanism that later flip coefficients to `calibrated`.

## Notes

_(none yet — first entries append here as work begins; consolidated design already
exists at `docs/MEMORY_HOOK.md`; route through a fresh-agent design review before
implementation dispatch per the task-lifecycle convention.)_
