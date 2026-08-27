---
id: TC15
title: Axiom gate closure coverage (import-closure blind spot)
status: implementing
blocked_on: ""
after: []
related: []
bar: ""
track: trust-core
priority: 8.7
priority_set: 2026-08-27T18:25:47Z
design: "inline"
design_review: "waived-mechanical"
date: 2026-08-27
---

# TC15: Axiom gate closure coverage (import-closure blind spot)

## Context

Sourced from `TCB.md` **T2 — Axiom gate sees only 81% of the tree — HIGHEST-VALUE SHRINK
(~20 lines)**, tied for TCB's #1 ranked item. `isProjectModule`
(`Tools/CheckGatesAxioms.lean:94-101`) determines which declarations the load-bearing Law-10 axiom
gate inspects by walking only the tool's own import closure (the `Gasm`/`Stdlib`/`Spikes` umbrella
roots). TCB's finding: **32 of 170 project `.lean` modules are invisible to this check** — "every
`Spikes/*/Emit.lean`, every `Test.lean`, all four fuzzer CLIs, `NASM.lean`, `RoundtripTests.lean`."
A `sorry`, a hand-declared `axiom`, or an unallowlisted `native_decide` anywhere in the emission
path — the code that actually turns a `VerifiedProgram` into bytes on disk — currently **passes
the gate that is supposed to be the load-bearing check for exactly this class of defect**,
because the gate never looks at it.

TCB also notes the demoted Python pre-check (`scripts/check_gates.py`) globs all 170 modules, so
"neither tool dominates; the real gate is their undocumented union" — a second-order finding worth
carrying into this task's fix: after this task lands, the axiom tool's coverage should be the one
authoritative statement of what's checked, not an implicit union nobody has written down.

This is, per TCB, a roughly 20-line fix and among the cheapest-to-close, highest-value items in
the entire ledger — it is purely mechanical (no new model, spec, or contract concept), which is
why its `design` field stays empty until a short inline `## Design` section covers it, with
`design_review: waived-mechanical` once that lands.

## Deliverables & acceptance criteria

- `Tools/CheckGatesAxioms.lean`'s module-discovery logic changed to enumerate `.lean` files
  **from disk** (walking `Gasm/`, `Stdlib/`, `Spikes/`, and any other project source root) rather
  than relying solely on the tool's own compiled import closure, and to fail loudly if any
  on-disk file has no corresponding module in `env.allImportedModuleNames` — i.e., the gate
  detects its own blind spots instead of silently having them.
- Control vector (Law 13(4), adapted to a build-time linter per Law 13(3)): a scratch `.lean`
  file with a `sorry` in it, placed somewhere currently outside the import closure (e.g. mimicking
  an `Emit.lean` or fuzzer-CLI location), must cause the tool to fail red. Demonstrate this
  concretely in the completion report — plant it, show red, remove it, show green again.
  Symmetrically, demonstrate the fix doesn't produce false positives against the current clean
  tree (a plain green run post-fix), so the before/after contrast is on record.
- All 32 previously-invisible modules TCB names by category (`Spikes/*/Emit.lean`,
  `Test.lean` files, the four fuzzer CLIs, `NASM.lean`, `RoundtripTests.lean`) now scanned;
  completion report states the new module count the tool inspects and confirms it against the
  170-module headline figure in `TCB.md`.
- Existing green status preserved (or any newly-surfaced `sorry`/axiom violations in the
  previously-blind modules fixed as part of this task, since finding them and not fixing them
  would leave the gate red without remediation — coordinate scope with whoever owns those files if
  genuine violations turn up).

## Pointers

- `Tools/CheckGatesAxioms.lean:94-101` — `isProjectModule`, the function this task rewrites (grep
  to confirm current line numbers; TCB's are from 2026-08-27 @ commit `1cf58d5`).
- `scripts/check_gates.py` — the demoted Python pre-check that already globs all 170 modules;
  useful as a reference for "enumerate from disk" logic, and worth reconciling once this task
  lands so the two tools' coverage isn't an undocumented union.
- `TCB.md` §T2 in full.
- `docs/REVIEW.md` §4.1 item 4 (the axiom tool is named there as the load-bearing gate; this task
  is what makes that claim actually true across the whole tree rather than 81% of it) and Law 13.

## Notes

- 2026-08-27: priority 8.7 — TCB ranked-top-8 #2 (T2 — the load-bearing axiom gate is blind to 32/170 modules, including every Emit.lean; TCB calls it the 'highest-value shrink, ~20 lines').

_(none yet — first entries append here as work begins; mechanical task, consolidate into an
inline `## Design` section before implementation, `design_review: waived-mechanical`.)_
