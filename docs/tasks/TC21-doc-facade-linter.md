---
id: TC21
title: doc-facade linter — enforcement-claim vs tree-reality drift
status: ready
blocked_on: ""
after: []
related: [TC16]
bar: ""
track: trust-core
priority: 7.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# TC21: doc-facade linter — enforcement-claim vs tree-reality drift

## Context

Sourced from the 2026-08-27 adversarial review round that found the normative governance
docs (`docs/REVIEW.md`, `docs/EQUIVALENCE_PROOFS.md`, `docs/SYSTEM_EFFECTS.md`) had drifted
into present-tense enforcement claims for mechanisms that do not yet exist in the tree — a
class of defect distinct from ordinary code bugs: the *docs* asserted current behavior for
code that was still design-only. Four concrete instances that round found, all in one pass:

- `progressProof` cited as an existing liveness obligation in `docs/REVIEW.md` §4.1 item 1,
  when no contract in the tree carries it.
- `canonicalizeTrace` described as "implemented as a normalization function" in
  `docs/SYSTEM_EFFECTS.md` §6.3, when the function does not exist anywhere in `Gasm.Effects`
  (tracked as PA5).
- `VerifiedReactiveProgram` described as an existing distinct contract type in
  `docs/EQUIVALENCE_PROOFS.md` §1.1, when it is a ratified design with no implementation
  (tracked as PA7) and Spike 4 ships as a plain `VerifiedProgram`.
- A `MemoryPerm`-fail-to-assemble claim (Law 11) stated as enforced, when zero modules are
  migrated to the capability-authoring path (tracked as PA4).

Per Law 13 (Findings Become Gates), each of these should have terminated in a mechanical
prevention of its *class*, not just a hand-fix of the four instances — this task is that
gate. Per `docs/tasks/PA6-read-binder-contract.md`'s and other design-tracked tasks' pattern,
the fix in this review round was to add explicit "Status" language (implemented-or-not,
citing the tracking task) next to each such claim; this linter is what makes that pattern
load-bearing rather than a one-time hand-audit.

## Deliverables & acceptance criteria

- A linter (Python, sibling to `scripts/check_refs.py`/`scripts/check_gates.py`) that scans
  normative docs — `docs/*.md`, explicitly excluding `docs/adr/` and `docs/tasks/` (those are
  process records and task briefs, not specification surfaces making enforcement claims about
  the tree) — for two defect shapes:
  1. **Enforcement-mechanism identifiers absent from the tree**: a backtick-quoted Lean
     identifier appearing inside a sentence that reads as a MUST/is-implemented/is-enforced
     claim (e.g. "is implemented as", "MUST fail", "carries a distinct contract type") where
     that identifier does not appear as a real declaration anywhere in the `.lean` tree.
  2. **Enforcement claims lacking a status marker or task reference**: a MUST/is-implemented
     claim about a mechanism that has no adjacent status sentence (implemented / ratified
     design pending implementation / tracked as `PA#`, `TC#`, `N#`, etc.) — i.e. the doc reads
     as present-tense fact with no way for a reader to tell whether it describes the tree
     today or a ratified future state.
- Control-vector demonstration (Law 13(3)-shaped, build-failing linter): show the linter
  correctly flags a synthetic instance of each defect shape planted in a scratch doc, and
  passes clean on the post-review-round tree once this round's fixes have landed (this
  task's own completion report should note that the four cited instances above --
  `progressProof`, `canonicalizeTrace`, `VerifiedReactiveProgram`, `MemoryPerm`-fail-to-
  assemble -- are exactly the class this linter would have caught in one pass, since all four
  were fixed in this same review round by adding the status language this linter checks for).
- Wired into the same manual gate-running path as `check_refs.py`/`check_gates.py` until
  `TC5`'s gate runner exists; exit-code contract (0 clean, nonzero on any finding) matches the
  existing linters' convention.
- False-positive budget stated explicitly: this is a heuristic linter over prose, not a
  proof: acceptable to require a small, documented allowlist/exception mechanism (mirroring
  `scripts/gate_allowlist.txt`'s shape) for identifiers that are legitimately discussed
  hypothetically (e.g. naming a *rejected* or *future-candidate* mechanism) rather than
  claimed as enforced; the linter must fail loud on a malformed exception entry, not
  silently swallow it (same discipline as the Law 10 tools).

## Pointers

- `docs/REVIEW.md` Law 13 (Findings Become Gates) — this task's own justification.
- `docs/REVIEW.md` §4.1.1 (Gate Tooling Specification) — the sibling gate-tooling
  documentation style this linter's own eventual doc-wiring should follow.
- The four instances this review round fixed by hand (see Context above) — use them as the
  seed corpus / regression fixtures for the linter's test suite.
- `scripts/check_refs.py` and `scripts/check_gates.py` — existing linters over the same
  `docs/`+`.lean` tree; reuse their file-walking and comment-stripping conventions rather
  than reinventing them.
- `docs/tasks/PA5-canonicalize-trace.md`, `docs/tasks/PA7-verified-reactive-program.md`,
  `docs/tasks/PA4-capability-adoption.md` — the tracking tasks the four fixed instances now
  cite; a correct linter run today should treat these citations as satisfying its
  status-marker requirement.

## Notes

- 2026-08-27: priority 7.0 — closes a real, already-demonstrated defect class (four
  enforcement-claim-vs-tree-reality drifts caught in one review round) with a mechanical
  gate; comparable in kind to TC16's references-integrity fix but not one of TCB.md's
  originally-ranked top-8 items (this task postdates that ledger).
- 2026-08-27: related: [TC16] — TC21 (doc-facade linter) and TC16 (references-pipeline
  integrity) are sibling "docs claim something the tree doesn't back up" gates: TC16 catches
  a citation/corpus pointing at content that isn't there, TC21 catches prose asserting a
  mechanism is enforced when it isn't yet implemented. A fresh agent building either linter
  should look at the other's file-walking/exception-allowlist conventions first.

_(none yet — first entries append here as work begins.)_
