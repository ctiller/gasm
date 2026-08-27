---
id: TC10
title: Continuous fuzzing + regression corpus
status: ready
blocked_on: ""
after: [TC5]
related: []
bar: ""
track: trust-core
priority: 6.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# TC10: Continuous fuzzing + regression corpus

## Context

PLAN.md's gaps register names this gap directly: **"Continuous fuzzing + regression corpus:
fuzzers only run at review time; any input that ever diverged should become a checked-in
permanent vector (Law 13 for inputs). Scheduled background fuzzing once gate-runner exists."**
TASKS.md's one-liner: **"continuous fuzzing + regression corpus (diverging inputs become
permanent vectors) — after: TC5."** The `after: TC5` edge is load-bearing, not incidental: this
task needs a single entry point that already knows how to invoke every gate/fuzzer with correct
exit-code capture and fail-closed oracle-presence handling (TC5) before it can be scheduled to
run unattended — scheduling a fuzzer that might silently no-op on a missing NASM/node install,
per TC1/TC2's own history, would just automate the exact failure mode this project has already
been burned by twice.

### The problem, in Law 13's own terms

Law 13 (`docs/REVIEW.md`, "Findings Become Gates") states: **"Every defect found by review,
fuzzing, or debugging MUST terminate in a mechanical prevention... that would have caught the
defect's entire class automatically."** Currently, every differential fuzzer in this repository
(`x86_fuzzer`, `encoding_fuzzer`, `wasm_fuzzer`, `GzipFuzzer`) generates fresh random vectors
each time it runs (per its own seeded RNG), checks them once, and discards them. If a fuzzer run
ever finds a genuinely diverging input — a case where the model and the real oracle (silicon,
V8, CPython) disagree — nothing currently guarantees that exact input gets re-checked on every
future run. A regression could silently reappear if a later change reintroduces the same class
of bug and the random seed on a subsequent run happens not to regenerate the same failing case.
This is the input-side analogue of Law 13's gate obligation: **a divergence found once should
become a permanent, checked-in test vector**, not a fact that lived only in one session's
terminal output.

This is explicitly framed as depending on scheduled/background fuzzing infrastructure existing
first (PLAN.md: "Scheduled background fuzzing once gate-runner exists") — TC5 is the
prerequisite that makes "run this fuzzer unattended, on a schedule, and trust its exit code" a
meaningful operation at all.

### What "becomes a permanent vector" should mean here

The project's existing fuzzers already have a category for hand-curated, deliberately-chosen
test cases distinct from randomly-generated ones — e.g. TC1's history describes "sign boundaries
moved into curated take-6 slice (xor-class caught by design, not random luck)" as part of the
x86 hygiene branch's final micro-cycle. This task generalizes that pattern into a mechanical,
automatic promotion path: when any of this project's differential fuzzers (hardware, encoding,
Wasm, gzip) reports a divergence, the specific input that diverged should be captured and
committed as a new entry in that fuzzer's curated/regression case list — not merely logged to a
session transcript that no future run will re-read. The corpus itself is the checked-in,
regenerable artifact (in the spirit of Law 4/Law 6's reference-reproducibility discipline, and
of MODEL_DEBT E5's proposed "third reference class" for calibration data — checked in,
machine-readable, with provenance, never hand-edited) — a divergence's byte-for-byte input
should be preservable exactly, with enough context (which fuzzer, what the expected-vs-actual
outcome was, when it was found) that a future regression is unambiguous.

### Interaction with TC11 (mutation-coverage tooling)

This task and TC11 are complementary, not overlapping: TC10 is about *automatically retaining
real divergences the fuzzers themselves already found* against real oracles; TC11 is about
*mechanically verifying the fuzz suites would catch a divergence if one existed* (via synthetic
model mutations). A suite that never actually diverges against a real oracle (because the model
is currently correct) produces no TC10 corpus growth, but might still be weak in the TC11 sense
(it might not have caught a planted mutation either, meaning its case coverage has gaps a real
bug could slip through). Both are needed; do not conflate them or treat one as substituting for
the other.

## Deliverables & acceptance criteria

- A mechanism (likely a small script or Lean-side hook invoked by each fuzzer's failure path)
  that captures a diverging input's exact bytes/state plus minimal provenance (which fuzzer,
  timestamp or commit, expected vs. actual outcome) and commits it to a checked-in regression
  corpus location, per fuzzer (hardware/encoding/Wasm/gzip fuzzers each likely need their own
  corpus directory or file, given their differing input shapes).
- Every fuzzer's normal run must include replaying its accumulated regression corpus *in
  addition to* freshly generated random vectors — a regression corpus that isn't actually
  re-checked on every run provides no protection.
- Scheduled/background fuzzing wired through TC5's gate runner (or a thin wrapper around it) so
  this can run unattended without reintroducing TC1/TC2-shaped fail-open risk; confirm with
  TC5's own file what hooks or exit-code conventions it expects a scheduled caller to rely on.
- Demonstrate the mechanism actually works: plant one known-diverging input into at least one
  fuzzer (e.g. via a deliberate, temporary model mutation — coordinate with TC11's mutation
  catalog if useful, though this task can stand alone with a single hand-planted case), confirm
  it gets captured into the regression corpus automatically, then revert the mutation and
  confirm the corpus entry is retained (a corpus that only holds inputs while the bug they
  reveal is still present is not durable regression protection).
- Completion report states, per fuzzer wired into this mechanism: how many corpus entries exist,
  what triggered each (if any were found from real fuzzing rather than the deliberate plant),
  and confirmation the corpus is replayed on every run (not just checked in and forgotten).

## Pointers

- `Gasm/Targets/X86_64/HardwareHarness.lean`, `Gasm/Targets/X86_64/EncodingFuzzer.lean`,
  `Gasm/Targets/Wasm/SemanticsFuzzer.lean`, `Stdlib/Zlib/GzipFuzzer.lean` — the four
  differential fuzzers this task needs a regression-corpus mechanism for; grep-confirmed
  present. Each has a different input shape (machine-state + bytes; encoded instruction bytes;
  Wasm module bytes; raw byte buffers for gzip), so the corpus format is unlikely to be uniform
  across all four — do not force a single schema prematurely.
- PLAN.md, "Gaps register" section, the "**Continuous fuzzing + regression corpus**" bullet —
  the original scope note this task file supersedes.
- `docs/tasks/TC5-gate-runner.md` — the prerequisite entry point this task's scheduled runs
  should invoke through, per the `after: [TC5]` edge.
- `docs/tasks/TC11-mutation-coverage-tooling.md` — the complementary (not overlapping) task; read
  it to keep the boundary between "retain real divergences" (TC10) and "verify suites would
  catch synthetic ones" (TC11) clear.
- MODEL_DEBT E5 ("Governance of measured calibration data under Law 4") — a structurally similar
  problem (checked-in, regenerable, provenance-stamped data that must never be hand-edited) whose
  proposed governance pattern is worth reusing for this task's corpus format.
- `docs/REVIEW.md` Law 13 (full text) and Law 4/Law 6 (reference reproducibility) — the governing
  rationale for treating diverging inputs as a permanent, checked-in artifact rather than
  session-local output.
- `docs/adr/NNNN-continuous-fuzzing-regression-corpus.md` (expected; cite once available).

## Notes

- 2026-08-27: priority 6.0 — TCB T13 (git/build-cache/result persistence), ranked lowest (#8-adjacent, priority 7) of the TCB ledger's numbered items.

_(none yet — first entries append here as work begins; likely mechanical per-fuzzer plumbing
work (inline `## Design` section, waived-mechanical review) unless the corpus-format design
turns out to need genuine cross-fuzzer unification, in which case treat that specific design
choice as warranting a real review before implementation.)_
