---
id: TC17
title: Vacuity floors — kill zero-vector auto-PASS across all fuzzers
status: implementing
blocked_on: ""
after: []
related: []
bar: ""
track: trust-core
priority: 7.8
priority_set: 2026-08-27T18:25:47Z
design: "inline"
design_review: "waived-mechanical"
date: 2026-08-27
---

# TC17: Vacuity floors — kill zero-vector auto-PASS across all fuzzers

## Context

Sourced from `TCB.md` **T11-b** (folded into T11 "The silicon itself," but flagged by TCB as
"cheap, priority 2" in its own right — read as effectively tied for TCB's #5 ranked item). This is
the generalized, mechanized version of a defect class this repository has already been burned by
twice: the x86 hardware fuzzer and the Wasm control-flow fuzzer were both found, independently, to
report "all green" when their oracle silently never ran (see TC1/TC2's history in PLAN.md — the
fail-open no-op and the V8-rejection-laundered-via-TRAP finding). Both of those were fixed at the
harness level with `Except`-typed outcomes and mandatory positive/negative controls. TCB's T11-b
finding is the sibling defect those fixes didn't close: **a fuzzer that runs zero vectors and
reports success is a distinct failure mode from a fuzzer whose oracle silently no-ops** — it
doesn't even need a broken oracle, just an empty test list.

TCB's concrete evidence: "zero-state instructions record `passed := true, totalTested := 0`;
flipping every `canFuzzHardware` to `false` yields '0 fuzzed, 0 failed, exit 0'; same shape in
[the] Wasm fuzzer; **`PerfFuzzerCLI --count 0` prints '100% SUCCESS' with no oracle at all**." Each
of these is a live, constructible vacuous-pass path today — an agent (or a config regression) that
accidentally excludes every test case from a suite gets a green checkmark, not a red flag, which
is precisely backwards for a project whose entire trust model rests on gates that cannot be
passed by an incomplete implementation (`docs/VISION.md` §2's founding corollary: "Any gate that
an incomplete or incorrect implementation can pass will eventually be passed by an incomplete or
incorrect implementation").

This is mechanical (a floor check added to existing harnesses, no new model concept), hence empty
`design` pending an inline `## Design` section.

## Deliverables & acceptance criteria

- Every fuzzer/harness entry point in the tree — the x86 hardware semantics fuzzer, the Wasm
  control-flow fuzzer, `PerfFuzzerCLI`, and any other suite driven by a runtime vector count —
  gains a **nonzero-vector floor**: if the number of vectors actually exercised is zero (or below
  a stated minimum), the run must **hard-fail**, never print a success summary.
- Specifically close the three instances TCB names by number: the `canFuzzHardware := false`
  zero-state path reporting `passed := true, totalTested := 0`; the equivalent Wasm-fuzzer shape;
  and `PerfFuzzerCLI --count 0`'s "100% SUCCESS" output.
- Control vectors demonstrating the fix: run each harness with its vector count forced to zero
  (or all cases excluded) post-fix, and show the harness now exits non-zero with a clear "zero
  vectors exercised" diagnostic rather than a success summary. Include the before/after contrast
  in the completion report.
- Where a harness's "zero fuzzed" state is architecturally reachable only through a real
  precondition (e.g. all `canFuzzHardware` flags legitimately false for a given instruction
  family), the floor still fails the run — the fix is not "detect and explain," it is "detect and
  fail," per TCB's framing; a suite that fuzzes nothing has verified nothing, full stop.
- As a light companion (TCB pairs this with T11's broader point): each fuzzer's output should also
  state which/how many microarchitectures or engines it validated against ("validated on exactly N
  microarchitectures" per TCB's suggested disclosure), so a green run's evidentiary scope is
  visible, not just its pass/fail bit. This disclosure is a smaller ask than the floor itself —
  include it if cheap, but the floor is the required deliverable.

## Pointers

- `Gasm/Targets/X86_64/Fuzzer.lean` / `SemanticsFuzzerCLI` — the x86 hardware fuzzer's
  zero-state accounting (grep for `canFuzzHardware`, `totalTested`).
- `Gasm/Targets/Wasm/SemanticsFuzzerCLI` (or wherever the Wasm fuzzer's summary is assembled) —
  the equivalent shape.
- `Gasm/Targets/X86_64/PerfFuzzerCLI.lean` — the `--count 0` → "100% SUCCESS" path.
- `TCB.md` §T11 (T11-b specifically) in full.
- `docs/REVIEW.md` Law 13 (findings become gates — this task converts a review finding into a
  mechanical floor) and `docs/VISION.md` §2 (the vacuous-gate corollary this task is a direct
  instance of).

## Notes

- 2026-08-27: priority 7.8 — TCB ranked-top-8 #5 (T11-b vacuity floors — 'cheap,' a zero-vector fuzzer run currently reports a clean PASS).

_(none yet — first entries append here as work begins; mechanical task, consolidate into an
inline `## Design` section before implementation, `design_review: waived-mechanical`.)_
