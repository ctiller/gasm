# 0009. Findings Become Gates

## Status

Accepted, 2026-08-27. (PLAN.md D9.)

## Context

Two independent Phase 1 review cycles uncovered the same class of defect: a differential
oracle silently failing open. The x86 hardware semantics fuzzer had been a silent
fail-open no-op — a bare relative spawn path failed on Windows, and a `catch` synthesized
`faulted := true` for every vector, so the oracle never actually executed while reporting
a passing baseline (6/49 "passing"). Independently, the Wasm control-flow fuzzer
laundered V8's module-rejection errors through a `TRAP:` prefix into a reported PASS,
with 3 of 9 cases — the headline coverage — never executing at all. In both cases a
reviewer caught the defect by hand; per the north star in
[`docs/VISION.md` §2](../VISION.md#2-the-consequence-the-validation-gate-is-the-product),
a reviewer catching a bug by hand is evidence of a missing gate, not evidence the process
worked.

## Decision

Adopt [Law 13](../REVIEW.md#law-13-findings-become-gates-the-ratchet-law) as binding
policy: every review or fuzz finding must terminate in a mechanical prevention of its
whole class, in preference order — unrepresentable by construction, kernel-checked
theorem, build-failing linter, and only where the world itself is being sampled, mandatory
positive/negative oracle control vectors. An oracle that cannot run must fail the run; it
must never no-op, skip, or synthesize a result. Every dispatch must include the gate
obligation alongside the fix, and reviewer prompts weight this — "are we proving the
right theorems" (Pillar 2) is the one question that can never be delegated to a gate;
every other review finding marks a gate still missing.

## Consequences

Both discovered fail-open oracles were converted to `Except`-typed outcomes (type-level
fail-closed — no code path can synthesize a passing result) with mandatory
positive/negative/trap control vectors, per this decision, not as one-off patches. A
fail-open audit of every remaining oracle/harness error path (GzipFuzzer's Python
subprocess handling, spike `Test.lean` external-runner fallbacks, the NASM fuzzer) is
tracked as required follow-up (TASKS.md TC9). Mutation-coverage tooling (TASKS.md TC11) —
mechanizing what reviewers were doing by hand, catalog a mutation and require the suite to
go red — is the further mechanization this decision obligates for "executes" vs.
"discriminates."

## Provenance

Mixed. The north-star principle is owner-stated, verbatim: "yeah, the true value of
review in this system should be 'are we proving the right theorems' and everything else
should be implementation and mechanical (we're not there yet)," together with a separate,
sharper directive: "don't check pointwise, check forall -- and don't fix pointwise, fix
forall." Law 13's specific gate-preference hierarchy (unrepresentable-by-construction >
kernel-checked theorem > build-failing linter > oracle control vectors) and its framing
as "the ratchet law" are the coordinator's formalization of those two owner statements
into binding policy, not owner-specified at that level of detail.
