# 0017. Task-DAG Operating Mode

## Status

Accepted, 2026-08-27.

## Context

`PLAN.md`'s original Phase 0–6 structure imposed a strict linear sequencing that the
epic's actual dependency structure did not have: independent workstreams (build
performance, networking, graphics, performance modeling) could proceed in parallel once
their individual prerequisites were met, and forcing them into phase order was blocking
readily-available work behind unrelated phase completion.

## Decision

`PLAN.md`'s phases are downgraded to advisory/historical status. The live plan is
`TASKS.md`: a happens-after task DAG, where each task lists explicit `after:` edges to
its true prerequisites rather than a phase number, and **BARs** mark the points on the
DAG that trigger a fresh-agent deep re-review
([`0010`](0010-bar-triggered-deep-re-reviews.md)), replacing the fixed per-phase
checkpoint. Work proceeds by grinding through whatever tasks are currently ready (`[ ]`
with satisfied `after:` edges), with the critical paths to graphics and networking made
explicit as first-class chains in the DAG rather than implicit in phase ordering.
Decisions, ledgers, and history stay recorded in `PLAN.md`, `MODEL_DEBT.md`,
`GRAPHICS_PREBUILD_AUDIT.md`, and `TCB.md`
([`0013`](0013-tcb-ledger-and-trust-implies-fuzzer.md)) — `TASKS.md` records only the
DAG and status, not rationale.

## Consequences

The repair epic's exit criterion is restated in DAG terms rather than phase-completion
terms: **we trust the system enough that spec & model review is something we do,
implementation review is something we trust mechanically** — i.e., mechanical gates
(Laws 10–13, [`0002`](0002-native-decide-restricted-to-exhaustive-finite-domains.md),
[`0009`](0009-findings-become-gates.md)) have absorbed enough of what adversarial review
currently does by hand that human/agent review attention concentrates on
[`0001`](0001-vision-and-insights.md)'s one irreplaceable question. Any future planning
document that reintroduces strict phase sequencing as the primary tracker supersedes this
ADR explicitly rather than silently reverting practice.

## Provenance

Mixed. The core idea — a task list with happens-after edges, replacing rigid phasing, with
bars for deep re-review — is owner-stated: "phasing i think is advisory, really we should
have a task list with happens-after edges, and grind through (with some bars for when
it's worth deep re-review by fresh agents)." The specific realization — a separate
`TASKS.md` file, the `after:` edge syntax, `PLAN.md` retained for decisions/ledgers/history
while `TASKS.md` carries only DAG and status — is the coordinator's implementation of that
owner-stated concept, not owner-specified in that detail.
