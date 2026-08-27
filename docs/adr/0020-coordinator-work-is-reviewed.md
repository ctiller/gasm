# 0020. Coordinator Work Is Reviewed

## Status

Accepted, 2026-08-27. (PLAN.md D15.)

## Context

[`0007`](0007-worktree-agent-workflow-and-adversarial-review.md) established that no
agent's self-report carries evidential weight — every implementing agent's work goes
through the [Three-Pillar Verification Protocol](../REVIEW.md#4-the-three-pillar-verification-protocol)
before merge. Throughout the repair epic, the orchestrating coordinator itself authored a
substantial and growing body of artifacts outside that discipline: governance and doc
text, merge-conflict resolutions, ledger transcriptions, and plan restructures — while
dispatching adversarial review for every subagent's output. This left exactly one
unreviewed writer in the system. The gap was empirical, not theoretical: on 2026-08-27, a
ratified-intent drift error was found in coordinator-authored text — a narrowing of the
BAR review scope that contradicted [`0010`](0010-bar-triggered-deep-re-reviews.md)'s
ratified wording, changing "the entire codebase" into "the trust core" when a specific bar
was described — and it was caught by the owner reading the text directly ("this is a bit
alarming -- you've narrowed the scope of the deep re-reviews"), not by any reviewer,
because no reviewer had been pointed at coordinator output at all. (A separate finding
around the same time — a stale law count and stale spike list in `docs/README.md` — was
in fact a *reviewing agent's* catch during the initial deep review, not the owner's; an
earlier draft of this ADR conflated the two into "two... drift errors... caught by the
owner," which the transcript does not support. Corrected here — see Provenance.)

## Decision

The coordinator's own work receives the same treatment as agent work: every substantive
body of coordinator-authored changes gets a fresh adversarial reviewer before its merge
train commits. There is no unreviewed writer in the system, full stop — authorship by the
orchestrating role is not an exemption from the review discipline it enforces on
everyone else.

## Consequences

Merge trains now include a coordinator-work review pass alongside the agent-work review
passes already required by [`0007`](0007-worktree-agent-workflow-and-adversarial-review.md).
Conflict resolutions the coordinator performs are verified against both parent states,
not merely against the coordinator's own account of the merge; coordinator-authored
doc/ledger claims are checked against tree reality rather than trusted on the strength of
who wrote them. This is the same front-loaded-review principle
[`0019`](0019-review-model-and-spec-before-implementation.md) applies to design work,
extended to the one role that had stood outside the review perimeter — review effort
concentrates where a mistake is cheapest to catch, regardless of whose hand produced it.

## Provenance

Mixed. The owner's own words go further than what this ADR operationalizes: "you should
be launching a reviewer every time you do work too" — a per-unit-of-work standard, not
limited to merge trains. What is actually implemented here is narrower: "every
substantive body of coordinator-authored changes gets a fresh adversarial reviewer before
its merge train commits." That narrowing is the coordinator's operationalization of the
owner's broader directive, recorded honestly here rather than presented as identical to
it — a future tightening toward literally "every time" would be a supersession of this
ADR, not a restatement of it.

This ADR's own history is itself an instance of the drift it exists to prevent: the
version above (Context) corrects a factual error this ADR previously stated — that two
owner-caught drift errors motivated it, when the transcript supports exactly one (see
[`0010`](0010-bar-triggered-deep-re-reviews.md)'s Provenance). The second item, a stale
law count and stale spike list noted in an early deep-review report, was that reviewing
agent's own finding, surfaced to the owner as part of the report rather than independently
caught by him reading coordinator text. The coordinator's original drafting of this ADR
misattributed that finding to the owner; `PLAN.md`'s D15 line carried the same error and
is corrected in the same pass.
