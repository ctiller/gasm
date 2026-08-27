# 0007. Worktree Agent Workflow and Adversarial Review

## Status

Accepted, 2026-08-27. (PLAN.md D6.)

## Context

Generated-code trust ([`0001`](0001-vision-and-insights.md)) has to be enforced at the
workflow level, not just the theorem level: an agent's self-reported "done" carries no
evidential weight. The repair epic needed a concrete process for fanning out
implementation work across multiple agents while keeping the merged tree the sole source
of truth — and Merge Train 2 supplied direct evidence for why re-verification in the
merged tree specifically (not just in each agent's branch) is load-bearing: both
mechanical gates caught a cross-branch violation on day one (an unallowlisted axiom
dependency introduced by one branch, invisible until the other branch's gate ran against
the merged result).

## Decision

Fan out sonnet agents into separate worktrees for implementation. Every branch goes
through adversarial review — the [Three-Pillar Verification Protocol](../REVIEW.md#4-the-three-pillar-verification-protocol)
(mechanical CI gates, adversarial semantic/domain-gap hunting, structured architectural
audit) — before merge, conducted by Opus reviewers. An agent's claimed results (tests
passed, gates green, bugs fixed) are treated as unverified until independently re-run in
the merged tree; fix cycles for review findings return to the same implementing agent's
worktree rather than starting fresh.

## Consequences

No merge lands on self-report alone. The repeated pattern seen across Phase 1 branches —
review verdicts of MERGE-WITH-FIXES or REJECT followed by a fix cycle and re-review, with
reviewers independently reproducing claimed mutations and finding additional bypasses
each round — is this decision operating as intended, not a process failure. Review
findings that are not "are we proving the right theorem" questions are themselves
findings against a missing mechanical gate, per [`0009`](0009-findings-become-gates.md);
bar-triggered deep re-reviews ([`0010`](0010-bar-triggered-deep-re-reviews.md)) are the
periodic, fresh-eyes escalation of this same discipline.

## Provenance

Mixed. The core mechanics are owner-stated, in two separate remarks: "you can fan out
sonnet agents in different worktrees for implementation," and, offered as a tentative
suggestion rather than a mandate, "i was going to suggest opus agents for reviewers if
you need." The full Three-Pillar Verification Protocol, the specific "no merge on
self-report alone" framing, and the fix-cycle-returns-to-the-same-worktree procedure are
the coordinator's elaboration of those two remarks into a complete workflow, not
owner-specified in that detail.
