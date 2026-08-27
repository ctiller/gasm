# 0023. Merge Discipline: Everything Reaches Main

## Status

Accepted, 2026-08-27.

## Context

The worktree-agent workflow ([`0007`](0007-worktree-agent-workflow-and-adversarial-review.md))
fans work out across many isolated branches and worktrees. A branch that passes review
but is never actually merged to `main` is indistinguishable, from the repository's
perspective, from work that was never done — and the more workstreams run in parallel,
the easier it is for a reviewed, ready branch to sit unmerged while the coordinator's
attention moves on to dispatching the next wave.

## Decision

The owner's own words, in full: "can you make sure everything is making it to the main
branch also." This is a standing check, not a one-time task: the coordinator is
responsible for confirming that reviewed, merge-ready work actually lands on `main`, not
merely that it exists somewhere in a worktree branch.

## Consequences

Merge trains (see the `PLAN.md` "Merge train N" entries) are the mechanism by which this
obligation is discharged; a merge train's completion is verified in the merged tree per
[`0007`](0007-worktree-agent-workflow-and-adversarial-review.md) (agents' claimed results
are unverified until independently re-run post-merge). Any coordinator status report that
lists a branch as "MERGE-READY" without a corresponding landed commit on `main` is
incomplete under this decision. This obligation extends to the coordinator's own
governance/doc work once [`0020`](0020-coordinator-work-is-reviewed.md)'s review pass
clears it — a reviewed coordinator change that never reaches `main` is the same failure
mode as an unmerged agent branch.

## Provenance

Owner-stated. The owner's own words, quoted in full above.
