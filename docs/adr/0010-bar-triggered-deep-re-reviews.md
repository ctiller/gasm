# 0010. Bar-Triggered Deep Re-Reviews

## Status

Accepted, 2026-08-27.
(PLAN.md D10.)

## Context

Per-branch adversarial review ([`0007`](0007-worktree-agent-workflow-and-adversarial-review.md))
catches defects local to a branch's diff, but not drift between the accumulated codebase
and the laws/docs that govern it, nor whether a phase's claimed outcomes actually hold
once everything is merged. D10 originally scoped this as a fixed per-phase checkpoint
(after each phase's merge train lands on `main`). The operating-mode change recorded at
the top of `PLAN.md` (2026-08-27) superseded phases as the organizing structure in favor
of `TASKS.md`'s happens-after task DAG; the re-review trigger moved with it.

## Decision

At designated **BARs** on the `TASKS.md` task DAG (not phase boundaries), a fresh Opus
agent — blinded to prior review conclusions, though it may read `PLAN.md`/`TASKS.md`/the
ledgers as the CLAIMED state to check against reality — re-does the deep codebase review
from scratch and reports: (a) drift between docs/laws/ADRs and code reality anywhere in
the tree, (b) whether merged work's claimed outcomes actually hold in the merged tree,
(c) new findings, ranked, across the whole codebase, (d) a tracking verdict against the
plan (on/off course), (e) the convergence metric — what fraction of findings are
right-theorem questions vs. mechanical catches, per the end-state-of-review standard in
`docs/VISION.md` [§2](../VISION.md#2-the-consequence-the-validation-gate-is-the-product).
That ratio is the meter tracked across these checkpoints for the whole epic.

The scope of a bar review is **always the entire codebase, never the recent work**. The
bar's *trigger* is a milestone, but its *coverage* is global: scoped review of a change
is what the per-branch adversarial reviewers already performed, and repeating it adds
little. The bar exists to catch what scoped reviews structurally cannot — unknown
unknowns, interactions between independently-reviewed changes, and rot in corners
nothing recent touched. Narrowing a bar to "re-review what just landed" is a process
violation of this decision.

## Consequences

`TASKS.md` currently designates four BARs: after the trust core (TC4+TC5), after the
proof-architecture pathfinder (PA1), before the networking model buildout (N6), and
before Spike 6 GPU implementation (G7). Each BAR is a scheduled fresh-eyes checkpoint, not
an optional one; placing a BAR before implementation work (rather than only after) is a
direct application of [`0008`](0008-demand-driven-model-growth.md)'s validate-before-building
discipline to the review cadence itself.

## Provenance

Mixed. The task-list/bar structure is owner-stated: "phasing i think is advisory, really
we should have a task list with happens-after edges, and grind through (with some bars
for when it's worth deep re-review by fresh agents)" — an earlier remark, from before the
DAG pivot, made the same basic request in phase terms: "periodically you should have an
opus agent re-do the deep review (maybe once per phase) and check how you're tracking."
The **global-scope-always** rule in this ADR's Decision section is present specifically
because the owner caught a coordinator drift from it: on reading a coordinator-authored
description of "Bar 1 (fresh-agent deep re-review of the trust core)," the owner wrote,
"this is a bit alarming -- you've narrowed the scope of the deep re-reviews." This is the
one confirmed instance in this corpus of the owner catching a coordinator drift from a
ratified decision by reading the record directly (see [`0020`](0020-coordinator-work-is-reviewed.md)'s
Provenance for the corrected count — an earlier draft of that ADR and of `PLAN.md`'s D15
claimed a second such catch that the transcript does not support).
