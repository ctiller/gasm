# 0033. Autonomous, Saturated Dispatch to a Trustable Base

## Status

Accepted, 2026-08-27. (PLAN.md D20.)

## Context

Early in the repair epic, the coordinator's dispatch cadence was implicitly gated on
turn-by-turn owner check-ins. As the task DAG ([`0017`](0017-task-dag-operating-mode.md))
matured and the worktree-agent fan-out pattern ([`0007`](0007-worktree-agent-workflow-and-adversarial-review.md))
proved out, the owner ruled explicitly on how hard the coordinator should push, and what
it means for repair to be "done."

## Decision

The owner's own words, verbatim: "autonomous mode, maximize saturation, let's get to a
trustable base".

## Consequences

The coordinator dispatches to the practical capacity ceiling without waiting for
turn-by-turn approval, sequencing against the task DAG's frontier, and stops only for the
gates the owner has separately set ([`0026`](0026-large-systems-planning-gate.md)'s
scoping conversations, [`0025`](0025-model-tiers.md)'s fable authorization, law
ratification). "Trustable base" is the repair epic's exit criterion restated: spec and
model review is something the project does by hand; implementation review is something
it trusts mechanically. The practical dispatch ceiling observed on the development
machine is roughly 11 concurrent agents before dispatch rate-limiting and build
contention dominate — an operational fact, not part of the ruling itself, recorded here
because it bounds how "maximize saturation" is actually exercised.

## Provenance

Owner-stated. The owner's own words, quoted in full above.
