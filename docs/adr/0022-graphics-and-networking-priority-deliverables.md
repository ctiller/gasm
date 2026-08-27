# 0022. Graphics and Networking as Priority Deliverables

## Status

Accepted, 2026-08-27.

## Context

The task-DAG operating mode ([`0017`](0017-task-dag-operating-mode.md)) lets independent
workstreams proceed in parallel once their prerequisites clear, which raises an ordering
question a pure dependency graph cannot answer on its own: when multiple ready tasks
compete for the same dispatch capacity, which ones should the coordinator prioritize
first? Until this ADR, that preference existed only as an aside inside a different
decision's transcript context, unrecorded anywhere in the ADR corpus despite directly
shaping which critical paths the DAG treats as first-class chains.

## Decision

The owner's own words, offered as a coda to a set of numbered answers about repair-epic
process questions: "the task list carries a bonus (for me) -- i'm quite eager to have
graphics and networking built out here." This is a stated preference among ready and
future work, not a reordering of prerequisites — it does not license skipping a
workstream's Law 5 design gates or its D18 large-systems-planning gate
([`0026`](0026-large-systems-planning-gate.md)) to get there faster.

## Consequences

`TASKS.md`'s explicit critical-path framing for graphics and networking (recorded in
`PLAN.md`'s operating-mode header: "critical paths to graphics and networking are
explicit there") is a direct response to this stated preference. When the coordinator has
discretion over which of several equally-ready tasks to dispatch next, graphics-track
(G-prefixed) and networking-track (N-prefixed) tasks are weighted accordingly — subject
to all other gates (D18 scoping conversations for the large designs among them,
[`0008`](0008-demand-driven-model-growth.md)'s demand-driven growth discipline, and
[`0019`](0019-review-model-and-spec-before-implementation.md)'s design-before-implementation
requirement). This ADR records a priority preference, not an exemption from any other
ratified gate.

## Provenance

Owner-stated. The owner's own words, quoted in full above. This ADR was previously
unrecorded — the audit that produced this remediation pass found it "recorded NOWHERE
despite shaping the DAG's critical paths," which this ADR corrects.
