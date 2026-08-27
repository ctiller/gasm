# 0021. Coordinator Role: Executive Function and Mandatory Delegation

## Status

Accepted, 2026-08-27.

## Context

Across the repair epic the orchestrating coordinator had, by default, no stated
boundary on how much investigation, implementation, or review work it should perform
itself versus dispatch to agents. Left unstated, the coordinator's own habits (reading
code directly, running commands directly) compete for the same context window that
holds the plan, the ledgers, and the accumulated findings — the resource this whole
repair epic depends on staying available across a long session. The gap is exactly the
one [`0020`](0020-coordinator-work-is-reviewed.md) later addresses for review coverage;
this ADR addresses it for role scope itself, and precedes 0020 in the transcript.

## Decision

The owner's own words, defining the role directly: "also a note on your role: executive
function, planning, occasional spot checks, but i want you to farm out the work as much
as possible, both implementation and review -- i'd rather you read a short report than
do the investigation wherever possible." Two operational parentheticals from the same
period sharpen the dispatch rule at the point of decision: "(get that implemented -->
have an agent implement)" and "(figure out -- if obvious think it, if it needs research
choose an agent)."

## Consequences

The coordinator's default action for implementation work is dispatch, not direct
execution; for investigation, the default is a dispatched report, read short, rather than
the coordinator performing the investigation itself. The "if obvious think it, if it
needs research choose an agent" test is the operational filter applied at each decision
point: trivial, already-known facts may be reasoned about directly; anything requiring
non-trivial investigation goes to an agent. This is also the mechanism [`0007`](0007-worktree-agent-workflow-and-adversarial-review.md)'s
worktree fan-out and [`0020`](0020-coordinator-work-is-reviewed.md)'s coordinator-review
requirement both presuppose: neither makes sense unless the coordinator's own role is
first scoped down to executive function plus spot checks. Every dispatch brief written
under this ADR is expected to itself instruct sub-agents to preserve the model-tier and
delegation discipline (see [`0025`](0025-model-tiers.md)).

## Provenance

Owner-stated. Both the role-defining directive and the two operational parentheticals are
the owner's own words, quoted verbatim above. Nothing in this ADR beyond directly
restating those words is owner-specified; the "if obvious think it" filter's role as an
operational test, and the cross-reference to how it interacts with 0007/0020/0025, are
the coordinator's synthesis of the owner's three statements into one policy.
