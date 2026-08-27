# 0025. Model Tiers: Implementors, Reviewers, and Coordinator Tier by Phase

## Status

Accepted, 2026-08-27. (PLAN.md D17.)

## Context

As agent fan-out scaled (per [`0007`](0007-worktree-agent-workflow-and-adversarial-review.md)),
which model tier ran which kind of work — and which tier the coordinator itself ran
under, at different points in the epic — had been left to ad hoc choice. An incident on
2026-08-27 demonstrated the concrete cost of leaving it implicit: 11 direct dispatches
were correctly tiered, but nested grandchildren from three fan-outs were not, because an
omitted `model` parameter can silently inherit the session's top tier — "did i just see
fables launched as implementors?" was the owner's own reaction on observing it.

## Decision

The owner's own words, in two parts. The workforce/reviewer split and the coordinator's
own tier: "i authorized sonnets as implementors, opus as reviewers" — stated in direct
response to the fables-as-implementors incident, correcting it. And, on the coordinator's
own tier across the epic's phases: "that's the intent... bootstrapping i wanted fable,
running the queue i think we're ok -- for *systems planning* going forward (eg what does
the graphics subsystem look like, vision scale things) we might deploy fable on my say."

## Consequences

Workforce tiering: sonnet implements, opus reviews. Coordinator tiering: fable for
bootstrapping (standing up the system — the session in which these decisions were made),
opus for running the queue (dispatch/synthesis against an already-established DAG).
Systems-planning tasks (graphics subsystem design, vision-scale architecture) may be
escalated to fable, but only on the owner's explicit say — never as a default or at the
coordinator's own discretion; see [`0026`](0026-large-systems-planning-gate.md) for how
this interacts with the large-systems-planning gate. Every agent dispatch must pass
`model` explicitly, and every dispatch brief must instruct any agent it spawns to do the
same — the incident that prompted this ADR was specifically a case of an omitted `model`
parameter inheriting the session's top tier through a nested fan-out, not a case of
someone deliberately choosing the wrong tier.

## Provenance

Owner-stated. Both quotes above are the owner's own words. The "workforce" /
"coordinator tier" split as a taxonomy, and the explicit-`model`-parameter enforcement
rule, are the coordinator's operationalization of those two statements.
