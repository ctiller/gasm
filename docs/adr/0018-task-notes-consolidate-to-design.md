# 0018. Task Notes Consolidate to Design

## Status

Accepted, 2026-08-27. (PLAN.md D14.)

## Context

[`0017`](0017-task-dag-operating-mode.md) moved planning from a single narrative
`PLAN.md` to per-task tracking because conversational and phase-narrative context gets
compressed away over a long-running epic — decisions and findings that only exist as
prose in an old session are effectively lost. The same failure mode applies one level
down, to design thinking itself: an agent's working notes while investigating a task
(false starts, half-formed invariants, "tried X, didn't work because Y") are exactly the
material most likely to be silently discarded once a session ends, and exactly the
material a later agent most needs when picking the same task back up or debugging a
regression in it.

## Decision

Working notes are recorded **append-only** against the task file as they arise —
investigation, dead ends, partial results, all of it, timestamped and never deleted.
Before implementation begins, notes are **consolidated into a design**: a full
`docs/`-level [Law 5](../REVIEW.md#law-5-the-stop-and-design-invariant) stop-and-design
document for model/contract-shaping work (new typeclasses, capability shapes, effect
semantics — anything a future Lean declaration would cite via `REF:`), or an inline
`## Design` section within the task file itself for purely mechanical work (orchestration,
tooling, no new modeled concept). Implementation dispatches reference the design, never
the raw notes — the notes are what got you there, the design is what implementation is
held accountable to.

## Consequences

Task files carry both a `Notes` section and a `design` frontmatter field (already present
on live task files, e.g. `docs/tasks/PA1-crc32-pathfinder.md`,
`docs/tasks/TC5-gate-runner.md`); a task with Law-5-class scope and an empty `design`
field is not yet eligible for implementation dispatch. The planned task-DAG checker
(tracked as `TC13` in the concurrent `docs/tasks` buildout) is expected to enforce
design-before-implementation mechanically once it lands, in the same spirit as
[`0009`](0009-findings-become-gates.md). Dead ends recorded in Notes become cheap
institutional memory — a later agent re-deriving the same failed approach is a cost this
decision is meant to eliminate. This ADR and [`0019`](0019-review-model-and-spec-before-implementation.md)
were ratified together (D14) and are read as a pair: this one shapes how a design comes
to exist; the other governs what happens to it before implementation may begin.

## Provenance

Owner-stated. The owner's own words, in full: "discipline: record notes against the
task, consolidate into a design before implementation." The specific mechanics —
append-only Notes sections, the `design` frontmatter field, the Law-5-class vs. inline
`## Design` distinction — are the coordinator's operationalization of that one-sentence
directive.
