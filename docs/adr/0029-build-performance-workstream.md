# 0029. Build-Performance Workstream

## Status

Accepted, 2026-08-27. (PLAN.md "Ongoing workstream — build performance.")

## Context

Build times had been creeping up over the course of the repair epic, and agent iteration
speed is bottlenecked directly on checker/build feedback latency — a slow build tax is
paid by every worktree agent, on every fix cycle, for the epic's entire duration. Unlike
most of this ADR corpus, this workstream has no numbered `D`-entry and no ADR of its own
until this remediation pass, despite being flagged by the audit as materially affecting
the repair epic's velocity (`PLAN.md`'s Ongoing Workstream section already tracked it in
prose, but no ADR recorded the owner's directive behind it).

## Decision

The owner's own words, across the messages that established this as a standing
workstream rather than a one-off cleanup: "the other thing you should be watching during
repair and ongoing is build times -- they've been creeping up, and they'll be critical
for our workflow"; "important to the point that i'd be supportive of keeping a sonnet
background thread on iterating on build performance as we repair then build"; and his own
hypothesis about where the win is: "and i think *most* of it comes from the correct
sharding."

## Consequences

Build performance is a standing sonnet background thread running through repair and
beyond, not a task that closes once addressed — `PLAN.md`'s "Ongoing workstream" section
tracks iteration state (iteration 1 done: phantom no-op diagnosis, cold-baseline
measurement, cascade analysis identifying `Instructions.lean`'s aggregator as the
top-payoff sharding target; iteration 2: aggregator restructuring, sequenced after the
decoder registry gate lands on the same files). The owner's sharding hypothesis is the
standing prioritization heuristic for this workstream: when choosing what to shard next,
prefer changes that reduce the transitive-dependency closure invalidated by a single-file
edit over other build-time optimizations, and validate against `scripts/build_baseline.md`
as the trend baseline.

## Provenance

Owner-stated. All three quotes above are the owner's own words. The specific
iteration-by-iteration findings (cascade analysis, phantom-no-op diagnosis) are agent
research conducted under this workstream's standing mandate, not separate owner
directives.
