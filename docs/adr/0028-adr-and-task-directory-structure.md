# 0028. The `docs/adr` and `docs/tasks` Directory Structure

## Status

Accepted, 2026-08-27.

## Context

Two related problems were surfacing at once: decisions were being made and re-justified
without a durable, append-only record of *when* and *why* (the gap [`0001`](0001-vision-and-insights.md)
onward eventually fills via this very directory), and per-task working state — notes,
findings, design status — was living only in prose inside `PLAN.md`, a single
narrative document that, over a long-running epic, is exactly the kind of artifact that
gets compressed away for context reasons once a session ends. A single flat task list
also has no way to express genuine prerequisite structure or let a reader rank what
matters most right now.

## Decision

The owner's own words, across several remarks. On creating the ADR directory: "it's
probably worth picking up a docs/adr directory." On creating a per-task directory
separately from the single planning narrative, with the reason stated directly: "and
honestly probably a docs/tasks directory too... a document is going to get compressed for
context reasons." On why frontmatter (structured per-task metadata) beats prose for this
purpose: "frontmatter makes a better dag." And on the specific fields needed once the
per-task directory existed: "tasking ask (have a sonnet go off and build this): add a
priority: field to frontmatter, probably a float, and a related: linkset (you'll find
uses, trust me), and build a little python tool for you to pull up the frontier (ranked
by priority weighted leverage - recommend pagerank and taking into account all
linksets)," followed by the anti-staleness rule: "oh on dating -- let's have priority
auto-raise 1 point per hour so that we prohibit aging out."

## Consequences

`docs/adr/` (this directory) holds ratified decisions, immutable once accepted (see
`docs/adr/README.md`). `docs/tasks/` holds one file per task, each carrying frontmatter
including a `priority` field (float), a `related` linkset connecting it to other tasks,
and `design`/`design_review` fields tracking the [`0018`](0018-task-notes-consolidate-to-design.md)/
[`0019`](0019-review-model-and-spec-before-implementation.md) lifecycle. A python tool
computes the current frontier — the ready tasks ranked by priority-weighted leverage,
using a PageRank-style computation over the `related` linksets rather than raw priority
alone — so that a task connected to many other live tasks surfaces even if its own stated
priority is modest. Every task's effective priority auto-raises by 1 point per hour of
elapsed time since last touched, specifically to prevent a task from aging out of
consideration simply by sitting unaddressed while newer, louder tasks accumulate higher
stated priority.

## Provenance

Owner-stated. All four quotes above are the owner's own words, verbatim. The specific
tool implementation (PageRank-style ranking, the frontier-pulling mechanics) was
delegated per the owner's own instruction ("have a sonnet go off and build this") and is
sonnet-authored work under this ADR's directive, not owner-specified beyond the
requirements quoted above.
