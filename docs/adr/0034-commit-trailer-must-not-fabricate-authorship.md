# 0034. Commit Trailer Must Not Fabricate Authorship

## Status

Accepted, 2026-08-27. (PLAN.md D21.)

## Context

During the open-sourcing push, the coordinator had instructed dispatched agents to write
`Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>` on commits, including on
commits whose actual work was done by Sonnet or Opus agents, not Fable. This was a false
attribution on two independent counts: it named a model tier that did not do the work,
and `Claude Fable 5` is not a string the harness's own trailer convention specifies. The
owner caught this directly.

## Decision

The owner's own words: "you're telling agents to state co-authored by: fable 5, which i
think is a fabrication."

## Consequences

Correct form going forward, for every agent-authored commit regardless of which model
tier did the work: `Co-Authored-By: Claude <noreply@anthropic.com>` — true without
asserting a specific model that did not do the work. Approximately 15 existing commits
carried the false trailer at the time this was caught; per D22/[`0031`](0031-flatten-not-history-scrub.md),
the flatten ruling makes those commits' trailers moot rather than requiring individual
correction, since history is dropped rather than rewritten. This decision is a standing
constraint on every dispatch brief going forward, independent of the flatten: no commit
trailer may name a specific model tier or agent identity that was not the one that
produced the work.

## Provenance

Owner-stated. The owner's own words, quoted in full above.
