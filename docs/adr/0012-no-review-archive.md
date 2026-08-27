# 0012. No Review Archive

## Status

Accepted, 2026-08-27. (PLAN.md D12.)

## Context

The repair epic's self-audit (PLAN.md Gaps register, 2026-08-27) flagged that all Opus
review reports and dispatch briefs from Phase 1 live only in temporary directories, and
raised committing a `reviews/` archive per merge train as a candidate fix — on the
grounds that the Three-Pillar protocol's artifacts are also calibration material for
future reviewers. This decision reconsiders and rejects that fix.

## Decision

Do not maintain a persistent `reviews/` archive. A review's value is as **proof-of-work
and falsifiability at read time** (someone should read them and believe them): does this
specific review, against this specific diff, satisfy the Three-Pillar protocol
([`docs/REVIEW.md` §4](../REVIEW.md#4-the-three-pillar-verification-protocol)) right now.
Once a fix cycle lands and a re-review has run against it, the prior review's findings are
consumed — its judgments about a codebase state that no longer exists are not durable
calibration data; the codebase itself, its gates, and its live `PLAN.md`/`TASKS.md`
entries are the durable record.

## Consequences

Review artifacts stay ephemeral by design, not by oversight; the earlier self-audit
finding is superseded by this ADR. Durable institutional memory about *decisions* lives
in this `docs/adr/` directory instead ([`docs/adr/README.md`](README.md)) — which is
exactly why ADRs, unlike reviews, are immutable and permanent: a decision's justification
stays true regardless of later codebase state, where a review's verdict does not. Any
future proposal to persist review artifacts must supersede this ADR explicitly rather
than quietly reintroducing a `reviews/` directory.

## Provenance

Owner-stated. The owner's own words, in full: "i would skip, they're instantly stale:
the reason for writing them down is to establish a protocol of proof of work, and
falsifiability by the reader (someone should read them and believe them)." An earlier
pass through this ADR dropped the parenthetical gloss when restating the rationale in the
Decision section; it is restored above.
