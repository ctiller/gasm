# 0031. Flatten the Repository Rather Than Scrub History

## Status

Accepted, 2026-08-27. (PLAN.md D23.) Supersedes the surgical history-rewrite plan
recorded as D22 (`git filter-repo` path-glob excision of the non-redistributable
`references/intel_sdm/` corpus and the fabricated `Co-Authored-By: Claude Fable 5`
trailers).

## Context

The open-sourcing push ([`0025`](0025-model-tiers.md) and the Apache-2.0 licensing work
it preceded) surfaced two classes of history defect: roughly 15 commits carrying a
fabricated `Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>` trailer (D21), and a
non-redistributable vendored corpus (`references/intel_sdm/`, 928 files) present across
hundreds of historical commits. The plan on file (D22) was to excise both surgically from
history via `git filter-repo` before publication — preserving the rest of the commit
history intact. The owner then ruled a simpler and more drastic path: drop history
entirely rather than rewrite it.

## Decision

The owner's own words, in full: "we will flatten the repo as soon as the scrub is done -
history will be dropped."

## Consequences

This supersedes D22: the path-glob surgery across ~900 commits, and the trailer-by-trailer
fix-up, are both cancelled — the defects they targeted simply cease to exist once history
is dropped, rather than needing excision. This is cheaper, but more dangerous in a
direction D22 did not carry: only the final working tree is published, so every defect
present in the tree at flatten time becomes permanent public record, and anything recorded
only in a commit message is destroyed. Commit messages stop being a durable record from
this point forward; `PLAN.md`, `docs/adr/`, and `docs/tasks/` become the sole surviving
decision history of the project, and anything load-bearing must be written into the tree
itself before the flatten, not left to a commit message to carry. Two concrete
consequences follow directly: the Intel SDM frontmatter side-table (926 files: page
ranges, order number, printed page labels) exists nowhere else on earth and must be
extracted to JSON before the corpus is deleted and history dropped, or it is
unrecoverable; and the flatten itself is irreversible and gated on a pre-flatten checklist
(`docs/PRE_FLATTEN_CHECKLIST.md`) covering secrets, machine-local paths, redistributability
of every retained corpus, and license/attribution completeness.

## Provenance

Owner-stated. The owner's own words, quoted in full above.
