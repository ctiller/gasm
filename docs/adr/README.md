# Architecture Decision Records

This directory holds the project's ratified decisions as immutable, dated records. An
ADR captures the **decision event**: the problem or evidence that forced it, what was
decided, and the expected consequences — not the normative text itself when that text
already lives elsewhere.

## What belongs here, and what doesn't

- An ADR records that a decision was made, when, why, and what follows from it.
- Where the decision's normative wording already lives in a canonical spec — a Law in
  [`docs/REVIEW.md`](../REVIEW.md), a section of [`docs/VISION.md`](../VISION.md) or
  [`docs/EQUIVALENCE_PROOFS.md`](../EQUIVALENCE_PROOFS.md), an algebra in
  [`docs/SYSTEM_EFFECTS.md`](../SYSTEM_EFFECTS.md) — the ADR **cites** that text with a
  relative link. It does not restate or paraphrase it. This is Law 12 (No Unlinked
  Twins) applied to documentation itself: two copies of the same normative fact,
  unlinked, is exactly the defect Law 12 prohibits, and an ADR that duplicates a Law's
  wording is a twin like any other.
- Purely operational decisions (workflow, tooling process, review cadence) that have no
  canonical spec home elsewhere are written out directly in the ADR's `## Decision`
  section, since there is no other authoritative text to cite.

## Numbering

ADRs are numbered sequentially, `NNNN-short-slug.md`, in ratification order. Numbers are
never reused and never renumbered.

## Immutability

**An accepted ADR is never edited.** Once its status is `Accepted`, its Context,
Decision, and Consequences sections are historical record and stay exactly as
ratified — including when the decision later turns out to be wrong, incomplete, or is
reversed. A changed decision gets a **new** ADR that states `Superseded-by: NNNN` in the
old record's `## Status` section (added as a status update, not a rewrite of the body)
and the new record states `Supersedes: MMMM`. Typo/formatting fixes that touch no
normative content are the only mutations permitted to an accepted ADR's body.

**Note (2026-08-27 remediation pass).** ADRs 0001–0020 in this directory were corrected
in place — not superseded — on 2026-08-27, to fix attribution and modality errors found
by a trajectory audit (misquoted owner text, coordinator design filed under the owner's
name, one invented owner-attributed fact, and a predecessor-project misnaming). This is
consistent with the immutability rule above rather than an exception to it: the entire
corpus was same-day and uncommitted at the time of correction, so no accepted-and-shipped
record was altered — nothing had left draft state to become the historical record this
rule protects. This note exists so the fact is stated once, here, rather than by
manufacturing a superseding ADR for every corrected entry.

## Format

Every ADR has exactly these sections:

```markdown
# NNNN. Title

## Status

Accepted, date YYYY-MM-DD.
(Supersedes: MMMM / Superseded-by: MMMM — only when relevant.)

## Context

The problem or evidence that forced the decision. Concrete: cite the finding, the
finding's source, or the failure mode, not a generic justification.

## Decision

What was decided. If normative wording exists elsewhere, this section cites it with a
relative link and states only the decision to adopt it — it does not reproduce the
wording.

## Consequences

What follows: what changes, what becomes required, what future work this obligates or
forecloses.
```

## Citing an ADR

ADR sections are ordinary `docs/` headings and are citable via `/- REF: ... -/` (see
[`docs/REVIEW.md`](../REVIEW.md) §1) exactly like any other design-spec section — e.g. a
Lean declaration whose existence is *because* of a ratified decision, rather than
because of a Law's normative content directly, may cite the ADR that decided it.

## Every future ratified decision gets one

The day a decision is ratified, it gets an ADR. This directory is the append-only log of
"what did we decide, and why" across the life of the project; it is deliberately not
pruned or archived the way `docs/REVIEW.md`'s Pillar-3 review artifacts are (see
[`0012-no-review-archive.md`](0012-no-review-archive.md) for why reviews and decisions
are treated differently).
