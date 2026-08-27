# 0026. Large-Systems-Planning Gate

## Status

Accepted, 2026-08-27. (PLAN.md D18.)

## Context

[`0019`](0019-review-model-and-spec-before-implementation.md) requires design review
before implementation for Law-5-class work generally, but says nothing about who decides
the *scope* of a design before it is even dispatched for authoring. For a design whose
resulting implementation will be large, a coordinator that pre-empts the owner with a
fully-formed design brief has already made scope decisions — what the subsystem covers,
what it excludes, what tradeoffs it resolves — that the owner may not have intended to
delegate. [`0025`](0025-model-tiers.md)'s systems-planning fable-tier option makes this
sharper still: a fable-tier design, dispatched cold, could lock in a vision-scale
architectural choice before the owner ever saw the question.

## Decision

The owner's own words: "large systems planning tasks: never sonnet, if we need to plan a
system we talk, we decide on the scope, and then you dispatch," and, defining the
threshold: "large means: >10kLOC will be written under the design."

## Consequences

A design task crossing the ~10kLOC threshold is never dispatched cold, regardless of
model tier — not to sonnet, and not pre-emptively to opus or fable either. The sequence
is fixed: a scoping conversation between the owner and the coordinator first, which
settles what the design covers and what tradeoffs it makes; only then does the
coordinator dispatch the design-authoring task (tier per [`0025`](0025-model-tiers.md) —
opus by default, fable only on the owner's explicit say). The coordinator's
responsibility going into that conversation is to bring the question, the options, and
the tradeoffs — not a pre-written design brief that already presumes an answer. At the
time of ratification, `PLAN.md` names PA2 (step-lemma/composition calculus), PA4 (Law 11
capability migration + Zlib), PA9 (VerifiedProgram as derived theorem), the graphics
subsystem (G2/G3/G5/G6/G7), N6 (networking buildout), and F6 (zlib optimization epic) as
gated on this scoping conversation; TC14, B3, and PA5–PA7 are flagged as borderline,
left to coordinator judgment about when the threshold is actually crossed.

## Provenance

Owner-stated. Both quotes above are the owner's own words. The specific task list gated
by this decision is `PLAN.md`'s tracking of which live tasks currently meet the
threshold, not a separate owner enumeration.
