# 0001. Vision and the Three Insights

## Status

Accepted, 2026-08-27.

## Context

The project needed a stated foundation before the repair epic's governance documents
(Laws 10–12, the review protocol) could be written against anything: what is `gasm` for,
and why does correctness work concentrate where it does. The forcing evidence was
concrete and already in hand — a target realization had legitimately satisfied a
pointwise equivalence theorem by emitting a single hardcoded output stream, because the
theorem only examined the one input the stream was precomputed from (the Spike5-Wasm
canned-stream exhibit; see [`0002`](0002-native-decide-restricted-to-exhaustive-finite-domains.md)
for the mechanical countermeasure). That was not a violation of the gate as designed — it
was the gate working as designed, badly. Any framework built on generated, untrusted
implementation code needs a first-principles answer for why that failure mode is
structural, not a one-off bug, before it can decide what to build next.

## Decision

Ratify `docs/VISION.md` as the project's founding statement, superior to every other
design document when a question is ambiguous. Its content is canonical and cited here,
not restated:

- [Insight 0](../VISION.md#insight-0-concrete-implementation-code-is-discardable) —
  implementation code is discardable; the durable artifact is the formal boundary.
- [Insight 1](../VISION.md#insight-1-programs-are-formal-boundaries-on-what-must-be-true) —
  a program is a formal statement of what MUST be true of any implementation.
- [Insight 2](../VISION.md#insight-2-agents-generate-the-low-level-boundaries-keep-them-honest) —
  agents generate the low level; boundaries keep them honest.
- [§2, The Consequence](../VISION.md#2-the-consequence-the-validation-gate-is-the-product) —
  the validation gate, not the generated code, is the product of this repository.
- [The Target Systems](../VISION.md#the-target-systems) — game engines, operating
  systems, web/gRPC servers, databases are the demand horizon that every later
  demand-driven extension (Law 5, [`0008`](0008-demand-driven-model-growth.md)) grows
  toward.

## Consequences

Every subsequent architectural decision in this repository is answerable to this
document: when a design question is ambiguous, it resolves against `docs/VISION.md`, not
against local convenience. Every ADR that follows in this directory is, in one sense, a
consequence of this one — Laws 9–13 and the workflow decisions below are the mechanical
instruments for holding the line this document draws. Review attention shifts
permanently away from implementation style and onto contracts, models, and the gates
that check them (VISION §6).

## Provenance

Owner-stated. The three insights are the owner's own framing, from the session's
founding message: "we don't care about the concrete code that's written anymore, that's
discardable - so rust, c, etc ought to be dead languages" (Insight 0); "we care about
large scale system correctness - so programs should be high level formal boundaries on
what MUST BE true of the implementation" (Insight 1); "agents can creatively and quickly
churn out assembly and other low level artifacts, especially if they have a formal model
and boundaries to work within" (Insight 2). The target-system list is likewise the
owner's own words, from a later message: "just to push on scope here: the target systems
we'll build with gasm are game engines, operating systems, web/grpc servers, databases."
The specific prose of `docs/VISION.md` (section structure, "gate-is-the-product" framing,
the canonical exhibit) is the coordinator's drafting of these owner-stated points, not a
verbatim owner text.
