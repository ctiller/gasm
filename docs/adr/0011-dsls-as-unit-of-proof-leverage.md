# 0011. DSLs as the Unit of Proof Leverage

## Status

Accepted, 2026-08-27. (PLAN.md D11.)

## Context

The modular-decomposition strategy of [`0003`](0003-universal-equivalence-via-modular-decomposition.md)
still leaves an open question at every layer: what is the actual unit that a total
theorem should be proven about? A lesson imported from prior projects supplied the
answer, and the graphics pre-build audit (2026-08-27) supplied a live test case: it found
`SPIRV_VULKAN.md`'s synchronization design modeling GPU barriers as a resource-layout FSM
that omits RAW hazards entirely — the exact shape of bug a total theorem about a
*language* of command streams (rather than a per-program synchronization argument) is
built to prevent structurally.

## Decision

Adopt [`docs/VISION.md` §4](../VISION.md#4-tractability-modular-contracts-composed-proofs)'s
DSL principle as an operating rule: prove the language in total, once, and the proof
applies to every inhabitant. Reach for a DSL wherever there is a population of artifacts —
even a closed population, even a population of one, whenever a DSL separates the proof
into a reusable language-level part and a small program-level part. Every new subsystem
design starts by asking "what is the language here?"

## Consequences

Concretely, this decision reframes Phase 4's step-lemma library and composition calculus
as the total theorems of the assembly DSL (not a per-routine proof style), and identifies
the instruction registry's roundtrip gate as the closed-population exemplar already built.
Zlib's bit-reader/Huffman machinery is scheduled to become mini-DSLs with their own lemma
libraries before the "zlib to infinity" optimization epic. For the graphics path
specifically, per the audit's tactic note, two DSLs are adopted as the graphics tactic
rather than per-spike ad hoc reasoning: a **synchronization DSL** (race-freedom/happens-before
soundness proven in total over the command-stream language, replacing the layout-FSM
approach the audit flagged — see
[`GRAPHICS_PREBUILD_AUDIT.md` §2](../../GRAPHICS_PREBUILD_AUDIT.md#2-observation-standard-mapping))
and a **floating-point kernel DSL** (a Deterministic Shader Profile as a language, so
determinism and ULP-bound theorems are proven once per kernel-language membership rather
than once per shader).

## Provenance

Mixed. The general DSL-as-proof-leverage principle is owner-stated, verbatim: "one note
we've learned from other projects: dsls in lean are a superpower for proofs as we can
prove things about the dsl in total, and apply it to any program written in that
language (and they can compose done well); anywhere there's a population, even closed, a
dsl is a good idea; even if the population is one if it helps separate proofs we've done
a good thing." Its application to the graphics path is also owner-stated, but tentative
rather than mandatory in the owner's own words: "it's also the tactic we should apply for
the graphics work... i'm imagining a synchronization dsl, a floating point kernel dsl."
The two DSLs are the coordinator's adoption of that tentative framing as settled graphics
tactic — this ADR previously described them as "mandated designs," which overstated the
owner's "i'm imagining" into a directive he did not give in those terms; corrected here.
