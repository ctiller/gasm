# 0003. Universal Equivalence via Modular Decomposition

## Status

Accepted, 2026-08-27. (PLAN.md D2.)

## Context

Two obligations follow from [`0001`](0001-vision-and-insights.md): the Lean model must
be ∀-correct, and the model↔asm mapping must be ∀-equivalent. Stated as one monolithic
whole-program proof, universal trace equivalence is intractable for realistically sized
programs — there is no way to discharge "for all inputs, this entire binary matches this
entire spec" as a single proof obligation at any scale beyond a toy. Two tempting
alternatives were considered and rejected: fuzzing first (samples the domain, inherits
exactly the pointwise unsoundness [`0002`](0002-native-decide-restricted-to-exhaustive-finite-domains.md)
rules out) and monolithic whole-program proof (does not scale).

## Decision

Make universal correctness tractable via **modular decomposition**, per
[`docs/VISION.md` §4](../VISION.md#4-tractability-modular-contracts-composed-proofs):
per-routine contracts (precondition, postcondition, memory frame, ABI discipline, emitted
trace) stated over all valid inputs; local proofs against those contracts using
per-instruction step lemmas and loop invariants; composition rules (sequential, call,
loop) that assemble routine contracts into whole-program theorems, making
`VerifiedProgram` a *derived* theorem rather than a directly-discharged obligation. The
unit of generated work is the triple (contract, assembly, proof), authored together by
agents, per [`docs/EQUIVALENCE_PROOFS.md`](../EQUIVALENCE_PROOFS.md)'s three independent
split theorems (functional equivalence, callability/ABI, memory safety).

## Consequences

Proof burden becomes local: a routine's proof depends only on the step lemmas of the
instructions it uses and the contracts of the routines it calls, not on global program
state. This is the architectural premise that the step-lemma library and composition
calculus (Phase 4 / TASKS.md PA2–PA3) exist to implement, and that the crc32 pathfinder
(TASKS.md PA1) exists to validate end-to-end before more design is built on the
hypothesis. Memory-capability tokens ([`0004`](0004-adopt-core-capability-machinery-for-memory-safety.md))
double as the frame conditions that let these local proofs compose without global
reasoning — the two decisions are one mechanism viewed from two angles.

## Provenance

Coordinator-decided under delegation. The transcript records the owner's general mandate
for universal correctness (see [`0001`](0001-vision-and-insights.md)'s Provenance) but
contains nothing — no statement, question, or assent — addressing modular decomposition,
per-routine contracts, or the rejection of fuzz-first/monolithic-proof alternatives as the
specific strategy for making that correctness tractable. This decision was made by the
coordinator under the owner's delegation of implementation and design authority, not
stated or ratified by the owner directly. It is the clearest instance in this corpus of a
design filed as decided without any owner text behind it.
