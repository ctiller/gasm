# 0015. `read` as the Universal Binder

## Status

Accepted, 2026-08-27. (PLAN.md, Phase 4; folded into Law 9.)

## Context

[`0002`](0002-native-decide-restricted-to-exhaustive-finite-domains.md) closes the
gameable-gate problem for finite domains, but the codebase's live evasion shapes needed a
structural answer for the infinite case specifically: the Spike5-Wasm canned-stream
exhibit is a hardcoded-output stub; a parallel, subtler shape found in Spike5's own
equivalence proof is domain-shrinking — `GzipOp | compress` / `GunzipOp | decompress` are
single-constructor types, so `∀ op` technically quantifies over one element while the
spec ignores the parameter entirely, passing both the twin-detection linter and a casual
Law 9 reading. A third shape, pointwise evaluation, is what Law 10
([`0002`](0002-native-decide-restricted-to-exhaustive-finite-domains.md)) already closes
for finite domains but not for `ByteArray`-shaped input.

## Decision

Adopt the `read`-is-the-universal-binder principle, now folded into
[Law 9](../REVIEW.md#law-9-universal-quantification-input-completeness-mandate-the-anti-pointwise-law):
every monadic input operation in a spec (`readFile`, `recv`, `accept`, console reads —
every form of `read`) binds an arbitrary result, and the contract must be parametric in
that binding — the continuation is proven correct for *any* returned `ByteArray`: any
contents, any length, including partial reads, empty reads, and EOF. A contract that pins
a read's result to a concrete vector is unrepresentable as verified.

## Consequences

This closes all three known evasion shapes structurally rather than by review vigilance:
a spec that reads cannot be satisfied by a hardcoded-output stub; domain-shrinking via a
purpose-built input enum is foreclosed because the read binds the real byte-array domain,
not a spike-defined stand-in; pointwise evaluation cannot discharge a claim over a bound
variable. Because `read` may return any chunking of the input, input-side chunk-robustness
becomes a forced universal obligation as a corollary — the dual of the output coalescing
congruence ratified in [`0014`](0014-observation-standard.md). The Phase 4 census of
mock-verification patterns (Tier 1: constant functions ignoring the environment; Tier 2:
domain-shrinking via single-constructor enums, Spike5 first; Tier 3: legitimate
finite-∀ composition) is the migration priority order this decision sets: Tier 2 first
since it is also the gzip epic's bed, then Tier 1. The successor `VerifiedProgram`
contract shape (Phase 4) is designed around read-continuations as its ∀ entry points.

## Provenance

Mixed. The owner's own words, stated as a personal preference rather than as a universal
or exclusive rule: "`read` (in all its forms) is my preferred vector for forcing
reasoning forall byte arrays -- the high level monadic read should force reasoning over
any result for proofs." The framing adopted here and in Law 9 — `read` as *the*
universal binder, the single structural mechanism that forecloses all three known
evasion shapes (canned-output stubs, domain-shrinking enums, pointwise evaluation) — is
the coordinator's generalization of the owner's stated preference into a binding,
exclusive enforcement mechanism. The owner did not himself claim exclusivity or
universality for it; that step is the coordinator's.
