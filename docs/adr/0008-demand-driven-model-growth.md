# 0008. Demand-Driven Model Growth

## Status

Accepted, 2026-08-27. (PLAN.md D7.)

## Context

The project's predecessor, `wsc` (the Lean library inside that repository is
namespaced `Lasm`), died in a specific, instructive way: it built out large portions of
the ISA as code before the instruction model was right. Once a mountain of code depended
on a wrong model, repair cost exceeded the cost of rebuilding the project from scratch.
This is the single most consequential lesson carried forward from that project's failure.

## Decision

Adopt [`docs/VISION.md` §3.3](../VISION.md#33-grow-models-demand-driven-validate-before-building-on-them)
as binding practice: target models (instructions, API surfaces, capabilities) stay
deliberately incomplete and grow only on spike demand (Law 5), never speculatively or in
bulk. Every increment is differentially validated in the same change that introduces it,
before anything depends on it — an incomplete, validated model is an asset; a complete,
unvalidated one is a liability.

## Consequences

"Complete the ISA" is explicitly ruled out as a goal at any point in the roadmap. Phase 3
(validating the existing unvalidated half of the x86 model — memory-operand and branch
instructions currently marked `canFuzzHardware := false`) is the direct countermeasure to
the `Lasm` failure mode: it forces validating what already exists before growing further,
rather than growing further before validating. The graphics pre-build audit's top finding
— six speculative target pairings with zero Lean code and a D7 violation flagged
explicitly — is this decision being applied retroactively to catch a plan that had
already drifted into bulk-import thinking; see
[`GRAPHICS_PREBUILD_AUDIT.md` §9](../../GRAPHICS_PREBUILD_AUDIT.md#9-verdict-and-top-10-pre-build-fixes),
item 5.

## Provenance

Owner-stated. The owner's own words, describing the predecessor's failure directly:
"wsc failure: we didn't get the instruction model right and built out too much of the
isa as code - so going back and fixing it was more expensive then rebuilding," and,
separately, tying the lesson to this project's practice: "that's why we have incomplete
isas now and spike by spike development to catch errors early." The specific name
`Lasm` for the predecessor is a documentation error corrected in this pass — the owner
named the predecessor project `wsc` (a private, unpublished repository); `Lasm` is the Lean
library namespace inside that repository, not the project's name.
