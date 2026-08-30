# Research index

This index makes design research durable without confusing it with accepted semantics or reusable
proof machinery.  A note records evidence, unresolved questions, and the next falsifiable step.
Only checked Lean declarations, normative target documents, and the final verification/emission
authority described in `docs/REVIEW.md` can establish repository claims.

## How to use this index

Start from the caller-visible obligation: that is the shortest possible proof path.  Compare the
current path against it in premises, semantic replay, adapters, imports, invalidated jobs, wall
time, and memory.  The difference is the burden delta.  Redesign ownership and interfaces until
the delta disappears; never make the theorem weaker to make the measurement smaller.

Every candidate should record:

1. the exact need and owning layer;
2. accepted examples and a negative control;
3. what remains deliberately local;
4. dependency/build measurements with base, command, cache state, invalidated jobs, wall time, and
   peak memory where available; and
5. the review condition that promotes or rejects it.

## Current research map

| Area | Durable note | Status | Next evidence |
|---|---|---|---|
| Reusable proof algebra and proof dictionaries | [`PROOF_MACHINERY_INDEX.md`](PROOF_MACHINERY_INDEX.md) | Accepted machinery and visibly separated candidates | Two real consumers with equal theorem strength and measured proof/build burden |
| Practical proof patterns | [`PROOF_TACTICS.md`](PROOF_TACTICS.md) | Accepted-code guidebook | Add a tactic only after accepted code demonstrates it and name the owning layer |
| SPIR-V/Vulkan architecture and promotion | [`GRAPHICS_ARCHITECTURE.md`](GRAPHICS_ARCHITECTURE.md) and the SPIR-V entries in [`PROOF_MACHINERY_INDEX.md`](PROOF_MACHINERY_INDEX.md) | Candidate commits are recorded, not imported as authority | Close ancestry/attribution review, then preserve one identifier namespace during value-family migration |
| Win32 windowing source intake | [`WIN32_WINDOWING_INTAKE.md`](WIN32_WINDOWING_INTAKE.md) | Research plan; deliberately nonnormative | Register, fetch, hash, and review each official source before authoring `TARGETS/WIN32_WINDOWING.md` |
| External-reference mechanics | [`REFERENCE_INDEX.md`](REFERENCE_INDEX.md) | Canonical workflow | Keep source bytes out of the publishable tree and make drift explicit |

## Promotion rule

Research becomes guidebook prose after accepted code demonstrates it.  It becomes reusable Lean
machinery only when at least two real consumers reduce local burden without broadening dependency
closure or moving target semantics upward.  Commit identifiers in research notes are provenance,
not API names.  Provisional notes must remain explicit when their source commits are not on main.
