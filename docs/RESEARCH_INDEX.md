# Research index

This index makes design research durable without confusing it with accepted semantics or reusable
proof machinery.  A note records evidence, unresolved questions, and the next falsifiable step.
Only checked Lean declarations, normative target documents, and the final verification/emission
authority described in `docs/REVIEW.md` can establish repository claims.

## How to use this index

Start with the guidebook's [burden-delta procedure](PROOF_TACTICS.md#eliminate-the-burden-delta).
This index stores candidate evidence and promotion conditions produced by that method; it does not
restate the proof-authoring procedure or turn measurements into accepted semantics.

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
| Memory-model carriers and provider worlds | [candidate ledger](PROOF_MACHINERY_INDEX.md#memory-model-carriers-and-provider-worlds) | Mixed accepted design guidance and explicitly provisional implementation shapes | Preserve exact identities and relational worlds; promote only landed declarations with real consumers |
| Graphics and compiler proof economy | [candidate ledger](PROOF_MACHINERY_INDEX.md#graphics-and-compiler-proof-economy) | Accepted guidance plus superseded and integration-blocked candidates | Keep target/API authority local and measure the invalidation frontier of every extension |
| Resource, concurrency, and checked access | [candidate ledger](PROOF_MACHINERY_INDEX.md#resource-concurrency-and-checked-access) | Negative controls and design-only checked-x86 brief | Land the canonical typed-world/profile seam before presenting checked access as implemented |
| Proof delivery, termination, and CFG composition | [candidate ledger](PROOF_MACHINERY_INDEX.md#proof-delivery-termination-and-cfg-composition) | Candidate combinators separated from accepted local certificates | Require another real consumer, exact outcome strength, and measured dependency closure before extraction |
| Linker and target-family admission | [candidate ledger](PROOF_MACHINERY_INDEX.md#linker-and-target-family-admission) | Provisional linked-text and SPIR-V family boundaries | Close ancestry, attribution, collision controls, and exact target-owned admission before promotion |
| Byte and production-prefix utilities | [candidate ledger](PROOF_MACHINERY_INDEX.md#byte-and-prefix-utility-candidates) | Repeated shapes without a justified neutral owner yet | Demonstrate two matching consumers without importing codec or target semantics upward |
| Controlled x86 ISA expansion | [current qualification](X86_ISA_EXPANSION_PREREQUISITES.md#current-qualification-controlled-scalar-scale-is-ready) | MP+Reviewer-accepted and Trust-integrated design guidance; implementation contract pending | Pilot only deterministic current-state scalar forms; close scale gates before unconstrained expansion and keep excluded classes behind their owning seams |
| SPIR-V/Vulkan architecture and promotion | [`GRAPHICS_ARCHITECTURE.md`](GRAPHICS_ARCHITECTURE.md) and the SPIR-V entries in [`PROOF_MACHINERY_INDEX.md`](PROOF_MACHINERY_INDEX.md) | Candidate commits are recorded, not imported as authority | Close ancestry/attribution review, then preserve one identifier namespace during value-family migration |
| Win32 windowing source intake | [`WIN32_WINDOWING_INTAKE.md`](WIN32_WINDOWING_INTAKE.md) | Research plan; deliberately nonnormative | Register, fetch, hash, and review each official source before authoring `TARGETS/WIN32_WINDOWING.md` |
| External-reference mechanics | [`REFERENCE_INDEX.md`](REFERENCE_INDEX.md) | Canonical workflow | Keep source bytes out of the publishable tree and make drift explicit |

## Promotion rule

Research becomes guidebook prose after accepted code demonstrates it.  It becomes reusable Lean
machinery only when at least two real consumers reduce local burden without broadening dependency
closure or moving target semantics upward.  Commit identifiers in research notes are provenance,
not API names.  Provisional notes must remain explicit when their source commits are not on main.
