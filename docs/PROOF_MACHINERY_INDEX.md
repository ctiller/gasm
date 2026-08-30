# Proof machinery index

This index answers a practical question: **what is the shortest already-accepted path from a proof
need to reusable machinery?**  It complements [Practical proof tactics](PROOF_TACTICS.md), which
explains why the patterns work.  Entries here point to checked code, its owning layer, demonstrated
consumers, and the facts that deliberately remain local.

An entry is not permission to force a proof through the nearest abstraction.  Start with the exact
caller-visible theorem, compare it with the reusable result, and keep the semantic delta in the
layer that owns it.  If adapting the library costs as much as proving the local fact, record the
candidate rather than widening the library speculatively.

Treat the exact caller-visible obligation as the proof's speed of light.  Measure the current path
against it: extra premises, repeated semantic replay, adapters, imported modules, invalidated jobs,
and wall time are the burden delta.  Redesign ownership and interfaces until that delta shrinks;
do not shrink the theorem.  `LocalExecution` removed duplicated list induction for two targets, and
the decimal-pass boundaries reduced both rebuilt jobs and warm edit time.  A relocation with the
same dependency direction did neither and is the useful negative control.  Keep this comparison
diagnostic until repeated accepted cases justify new machinery.

## Find machinery by proof need

| Proof need | Reusable machinery | Owning layer | Demonstrated use | Deliberate boundary |
|---|---|---|---|---|
| Execute a list of local steps and compose the result | `Gasm.Proof.LocalExecution.runSteps_append` | target-independent list algebra | x86-64 and AArch64 macro assemblers | fetch, faults, fuel, host effects, termination, instruction admission, and artifact identity stay target-owned |
| Lift a one-step frame fact over a list | `runSteps_preserves`, `runSteps_preservesOutside` | target-independent observation algebra | AArch64 memory, SP, flags, fault, termination, and GPR frames; x86-64 composed GPR frames | the target supplies the one-step theorem and clobber classification |
| Compose frame facts without clobber-order obligations | `preserves_comp`, `preservesOutside_comp`, `preservesOutside_comp_append` | target-independent observation algebra | x86-64 segment composition and the shared list-execution consumers | append is only a conservative union representation; uniqueness and order are irrelevant |
| Preserve an x86 64-bit read across a lower, non-wrapping write | `Gasm.Targets.X86_64.X86_64Mem.read64_write_below` | x86-64 memory semantics | Spike 2 decimal authority and Spike 5 native proofs | address arithmetic, write width, nowrap, and strict-below premises remain explicit; this is not a target-independent memory model |
| Show bounded finite exploration contains only normative reachable states | `Gasm.MemoryModel.FiniteSearch.Enumerator.search_sound` | memory-model presentation/search boundary | the checked incomplete-enumerator negative control exercises the one-way guarantee | completeness is separate and may not be inferred from bounded fuel or a finite result |
| Preserve dependent CFG identity through lowering or nominal remapping | `Gasm.Compiler.TypedCFG.ProgramPlan.loweredBlock`, `lower_ref_exact`, and `lowerDefinitions_mapBlockId_block` | compiler CFG authoring/lowering | typed CFG lowering and x86-64 control-point remapping | matching names or entries do not substitute for equality of the complete dependent definition |
| Turn bounded UInt64 decimal progress into a reusable certificate | `Stdlib.Fmt.UInt64DecimalScheduleCertificate` and `Gasm.Targets.X86_64.UInt64DecimalScheduleRealization` | pure formatting schedule, then x86 realization | Spike 2 native decimal loop | the pure layer owns digit/count bounds; the target owns machine effects and the final production connection |
| Cache an exact selected x86 production prefix | `ProductionPrefix.SelectedPrefix.Cutpoint` | x86-64 eventful production semantics | canonical evidence carried by `LocalBlockRun` | a cutpoint proves an exact prefix only; it does not classify the caller's logical phase or prove termination |
| Discharge and compose an x86 local body contract | `LocalBlockDischarge`, `LocalBlockDischarge.refine`, and `LocalBlockRun.then` | x86-64 local contract/production-prefix bridge | accepted implementation-hole mechanism for proof-directed blocks | contracts and middle-entry facts remain explicit; CFG identity, placement, terminal outcomes, and artifact authority are separate |

## Proven composition patterns

- For an expensive exact execution proof, keep the complete certificate in its producer and export
  a separate typed boundary containing only the observations required by the successor.  The
  accepted Spike 2 Linux Row 8 proof uses `spike2_row8_selected_prefix` for the exact 64-transition
  execution.  `spike2_row8_opening_selected_prefix` consumes the predecessor-only
  `Row7BoundaryFacts.spike2Row7HeaderFacts`; the successor-facing
  `Row8BoundaryFacts.spike2Row8HeaderFacts` imports only `Row8BoundaryData` and exposes RIP,
  recurrence/ABI registers, stack, and fault facts.  Do not use the convenience re-export from
  heavyweight `Row8.lean` as the cache boundary.  Exact generator reproduction and output/event
  facts stay with the producer.  Clean builds measured roughly 24--37 seconds for boundary
  data/opening and about 1.6 seconds for final composition.  This is a proven proof-term caching and
  forward-boundary pattern, not yet a target-independent API.
- For one x86 body hole, package the canonical `SelectedPrefix.Cutpoint` in a `LocalBlockRun` and
  expose a `LocalBlockDischarge` for every admitted entry.  `refine` has the correct variance:
  strengthen the required entry and weaken or project the guaranteed exit.  `LocalBlockRun.then`
  applies the next discharge to the first run's exact final machine, reverse-event accumulator, and
  ghost state; `SequentialLocalBlockRuns.combinedPrefix` composes the real selected prefixes and
  event deltas.  The caller-logical `Result` classifies a proof phase only.  Native termination or a
  production outcome still needs separate target-owned terminal evidence.
- For a repeated production pass, distinguish the state projections consumed by the next layer
  from the larger state the proof currently computes.  Commit `25a375f` caches exact instruction
  projections in `DecimalStepFacts`, packages the seven-step extraction and five-step write
  contracts in `DecimalPass`, and leaves `DecimalSchedule` to compose phases.  Selected passes store
  only irreducible safety and placement evidence and derive redundant architectural effects as
  theorems.  The representative warm edit frontier fell from 12.64 seconds/seven rebuilds to 5.54
  seconds/three rebuilds, and the pass module from 1.5 seconds to 0.761 seconds.  The negative
  control matters: moving facts without reversing the dependency direction measured 12.65 seconds
  versus 12.64 seconds.  The reusable pattern is an observation-shaped invalidation boundary, not
  a new facts namespace.  Register-frame, `does_not_use_memory`, jump, and syscall summaries are
  likely consumers; their instruction and platform semantics remain owner-local.

## Admission record

Reusable extraction should leave a short audit trail.  Record:

1. the exact repeated local theorem or proof shape;
2. the lowest layer that owns the common semantics;
3. at least two real consumers, unless Trust explicitly requests the abstraction;
4. the before/after local proof burden;
5. focused build cost and dependency closure;
6. the negative boundary: tempting facts the abstraction does **not** prove; and
7. the canonical commit after independent review.

Two useful precedents are:

- `a7002a5` extracted local list execution and frame composition into
  `Gasm.Proof.LocalExecution`, migrated x86-64 and AArch64, and retained each target's established
  `runLocalSteps` reduction behavior through a small equality proof.
- `a65316a` extracted `X86_64Mem.read64_write_below`, migrated Spike 2 and Spike 5, and removed the
  duplicated local proofs without weakening their arbitrary-width or address-bound premises.
- `7b89615` introduced the canonical x86 `SelectedPrefix.Cutpoint` cache without adding a second
  evaluator; `81cc49a` built the accepted `LocalBlockDischarge` body-hole mechanism over it, with
  exact-middle sequential composition and no termination or artifact claim.
- `25a375f` separated x86 decimal instruction projections, one-pass contracts, and schedule
  composition.  Its before/after and unchanged-direction control demonstrate that dependency
  invalidation, rather than theorem relocation alone, produced the build improvement; the accepted
  implementation is integrated as `cec7e8e`.

Commit identifiers are provenance, not API names.  Follow the declarations above on current main;
use the commits to inspect the reviewed extraction delta.

## Indexed candidates, not yet reusable machinery

The following code shapes have enough evidence to investigate but are not canonical generic APIs:

- Bidirectional contract derivation for typed CFGs is not yet present.
  `Gasm.Compiler.TypedCFG.SourceScope` permits contracts to be declared before bodies, but the
  author still supplies them;
  `Gasm.Core.CFG.Invariant.alongReachable` checks an invariant over already defined block steps, and
  `Gasm.Targets.X86_64.VerifiedProgramCFG` connects reached blocks to exact emitted realizations.
  A candidate derivation layer would use the same named typed boundaries in both directions:
  propagate strongest useful reachable and ghost facts forward from the entry, propagate weakest
  requirements backward from exits and target postconditions, and alternate refinements to a stable
  contract at every join and loop invariant.  On x86, accepted `LocalBlockDischarge` now fills one
  such body hole and composes adjacent exact runs.  Graph-level contract derivation and closure are
  still absent.  Candidate combinators are monotone forward and backward transfer, checked join
  stabilization, and one closed-graph composition theorem—not a mandated worklist algorithm or
  automatic invariant discovery.  Failed inclusion should be reported at its edge rather than
  rediscovered by whole-path replay.

  Project each candidate contract into control, live data, relational ghost state, and outstanding
  obligations, retaining only observations consumed by adjacent blocks.  Final graph composition
  should request contracts only for selected, reachable blocks and edges, so absent features create
  no proof burden.  The Linux Spike 2 write-setup/syscall bridge is the active first bidirectional
  trial.  Its accepted result may justify transfer or inclusion lemmas; generic join/loop iteration
  still requires another real consumer and a measured dependency-closure comparison.

  Spike 2 Row 8 remains the concrete factored forward-boundary exemplar; it does not demonstrate
  derived contracts, backward propagation, or fixed-point convergence.  A generic consumer must
  also add a progress measure or runtime-enforced bound: closed-graph typing alone proves neither
  functional correctness nor termination.  Spike 3 should wait for accepted streaming, relational
  ghost-state, and resource-recovery invariants.  Keep generic worklist or dataflow iteration
  separate until the candidates in `docs/STDLIB_FACILITIES_PLAN.md` earn promotion.
- Bounded byte reads appear in ELF, x86-64, AArch64, PNG, Zlib, and Gzip.  A first cursor slice
  should validate against two consumers with the same offset/progress needs while keeping format
  errors and validation consumer-owned.
- Endian assembly is repeated across those formats, but read/write roundtrip laws should be
  extracted independently of cursor control flow.
- Variable-fuel production-prefix composition exists in x86-64 `EventfulSegment`; it stays
  target-owned until a second accepted consumer demonstrates the same algebra.
- Generic `ByteArray` facts in `Stdlib/Zlib/ByteArrayBridge.lean` are shared by PNG and Zlib but
  should move atomically so the neutral module does not inherit a codec dependency.

Candidate status is intentionally visible: it tells agents where the delta may be removable without
pretending the reusable contract has already been established.
