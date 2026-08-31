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
| Establish that a proof build reads the committed source under review | `scripts/check_no_ignored_lean_sources.py` | repository source/build boundary, before cached compilation | every hosted Lean-bearing build and the unfiltered local gate | it establishes source identity, not theorem correctness; an intentional uncommitted source remains a reported failure rather than something the gate may remove |
| Execute a list of local steps and compose the result | `Gasm.Proof.LocalExecution.runSteps_append` | target-independent list algebra | x86-64 and AArch64 macro assemblers | fetch, faults, fuel, host effects, termination, instruction admission, and artifact identity stay target-owned |
| Lift a one-step frame fact over a list | `runSteps_preserves`, `runSteps_preservesOutside` | target-independent observation algebra | AArch64 memory, SP, flags, fault, termination, and GPR frames; x86-64 composed GPR frames | the target supplies the one-step theorem and clobber classification |
| Compose frame facts without clobber-order obligations | `preserves_comp`, `preservesOutside_comp`, `preservesOutside_comp_append` | target-independent observation algebra | x86-64 segment composition and the shared list-execution consumers | append is only a conservative union representation; uniqueness and order are irrelevant |
| Preserve an x86 64-bit read across a lower, non-wrapping write | `Gasm.Targets.X86_64.X86_64Mem.read64_write_below` | x86-64 memory semantics | Spike 2 decimal authority and Spike 5 native proofs | address arithmetic, write width, nowrap, and strict-below premises remain explicit; this is not a target-independent memory model |
| Show bounded finite exploration contains only normative reachable states | `Gasm.MemoryModel.FiniteSearch.Enumerator.search_sound` | memory-model presentation/search boundary | the checked incomplete-enumerator negative control exercises the one-way guarantee | completeness is separate and may not be inferred from bounded fuel or a finite result |
| Prove bounded finite exploration complete for one exact finite fixture | reverse completeness in `Gasm.MemoryModel.FiniteSearchPositiveControls` (`2059cd3`) | private memory-model validation fixture | its proof consumes actual `ReachesAt` and the exact transition relation | fixture-only evidence; widening the relation with an unenumerated edge breaks the proof, and no generic completeness or production authority follows |
| Reuse canonical program-order transitivity | `ProgramOrderProjection.po_trans` | CPU-graph program-order projection | `ProgramOrderPath` (`e4857567`) removed its duplicate transitivity proof | the premise-free canonical consequence is reused unchanged; no stronger ordering relation is inferred |
| Recover stable from-read endpoint, source, and value facts | `fr_support`, `fr_source_value` | CPU-graph derived from-read layer | downstream from-read proofs (`4433e1d`) share the same existential source witness | target classification and independent facts remain outside the package |
| Recover a canonical atomic read source across fragments | atomic source/value/coherence/adjacency package in `Gasm.MemoryModel.CpuGraphAtomicRead` | CPU-graph atomic-read layer | combined-RMW controls (`4c980cf`) | redundant `readAt` premises are derived, not requested; this proves neither target classification nor linearization |
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
- Before exporting a helper, remove premises already implied by its strongest supplied evidence.
  `e4857567` reused the canonical premise-free program-order transitivity law instead of maintaining
  a duplicate path proof.  `4433e1d` and `4c980cf` package stable endpoint, source, value, coherence,
  and adjacency consequences around the same existential read-source witness, so consumers do not
  reconstruct that witness or resupply derivable `readAt` facts.  Package consequences that share
  one semantic witness; do not accumulate independent facts merely to produce a large theorem.

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

- Exact fallible-fold candidate `e533d83` demonstrates a deliberately narrow generic ownership
  boundary in `Stdlib.Control.FallibleFold`.  The generic layer owns only committed state, the
  accepted prefix, first refused input, untouched tail, and conservation plus accepted-transition
  theorems.  Spike 3's additive bridge preserves its existing pure ingestion and classified sort
  results by equality; resource identity, unique reclamation, cleanup, target execution, and final
  artifact authority remain consumer-owned.  The focused fold-plus-bridge build completed warm in
  1.7 seconds over 24 jobs.  The negative control is equally important: a proposed generic
  `ResourceAccounting` count snapshot was removed because it had neither two domain connections nor
  enough identity to prove unique reclamation or terminal cleanup.  Counts alone are not resource
  accounting when aliasing and ownership determine correctness.  A later single-job focused Spike 3
  WASI `Equivalence` build reached approximately 52.6 GiB RSS in one Lean process without a
  diagnostic and was stopped.  Do not attribute that event to this extraction: the fold modules had
  already passed, and no loaded rerun isolated the cause.  Preserve it as a build-triage observation,
  not performance evidence for or against the candidate.
- Dependent finite-table candidate `2d73a3a` keeps its public model representation-free as
  `(i : Fin n) -> family i`, while using a wrapped function-backed executable realization permitted
  by the facilities plan.  Its laws cover tabulation, dependent mapping, arbitrary finite
  reindexing, reindex identity and composition, and model/get roundtrips.  The first genuine
  consumer, `TypedCFG.ProgramPlan.block`, now expresses nominal remapping with dependent map while
  lowering through the sole existing `RecursiveCFGBuilder`; the table creates no parallel CFG
  authority.  The focused FinTable plus TypedCFG build completed in 3.4 seconds over 13 jobs.  An
  attempted dependent append/split API is the negative control: `Fin.addCases` left family
  transports observable and non-definitional at the `castAdd`/`natAdd` boundary, so the API was
  removed rather than export cast obligations to every consumer.  Append/split should remain on the
  roadmap until an implementation can internalize those transports.  With only one demonstrated
  consumer, this remains extraction evidence rather than canonical generic machinery.
- MP's provisional external-provider ruling supplies an extraction gate, not yet a reusable API.
  Keep the production runner functional and any future raw provider input universally quantified,
  default-empty, and semantically decoded by its target; missing, malformed, mismatched, and
  oversized inputs must totalize to explicit outcomes with bounded writes and defined authority
  return.  A synchronous emitted Win32 `GetMessage` path through the sole `VerifiedProgram` is only
  a checkpoint.  The neutral envelope is eligible to land only after a materially different
  synchronous Vulkan scalar/out-buffer consumer validates the same shape and both consumers are
  independently falsified.  A mismatch changes the still-unlanded shape rather than adding a
  compatibility facade.  Target-local operation identity, decoding, loans, exact frames,
  callbacks, and asynchronous consequences do not promote with the envelope.  This entry records
  the proof-method and two-consumer gate; MP owns the canonical architecture specification.
- Resource protocols supply three related negative controls.  A range/nonempty `MemoryPerm` is not
  generative or linear ownership.  Timeout-capable queue locks may return a typed outstanding-node
  withdrawal obligation rather than an immediately reclaimed auxiliary loan.  Destroying a handle
  or deleting a `PresentReady` table entry cannot erase evidence required to retire its backing
  generation.  Likewise operation terminality, notification, observation, buffer/registration
  return, queue reclamation, delivery, acknowledgement, persistence, and GPU completion remain
  distinct unless a selected profile proves a relation between them.  Reusable helpers should
  preserve these indexed obligations across the same witness; they must not collapse them into a
  count, Boolean completion flag, or destructive table update.
- Literal or Boolean-domain execution checks do not establish a universal finite-input theorem.
  Spike 3 still needs a theorem over every finite stdin with explicit reservation, allocation,
  read, output, exhaustion, and cleanup outcomes before its downstream production certificates can
  cease depending on grandfathered checks.  Narrowing the input domain is not proof reuse.
- A failure-path composition candidate should prove the successful prefix, first failure
  transition, unreachable untouched tail, and preservation of the relational ghost invariants and
  outstanding obligations consumed at the typed block boundary.  Applicability remains edge-local:
  an unselected failure mode adds no premise, while a selected local failure classification cannot
  erase resource-return or cleanup obligations.  Keep this in the candidate ledger until accepted
  code demonstrates the complete pattern.
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
- Separately compiled typeclass proof dictionaries are a candidate delivery mechanism for stable
  block-law schemas, complementary to forward-post/backward-precondition discovery.
  `LocalBlockDischarge` already has the right dictionary shape, while `LocalBlockRun.then` exposes
  the exact middle-state premise that composition must still prove.  A prototype may register a
  local, shallow instance for an explicitly named block/interface key and let final graph
  composition resolve that law; nominal `SourceScope`/`SourceRef` identity, selected artifacts,
  contracts, and arbitrary state facts must remain explicit and outside instance search.  Compare
  it against the existing explicit dictionary on identical theorems: consumer elaboration time,
  invalidated jobs, dependency closure, search depth, and ambiguity/coherence failures.  Do not
  extract a class unless two real blocks improve; Lean's compiled modules already avoid replaying
  imported proof bodies, so shorter call syntax alone is not evidence of proof-economy.
  The repeated module-local Spike 2 runtime instances expose a possible need for a
  platform-indexed proof environment, but they are not evidence that the current declarations are
  ergonomic or should be canonized.  A prototype must make cross-platform contamination
  unrepresentable or mechanically rejected; a high-priority global x86 interceptor entering Linux
  or generic proofs is the negative control.
- Block-chain congruence and associativity, with fallthrough-versus-jump reasoning delayed until
  realization, is a candidate extracted from the Spike 2 Windows prefix chain (`75d01c8` and
  `f90bfc9`).  The accepted-in-practice consumer first proves one exact typed execution outcome,
  classifies that outcome cheaply, and crosses the platform boundary through a named opaque
  admissibility predicate.  Do not generalize the chain algebra until a second consumer preserves
  the same exact outcome strength.  Negative controls are direct projection of platform
  admissibility from the dependent prefix witness and application of a fuel-recursive theorem at a
  concrete 50,000-step budget: both unfold the runner, timed out, and one attempt reached roughly
  19.2 GiB before cancellation.  The separated final equivalence target built in approximately
  4.4 seconds warm.  Host-runtime instances remain module-local or platform-indexed so an x86
  interceptor cannot enter Linux or generic instance search.
- A provisional linked-text boundary reported after accepted main `4863346` separates reusable
  local execution facts from platform admission.  A finite, reviewed linked-text authority should
  expose only the property needed at named reachable successors--for the current x86 use case,
  `read64 rip != rip`.  A generic `ordinaryAt` bridge can then combine successor membership and
  bounds with that projection to rule out both the Linux syscall pseudo-address and a Win32 IAT
  slot.  This replaces repeated OS-selector facts without claiming execution, placement, or final
  verification authority.  The proposed `IsPlatformAgnosticX86` split keeps local semantic/block
  certificates dispatcher-free; each concrete target must still provide exact placement/lookup
  and prove that every reached successor lies outside its interception surface.  ISA identity alone
  is not sufficient because placement may alias an OS boundary.  This remains a reported technique,
  not accepted machinery: the `ordinaryAt` theorem was still compiling locally and the proposed
  shared Spike 2 formatter/recurrence consumer had not yet demonstrated the boundary.
- Open nominal type-family admission in SPIR-V is represented by provisional candidate `fa98935`
  (the clean-lineage integration of `78b9397`), which supersedes the rejected public-`String`
  design in `71e6991`.  A finite `TypeFamilyDescriptor` proves its role list has no duplicates;
  `SelectedTypeFamilies` proves both unique family ownership and uniqueness of the flattened
  type-kind vocabulary before physicalization.  Raster declarations and mixed-table
  physicalization retain sealed-family inclusion evidence, so a public token alone grants no
  authority.  The explicit collision control rejects duplicate ownership.  A downstream
  pointer-family probe measured 28.51 seconds and eight prerequisite rebuilds with the closed role
  enumeration, versus 0.74 seconds and one leaf rebuild with the candidate boundary (maximum RSS
  1,635,992 KiB).  Real pointer-family consumer `b098734` adds no central type/role edit; its two
  cached leaf controls completed together in 0.756 seconds.  Its roughly 36.1-second, 80-target
  first root build is a one-time branch/object-lineage rebuild, not incremental pointer cost.
  Repair `7fc7752` makes pointer physicalization retain exact pointee-kind selection and carries a
  property-relative witness over only the sealed table's pointer declarations; its pointer-only
  negative control closes the prior admission hole without burdening unused base families.  Keep
  the family boundary provisional until ancestry and attribution review closes; it is not a
  universal plugin registry.
- Exact-descriptor SPIR-V value-family candidate `ed5f3bf16871285a272f131ee57ba0e816dcad38`
  (parent `19d36fd0defeab920b230bc02ce9b3b3718bd06b`) supersedes the coarse
  predecessor `9c7d80d`; it is evidence for the boundary, not yet canonical reusable machinery.
  Nominal value identity is `(ValueKind, exact AnyTypeRef, ordinal)`.  Allocation collision
  intentionally projects only the ordinal, rejecting reuse across families and types in the one
  physical Result-ID namespace; descriptor equality must not be weakened merely to implement that
  collision policy.  Core embedding is explicit and `CoreValueTyping` is derived only from exact
  `BodyTypeSelection`, with no ambient coercion or second physical map.  Raster sealing retains the
  selected family, exact mixed-type-table membership, position compatibility, and resolution.
  Controls distinguish same-role/same-ordinal values of different vector types, reject core/raster
  ordinal collisions, absent and incompatible types, prove core injectivity, and preserve distinct
  two-wide and four-wide vector types through the shared namespace.  At an identical warm frontier,
  the central `Types` probe took 14.939 seconds, invalidated 74 jobs, and reported 15,723.9 MiB
  aggregate peak memory; the leaf `RasterValue` probe took 2.282 seconds, four jobs, and 3,010.8 MiB.
  Full SPIR-V plus tests was green and both measurement worktrees were clean.  The demonstrated
  optimization is dependency-fanout avoidance through exact nominal descriptors and a leaf-owned
  extension, not lower per-process memory or generic final-emission authority.  The selected raw
  codec in `0a31cb8` remains evidence only for the target-owned encoding boundary.
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
