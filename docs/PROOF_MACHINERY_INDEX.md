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

- Four isolated memory-model checkpoints demonstrate useful proof shapes but are not integrated and
  must not be read as current-main APIs.  Reverse-completeness fixture `2059cd3` consumes actual
  `ReachesAt` evidence and the exact transition relation; widening the relation with one unenumerated
  edge breaks the proof, unlike the rejected insensitive shape `state <= fuel -> reported`.
  `e4857567` removes a duplicate program-order transitivity proof by reusing the canonical
  premise-free `ProgramOrderProjection.po_trans`.  `4433e1d` and `4c980cf` package endpoint, source,
  value, coherence, and adjacency consequences around the same existential read-source witness so
  consumers do not reconstruct it or resupply derivable `readAt` facts.  The candidate lesson is to
  remove premises implied by stronger evidence and package consequences sharing one semantic
  witness--not to bundle independent facts into one theorem.  Promote declarations only after their
  exact commits integrate and current main contains the named modules.
- Exact fallible-fold candidate `e533d83` demonstrates a deliberately narrow generic ownership
  boundary in `Stdlib.Control.FallibleFold`.  The generic layer owns only committed state, the
  accepted prefix, first refused input, untouched tail, and conservation plus accepted-transition
  theorems.  Spike 3's additive bridge preserves its existing pure ingestion and classified sort
  results by equality; resource identity, unique reclamation, cleanup, target execution, and final
  artifact authority remain consumer-owned.  The focused fold-plus-bridge build completed warm in
  1.7 seconds over 24 jobs.  A second materially different candidate consumer now exists in
  `Stdlib.Zlib.Streaming`: the fold commits codec state, `AllocationScope`, and emitted chunks, while
  a domain refusal returns its post-attempt `AllocationScope` inside the consumer-owned error
  payload.  Thus generic refusal still commits no successor state, but the domain can account
  exactly for resources touched by the failed attempt.  The first green bridge accumulated output as
  `accumulated ++ newlyEmitted`: its equivalence theorem was behaviorally correct, but repeated
  left-append made the production driver quadratic.  Reviewer correction `4a6b806` carries the
  difference list `emitOutput : List ByteArray -> List ByteArray`; an accepted step composes
  `fun tail => prior (newlyEmitted ++ tail)`, and final observation applies it to `[]`.  This keeps
  the legacy right-associated order with constant-time accumulation per step and linear final
  materialization.  Proof equivalence alone is therefore not enough evidence for an extraction that
  replaces production code: preserve the relevant cost shape too.

  The correction also exposes `driveStreamingFoldResult`, the raw `FallibleFoldResult`, before the
  legacy projection.  Generic conservation, accepted-prefix, and refused-boundary laws now apply
  directly; `driveStreamingViaFallibleFold_eq` still preserves the legacy driver for arbitrary push
  function, state, scope, and input, and compression plus decompression consume it.  The initial
  focused bridge build completed green in about 2.3 seconds over 23 jobs.  Reviewer confirmed the
  corrected difference-list formula, order, and linear-materialization explanation; do not transfer
  the initial measurement or canonical status without a corrected run and integration.  The useful
  proof pattern generalizes over the output accumulator, splits both the recursive
  fold result and legacy driver result, uses associativity on success, and eliminates incompatible
  failure equalities.  Direct rewriting beneath the fold's accepted-prefix reconstruction match did
  not fire; split the recursive fold result instead.  The prior Spike 5 `RuntimeContext` mismatch
  was repaired and independently accepted at `80f19e7`; it is no longer a blocker attributable to
  this extraction.  No runnable whole-program connection has yet been reported to this ledger, so
  independent review and an exact completion report still precede canonical promotion.

  The abstraction negative control is equally important: a proposed generic
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
- MP-authored provider candidate `988463a21a828c4cc0478a78048eb49025796226` (parent main
  `36771e2`) supersedes `360f86c` and blocked `355a6f7`; it remains a pre-hardening candidate.
  After integration,
  `docs/ARCHITECTURE.md` §2.1 and `docs/GRAPHICS_ARCHITECTURE.md` §2.3 are the canonical mechanism
  and rationale.  The proof-facing extraction gate is concise: one emitted Win32 `GetMessage`
  `VerifiedProgram` earns checkpoint acceptance, while the neutral raw envelope may land only after
  a materially different synchronous Vulkan scalar/out-buffer consumer validates it and both are
  independently falsified.  A mismatch revises the still-unlanded shape without compatibility debt;
  target-local identity, decoding, loans, frames, callbacks, and async consequences do not promote
  merely with the envelope.  The blocked predecessor supplies four durable controls.  A provider
  state wrapper is dead unless actual load, run, and admissibility relations initialize, consume,
  and advance it.  Queue exactness accounts for head, tail, counter, and consumption history rather
  than only the current payload.  Pre-enqueue readiness and post-enqueue durable retirement evidence
  are distinct; a one-shot witness cannot discharge later generation retirement.  Finally, deferring
  `DispatchMessage` does not remove callback/reentrancy behavior that `GetMessage` itself permits at
  retrieval time.  The latest correction adds a fifth control: distinct nominal `OperationId` and
  `ResponseId` tags do not establish distinct generative histories if both draw from one aliased
  sequence.  Give them independent counters, exact advance conditions, and separate
  prefix-preserving disposition histories, with controls that reject cross-history reuse.  The
  callback transcript must also be result-indexed: callback fault, process termination, or nonreturn
  is terminal, and a `GetMessage` result exists only after every retrieval-time callback returns
  normally.  MP-authored canonical-doc correction candidate
  `563c9acfbe0db35ded3c826f5adf63b01deadb32` (parent main `1dc7686`) records this terminality and
  registered-wait-compatible readiness; its checks pass and Reviewer verdict is pending.  These are
  active design constraints, not landed provider machinery.

  Provider identity has a separate generativity control.  Namespace-only checkpoint `d9685b5` does
  not obtain freshness merely from a sealed existential or rank-2 interface.  Production requires a
  runner-allocated generative `ExecutionInstanceId` root with uniqueness evidence, independent
  root-indexed operation and response sequences, opaque provider mutation, and target-specific
  transitions.  It must not expose a globally comparable erased correlation token.  Reviewer is
  actively attacking this proposed boundary; it is not established machinery.
- Resource protocols supply three related negative controls.  A range/nonempty `MemoryPerm` is not
  generative or linear ownership.  Timeout-capable queue locks may return a typed outstanding-node
  withdrawal obligation rather than an immediately reclaimed auxiliary loan.  Destroying a handle
  or deleting a `PresentReady` table entry cannot erase evidence required to retire its backing
  generation.  Likewise operation terminality, notification, observation, buffer/registration
  return, queue reclamation, delivery, acknowledgement, persistence, and GPU completion remain
  distinct unless a selected profile proves a relation between them.  Reusable helpers should
  preserve these indexed obligations across the same witness; they must not collapse them into a
  count, Boolean completion flag, or destructive table update.  Readiness need not forbid enqueue:
  enqueue may consume a registered wait.  The correction is that pre-enqueue one-shot readiness is
  not the durable post-enqueue evidence needed for exact generation retirement.
- The first multithreading vertical-demo ruling requires actual emitted Windows x86-64
  `CreateThread`, successful thread-object wait/close, and the sole production `VerifiedProgram`.
  Its first payload is deliberately one-shot: child ordinary store, join publication, then parent
  ordinary load--neither atomic RMW nor a cooperative scheduler presented as hardware concurrency.
  Before lifecycle types harden, the canonical M0 envelope must close heterogeneous structural
  identity: profile-indexed generative agents, references, events, relations, consequences, binding
  generations and rebind invalidation, plus exact origin/projection with a CPU projection and opaque
  non-CPU sentinel.  M0 imposes only laws selected by that structure, not every target consistency
  theorem; an unselected single-threaded program incurs no concurrency premise.

  The Windows demo must totalize `CreateThread`, thread-object wait, and close failures while
  preserving every result-indexed obligation.  `WAIT_OBJECT_0` supplies the selected join-publication
  synchronization; actual concurrency permits the child to execute before `CreateThread` returns.
  Any proof assuming parent-return-before-child is therefore a scheduler trace, not this demo.

  Accuracy follow-up `67bf9db02bb335b373d558feb142fe10d1a15c47` supersedes `4a27b2e` on
  canonical main `2a0ff225ae8521ceeed31c60f92ccbeffa79dc4c`.  It preserves the MP- and
  independently Reviewer-accepted semantics of `ecd5f9ec5da481c4eca0ee85765c9571f709ad24`.
  Reviewer nevertheless held the exact first public shape because the current ternary relation
  `Prop` has no stable relation-occurrence identity; exact redesign and re-review are required before
  Trust integration.  The minimal proposal under review adds a stable `RelationOccurrenceId` and
  relation-occurrence record carrier, plus a reserved `ConsequenceOccurrenceId`; it is not yet an
  accepted interface.  The checkpoint implements only the thin
  structural `Envelope` slice: existential event coverage, finite duplicate-free carriers,
  event-agent and relation-endpoint laws, nonsemantic carrier-list order, proportionate eliminators,
  and private positive plus malformed-carrier controls.  Public `Domains` carries opaque
  `Consequence` vocabulary for the heterogeneous envelope, but proves no consequence carrier
  membership, identity, occurrence/path binding, semantics, fidelity, admission, or authority.  It
  likewise proves no target fidelity, execution admission, binding, or aliasing law.  Binding-history
  work remains gated; this checkpoint does not complete M0 or the native-thread demonstration.

  Signature review accepted the layer split but held implementation for four failures.  An
  unrestricted `PathConsequence.value` could invent completion, visibility, or resource return
  without profile admission.  Capturing a value plus generation inequality did not correlate the
  later use occurrence, so it did not reject stale re-resolution.  Exact list equality exposed
  irrelevant carrier order and supplied no stable identity for equal duplicate consequences.  A CPU
  carrier partial bijection alone did not prove the generic relation-occurrence/path roundtrip.
  Revised signatures must keep `Execution` thin; select `BindingHistory` with a stable use
  occurrence; carry event/generation-indexed overlap evidence; make consequence admission
  profile-owned; identify occurrences generatively; compare consequence carriers by `List.Perm` plus
  a bijection and CPU carriers by permutation; and prove the generic relation-occurrence/path
  roundtrip separately before M0 exit.  These are structural obligations only--target consistency
  and admission remain above M0.  Multi must return the revised signatures before implementation;
  MP will author canonical `MEMORY_MODEL` interface text only after the shape stabilizes.
- A Microsoft x64 process-entry-only, no-return straight-line body may clobber nonvolatile registers
  only when target-owned entry and termination evidence proves that no caller, unwind, or callback
  continuation can observe them.  Keep the exact clobber set and make no callable claim.  This is an
  applicability boundary, not an ABI exception: a future callable wrapper must consume that clobber
  set and prove ordinary preservation.  Do not extract a generic save/restore API before that real
  consumer demonstrates the reusable shape.  Reviewer found this ruling sound under the stated
  no-caller/no-unwind/no-callback exclusions; it remains unlanded.
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
