# Proof machinery index

This index answers a practical question: **what is the shortest already-accepted path from a proof
need to reusable machinery?**  It complements [Practical proof tactics](PROOF_TACTICS.md), which
explains why the patterns work.  Entries here point to checked code, its owning layer, demonstrated
consumers, and the facts that deliberately remain local.

An entry is not permission to force a proof through the nearest abstraction.  Start with the exact
caller-visible theorem, compare it with the reusable result, and keep the semantic delta in the
layer that owns it.  If adapting the library costs as much as proving the local fact, record the
candidate rather than widening the library speculatively.

Use the guidebook's [burden-delta procedure](PROOF_TACTICS.md#eliminate-the-burden-delta) to compare
the shortest required proof with its current delivery path.  This index records the reusable result,
evidence, and negative boundary after that comparison; it does not own a second optimization method.

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
| Stop a finite fold at the first refused input | `Stdlib.fallibleFold`, `fallibleFold_conservation`, `fallibleFold_acceptedPrefix`, and `fallibleFold_refused_boundary` | dependency-light pure control algebra | Zlib streaming plus Spike 5 accepted and zero-capacity refusal outcomes | resource identity, reclamation, cleanup, effects, target execution, and artifact authority remain consumer-owned |
| Lower bounded structured straight-line code to Microsoft x64 | `StructuredStraightLineMicrosoftX64Entry.lowerFunction` and its `LocalCertificate` | compiler's target-specific local lowering layer | canonical bounded Microsoft x64 entry backend | exact clobbers and local semantics are proved; process entry, non-return, platform outcome, PE placement, and `VerifiedProgram` authority remain separate |

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
- For fallible finite processing, `Stdlib.Control.FallibleFold` makes the accepted prefix, first
  refusal, retained remainder, conservation, and committed-state chain explicit.  Canonical
  `89c46f7` supplies the pure algebra, `c107938` connects Zlib compression and decompression by exact
  refinement, and `186f389` supplies runnable accepted/refused Spike 5 outcomes.  Zlib keeps
  post-attempt allocation scope in its own error and uses a difference-list output so the production
  replacement preserves linear accumulation.  The rejected generic count snapshot could not prove
  identity, reclamation, or cleanup; the first extensionally equal Zlib bridge used quadratic left
  append.  Those controls define the abstraction and cost boundaries.
- For a bounded target backend, prove source evaluation, instruction effects, bytes, frames, exact
  clobbers, and control-flow freedom locally, but do not let metadata assert entry or callability.
  The rejected `60e744f` carried proof-free Boolean authority tags.  Accepted replacement
  `dfead99b5441c6b78398bc4f2f3c13720a5c7582` removes them, and its identical tree is canonical as
  `11f60475de851c4abab0e6938890d2be7d61603e`.  Absence of a callable certificate is honest; a later
  PE terminal `VerifiedProgram` must still establish process entry, observer exclusions, placement,
  outcome, and final artifact authority.

## Admission record

Reusable extraction should leave a short audit trail.  Record:

1. the exact repeated local theorem or proof shape;
2. the lowest layer that owns the common semantics;
3. at least two real consumers, unless Trust explicitly requests the abstraction;
4. the before/after local proof burden;
5. focused build cost and dependency closure;
6. the negative boundary: tempting facts the abstraction does **not** prove; and
7. the canonical commit after independent review.

For each stdlib-worthy item, inventory three statuses separately: representation-independent
interface and laws, proved concrete representation, and executable implementation.  A pure function
or container needs two real consumers or a named Trust request before extraction; a runnable
end-to-end failure-boundary demonstration is a separate completion condition, not implied by the
generic laws.

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
- `89c46f7`, `c107938`, and `186f389` land the pure FallibleFold algebra, its Zlib refinement, and
  the runnable accepted/refused Spike 5 demonstration respectively.
- `11f6047` lands the bounded Microsoft x64 local backend after removing self-asserted authority
  metadata; it is a compiler-local certificate, not completion of the PE `VerifiedProgram` slice.

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
  registered-wait-compatible readiness.  Reviewer accepted the exact candidate; Trust integration
  is pending, so it is not yet current-main guidance.  These are active design constraints, not
  landed provider machinery.

  Provider identity has a separate generativity control.  Namespace-only checkpoint `d9685b5` does
  not obtain freshness merely from a sealed existential or rank-2 interface.  Deterministic pure
  `Platform.load` cannot mint a target-owned fresh root, and an `Environment` nonce is caller oracle
  data rather than freshness.  The current Environment-only `entryContext` likewise cannot carry
  root-indexed authority.  The resolved design requires a selected, state-threaded target-owned
  `LoadWorld` and `loadStep` connected through the sole `VerifiedProgram`.  Its exact result flows
  through root-indexed context establishment, admissibility, and behavior, universally quantified
  over every `WorldWF` input.  The observable specification remains Environment-only and
  root-irrelevant.  Two roots are distinct only when their loads sequence through the same world;
  stateless platforms use a canonical zero-burden discipline.  `BoundaryWorld` or capability
  establishment is insufficient unless changed to participate in the load transition.  No globally
  comparable erased correlation token is exposed.

  Blocked candidate `a4976bfe5ae9fb994ed8ed3a5597e99b32092194` (parent canonical main
  `31d1ac6`) specifies `LoadDiscipline`, a stateless `Unit` adapter, sole-`VerifiedProgram` world
  threading, and a selected `GenerativeLoadCertificate`.  The graphics specialization allocates its
  root plus operation/response identities in the exact load transition and rejects phantom or
  existential authority.  Reviewer and Trust blocked the candidate because `WorldWF` may be empty,
  making every universal load, `VerifiedProgram`, and generative-certificate law vacuous.  The repair
  must supply a target-owned `initialWorld` with `initialWorld_wf`, or an equivalent well-formed outer
  session start actually consumed by production; share the one exact dependent load result across
  entry establishment, admissibility, and behavior; and derive distinct roots for two sequential
  loads through that world.  For the stateless discipline, `Unit` and `True` provide the witness
  definitionally.  Superseding candidate `a88a6b1240d3e969cc881d233808fa0bd6e02c35`
  adds the initial world and proof, production world threading, one named dependent load-result index
  shared by entry/admissibility/behavior, a generative certificate tied to that exact
  discipline/result, witness-consuming handles, and derived two-load root distinctness.  Reviewer
  accepted the exact candidate with no remaining blocker.  The design is now canonical as
  `a83a5441054be8385eade44ce24e78cfb0cd3a49` within GitHub main
  `a62ca537f33e12be117f50c507fd462f92c3a5b9`.  `d9685b5` remains namespace-only; target consumers
  still require their own exact transitions and authority proofs.
- The graphics proof-economy worklist seeks theorem boundaries that preserve universal provider,
  memory, and authority claims while keeping final verification tractable.  Candidate shapes are: a
  total byte decoder paired with a sparse exact-write footprint and complement frame theorem; a
  head-strict provider transition with independent operation/response counters and append-only
  disposition history; definitional lifting of ordinary CPU steps over the provider wrapper; proof
  obligations selected only by imported capabilities; local `ProgramArtifact`, provider, entry,
  admissibility, and behavior certificates composed without unfolding final runners; structural or
  kernel negative controls instead of evaluation shortcuts; and SPIR-V instruction/value-family
  interfaces whose changes remain leaf-local.  Known failed shapes are provider queues inside ISA
  state, phantom or rank-2 hiding presented as freshness, a shared operation/response counter,
  `native_decide` controls, projecting `.cpu` through the old runner, `spec := run`, and central
  value-type edits that invalidate the target closure.  Keep this as a worklist until checked
  consumers and dependency/build evidence identify reusable declarations.
- Graphics tractability candidate `007212fd127c4e88d408aafb72cf4c643e4124b0` was re-authored directly
  on `a62ca53` and received a Reviewer exact-hash ACCEPT/no P1, but MP blocked its environment-prefix
  theorem; its other proof-economy layers conform.  The canonical finite
  Environment response list is replay input, not an appendable observation prefix: exhaustion has an
  explicit operation history, and loading a longer Environment may allocate a new root.  Therefore
  same-state continuation and prefix preservation across reloads are false.  The current theorem must
  concern finite execution prefixes of one exact loaded run; `blocked` is an outcome only when the
  target explicitly models it.  A future open/closed supply and same-root supply transition is a
  separate design gate.  Outcome reasoning must distinguish normal, blocked, continuing-divergent,
  and failure cases, and separate fairness-free cleanup safety from fairness-dependent eventual
  cleanup.  Replacement `c178dd7424f5535d295ba449da97404b68398184` on `a62ca53` corrects
  these semantics and is MP+Reviewer exact-hash accepted with no P1.  Trust landed its identical tree
  canonically as `7e498f22d3f5b8db01550abf976d4c2408fa9162`; this is established guidance, not a
  proof-library declaration.  Rejected `007212f` is superseded and is not an ancestor of the
  accepted replacement.
- Compiler-roadmap candidate `ee11b405b36c48fca1ebbcd6f4bf9f17c3fa2d0a` contains supported
  evidence but is MP-blocked as a design document.  Its replacement must classify SPIR-V as a
  first-class target ISA while separating shader frontends from platform APIs; scope exception,
  cancellation, allocation, cleanup, termination, ranking, and resource proofs to selected claims
  while reusing canonical ownership; add fault continuation/fallthrough and selected
  teardown/callback honesty to the Microsoft x64 entry gate; and state governance as MP design,
  Reviewer falsification, and Trust integration.  Actual follow-up
  `933efba56baa6793dda7336a424410c90d115d79` closes all four content findings, but its reported
  `933efba340...` hash is invalid and its actual parent is stale `36771e2`, not canonical `a62ca53`.
  Fresh replacement `d9c033a2b5d5b5007e49ffc60f50f4c73ed79d9d` re-authors the exact roadmap on
  `a62ca53` and is MP+Reviewer exact-hash accepted with no P1.  Trust landed the identical narrow
  delta canonically as `8db418abcc5789b62424c49ab3c16596196ff4d5`; this is established guidance, not a
  proof-library declaration.
- Graphics candidates `733501b`, `6044dad`, and `5c405ca` remain integration-blocked on old base
  `da60357`: rebasing them would resurrect noncanonical `WINDOWS_VULKAN_PROFILE.md`.  Any retained
  mechanism must be re-authored on canonical `a62ca53` and independently reviewed again.
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
  identity: profile-indexed nominal execution-local agents, references, events, relations,
  consequences, binding
  generations and rebind invalidation, plus exact origin/projection with a CPU projection and opaque
  non-CPU sentinel.  M0 imposes only laws selected by that structure, not every target consistency
  theorem; an unselected single-threaded program incurs no concurrency premise.

  The Windows demo must totalize `CreateThread`, thread-object wait, and close failures while
  preserving every result-indexed obligation.  `WAIT_OBJECT_0` supplies the selected join-publication
  synchronization; actual concurrency permits the child to execute before `CreateThread` returns.
  Any proof assuming parent-return-before-child is therefore a scheduler trace, not this demo.

  Accuracy follow-up `67bf9db02bb335b373d558feb142fe10d1a15c47` supersedes `4a27b2e` on
  canonical main `2a0ff225ae8521ceeed31c60f92ccbeffa79dc4c`.  It preserves the MP- and
  independently Reviewer-accepted semantics of `ecd5f9ec5da481c4eca0ee85765c9571f709ad24`,
  but is superseded for integration readiness because its ternary relation `Prop` has no stable
  occurrence identity.  Reviewer accepts the minimum replacement shape: stable
  `RelationOccurrenceId`; `RelationRecord` carrying source, label, and target; a finite duplicate-free
  occurrence-ID carrier; exact `Option`-map coverage and endpoint laws; and a ternary relation derived
  solely as an existential over that table, never as independent authority.  `EventId` already names
  event occurrences.  `ConsequenceOccurrenceId` remains reserved opaque vocabulary with no
  consequence carrier, coverage, admission, or premise until a selected extension requires it.
  Exact candidate `28228055263b5e95676615dcf82d989be93608eb` implements this mechanism: sole
  relation-occurrence-table authority, stable IDs, exact coverage/endpoints, preservation of
  multiplicity for equal records, and consequence vocabulary only.  MP nevertheless blocked its
  prose because `WellFormed` and `Nodup` establish only nominal execution-local carrier identity.
  They prove no allocation history, global freshness, cross-execution inequality, or authority.
  Prose-only precursor `82f743eb4f511cd1d88375c82b8eb02e42bf60e9` accurately limits
  identity to nominal carrier membership with no freshness and acknowledges consequence-occurrence
  vocabulary without carrier semantics.  Corrected mechanism and prose are now integrated on
  canonical GitHub main at `a62ca537f33e12be117f50c507fd462f92c3a5b9`, after MP and Reviewer
  acceptance plus Trust semantic-queue verification.  Binding-history design may begin from this
  base; its implementation and later projection layers remain design/review-gated.

  The first binding-history proposal is not accepted: an arbitrary strict order grants excess
  authority, and its live-resolution rule did not identify the exact later use occurrence.  A second
  transition-only frontier also failed: inherited/load-time bindings contradict
  `predecessor = none -> before = none` and may be captured before any transition.  MP's current
  provisional replacement adds `BindingRootId` and `RootRecord` with a key and initial optional
  binding; defines `Frontier` as either root or transition; stores only predecessor plus `after` on
  transitions and derives `before`; and makes each exact use-to-capture map name a `Frontier`.  A
  captured binding is derived from that frontier and cannot redirect after rebind.  Key/generation
  uniqueness alone is insufficient: `b0 -> b1 -> b0` can reuse the same `BindingInstanceId`.  The
  amended design adds a finite exact binding-instance carrier/map and requires exactly one in-history
  introduction site for each ID--root initial XOR one transition `after`.  A root site may represent
  an inherited binding; it is not a claim of global birth, origin, or event occurrence.  Controls
  reject root/transition reuse, duplicate `after` sites, rebind-back, and reuse after unbind.
  Reviewer accepted the complete root/frontier design with no P1 and authorized implementation on
  canonical base `a62ca53`.  A prefix may re-root its inherited state; no raw truncation,
  concatenation, or composition theorem is yet justified.
  Chronology, liveness, alias semantics, and global origin remain deferred.  MP, Trust, and Reviewer
  also accept the layer boundary that `History.WellFormed` establishes only relative endpoint
  membership and structural history; it remains independent of `Envelope.Execution.WellFormed` and
  cannot repair a malformed envelope carrier or confer execution authority.  Later consumers must
  require both facts separately, or use a thin nonduplicating private bundle when a concrete consumer
  earns it; a fixture may construct both independently.  There is no public bundle or derivation
  between them.  This layer boundary is accepted design guidance.  Exact implementation candidate
  `27685ea` conforms to the public root/frontier, unique-introduction, exact capture/use, and
  independent-envelope structure, but MP blocked it for two missing private controls.  Distinct root
  IDs with the same key must fail through `root_key_unique`, and distinct binding IDs with the same
  key and generation must fail through `binding_key_generation_unique`; the existing duplicate-root
  fixture exercises only duplicate identity and `Nodup`.  Replacement
  `1cc0c4e5574eb21440e389df71b01d7bf9e64b94` adds both controls without changing the public
  mechanism and is MP+Reviewer exact-hash accepted with no P1, but its old-base integration exposed
  37 stale `REF:` anchors.  Citation validity must be rerun after rebasing even when the Lean
  mechanism is unchanged.  Current-base reauthor `fde9975446eb8ff9ad1303a4879259b6fe720ecf`
  preserves the accepted semantics and controls, and Trust landed its identical tree canonically as
  `ece4308a92d3cc00773c4619c392bb36109b769e`.  Chronology, liveness, alias, path, and composition
  semantics remain nonclaims.

  The checkpoint implements only the thin
  structural `Envelope` slice: existential event coverage, finite duplicate-free carriers,
  event-agent and relation-endpoint laws, nonsemantic carrier-list order, proportionate eliminators,
  and private positive plus malformed-carrier controls.  Public `Domains` carries opaque
  `Consequence` vocabulary for the heterogeneous envelope, but proves no consequence carrier
  membership, identity, occurrence/path binding, semantics, fidelity, admission, or authority.  It
  likewise proves no target fidelity, execution admission, binding, or aliasing law.  It does not
  complete M0 or the native-thread demonstration.

  Reviewer accepts the next narrow M0 design boundary, `EnvelopeOccurrencePath`: derive an exact
  occurrence edge from a carrier occurrence ID and its stored relation record, build labelled paths
  from those edges, and provide only one-way erasure to the extensional label path.  It proves no
  envelope well-formedness, admission, observable-node coverage, selected path, projected-edge
  identity, consequence, or reverse reconstruction.  Carrier-position multiplicity is not available
  without a separate well-formedness premise.  Observable projection and quotient choices remain M8.
  Implementation is authorized, but no exact candidate or canonical hash exists yet.

  Signature review accepted the layer split but held implementation for four failures.  An
  unrestricted `PathConsequence.value` could invent completion, visibility, or resource return
  without profile admission.  Capturing a value plus generation inequality did not correlate the
  later use occurrence, so it did not reject stale re-resolution.  Exact list equality exposed
  irrelevant carrier order and supplied no stable identity for equal duplicate consequences.  A CPU
  carrier partial bijection alone did not prove the generic relation-occurrence/path roundtrip.
  Revised signatures must keep `Execution` thin; select `BindingHistory` with a stable use
  occurrence; carry event/generation-indexed overlap evidence; make consequence admission
  profile-owned; identify occurrences with stable execution-local IDs; compare consequence carriers
  by `List.Perm` plus a bijection and CPU carriers by permutation; and prove the generic
  relation-occurrence/path
  roundtrip separately before M0 exit.  These are structural obligations only--target consistency
  and admission remain above M0.  Multi must return the revised signatures before implementation;
  MP will author canonical `MEMORY_MODEL` interface text only after the shape stabilizes.
- Checked-x86-authoring proof brief `97595be15389e296addcb91f44e5680ef673c99b` is accepted
  design-only; implementation remains blocked until a canonical sound typed-`ObligationWorld`/M2-B
  seam lands.  Its decisive prototype is one real
  straight-line Windows artifact with exactly one dynamic byte-store use and a real terminal
  transition.  The checked path reuses canonical BindingHistory identities and world tokens,
  separately proves latest-live capture-to-use evidence and x86 physical realization, erases to the
  ordinary encodable instruction, retains/discharges obligations through indexed transitions, and
  ends in the artifact's sole `VerifiedProgram.compose` value.  It deliberately rejects a parallel
  permission ledger, static-instruction/dynamic-use conflation, whole-allocation equality in place of
  byte-subview containment and backing translation, decoder-created authority, freely constructible
  discharge, and ghost ownership as proof of mapping or fault freedom.  A subsequent ownership
  clarification assigns mapped+writable access to an M2-B Windows-x64-process-entry profile grant,
  tied to the exact artifact, load state, initial stack pointer, committed writable range, lifetime,
  and selected dynamic occurrence.  The artifact explicitly allocates its Windows stack frame; it
  assumes no red zone, and leaves the terminal `ExitProcess` CALL's memory effects outside the first
  checked family.  Neither total x86 memory nor the logical world derives the grant.  Prototype
  declarations remain provisional and profile-local; commit `934d39a` is only a temporary
  integration repair, not the stable M1 implementation base.
- Literal or Boolean-domain execution checks do not establish a universal finite-input theorem.
  Spike 3 still needs a theorem over every finite stdin with explicit reservation, allocation,
  read, output, exhaustion, and cleanup outcomes before its downstream production certificates can
  cease depending on grandfathered checks.  Narrowing the input domain is not proof reuse.
- `FallibleFold` now supplies the accepted pure algebra for successful prefix, first refusal, and
  retained tail.  A CFG failure-path composition candidate must additionally preserve relational
  ghost invariants and outstanding obligations at the typed block boundary and prove the untouched
  tail unreachable.  Applicability remains edge-local: an unselected failure mode adds no premise,
  while a selected local failure classification cannot erase resource-return or cleanup obligations.
  Keep only this CFG-specific remainder in the candidate ledger.
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
  should move atomically so the neutral module does not inherit a codec dependency.  Replacing
  `ByteArray` with `Vec Byte` is a migration candidate, not a wholesale alias substitution: require
  observation and roundtrip bridges plus one demonstration consumer before changing representation.

Candidate status is intentionally visible: it tells agents where the delta may be removable without
pretending the reusable contract has already been established.
