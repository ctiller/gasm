# Proof machinery index

This index answers a practical question: **what is the shortest already-accepted path from a proof
need to reusable machinery?**  It complements [Practical proof tactics](PROOF_TACTICS.md), which
explains why the patterns work.  Entries here point to checked code, its owning layer, demonstrated
consumers, and the facts that deliberately remain local.

> **VerifiedProgram proof reset:** entries describing existing whole-program compositions are
> historical evidence, not approved starting points for new proofs.  Do not extend, repair for
> integration, or generalize them until `trustplan` announces a validated replacement template.
> Rebuild applicable proofs by duplicating and adapting that template.  Dependency-light algebra
> below remains available only where its use does not continue the paused whole-program pattern.
> Publication requires an exact integrated commit, two clean-slate consumers, and explicit
> nonclaims; archive the old path rather than blending both designs.

## Accepted replacement-track building blocks

These declarations are accepted, landed components of the clean-slate direction.  They are
individually reusable only within their stated ownership boundary; together they do **not** yet
constitute the validated replacement template.

| Need | Owning machinery | Landed evidence | Deliberate boundary |
|---|---|---|---|
| Independent Spike 2 source meaning | `Spikes/Rebuilt/Spike2Fibonacci/Spec.lean`: `runModelTrace_spec`; `Blocks.lean`: `rowBlock_source`, `loopBlock_source`, `loopBlock_fibonacci_state`, `programBlock_state`, `programBlock_events` | source rebuild `3b22faf6` (reviewed candidate `ea5757ae`) | no ISA, target, linker, artifact, or execution authority |
| Exact x86 body plus terminal exit | `Gasm/Targets/X86_64/ClosedExecution.lean`: `ClosedExecution`, `.run`, `.terminates`, `.admissible`, `.observable`, `.terminationCertificate` | `ae22a008` (reviewed candidate `1e47693c`) | process-exit backend leaf only; no independent behavior specification |
| Sealed Windows linkage and independent behavior refinement | `Gasm/Targets/Windows/ProgramCertificates.lean`: `StandardProviderLinkCertificate.ofLinkedProgram`, `standardProviderCertificate`, `NonInputStandardNativeProgram.externalInputFrame`, `.admissibilityCertificate`, `.behaviorCertificate` | `4574db1b` (corrected reviewed candidate `4e502c88`; abstract `spec := run` predecessor `357b9640` was blocked) | non-input standard runtime only; behavior comes from the caller's independent spec/refinement, never from execution |
| Certified finite container semantics | `Stdlib/Containers/VecSpec.lean`, `Vec.lean`, and `ByteVec.lean`: model/representation laws, indexed get/set/swap/append laws, `Vec.toModel_complete`, and the ByteArray/Vec bridge | `2f359da5` (reviewed candidate `762f4b0`) | container representation only; no program invariant, target memory authority, or artifact claim |

The corresponding negative index entry is isolated Spike 2 backend `84a52476` with children
`791d5980` and `41601644`.  Its `RowProducer.produce` requires the consumer to supply the full exact
`SelectedPrefix`, then packages that premise without deriving the Fibonacci state/event relation.
It is evidence that a proposition field is not an abstraction: do not integrate it, use it as a
template, or count moved proof text as reduced burden.

The next candidate direction remains design-only: owner-local, exact-index, kernel-derived action,
frame, event, transfer, and result attributes may compose into the consequence needed by the next
boundary.  No public arbitrary proposition/Boolean constructors, universal attribute or obligation
world, trusted evaluator, artifact-as-authority shortcut, or absent-feature tax is permitted.
Shared machinery still requires a materially different second consumer and Craig's approval.

The first replacement-plan revision is reproducibly preserved at
`archive/design/trust-rebuild-plan-f3af290c` (`f3af290c5b9271bb0119bce4caac4fba65f64f8c`).
Primary design and independent Reviewer approve its spec-directed staged-lowering direction but
require amendment before it can become the validated template.  The amended plan must define the
artifact/load/execution dependency DAG; use a small layered execution identity rather than a
proof-budget god object; and keep canonical `Environment` universally quantified.  Staged lowering
must be explicitly well-founded, with transitive refinement across values, traces, effects,
failures, obligations, frames, and cost.  Dictionary selection must be explicit and reproducible,
with authority minted by the target; source-visible contracts remain separate from target clobbers
and mappings.

The replacement must also retain the checked-access leaf checklist and current `MemRef`/hardware
no-freeze gates and assign shared facts to noncircular library owners.  The advisory 10:1 figure is
an upper-pressure observation about marginal bespoke proof bulk per assembly-semantics or
implementation line--not staffing or reviewer counts.  Repeated ordinary work near that burden
suggests missing shared lemmas or a misplaced boundary; mature routine flow aims roughly at the
inverse marginal glue burden while allowing large foundations that amortize across families and
targets.  An overage prompts judgment and an underage proves nothing.  Do not add counters,
manifests, charging or amortization infrastructure, CI gates, semantic proof-budget indices, or
acceptance rules around it.  Soundness, applicability, universality, authority, lifecycle, and
cleanup cannot be weakened to improve the ratio.  Cutover deletion remains unpushed until review
and the substantive gates pass.
This is a blocked design checkpoint, not permission to implement or integrate the old proof chain.
Archived follow-up plan `archive/design/trust-rebuild-plan-f97b3bd5` (`f97b3bd5`) remains blocked
until it removes its blanket `Sᵢ₊₁ → Sᵢ` and supersession-record requirement.  Intermediate layers
may be replaced and their dependents rebuilt without preserving their shape; only guarantees
deliberately promoted into the owner-level semantic contract require preservation.  Any change to
that top-level meaning requires an explicit owner requirement decision and cannot be inferred from
the emitted artifact.

Canonical `e276448b` lands the accepted Trust rebuild plan and VISION; its document blobs exactly
match archived review tip `archive/design/trust-rebuild-plan-3186fd9e`
(`3186fd9e2d112db36b9980176829aedbcf6f47b1`).  It preserves
owner-level semantic specifications while treating rederivable intermediates as disposable; lowers
in explicit spec-directed stages; proves facts at the highest instruction-independent layer; and
leaves only irreducible ISA, ABI, artifact, and physical-authority deltas below.  It keeps canonical
`Environment`, conservative applicability, dynamic use plus descriptor ordinal identity, sealed
minimal admission, `MemRef` and hardware no-freeze boundaries, advisory-only burden language, and
owner escalation only for new shared or public proof machinery.  Plan acceptance is not acceptance
of a concrete reusable template.  The freeze remains until a pathfinder and a materially different
Spike 1 consumer validate the construction.
The landing deliberately excludes two unrelated ByteArray commits, preserved on
`codex/stdlib-bytearray-laws`, and does not modify `ScratchSpike3.lean`.

Archive `archive/design/rebuild-candidate-blocked-2bc1c1ee` (`2bc1c1ee`) is **BLOCKED** and grants no
implementation authority.  Its mandatory human feedback round is valid: when a fallback-boundary
consumer is not plausibly moving toward roughly ten program-specific proof lines per authored
assembly line, perform another specification/architecture/lowering iteration and leave a lightweight
note of the burden and attempted change.  This creates no counters, CI, dashboard, waiver process,
mandatory abstraction, integration gate, or permission to weaken claims; a direct sound proof may
still exceed the ratio.  Perform one such feedback iteration for each fallback consumer that
triggers that condition before owner review; it forces neither adoption nor reusable machinery and
does not authorize unbounded churn.

The candidate's common-law bundle is accidentally mandatory for every instantiation.  Replace it
with orthogonal feature-selected bundles and derive irrelevance once from closed selected rows, so
identity-only, capacity-free, or noncancellable domains pay no unrelated tax.  Its
`TargetResourceAdmits` is memory-access-only despite claimed provider, lifecycle, and non-memory
operations; the destination needs an occurrence-indexed target-action realization/admission seam
with descriptor access as one specialization.  The proposed judgment set and its connection also
omit result-indexed faults, a general architectural step, and explicit ABI/artifact connection.

Positive relational ghost transport is absent: selected source/domain facts must cross zero-, one-,
or many-event segments, stuttering/asynchrony, framing, and representation change without replay,
universal ghost state, or fabricated authority.  Pointwise `lowering_refines` is therefore not a
trace or applicable memory-consistency refinement.  `DischargeDerivation` lacks preservation,
transfer, and persistent-protocol conservation and overuses natural-number stage descent instead of
a well-founded semantic translation.  Its memory appendix is not clause-complete, notably for
§6.3, §§7.5–7.6, §§8.1–8.3, §§9.1–9.2, and their exact gates.  Its conflict inventory omits
`REVIEW.md`'s live ghost-transfer, feature-selected burden, exemplar, and progress rules and
under-scopes Spike 3.

Remaining P2 defects are a generationless parent reference; caller-selectable access pre-state/PC
rather than derivation from the certified step; an overly linear lifecycle that conflates successful
cleanup with administrative sealing or recovery-owned outstanding bundles; unmodeled capacity
shrink/revocation; narrowed baseline wording; allocation-count ambiguity; an unclear source-algorithm
boundary; and a compound/multishot primary handler.  Compression is unsafe until this union of MP
and Reviewer findings is reconciled through the semantic-preservation ledger.

Early specification-lowering review is **NARROW**, not accepted design or implementation
authorization.  Interpret one explicit algebraic effect or capability-directed operation; do not
introduce a generic handler framework.  AOP is only a metaphor: there are no ambient pointcuts,
advice, or implicit ordering.  Keep demands, constraints, offers, and modal authority/lifecycle
separate.  Handler selection is explicit structural data; fingerprints are metadata only.  The
owner decides logging semantics before any sink design.  Composition or fusion requires explicit
noninterference or a bespoke refinement, and local obligation conservation translates into the
existing world rather than creating a global ledger.  Behavioral refinement, ISA definedness,
physical resource admission, and policy authorization remain orthogonal.

Approved design checkpoint `archive/design/lowering-private-relational-seam-6d89327f`
(`6d89327f2349a4b34a9ce4057554ed978019fc94`) authorizes only a private target/profile-owned
exact-artifact relational experiment.  Its provider-labelled execution consumes the exact response
list; eligibility includes acquisition; coverage and universal conditional termination are
separate; an acquisition-only control rejects plan reselection; zero writes remain safe but outside
conditional progress; and source-prefix preservation is derived rather than supplied by provider
failure.  Oversized success has no abstract step and cannot be relabelled as source `writeFailure`.
The first Windows scope is live, writable, and synchronous; asynchronous/`ERROR_IO_PENDING`
execution is excluded, and the 10:1 ratio remains only an informal architecture smell test.

The next private seam must make synchronous/writable eligibility a real profile-admission witness;
bind exact artifact execution to occurrence identity, returned count, output-memory update,
emitted-prefix effect, and fatal cause; preserve oversized/provider-fault provenance rather than
erase it through shared fatal control flow; and quantify final verification over every admitted
execution.  This checkpoint authorizes neither a public/shared interface nor canonical cutover.

Follow-up chain `b8368cd2903283c31288912b2de15534966c8280`,
`0dc2efcfe99dbe6d916a17330052f5bea6d32402`, and latest archive
`archive/experimental/spike1-private-verifiedartifact-gap-be83d334`
(`be83d3345221b130208ac5ec5b8b9ea0b36264d2`) is **BLOCKED**.  Its exact provider projection
theorem and grouping of provider occurrence, returned count, output effect, and fatal cause are
useful.  But its private `VerifiedArtifact` is neither stronger than canonical `VerifiedProgram`
nor adequate emission authority.  The `0dc2efcf` witness layer introduces 32 `native_decide`
proofs and `be83d334` adds further closed-proof debt.  The certificate omits canonical
`Environment`, artifact connection, exports, imports/providers, entry, platform admissibility, and
behavior-equivalence obligations.  `ProviderStep` circularly requires the source logical `Step` it
is meant to derive, while `Config.Agrees` omits machine, ABI, message, output, emitted-prefix,
pending-cause, and artifact simulation invariants.

Its progress result establishes only that an existing execution implies a logical terminal state;
it does not show that every `EligiblePlan` has an exact execution with exact response projection and
terminal `ExitProcess`.  Writable eligibility is unused, synchronous-handle admission is unproved,
the no-stdout case omits `INVALID_HANDLE_VALUE`, and symbolic/boundary instruction indices,
recomputed layout, and message address lack linker-owned artifact/import/symbol connections.  The
replacement remains target-only: define provider outcomes without a source-`Step` premise, carry a
phase-indexed `ExactInvariant`, and use a spike-local checked derivation over every eligible plan to
produce exact execution, provider projection, and terminal exit.  Prove one structural soundness
theorem plus totality/coverage, then compose every canonical `VerifiedProgram` subcertificate before
emission.  Full, short, zero, no-stdout, and write-failure traces survive only as regressions.  The
measured 21.1 then 24.4 proof-lines-per-instruction burden supports redesign because it accompanies
missing universal coverage and visible repetition; the ratio itself remains advisory and is not an
acceptance gate.

The semantic model must be fixed now, independently of implementation order.  It covers generative
nested scopes; distinct cancellation authorization, request, delivery, observation, masking,
unwind, cleanup, join, and terminal events; top-down rights versus bottom-up classified-refusal
escalation; overcommit with atomic reservations and acquisition/cancel/spawn races; partial
acquisitions; HTTP uncommitted, streaming-prefix, and complete phases; irreversible effects;
cleanup failures and dispositions; persistent services versus linear handles; and cooperative
versus forced termination and their failure domains.  State safety, progress, and latency
assumptions separately.  Obligation conservation is local, translations are well-founded, and
applicability is conservative.  Completing this model authorizes neither an implementation nor a
generic framework.  Shared or public machinery still waits for a materially different second
consumer and owner approval.

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
| Derive an exact singleton-store frame | `X86_64Mem.readByte_write_outside_addresses`, `readByte_write_inside`, `MemoryFrame.singleStore_writesWithin`, and `singleStore_readsWithin` | x86-64 memory and frame semantics | `MovMem32DispReg32` and `MovMem64DispReg64` | exact singleton descriptor and step-memory equality are mandatory; address, value, and non-memory projection congruence remain consumer facts; this supplies no admission or artifact authority |
| Derive an exact singleton-load read frame | `MemoryFrame.singleLoad_readsWithin`, with `registerOnly_writesWithin` for the separate no-write frame | x86-64 memory and frame semantics | `MovReg32Mem32Disp` and `MovReg64Mem64Disp` | exact singleton descriptor, address congruence, one-read step factorization, and memory-insensitive post transformation are mandatory; write preservation remains a separate audited obligation |
| Show bounded finite exploration contains only normative reachable states | `Gasm.MemoryModel.FiniteSearch.Enumerator.search_sound` | memory-model presentation/search boundary | the checked incomplete-enumerator negative control exercises the one-way guarantee | completeness is separate and may not be inferred from bounded fuel or a finite result |
| Preserve dependent CFG identity through lowering or nominal remapping | `Gasm.Compiler.TypedCFG.ProgramPlan.loweredBlock`, `lower_ref_exact`, and `lowerDefinitions_mapBlockId_block` | compiler CFG authoring/lowering | typed CFG lowering and x86-64 control-point remapping | matching names or entries do not substitute for equality of the complete dependent definition |
| Turn bounded UInt64 decimal progress into a reusable certificate | `Stdlib.Fmt.UInt64DecimalScheduleCertificate` and `Gasm.Targets.X86_64.DecimalSchedule.UInt64DecimalScheduleRealization.selectedPrefix_bounded` | pure formatting schedule, then x86 realization | Spike 2 native decimal loop | the pure layer owns digit/count bounds; the target owns machine effects and the final production connection; the fuel theorem supplies no resource authority |
| Cache an exact selected x86 production prefix | `ProductionPrefix.SelectedPrefix.Cutpoint` | x86-64 eventful production semantics | canonical evidence carried by `LocalBlockRun` | a cutpoint proves an exact prefix only; it does not classify the caller's logical phase or prove termination |
| Discharge and compose an x86 local body contract | `LocalBlockDischarge`, `LocalBlockDischarge.refine`, and `LocalBlockRun.then` | x86-64 local contract/production-prefix bridge | accepted implementation-hole mechanism for proof-directed blocks | contracts and middle-entry facts remain explicit; CFG identity, placement, terminal outcomes, and artifact authority are separate |
| Stop a finite fold at the first refused input | `Stdlib.fallibleFold`, `fallibleFold_conservation`, `fallibleFold_acceptedPrefix`, and `fallibleFold_refused_boundary` | dependency-light pure control algebra | Zlib streaming plus Spike 5 accepted and zero-capacity refusal outcomes | resource identity, reclamation, cleanup, effects, target execution, and artifact authority remain consumer-owned |
| Refine one successful observation without unfolding its producer | `WasiObservable.normalizeSuccessfulExit`, its constructor equations, and `WasiObservable.refines_normalizeSuccessfulExit` | WASI observation algebra | Spike 3 Wasm equivalence | the consumer must prove the exact success payload and exclude fuel exhaustion; evaluator, outcome vocabulary, runtime bounds, and `VerifiedProgram` authority are unchanged |
| Prove projected-key insertion-sort stability | `Stdlib.Sort.StableOn` and `insertionSort_stableOn` | pure container algebra | Spike 3 byte-line model plus distinct tagged equal-key regression | ordering and permutation are separate theorems; target execution and artifact authority remain consumer-owned |
| Lower bounded structured straight-line code to Microsoft x64 | `StructuredStraightLineMicrosoftX64Entry.lowerFunction` and its `LocalCertificate` | compiler's target-specific local lowering layer | canonical bounded Microsoft x64 entry backend | exact clobbers and local semantics are proved; process entry, non-return, platform outcome, PE placement, and `VerifiedProgram` authority remain separate |
| Bind a replaceable Microsoft x64 leaf into the stable symbolic CFG | `StructuredLeafMicrosoftX64CFG.Body`, `Body.ofGenerated`, `Body.ofReplacement`, `Terminal`, and `realizes` | compiler's target-specific leaf/typed-CFG bridge | generated backend and handwritten differential bodies | exact bytes, result, frames, clobbers, and control-flow freedom are retained; the caller still owns termination, emitted terminator semantics, layout, graph closure, admission, artifact identity, and `VerifiedProgram` authority |
| Resume production execution after a proved local straight-line body | `ContextualStraightLinePlacement`, `RuntimeSilentOn`, and the target prefix-runner theorems | target production execution bridge | Microsoft x64 and AArch64 compiler-bulk spikes | the local certificate supplies no lookup, host-silence, ABI, outcome, artifact, admission, or `VerifiedProgram` authority |
| Replace a compiler body while retaining one selected functional theorem | the AArch64 and Microsoft x64 differential modules' `FunctionalDelta` and `FunctionalDelta.realize` | each compiler target's local realization layer | runnable AArch64 and Windows x64 compiler-bulk spikes | only the named result property is transported; replacement bytes, frames, clobbers, classification, placement, runtime behavior, and final authority are regenerated or re-proved |
| Emit production bytes from whole-program proof authority | `Gasm.Core.Platform.emitVerifiedProgram` | platform-neutral whole-program boundary | compiler-bulk plus migrated Spike 1, 2, 4, and 5 emitters/tests | serialization consumes an exact `VerifiedProgram` and may still return an error; public target-local serializers remain migration debt, while raw fuzzing requires `FuzzingEmitter` and confers no verification claim |

## Proven composition patterns

- Accepted extraction `archive/accepted/x86-singleton-store-frame-4c6fbf4c`
  (`4c6fbf4c46899c85e4db88110b050f906ecaf799`) realizes a dependency-light
  `MemoryFrame.Common` boundary for `MovMem32DispReg32` and `MovMem64DispReg64`.  Its plain theorem
  helpers include `readByte_write_outside_addresses` over the exact modular address list without a
  no-wrap premise; exact singleton `.store` descriptor equality; exact post-step memory equality to
  writing the descriptor address/value into pre-memory; and derivations of `WritesWithin` from
  outside-address preservation and `StoreAgreeOn` from `readByte_write_inside`.  The `ReadsWithin`
  helper additionally receives effective-address, stored-value, and post-step non-memory congruence
  under `agreeOutsideMemory`; the exact store descriptor makes the load footprint empty.

  Both W32 and W64 instantiate the unchanged theorem signature while preserving their public theorem
  names/types and compiled `MemoryFrameAudit`; every other form remains untouched.  The repeated
  consumer theorem text fell from 61 lines to 44 (28 percent), an observed burden delta rather than
  a metric or gate.  Focused audit validation passed 101/101; only three inherited Spike
  `native_decide` gate failures remained, with none introduced by this slice.  No record, typeclass,
  interface, negative fixture, admission, platform, carrier, atomic, CFG, authority, or ratio
  machinery was added; the existing `NegativeControl` remains authoritative.
- Accepted extraction `archive/accepted/x86-singleton-load-frame-aa80e2b1`
  (`aa80e2b184e043a33d5cd6d34e7ae8b3dd4cb7c6`; reviewed successor
  `dda5776618e4acea13c98e689672f6d1946c29e3`) adds `singleLoad_readsWithin` for
  the former RSP-specific W32 load (now subsumed by `MovReg32Mem32Disp`) and
  `MovReg64Mem64Disp`. One exact singleton `.load` descriptor,
  effective-address congruence, a step factorization through that width read, and a post transformer
  parametric under `agreeOutsideMemory` derive declared-read dependence via `agreeOn` and
  `X86_64Mem.read_congr'`.  The empty store footprint discharges `StoreAgreeOn`.
  `registerOnly_writesWithin` remains the single generic no-memory-change theorem and supplies each
  consumer's separately audited write frame; `singleLoad_readsWithin` does not duplicate a memory
  preservation premise.

  `undeclaredSecondLoad_no_singleLoad_factorization` is the load-bearing negative control.  Its
  hostile step materially combines the declared `[rdi]` value with hidden `[rsi]`; the counterexample
  pair fixes the declared value and varies only the hidden one, so no memory-insensitive post
  transformer can conceal the second dependency.  The blocked predecessor `58a624ff` instead ignored
  the declared value and tested a wholly misdeclared load.  The canonical slice preserves public
  theorem names/types and the compiled `MemoryFrameAudit`/`FamilyPipelineAudit`; focused validation
  built 101 jobs.  It supplies no admission, concurrency, platform, CFG, or artifact authority.
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
- For the composed decimal schedule, `UInt64DecimalScheduleRealization.selectedPrefix_bounded`
  packages both invariant loops and proves required fuel at most `12 * decimalDigitCount value`.
  Canonical `7088d9d` replaces 38 lines of Spike 2 phase reconstruction with one owner-theorem
  application while preserving the exact selected prefix, final frame, formatted bytes, and event
  facts.  The `7 + 5` coefficient is derived from the extraction and reverse-write pass certificates;
  it is not a runtime capability, allocation budget, or arbitrary proof-search limit.
- For a fixed suffix after a variable-length producer, state the suffix frame over the producer's
  arbitrary endpoint.  Canonical `9bcb4f2` gives Spike 2 Linux
  `RowTailParametric.selectedPrefix` a fixed 19-transition certificate for any formatted state, then
  `RowDecimalSchedule.twoDigitRowPrefix` appends the fixed opening, bounded decimal schedule, and
  tail.  Its bound `45 + 12 * decimalDigitCount current` preserves the schedule's quantitative
  evidence without specializing the tail to two passes.  Syscall interception, row-entry facts,
  live registers, and the back edge stay spike-owned; this is a proven composition pattern, not a
  generic row or termination library.
- Carry the successor's typed boundary alongside an exact variable-length certificate when the next
  composition layer would otherwise have to unfold the producer.  Canonical `866e7c6a` has
  `RowTailParametric.afterRecurrence_entry` reconstruct `Spike2LinuxRowEntry` from the tail frame
  and explicit counter/current/next projections, while
  `RowDecimalSchedule.twoDigitRowPrefix_successor` preserves those projections through the bounded
  decimal producer and returns the next entry.  This is a row-iteration seam, not the iteration or
  termination proof itself.
- For bounded iteration, keep the invariant, quantitative composition, physical evidence, and
  exceptional tail separate.  Canonical `896e2fa4` uses `TwoDigitIterationInvariant` and
  `SelectedFuelBoundedInvariantLoopStep` to compose an exact selected prefix for rows 10 through 89
  with actual `totalFuel ≤ 80 * 285`, while requiring target-owned `TwoDigitRowEvidence` for each
  pass.  Canonical
  `72adfc09` composes row 90 and the typed exit once outside the iterator, together with an explicit
  load-through-row-9 prefix and the whole bound `initialFuel + 80 * 285 + 285 + 5 ≤ 50000`.  The
  result is a conditional termination constructor; its evidence producers and final
  `VerifiedProgram` remain open.
- For fallible finite processing, `Stdlib.Control.FallibleFold` makes the accepted prefix, first
  refusal, retained remainder, conservation, and committed-state chain explicit.  Canonical
  `89c46f7` supplies the pure algebra, `c107938` connects Zlib compression and decompression by exact
  refinement, and `186f389` supplies runnable accepted/refused Spike 5 outcomes.  Zlib keeps
  post-attempt allocation scope in its own error and uses a difference-list output so the production
  replacement preserves linear accumulation.  The rejected generic count snapshot could not prove
  identity, reclamation, or cleanup; the first extensionally equal Zlib bridge used quadratic left
  append.  Those controls define the abstraction and cost boundaries.
- For a small refinement over an expensive evaluator result, prove the transformation over an
  abstract observation and make the consumer cross the evaluator boundary once.  Canonical
  `a10c2700` adds `WasiObservable.refines_normalizeSuccessfulExit` and an abstract
  `WasiRunOutcome.observable_ne_fuelExhausted`; Spike 3 supplies its existing no-fuel and exact
  successful-payload facts.  Every other WASI outcome is preserved by constructor equations.  This
  is observation-level proof reuse, not a new evaluator or an authority-bearing specification.
- For stable projected-key sorting, separate pairwise order, permutation, and stability.
  `Stdlib.Sort.StableOn` compares the exact filtered record sequence for every mutually related key;
  canonical `ddab78cb` proves this for insertion sort and exercises it with distinct tagged records
  sharing one byte key across a moving smaller record.  An identity-key test over untagged values is
  a vacuous control because key equivalence may force the complete values equal.
- For a bounded target backend, prove source evaluation, instruction effects, bytes, frames, exact
  clobbers, and control-flow freedom locally, but do not let metadata assert entry or callability.
  The rejected `60e744f` carried proof-free Boolean authority tags.  Accepted replacement
  `dfead99b5441c6b78398bc4f2f3c13720a5c7582` removes them, and its identical tree is canonical as
  `11f60475de851c4abab0e6938890d2be7d61603e`.  Absence of a callable certificate is honest; a later
  PE terminal `VerifiedProgram` must still establish process entry, observer exclusions, placement,
  outcome, and final artifact authority.
- For a runnable process-entry program, retain the long generated body as local evidence and prove a
  tiny handwritten ABI/terminal tail as a named typed slice.  Canonical Windows spike `8b39389`
  consumes a `LocalCertificate` through exact contextual placement and runtime silence, then proves
  `sub rsp, 40`, RAX-to-RCX transfer, and the linked `ExitProcess` call separately before the sole
  `VerifiedProgram.compose`.  Linux Spike 2 commits `e741e96` and `4a3b394` similarly close a named
  terminal tail and structural prefix while carrying exact RIP, fault, frame, and low-memory facts.
  Local execution is not platform execution; instruction execution does not establish ABI placement;
  and a native exit result is regression evidence rather than authority.  Empty exports accurately
  describe a process-entry executable, but are not evidence of a callable-library boundary.
- For a hand-optimized target body, relate the exact replacement to the compiler baseline only on
  properties the consumer observes.  The AArch64 and Microsoft x64 differential modules transport
  the selected result theorem and regenerate target-structural facts from the replacement segment;
  they do not copy the baseline's bytes, clobbers, input frames, placement, or authority.  X64 bridge
  `8485743` is consumed by runnable spike `88edac5`, which replaces nine generated instructions with
  one `mov rax, 42`, regenerates its ten bytes and local frames, then separately re-proves placement,
  runtime silence, terminal dispatch, artifact identity, admission, and final composition.
- The canonical Microsoft x64 structured-condition chain is comparison macro
  `cc64f4dfc4e193cd069edeedc4e4fe12f3adf66f`, compiler adapter
  `534369710c5a39acaa4129c9375f2865c61e06da`, corrected plan
  `eee3d8f10d920e702044fc53d938d2308d157616`, then exact typed-CFG block binding
  `f9223e5a3f9c4a863798a6c910afa32114a37666`.  Source role, logical contract, and symbolic topology
  remain stable across replacement; selected implementation identity and its certificate are
  regenerated.  The macro and adapter are local checked premises, and the block binding connects
  both exact successors without claiming runnable branch compilation or final `VerifiedProgram`
  authority.  The delivered differential control remains the nine-instruction-to-one-instruction
  Microsoft x64 replacement above.  Earlier hand-expanded IDs and noncanonical held commit
  `29b21f0b` are not provenance for this chain; use these repository-resolved canonical objects.
- Canonical `f2adc350aa5fd1c3a306a962c7dd55af6ceca129` turns that replacement boundary into one
  implementation-neutral typed-CFG leaf contract.  `Body.ofGenerated` and `Body.ofReplacement`
  retain each selected body's exact instructions, bytes, source-indexed RAX result, memory/fault/RIP
  frames, clobbers, outside-clobber preservation, and constructor-derived control-flow freedom.
  `afterBody_ghostFrame` changes only the physical machine, while caller-owned `Terminal` supplies
  an exhaustive target-free logical terminator before `realizes` constructs the existing
  `StructuredCFG.RealizesLeaf` premise.  The one-instruction handwritten control enters through the
  same `Body` as generated code.  This preserves stable source expression and symbolic topology
  without copying implementation identity, and it supplies no emitted terminator step, layout,
  graph closure, platform admission, artifact identity, or final `VerifiedProgram` authority.
- For production emission, pass the final `VerifiedProgram` to platform-neutral
  `emitVerifiedProgram`; handle its `Except` result rather than bypassing the proof boundary with a
  target serializer.  Canonical `94da7dd` migrated Spike 2 Linux's emitter and test to this path;
  compiler-bulk and migrated Spike 1, 4, and 5 targets demonstrate the same boundary.  The explicit
  `FuzzingEmitter` capability reserves `rawEmitForFuzzing` for target encoder fuzzers and has no
  production-profile instance.  Public target-local raw serializers still exist as migration debt,
  so their existence neither carries a verification claim nor proves mechanically that every
  repository emission path is already gated.

## Nonnormative proof-design references

These papers are design comparisons, not governing semantics, trusted code, or evidence for the
proof-burden heuristic.

- Kommrusch, Monperrus, and Pouchet's
  [S4Eq paper](https://par.nsf.gov/servlets/purl/10333807) demonstrates a useful proposer/checker
  split: an untrusted learned search emits an explicit rewrite sequence, while a deterministic
  checker validates each rule application and the final equality.  Self-supervised selection of
  hard examples is relevant to proof-search improvement.  Gasm may reuse that architecture, but not
  the paper's domain assumptions or failure classification.  S4Eq studies pure straight-line/SESE
  AST programs with known interfaces and excludes the aliasing, side effects, pointers, control
  flow, and concurrency central to Gasm.  Soundness remains conditional on the manually implemented
  rewrite rules and checker.  Search failure is incompleteness, so Gasm must report “not proved” or
  “unknown,” never semantic non-equivalence.  Model confidence supplies no admission authority and
  the paper provides no empirical basis for a 10:1 proof-burden ratio.
- Recoules et al.'s [TInA paper](https://arxiv.org/abs/1903.06407) supports per-artifact translation
  validation, lowering architecture-specific binary semantics into a small neutral IR, and
  proof-oriented recovery of types, predicates, unpacked logical values, expressions, and loop
  structure.  Its warning that declared inline-assembly inputs, outputs, and clobbers require
  checking parallels Gasm's descriptor-versus-step obligation.  TInA's CFG-isomorphism,
  blockwise-SMT, and `-O0` recompilation method cannot freeze Gasm CFG shape or replace relational
  phase invariants that admit code motion.  A failed proof followed by fuzzing is supplemental
  evidence, not validated equivalence.  Its binary lifter, compiler/debug mapping, and SMT solver
  remain trusted or correlated risks, while system instructions, interrupts, floats, dynamic jumps,
  concurrency, and general CFGs lie outside its demonstrated scope.

  Appendix E visibly presents division self-rewrites such as `x udiv x → 1` without a displayed
  nonzero premise.  Do not call this a paper bug without first resolving the source language's
  division-by-zero semantics; use it only as a reminder that plausible algebra is not validation and
  rewrite implementations stay outside the trusted base.  TInA's generated-C-statements figures are
  unrelated to marginal proof bulk and establish no 10:1 target.

## Admission record

Reusable extraction should leave a short audit trail.  Record:

1. the exact repeated local theorem or proof shape;
2. the lowest layer that owns the common semantics;
3. at least two real consumers, unless Trust explicitly requests the abstraction;
4. the before/after local proof burden;
5. focused build cost and dependency closure;
6. the negative boundary: tempting facts the abstraction does **not** prove;
7. the canonical commit after independent review; and
8. documentation alignment: the canonical owner, every conflicting or narrower document and
   section, stale examples or gates, and the exact decision to amend them or replace duplicate
   normative prose with a link.

A design is not documentation-complete while a live conflict remains unaccounted for.
Current document boundaries do not dictate the clean destination.  The proposed destination starts
from precious root specifications that own the complete admissible behavior envelope: observables,
safety, causality, permitted failure and partial effects, and claimed progress.  Effect/capability
contracts declare typed operations, polar demands/constraints/offers, authority pre/postconditions,
transfers, and retained obligations.  A small target-neutral parameterized resource/scope relation
layer supplies generative identity, modality/lifecycle/conservation schemas, cancellation phases,
dispositions, capacity/admission, and failure-domain laws.  It is neither a universal
`Resource`/`Obligation` sum nor a runtime framework.  Domain policy libraries instantiate their own
authority and obligation languages and refine those schemas; lowering explicitly selects handlers
and proves refinement, composition, and local conservation.

Memory-model roots continue to own `rf`/`co`/`fr`/`po`/`sw`/`hb` and target-indexed memory/device
relations.  ISA layers own architectural definedness, targets own physical admission, ABI layers
transport context, and artifacts record the selected tree as evidence rather than semantic
authority.  Required cross-domain laws include non-fabrication, generation non-revival,
conservation including outstanding cleanup, no scope-close erasure, cancellation as neither
visibility nor rollback, exact race winners, irreversible-prefix monotonicity, consequence
separation, explicit forced-termination failure domains, live-plus-reserved capacity bounds,
explicit composition/noninterference and handler selection, and conservative applicability with
demonstrated irrelevance before omitting a proof burden.  This split must be checked against both
god-object and dual-owner failure modes.

The current high-risk alignment ledger includes `EQUIVALENCE_PROOFS.md` reactive liveness;
`ARCHITECTURE.md`, `REVIEW.md`, and `VISION.md` spike normativity; `SYSTEM_EFFECTS.md` hidden or
typeclass selection and logging semantics; `ABI_CONTEXT.md` cancellation phases;
`COMPILER_PLAN.md`'s old lowering flow; and Spike 4 parser exhaustion versus server overload.
It also audits `OBLIGATIONS_AND_CAUSALITY.md`, `API_STATE_MODELS.md`, `READ_BINDER_CONTRACT.md`,
`SPIKES/SPIKE3_SORT_LINES.md`, `SPIKES/SPIKE5_GZIP.md`, and `TARGETS/WASI.md` against both the current
conflict inventory and the proposed destination.
Concrete P1 conflicts are unconditional reactive liveness; Spike 4's HTTP 414 versus overload
classification and premature scope discharge; blanket cooperative-cancellation assumptions; the
wrong stdlib cancellation owner; and partial-read types that cannot express a committed prefix plus
terminal status.  The earlier sole-`MEMORY_MODEL` destination verdict is superseded.
`MEMORY_MODEL.md` and `SYSTEM_EFFECTS.md` may be split or rebuilt; the reissued audit records current
state and clean destination in separate columns.
`MEMORY_MODEL.md` remains the authoritative semantic baseline until a successor is accepted.  Every
destination design and documentation change supplies a clause-level preservation ledger naming:
the existing section, claim, invariant, negative control, or gate; its destination owner and exact
successor clause; and whether its meaning is preserved, generalized, strengthened, intentionally
changed, or deferred.  Generalized, changed, or deferred entries include adversarial rationale,
affected target profiles, counterexamples, and proof/validation consequences.  A `no successor`
entry blocks the reorganization unless Craig explicitly approves removal.  The old text becomes
historical only after semantic coverage is proved and reviewed.  Semantic commitments are frozen;
document packaging and Lean interfaces are not.  Any split includes a memory-domain specialization
that recovers every moved claim and negative control.

The high-risk preservation set includes authority/provenance before ordering and the rule that bytes
do not manufacture provenance; generative identities and stale-generation rejection; loan and
obligation conservation; distinct ISA/program/scheduler/observable causality; architecture-neutral
events without TSO leakage; native x86 TSO and AArch64 weak-memory profiles; agent-local store
buffers/reservations; plain versus atomic operations; synchronization witnesses; result-indexed
lock/wait authority; queue-node and withdrawal obligations; and separation of completion,
notification, observation, resource return, reclamation, delivery, and persistence.  It also
preserves that wake is not visibility and CPU barriers are not cache maintenance; DMA/device/IOMMU
binding generations; cancellation as neither rollback nor synchronization; interrupt-path and
failure-domain separation; trace-quotient fidelity; bare-metal, hosted, futex/parking and progress
assumptions; honest QEMU/hardware validation boundaries; and stage/reference-intake gates.
Every decision touching one of these names its canonical owner and marks each affected document for
amendment, replacement by an owner link, or historical/non-normative status.

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
- `8b39389` closes the Windows compiler-bulk process-entry spike by joining a contextual generated
  body to a separately proved ABI/terminal tail.  `e741e96` and `4a3b394` demonstrate the same
  typed-slice discipline for the Linux Spike 2 exit and its structural prefixes.
- `7088d9d` moves the bounded two-phase decimal prefix theorem to the schedule realization that owns
  it.  `8485743` adds the Microsoft x64 property-relative differential bridge, and `88edac5` proves
  its exact replacement through the same runnable process-entry `VerifiedProgram` path.
- `94da7dd` removes Spike 2 Linux's target-specific production serializer use in favor of the
  canonical `emitVerifiedProgram` boundary; the remaining public raw serializers are still debt,
  not compatibility APIs to copy into new emitters.
- `9bcb4f2` demonstrates endpoint-parametric suffix framing and preserves the exact fixed-plus-
  variable fuel bound while composing real selected production prefixes.  It closes one continuing
  row shape, not the universal 90-row termination theorem.
- `866e7c6a` carries that composed row certificate into a typed successor entry using only explicit
  local projections and the fixed-tail frame.  It avoids re-elaborating the large dependent producer
  and supplies the boundary a future structural iterator should consume; no iterator or whole-run
  theorem is admitted by this commit.
- `896e2fa4` consumes that boundary in an eighty-pass bounded iterator without reopening instruction
  semantics.  `72adfc09` adds the exceptional row-90/exit tail and exact whole-budget premise.  These
  commits establish structural conditional termination composition, not the missing initial-prefix
  or per-row evidence producers, behavior equivalence, artifact authority, or final
  `VerifiedProgram`.
- `51a8c766` kernel-checks the exact Spike 3 Linux empty-input regression with `decide +kernel`.
  The corresponding canonical-trace attempt exceeded its resource envelope and was reverted, so the
  admitted technique is small-vector closure only, not monolithic decision of large traces.
- `a10c2700` promotes the archived observation-summary experiment into a dependency-light WASI
  refinement theorem and consumes it in Spike 3.  It preserves every non-success outcome and
  requires an explicit no-fuel premise; it changes no evaluator or proof authority.
- `ddab78cb` adds universal projected-key insertion-sort stability beside the existing ordering and
  permutation laws, plus a tagged nonvacuity control.  The Spike 3 model delegates its pure sort to
  the library while retaining target and artifact obligations above it.

Commit identifiers are provenance, not API names.  Follow the declarations above on current main;
use the commits to inspect the reviewed extraction delta.

## Indexed candidates, not yet reusable machinery

The following code shapes have enough evidence to investigate but are not canonical generic APIs:

- The blocked cross-consumer architecture dossier review is preserved in
  [Cross-consumer proof-architecture dossier review](PROOF_ARCHITECTURE_DOSSIER_REVIEW.md).  It is a
  pressure-test and correction checklist, not a second architecture owner or implementation seam.

### Effect-occurrence quotient candidate

- Design-reviewed but unimplemented: effect equivalence should quantify over every related
  source/target execution pair and compare canonical finite typed effect-occurrence graphs modulo
  node renaming.  Labelled relation occurrences and exact path witnesses are authority; vector
  clocks may only be proved caches.  A proposed effect-owned `Gasm.Effects.CausalTimeline` layer
  would own selected labelled causality, nonempty disjoint quotient fibers,
  `ProjectedCausalEdge`, forward/reverse quotient fidelity, acyclicity, renaming invariance, and
  graph-isomorphism equivalence.  Existing architecture-neutral `Gasm.MemoryModel.Envelope` and
  `RelationPath` remain structural spare parts and must not acquire effect semantics.
- A proposed effect-specific `Gasm.Effects.ConsoleCanonicalization` layer would own
  `ConsoleEvent.out`/`.err` merging: same stream tag, an ordered associative text fold, causally
  convex fibers, and input/cross-effect/barrier exclusions.  The Windows owner must separately
  prove a result-aware refinement from the exact `WriteFile` handle generation, return, and
  committed byte prefix to the emitted `ConsoleEvent.out`; Spike 1 then supplies its source/target
  execution projections, concrete console-merge eligibility, and final small quotient isomorphism.
  Current `FileSystemEvent.write` carries only a handle and length, so it cannot silently own this
  console fold.  A future filesystem canonicalization requires its own observation redesign and
  cross-effect refinement.
- Quotient boundary edges derive from raw labelled reachability and preserve incoming and outgoing
  causality.  The library should pay graph well-formedness, quotient/equivalence/idempotence,
  fold/partition/congruence, and barrier laws once.
- `Gasm.Effects.CanonicalizeTrace` is not authority in its current single-thread vector-clock form;
  replacement or a compatibility facade is only a proposed migration direction.  Timestamps,
  transitive reductions, deterministic node IDs, universal registries, predecessor pointers, and
  vector-clock families are rejected abstraction bases.  No implementation or accepted frozen hash
  exists yet.  Promotion waits for checked TrustRebuild1 code and exact-hash MP/TrustPlan acceptance.

### Memory-model carriers and provider worlds

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
### Graphics and compiler proof economy

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
### Resource, concurrency, and checked access

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

  Archived experimental branch `archive/experimental/envelope-occurrence-path-f7250a` at
  `f7250a57` implements the structurally approved narrow M0 boundary `EnvelopeOccurrencePath`:
  derive an exact occurrence edge from a carrier occurrence ID and its stored relation record, build labelled paths
  from those edges, append them, and erase them to the extensional label path.  It proves no
  envelope well-formedness, admission, observable-node coverage, selected path, projected-edge
  identity, consequence, or canonical, unique, or choice-preserving inverse.  An existential lift
  from an extensional path is possible and remains required as the generic roundtrip before M0 exit.
  The duplicate control retains `first ≠ duplicate` and both exact occurrence-path witnesses even
  though they erase to the same extensional path.  Carrier-position multiplicity is not available
  without a separate well-formedness premise.  Observable projection and quotient choices remain M8.
  This archive is reproducible research evidence, not a current-main API.

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

  The next `BindingHistory` consumer is conditionally approved only as optional structural
  correlation: exact use ID to stored use, stored capture, frontier-derived binding, and an exact
  occurrence/label path between the stored events.  It is neither validity nor happens-before, and
  not every use must have a nonempty path.  Envelope/history well-formedness stays separate;
  chronology, latestness, liveness or invalidation, rights and footprints, alias semantics, and
  admission remain profile proofs.  Required controls include an off-carrier but resolvable use,
  wrong capture, wrong binding/frontier, endpoint or label mismatch, and a stale old capture after
  rebind that still correlates structurally but grants no live authority.
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

  The structural `ObligationWorld` design uses a finite partial map from governed nominal IDs to
  typed issued payloads; a list with projected-ID `Nodup` is sufficient before any quotient, but it
  needs a permutation-invariance theorem.  Same-kind debts retain distinct IDs.  Issuance adds one
  fresh governed ID and payload while preserving every lookup; discharge removes exactly one ID
  while preserving every surviving payload.  Length or ID-set conservation alone is insufficient.
  Sequential composition uses exact boundary equality; independent composition needs disjoint
  namespaces or injective renaming.  Occurrence-ID uniqueness is generic, while resource/generation
  uniqueness is profile-owned.  Duplicable propositions are not linear authority: discharge
  prerequisites live in the full indexed authority state and are explicitly consumed, transformed,
  or transferred.  No caller-authored droppable Boolean or frozen public `CanDischarge` belongs in
  this layer.

  Archived branch `archive/experimental/checked-memory-admission-da8d836c` preserves three exact
  review states.  `dd245279` has sound generic ledger laws but its concrete checked-memory consumer
  is blocked: M2-B admission must join same-invocation fresh issuance, target-owned Windows
  load/stack mapping and lifetime, the exact production store occurrence with latest/live rights,
  containment and backing translation, and real terminal disposition for every resource and debt.
  Total-memory reflexivity, structural BindingHistory paths, fixed IDs, or decorative removal prove
  none of these; the final admission alone may feed `VerifiedProgram.compose` and must reject mixed
  artifact, invocation, domain, event, or world evidence.

  `0012b674` makes all admission legs load-bearing but remains blocked.  Its timeless
  `MappedWritable` survives a separate teardown; fixed page state is authored rather than produced
  by loader/page-map transitions; a resettable invocation world reissues generation zero; the
  SUB/MOV marker and empty history do not project complete production binding events; and terminal
  removals conflate return, discharge, and root destruction instead of following an indexed policy.
  `ProductionStoreUse` aligns the exact prefix, fetch, step, descriptor, and ghost payload, but still
  needs a real target dynamic-occurrence projection.

  Latest archive tip `da8d836cfa88d9fc9e2927520abd6bf364815327` is MP+Reviewer accepted for one exact,
  selected, single-invocation, noncomposed, model-relative checked-store spike.  The mapped-writable
  grant is host-state-indexed; teardown retains the page-table record as retired and makes the active
  committed entry unavailable.  Lifecycle
  dispositions distinguish invalidation/destruction/return, the target projection preserves the
  live binding, and every leg reaches the final `VerifiedProgram`.  This acceptance does not freeze
  an interface or make the archive a generalization base.  Caller-mintable namespaces do not justify
  independent composition; `verifiedProgram beforeHost` does not expose linear `afterHost`
  threading; whole-host equality in `MappedWritable` is an excessive future frame burden; logical
  binding still needs an explicit address-domain/page-map association; nonempty binding-change or
  rebind histories remain unexercised; fixed stack addresses remain a synthetic profile assumption;
  and generic CPU steps must eventually distinguish instructions that change host/interceptor state.

  Canonical follow-up `ad43d10d` has the same stable patch as independently accepted experimental
  `423f371ad38ea43f5d06965155a2cd3ab0446237`.  Within the sealed single-invocation spike, decoder
  roundtrip, MOV footprint, target/host identity, binding authority and origin, and their negative
  controls are load-bearing.  Do not promote that consumer's exact codec, frame, or alignment fields
  into a universal production-use API.  Reusable consumers should derive instruction-shape facts
  from the selected instruction-family certificate or registry and require alignment only for
  operations whose semantics need it.  A generalized execution-parameterized rebind-rejection
  theorem is deliberately deferred until a real consumer justifies the public seam and recurring
  proof burden.

  Canonical `6ceb8b51` has the same stable patch as independently accepted `7b1a8413c4e3c26b7f2d8265cd4eb476b18093a9`.
  It replaces whole-host equality in Windows `MappedWritable` with current namespace equality,
  selected invocation liveness, and membership of the exact active committed `PageMapping`.  A
  target-private `MappingFrame` with a private constructor transports only those facts across the
  concrete prepend-only loader evolution; retirement invalidates both mapping membership and
  invocation liveness.  This is physical-grant framing only, not independent-composition authority.
  Do not freeze the frame's exact fields into generic checked-authoring interfaces before a real
  consumer requires them.

  Accepted archive `archive/experimental/checked-store-binding-association-11801508` at
  `11801508217d6b0969216569371a272e1af01c36` adds one constructor-indexed
  `StoreBindingAssociation` tying the exact live logical binding and generation to the exact Windows
  address domain, complete active `PageMapping`, logical byte, and backing frame.
  `X86StoreRealization` no longer accepts independent current-host, mapped, or translation fields;
  the sole `MemoryAdmission`/`VerifiedProgram` path retains the association.  Controls reject wrong
  generation, domain, mapping, backing, and retired state through that association itself.  Its
  current seven indices and `hostExact` are local to the selected single-invocation spike.  A future
  consumer that survives unrelated host evolution must construct or transport the association
  through target-owned `MappingFrame` or an explicit use-host relation, never universalize equality
  with the original load host.

  The proposed reusable x86 checked-authoring envelope is paused as an implementation slice, not
  rejected conceptually.  Any replacement template must index descriptor occurrences by position;
  derive geometry from the exact descriptor and pre-state; require real `WritesWithin`/`ReadsWithin`
  and production-codec linkage for selected forms; and keep generic discharge conditional and
  authority-free.  Only sealed target adapters may admit production.  Host, mapping, and binding
  remain profile-owned; unselected instruction forms impose no premises; no global catchall is
  allowed; and the current `MemRef` shape is not frozen. The supplemental five-class x86
  `HardwareMemoryHarness` now supplies a rebased guarded scratch preimage plus observed exact
  postimage/footprint for sequential semantic differential evidence. It is not the registry
  `ValidationOracle.silicon` owner and supplies no applicability, capability, mapping, TSO,
  atomicity, platform-admission, or `VerifiedProgram` authority. These remain constraints on the
  future clean-slate template, not permission to continue the existing chain.

- Reviewer-accepted isolated candidate
  `archive/accepted/x86-hardware-memory-controls-04a62bdc`
  (`04a62bdce1b15bdb2db7843945340f0b807ac858`) demonstrates the current hardware-memory
  validation discipline.  Its Windows harness uses an owned, call-aligned `0x58`-byte frame rather
  than the nonexistent Microsoft x64 red zone, with captures confined to offsets `0x20..0x4f`.
  Crossing-footprint and trailing-canary mutations are load-bearing rejection controls.  Positive
  native observations count only after a deliberately corrupted observation is rejected, and the
  supplemental four-class inventory remains dependent and family-indexed.  This is accepted
  candidate evidence, not a current-main library or integration decision; it grants no profile,
  capability, mapping, TSO, atomicity, platform-admission, registry-oracle, or `VerifiedProgram`
  authority.

  First repair
  `archive/experimental/x86-consumer-host-register-gap-1d7d2232`
  (`1d7d2232cb0b79edad2a2b92c9041957cf96682c`) is **BLOCKED**.  Its `decodeAndStep`
  revalidates several cached plan fields but omits the mandatory `form.hostRegistersSafe` premise.
  A coherent mutation can change the form and exact bytes to use RSP as the base and set modeled
  RSP to the payload; all added checks pass even though the native harness cannot install that RSP
  because it owns the host stack, and the comparator omits RSP.  The consumer must check
  host-register safety and carry a coherent form/bytes/prestate rejection control.  It must also
  recheck decoded kind and width against the form expectation, and either verify that the native
  initial-memory region equals `regionBefore` or state precisely that preimage coherence is only a
  construction invariant.  Do not promote cached-field revalidation without these owner-local
  consumer checks.

  Second repair `archive/experimental/x86-consumer-preimage-gap-fc231645`
  (`fc231645cca4829e585d7609c378b5c86fa6d15e`) closes the coherent RSP mutation and adds
  form-independent kind/width checks, but remains **BLOCKED**.  Its preimage check compares two
  mutable copies: changing the overwritten store byte in both `regionBefore` and modeled initial
  memory preserves equality, leaves the native postimage unchanged, and lets `compare` succeed.
  Bind `regionBefore` to the independently defined `patternedRegion caseId`, retain its equality to
  modeled memory, and add a coherent two-field mutation control.  Equality between coordinated
  candidate fields is not independent calibration evidence.

  Third repair `archive/experimental/x86-consumer-caseid-gap-00ef12b7`
  (`00ef12b73109185543c8b1d62fb74fabb533dc78`) anchors `regionBefore` to `patternedRegion
  caseId` and closes the two-copy byte mutation, but is also **BLOCKED**.  `patternedRegion` masks
  each generated byte with `0xff`, so case IDs separated by `0x100` produce the same full preimage;
  public `HardwareMemoryDifferential.compare` also omits equality between result and plan case IDs.
  Retagging only `plan.caseId += 0x100` therefore preserves every validation check.  Require a
  full-width or injective identity anchor, unavoidable result/plan case-ID binding, and an explicit
  `+0x100` retag control before treating independent calibration as established.

  The fifth guarded class, `archive/experimental/x86-guarded-movzx-alias-gap-f3e6b846`
  (`f3e6b846af70b80a14bb753a6fa7d7f3e8b89c2c`), is **BLOCKED** despite its family/load/w8,
  case/preimage, full 64-bit zero-extension, and stale-bit controls.  A coherent mutation changes
  `MOVZX R13, byte [R15+0x7f]` to the exact bytes for `[R13+0x7f]` and sets modeled pre-state R13 to
  `accessAddress-0x7f`; the load overwrites that changed base, so public `compare` accepts the
  unchanged native result even though native execution used different bytes.  Require a
  native-framed owner identity covering exact emitted form, bytes, and pre-state--or prevent
  caller-authored plans from entering comparison evidence--plus this R15-to-R13 alias control.
  The supplemental-only nonclaims above remain in force.

  Fourth repair `archive/experimental/x86-sealed-observation-controls-632d6eb5`
  (`632d6eb5987c27cd15af6c0061140e5094d46362`) is **BLOCKED** only on control coverage.  Its
  owner-derived length-delimited plan identity is adequate for the closed admitted inventory,
  decode/step recomputes it and binds `caseId`, and the private `Observation` constructor prevents
  external Plan/Result pairing or record-update laundering.  The coherent MOVZX relabel control
  closes the prior attack, and its leading-canary falsifier remains present.  Before approval,
  restore the three missing sealed non-transforming falsifiers for stale MOVZX destination high
  bits, payload corruption outside the declared access, and trailing canary corruption.  They may
  call private comparison helpers but must not expose observation construction or transformation.
  The fixed inventory does not justify generic collision-proof machinery; this is test restoration,
  not interface growth.

  Accepted successor `archive/accepted/x86-sealed-observation-controls-1e9cc21a`
  (`1e9cc21a3a3a8e8ecfb132614929c60eb7a55704`), integrated on main as `f5e0c855`, restores the
  three missing falsifiers while retaining the existing leading-canary control.  The resulting four
  sealed pass/fail calibrators reject stale MOVZX destination high bits, leading-canary corruption,
  the first payload byte outside the fixed interior access, and the first trailing-canary byte.
  Private `compareMachine`/`compareRegion` are shared with the real comparison; calibrators mutate
  only local result/region copies and cannot construct, transform, update, or return an
  `Observation`.  Six exact native observations pass and all four calibrations fail as intended.
  This accepts v2 plan identity plus sealed observation construction for the supplemental five-class
  harness; the applicability, capability, mapping, memory-model, platform-admission,
  registry-oracle, and `VerifiedProgram` nonclaims remain unchanged.

  GPR Milestone 1 extension `archive/experimental/x86-gpr-m1-decoder-gap-ffc83591`
  (`ffc835915214672875292883e84a3b75bebd9501`) is **BLOCKED** on decoder admission.  Its
  `MovMem32DispReg32` production encoding, step, descriptors, uops, roundtrip, and exact W32 frame
  are correct for the supported base-only forms.  It also correctly handles the REX.W width split,
  extension bits, RSP/R12 SIB emission, RBP/R13 forced displacement, 32-bit source truncation, and
  four-byte read/write footprints.  Sealed plan identity remains intact, a source with nonzero high
  32 bits detects accidental widened writes, and the byte-after-footprint calibrator reaches the
  private full-region comparator.

  The decoder nevertheless accepts unsupported addressing encodings: `89 04 00` is really
  `[rax+rax]` but is relabelled `[rsp]`; `89 05 00000000` is RIP-relative but is relabelled
  `[rbp+0]` and under-consumed; and `42 89 04 24` uses REX.X to address `[rsp+r12]` but is relabelled
  `[rsp]`.  The mod=1/rm=4 path also accepts arbitrary SIB bytes.  The narrow repair is to bind
  REX.X, reject unsupported mod=0/rm=5 RIP-relative forms, and require the exact base-only SIB with
  REX.X clear whenever rm=4, preferably in both W32 and existing W64 `0x89` paths; retain the three
  hostile byte strings as decoder controls.  This needs no new proof machinery and grants no
  production-admission or final proof authority.

  Accepted successor `archive/accepted/x86-gpr-m1-decoder-controls-29bbc937`
  (`29bbc93795a29068600d38a28a2bf4e5b26bd6bf`), integrated on main as `5fbf3f3d`, closes that
  decoder-admission gap.  The `0x89` decoder retains REX.X, rejects unsupported mod=0/rm=5
  RIP-relative forms at W32 and W64, and admits rm=4 only when REX.X is clear and the SIB is the
  exact canonical no-index/base-4 form in mod=0 or mod=1.  Eight kernel-decided negative vectors
  cover indexed SIB, REX.X-created index, RIP-relative, and indexed disp8 cases at both widths.
  The three prior hostile byte strings now reject; supported W32/W64 RSP/R12 canonical-SIB and
  RBP/R13 forced-displacement forms decode with exact consumption and matching semantic identity.
  The exact W32 encode/step/descriptor/frame, sealed plan identity, nonzero-high-source native case,
  and byte-after-footprint comparator falsifier remain accepted.  The focused gate passed 19/19 and
  all nine independent probes succeeded.  This closes the Milestone 1 slice only; the supplemental
  harness's existing nonclaims and final-authority boundary remain in force.

  Provisional singleton-load scope from canonical `4c6fbf4c` permits a `MemoryFrame.Common`
  experiment for the W32 MOV load family and `MovReg64Mem64Disp`. The W32 family has since been
  canonicalized as `MovReg32Mem32Disp`, subsuming the former RSP-specific identity. Retain
  `registerOnly_writesWithin` under its existing name and implementation, correct its documentation
  to the genuinely generic no-memory-change meaning, and reuse it for both load consumers; do not
  introduce an alias or rename its existing call sites.  Proposed `singleLoad_readsWithin` requires
  one exact singleton `.load` descriptor, effective-address congruence, explicit post-state
  factorization through the one width read, and a post projection parametric in equal read values.
  It derives read equality from `agreeOn` plus `X86_64Mem.read_congr'` and discharges
  `StoreAgreeOn` from the empty store footprint.

  Do not add a step-memory-preservation premise to `singleLoad_readsWithin`: `ReadsWithin` does not
  demand it.  Exact memory preservation remains mandatory once, through each consumer's separately
  audited `WritesWithin` theorem.  A narrow `NegativeControl` must refute factorization for a
  declared-one-load instruction whose GPR result also depends on a second undeclared read.  Preserve
  both consumers' public theorem names/types and audits, leave every other form untouched, and update
  `MEMORY_HOOK.md` qualitatively without inventory counts.  This is a final implementation boundary,
  not accepted machinery; it authorizes no platform, shared, CFG, authority, or ratio framework.

  First implementation `archive/experimental/x86-singleton-load-control-gap-58a624ff`
  (`58a624ffc7c37684e38ab12508da43834a129362`) is **BLOCKED** on its advertised laundering
  control.  The helper and the two production consumers otherwise preserve the approved semantic
  boundary, but `undeclaredSecondLoad_no_singleLoad_factorization` does not make its observable
  result depend on both reads: it ignores the declared `[rdi]` value and depends only on hidden
  `[rsi]`.  It therefore proves rejection of a wholly misdeclared load, not the required case where
  an instruction genuinely uses its declared load and additionally launders a second undeclared
  read.  Replace the fixture with an observable result that materially combines both values and
  obtain renewed review before promoting the helper or citing the fixture as the load-bearing
  negative control.

  One-line successor `dda5776618e4acea13c98e689672f6d1946c29e3` makes the result depend on both
  values and is integrated canonically as `aa80e2b1`; the accepted reusable result is indexed under
  Proven composition patterns above.  Keep `58a624ff` as the defective-fixture checkpoint, not an
  accepted implementation.

  Design-approved target-owned experiment from canonical `aa80e2b1` reserves a new ISA-only MOV
  r32,[base+disp8] family; its type/name is a provisional spare-part API, not a frozen shared
  interface.  The authoritative owner ruling supersedes an interim disjoint-domain proposal: one
  `MovReg32Mem32Disp { dstReg : Reg32, basePtr : Reg64, disp : UInt8 }` production identity absorbs
  and retires `MovReg32RspDisp32`.  An optional `mov_r32_rsp` convenience constructor may return the
  general form, but it is not a second type, instance, registry entry, or compatibility authority.
  Existing frame proofs, roundtrip cases, census/registry entries, controls, comments, and downstream
  references migrate rather than preserve duplicate identities.

  Semantics computes effective address from the pre-state base plus signed disp8 modulo 2^64 before
  the destination update, including destination/base aliasing, then applies 32-bit GPR update
  semantics with cleared upper bits and unchanged memory.  RIP advances by
  `3 + rexPresent + sibPresent`, where the fixed bytes are opcode, ModRM, and disp8; REX is present
  exactly when destination REX.R or base REX.B is required, and SIB exactly when the low base code is
  4.  Encode and step must share one encoding-shape helper, or prove this length equal to encoded
  size, while preserving every other non-memory projection.

  Canonical encoding is always mod=01 with an explicit disp8, including zero, preserving existing
  RSP bytes.  Non-SIB rm values decode through REX.B; rm=4 requires exactly scale=0, index=4, base=4,
  with REX.B distinguishing RSP/R12.  Admission rejects REX.W, REX.X, redundant REX/prefix aliases,
  mod=00/10/11, RIP-relative, address-size and segment prefixes, indexed or no-base SIB, and
  noncanonical SIB spellings; decoded bytes must re-encode exactly.  Roundtrip and hostile controls
  cover all sixteen destination/base identities; destination=base; RSP/R12; RBP/R13; zero, +127,
  and -128; required REX.R/B combinations; truncation; forbidden W/X; all three instruction-length
  classes (3 without REX/SIB, 4 with exactly one, and 5 with both); and model-only modular EA wrap
  examples even when native scratch preparation excludes those host addresses.

  `memAccesses` is exactly one ordinary `.load`/`.w32` reference and `toUops` derives from it.  Frame
  proofs reuse `registerOnly_writesWithin` plus `singleLoad_readsWithin` without a second memory
  premise.  A supplemental `HardwareMemoryPlan` extension requires separate Trust acceptance, a
  distinct closed scratch class threaded through every exhaustive classifier/control, exact
  production byte/identity comparison pointing only to the new general identity, every GPR
  consequence including zero-extension, and the unchanged guarded region; native host-address
  limits remain non-admission, not a weakened form.
  The slice must replace brittle current inventory counts in `MEMORY_HOOK.md`,
  `X86_ISA_EXPANSION_PREREQUISITES.md`, and any exact-initial-family hardware prose with qualitative
  mechanically audited language.  It broadens no World, ABI, CFG, shared-memory, or authority layer.

  Canonical migration `71864fa48f53c7104b5f1d610b0ad1284c72f3bc` and documentation cleanup
  `190104845cf9083011da94b55683fa883ba84736` realize the one-identity ruling: current code and
  consumer references use `MovReg32Mem32Disp`, while the former RSP-specific identity is gone.
  Follow current declarations for the accepted target-owned family; the design scope above remains
  the admission and negative boundary, not a generic load framework or compatibility API.

- Blocked archive `archive/experimental/access-audit-b99ea1ce` (`b99ea1ce`) preserves a useful
  checked-access failure.  Its individual `execute` and provided `bind` laws are sound, and
  precondition-indexed `SafeUnder` is the right proof-economical goal shape.  But public
  `Checked := State → Outcome` plus public state/outcome constructors lets a caller run a denied
  computation, discard the appended violation, and fabricate an allowed result from the original
  clean state; current `Safe`/`SafeUnder` cannot distinguish that laundering.  A replacement needs
  constructor-controlled computation or a certified representation whose derivation/access
  coverage and prefix preservation exclude laundering, with an explicit negative control.  A later
  target bridge must separately prove real-access coverage and reachable-entry preconditions.  Do
  not use this archive as an implementation base.

  First repair `archive/experimental/access-audit-repair-5ad9e489`
  (`5ad9e48905b20f67aa58792aa0357e1c01502799`) is also **BLOCKED**.  Making the `Checked`
  constructor and evaluator private does not seal the abstraction: public `run` still returns a
  pattern-matchable `Outcome`, and Lean exposes generated `Checked.casesOn`, `rec`, and `recOn`
  eliminators.  An external client can observe denial, choose `pure 999`, prove the replacement
  safe with `Safe.pure`, and obtain a fabricated allowed result.  The added control exercises only
  fail-closed `bind`, so it misses this external-eliminator attack.  Preserve its useful coverage
  deferral and `SafeUnder` proof economy, but require either fixed checked syntax/derivations, a
  genuinely hidden evaluator/eliminator surface, or a certificate coupling safety to load-bearing
  semantic-access coverage and origin.  The next repair needs external negative controls.

### Proof delivery, termination, and CFG composition

- Literal or Boolean-domain execution checks do not establish a universal finite-input theorem.
  Spike 3 still needs a theorem over every finite stdin with explicit reservation, allocation,
  read, output, exhaustion, and cleanup outcomes before its downstream production certificates can
  cease depending on narrow pointwise checks. Narrowing the input domain is not proof reuse.
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
- Bounded-Lake candidate `a4562324da82d39040009bd6200df2c51ef69790` is rejected and was never
  integrated.  Warm project builds hid that it treated the Lean prefix as `LAKE_HOME`, while
  standalone Lake expects its own `.lake/build/{lib/lean,bin}` layout; its readable cache-key
  truncation could also erase the worker/source distinction on long toolchain identities.  The
  mandatory cold-package repair test then exposed two more assumptions hidden by the warm tree:
  omission of `Lake.DSL` registration and a hand-linked driver missing interpreter native symbols.
  Replacement `e9c85e44a5e4a3ac38cc656568c1ee067f5eab49` is under review, not accepted machinery.  Its
  acceptance bar is a fresh temporary Lake package built through supported Lake with interpreter
  support, a cache digest over the complete driver source/build recipe/toolchain/platform/worker
  identity, and proof that the generated task-manager patch survived.  On exact parent `01c5b0d`,
  with warm dependencies and comment-only edits invalidating the Add and Sub roundtrip-gate jobs,
  these exact invocations were measured:

  ```sh
  lake build +Gasm.Targets.X86_64.Instructions.RoundtripGate.Add +Gasm.Targets.X86_64.Instructions.RoundtripGate.Sub
  python scripts/run_bounded_lake.py --workers 1 -- build +Gasm.Targets.X86_64.Instructions.RoundtripGate.Add +Gasm.Targets.X86_64.Instructions.RoundtripGate.Sub
  ```

  The ordinary run took 5.219 seconds and peaked at 2462.3 MiB; the bounded run took 10.375 seconds
  and peaked at 1257.6 MiB.  Both built exactly two jobs.  The repository process-tree
  sampler measured root-plus-descendant resident sets every 100 ms, so these are aggregate peak RSS,
  not commit charge or one child's maximum.  Even if accepted, that trade reduces sibling overlap
  only; it does not repair one monolithic multi-gigabyte proof.  Warm success is therefore not
  evidence for generated build tooling unless an enforced cold integration path exercises its real
  runtime layout.
- Spike 3 Wasm observation-summary experiments are remotely archived evidence, not APIs or
  integration candidates.  Baseline `e2f3892` with warm direct imports ran
  `lake env lean -M 12288 Spikes/Spike3SortLines/Wasm/Equivalence.lean` under the repository
  process lease, GNU `time -v`, and a nonfiring 600-second timeout; it failed after 80.96 seconds at
  12,585,228 KiB maximum RSS.  Archive branch
  `archive/experimental/non-integrable-spike3-sort-seal-e2f3892` (`c4881bf`) adds an exact equation
  then marks `sortByteLines` irreducible; it still failed at 88.17 seconds/12,584,580 KiB.  Branch
  `archive/experimental/non-integrable-spike3-trace-seal-e2f3892` (`d621ed1`) similarly seals
  `spike3WasmTraceFor` behind one exact bridge and worsened to 176.43 seconds/12,584,732 KiB plus a
  later recursion failure.  Opacity did not change the consumer proposition's dependency on the
  evaluator-produced value.

  Archive branch `archive/experimental/non-integrable-spike3-summary-red-e2f3892` (`9a35ff2`)
  instead factors a pure `normalizeWasmObservation` over abstract input, proves its constructor and
  refinement theorems once, and lets artifact proofs supply exact observation equalities.  Under the
  stricter otherwise-identical `-M 4096` command it reached only the base's pre-existing failures in
  `spike3WasmFiniteSpec_preparationExhausted` and `Spike3WasmBehavior.noFuelExhausted` in 0.80
  seconds/1,708,400 KiB, with no memory or recursion error; it is intentionally non-integrable and
  not green.  Stronger archive branch `archive/experimental/spike3-summary-green-88edac5`
  (`ffee141`, exact parent `88edac5`) also abstracts the outcome-to-observation no-fuel theorem and
  repairs those drifted proofs.  Its complete direct module check passed in 0.90 seconds/
  1,681,788 KiB under `-M 4096`; edit-triggered
  `python3 scripts/measure_process_tree.py --sample-ms 100 -- lake build
  +Spikes.Spike3SortLines.Wasm.Equivalence` passed in 0.973 seconds with one built job, 1,789.6 MiB
  aggregate process-tree peak, and 1,648.8 MiB Lean-child peak.  The direct-probe KiB figures are
  GNU `time -v` maximum RSS for the dominant Lean process; the focused-build MiB figure is the
  sampler's root-plus-descendant maximum.  That archived commit remains experimental and is not a
  transplant candidate.  Canonical `a10c2700` separately lands the demonstrated technique in
  `Gasm.Targets.WASI.ObservableNormalization`: prove the small transformation over an abstract
  observation, preserve every non-success outcome, and cross into total execution through explicit
  success and no-fuel facts.  The archived branches remain negative and performance provenance;
  they are not APIs.  Merely making the total producer irreducible can leave kernel definitional
  equality equally expensive or worse.
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
### Linker and target-family admission

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
### Byte and prefix utility candidates

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
