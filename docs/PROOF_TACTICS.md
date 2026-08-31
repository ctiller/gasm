# Practical proof tactics

This is a short working guide, not a mandatory proof framework.  It records approaches that have
made real Gasm proofs smaller or more honest.  Add abstractions only after repeated use.

> **VerifiedProgram proof reset:** existing whole-program proof patterns are preserved evidence,
> not templates for extension.  Their proof burden grew far beyond the assembly they certify.
> Pause repair, integration, and generalization of those patterns until `trustplan` publishes a
> validated replacement template.  Then duplicate and adapt that template rather than layering
> further machinery onto the old proofs.  Import-light algebra and non-`VerifiedProgram` guidance
> below remain usable when they do not extend the paused pattern.

Preserve meaning, not intermediate shape.  At every rebuild scope, the precious artifact is the
owner's top-level semantic specification or contract.  Intermediate APIs, proof architecture,
representations, lowerings, certificates, module boundaries, generated code, and unpromoted
guarantees are disposable when they can be rederived quickly.  Replacing them may rebuild dependent
proofs without a supersession framework.  Preserve an intermediate guarantee only after the owner
deliberately promotes it into the relevant top-level contract.  Changing top-level meaning requires
an explicit owner requirement decision; emitted assembly cannot make that decision.

For a need-oriented map from these tactics to checked declarations, consumers, and deliberate
negative boundaries, see the [proof machinery index](PROOF_MACHINERY_INDEX.md).

## Bind proof authority to committed source bytes

A green proof build is evidence only when Lean read the exact source under review.  Before any
cached build, require the filesystem Lean-source census to equal unreplaced `HEAD` and the sole
ordinary stage-0 Git index, with CRLF-to-LF conversion as the only permitted byte normalization.
Reject ignored, untracked, staged, flagged, mode- or case-divergent sources; substituted Git
repositories, indexes, or object stores; symlink, junction, nested-repository, and hidden-namespace
source boundaries; and project `.olean` files with no corresponding authoritative source.

`scripts/check_no_ignored_lean_sources.py` owns this repository boundary and exercises its failure
classes with planted negative controls.  The motivating failure combined a broadly ignored Lean
source with a stale `.olean`: local imports succeeded although a clean checkout lacked the proof
text.  Running another compiler pass would not remove that delta; establishing source/build
identity before compilation does.  An intentional scratch source may therefore make the local
gate correctly red.  Report it; do not modify or delete someone else's work to obtain green.

## Start from the logical boundary

State the caller-visible success, failure, resource, and cancellation outcomes before symbolically
executing instructions.  Factor a reusable library contract when the hard loop is not specific to
the program using it.  Spike 2 became simpler once decimal formatting stopped being part of the
Fibonacci driver proof.

## Own source meaning before sealing target realization

Prove algorithm state, exact source events, and terminal source meaning in a target-free package,
then ask each lowering layer only for its irreducible realization delta.  Rebuilt Spike 2 does this
in `Spikes.Rebuilt.Spike2Fibonacci.Spec` and `.Blocks`: `programBlock_state` proves the ninety-row
Fibonacci endpoint and `programBlock_events` connects the pure typed blocks to the independently
authored trace specification.  Neither module imports an ISA, linker, or production evaluator.

At the target leaf, compose exact facts without inventing behavior.  X86
`ClosedExecution` joins one exact `SelectedPrefix` to one typed process-exit step while retaining
the selected index, initial/final states, event accumulator, and fuel.  Windows
`NonInputStandardNativeProgram.behaviorCertificate` transports that closed observation only after
the caller supplies an independent specification and refinement.  Provider linkage, artifact
identity, interceptor selection, fuel, admissibility, and source behavior remain separate evidence.

The failed control is a certificate field that asks the consumer for the whole result and merely
repackages it.  The isolated Spike 2 `RowProducer.produce` attempt required each consumer to provide
the exact `SelectedPrefix`, omitted the Fibonacci/event relation, and therefore moved rather than
removed the hard proof.  A useful producer derives its certificate from owner semantics and leaves
the consumer only the source invariant connection and root-specific consequence.  These accepted
pieces are replacement-track building blocks, not yet a validated whole-program template or a
shared iteration API.

## Witness identity with independently sensitive data

When a claim identifies the instruction or occurrence that produced an observation, do not infer
that identity from the postcondition and do not compare only duplicated caller-controlled labels.
Derive a canonical identity in the layer that owns the exact form, bytes, and pre-state; recompute it
at the consuming transition; and make at least one independent witness sensitive to the entire
identity.  For a fixed closed inventory, a length-delimited serialization may suffice without
inventing a generic collision-proof framework.

The guarded x86 memory work demonstrates both controls.  A `+0x100` case retag survived when the
scratch preimage observed only low case-id bits.  Later, coherently relabelling
`MOVZX R13, [R15+0x7f]` as `MOVZX R13, [R13+0x7f]` survived because MOVZX overwrote the changed input
register and left the same post-state.  Canonical `16b5f5a7` makes the preimage depend on all 64
case-id bits and binds result case identity to the plan; canonical `f5e0c855` additionally gives
the harness sole construction of a sealed observation carrying owner-derived plan identity.
Provenance or occurrence identity is a separate obligation from observational equivalence.

## Test decoder admission, not only roundtrip

An encode/decode roundtrip proves that bytes produced by the encoder are accepted; it does not prove
that the decoder rejects different byte strings which it might relabel as a supported form.  When a
codec intentionally supports only a subset of an ISA addressing family, keep the positive roundtrip
gate and targeted rejection controls in the target decoder.  Cover the load-bearing excluded
discriminators in the claimed or repaired boundary--such as prefix extension bits, ModRM modes, SIB
index/base fields, and displacement consumption--with kernel-decided hostile byte vectors.  Treat
those vectors as regression evidence, not an exhaustive characterization of decoder admission.

Canonical `5fbf3f3d` applies this to x86 `0x89`: indexed SIB, REX.X-created index, RIP-relative, and
indexed disp8 encodings are rejected at both W32 and W64, while canonical RSP/R12 SIB and RBP/R13
forced-displacement forms retain exact consumption and semantic identity.  This is decoder-admission
regression evidence for that stated boundary, not a complete subset theorem or a substitute for
instruction semantics, framing, hardware comparison, platform admission, or artifact authority.

## Keep falsification controls monotonic and evidence-sealed

Every validation repair must rerun the complete accumulated negative-control suite, not only its
newest regression.  When controls operate on sealed evidence, keep raw mutation and comparison
helpers private and expose at most pass/fail calibrators.  Such a calibrator accepts genuine
owner-created evidence, alters only local copies, and exercises the same private comparator as the
real path.  A control API must not construct, transform, or return evidence, because that would
reopen the invalid pairing it is meant to detect.

Canonical `f5e0c855` applies this discipline to the guarded x86 harness: the real comparison and
four calibrators share private comparison helpers; six exact native observations pass while stale
MOVZX destination bits, leading-canary corruption, payload-neighbor corruption, and trailing-canary
corruption are rejected.  These controls protect one supplemental target harness.  They confer no
profile admission, registry-oracle status, platform behavior, or `VerifiedProgram` authority.

## Eliminate the burden delta

Treat the exact caller-visible obligation as the proof's speed of light: the irreducible theorem and
owner-local facts that must exist even with perfect proof delivery.  Inventory what the current path
actually asks for--extra premises, repeated semantic replay, adapters, imports, invalidated jobs,
wall time, and memory.  Their difference from the irreducible path is the burden delta.

Redesign ownership, dependency direction, and typed interfaces until that delta disappears or every
remaining cost is attached to a selected semantic obligation.  Do not weaken the theorem, narrow its
domain, substitute a second evaluator, or move work behind a new name and call that optimization.
Compare the same consumer before and after, and keep an unchanged-direction or deliberately malformed
control when it distinguishes the mechanism from mere relocation.

Accepted `Gasm.Proof.LocalExecution` removed duplicated list induction while leaving both targets'
semantics local.  The decimal-pass split reduced the consumer's invalidation frontier; moving the same
facts without reversing dependency direction produced essentially no improvement.  These are evidence
for redesigning the proof-delivery path, not permission to trade away proof coverage.  Record build
measurements with their exact base, command, cache state, invalidated jobs, wall time, and peak memory;
they are comparative evidence, not universal performance facts.

## Design relational ghost state

Separate immutable logical facts from evolving progress, resources, phases, and obligations.  Relate
physical state to ghost state with a relation: ghost ownership, generations, and nominal identities
need not be reconstructible from machine bytes.  Transfer this state at typed calls and jumps, and
frame components a step does not affect.  Prefer several composable layers over one monolithic ghost
record.

Treat successful ghost-state transfer across lowering stages as a first-class technique.  The
source specification owns algorithm/domain mathematics and serialization laws; lowering transports
those theorems rather than re-proving the algorithm.  A genuinely different algorithm requires a
new source-level implementation and proof before lowering continues.  A stage-local relation may
carry a source object, abstract state, history, ownership fact, or theorem that final bytes cannot
reconstruct.  Its witness relates the selected source/domain fragment, intermediate or target
pre/post state, zero/one/many-event segment, framed fragments, and required observation or lifecycle
consequences.  Each edge proves directional preservation or translation; composed simulation
recovers the source fact transitively through stuttering and asynchronous or interleaved target
segments.

Transport may preserve generation, split/fuse/transfer, and retained-cleanup evidence, but never
mint authority.  Authority originates in the owning source/domain policy or target admission.
Index evidence by the selected source operation, dynamic occurrence where applicable,
resource/scope/binding generation, target/profile, and relevant state relation; matching bytes,
address, or PC never permits replay.  Keep ghost languages level-local and projected.  Independent
products use a closed-row framing/noninterference theorem; selected transfers name their destination
scope.  Interacting components need a bespoke relation theorem, not a universal ghost world,
constructor registry, or global ledger.  Lifecycle transport represents revoke, quarantine, and
disposition explicitly, including capacity shrink and failure effects; it cannot silently drop the
associated obligations.

Purely proof-relevant ghost state may erase.  Selection, layout, resource use, or other runtime
control becomes explicit lowering/artifact data with its own refinement.  Adequacy and non-vacuity
require the relation to arise from the source invariant and real lowering step, survive every
admitted target transition, and recover the source fact; an unconstrained existential proves
nothing.  Preserve theorem and relation meaning, not record layout or transport API.  Regenerate
stage-local adapters, and share transport/composition lemmas only after materially different
consumers meet the same theorem boundary.  Reject reconstructed-from-bytes provenance, replay across
occurrence or generation, opaque universal payloads, authority without origin, hidden ledgers, and
lowering that silently changes the source algorithm.  Prefer a cheaper direct proof when available;
the advisory proof-burden ratio creates no mechanism or gate.

## Consider every bound

For the selected routine and property, inventory applicable numeric ranges, input and output sizes,
loop counts, buffer capacity, allocation, stack, fragmentation, and execution work.  For each
material bound, either prove it, derive it, request it as a capability, eliminate it by streaming,
or specify failure and recovery.  Do not add ledgers for quantities the routine never uses.  Keep
proof fuel distinct from a resource enforced by emitted code.  A useful bound often supplies the
induction measure: `UInt64` decimal length is at most 20 and determines formatter capacity,
iterations, and work.

## Make refusal a first-class result

For finite processing that may stop, return the committed state, accepted prefix, first refused
input, and untouched tail.  Make refusal incapable of carrying a successor fold state, then prove
input conservation, the accepted transition chain, and the exact first-refusal boundary once in the
pure layer.  `Stdlib.Control.FallibleFold` owns this algebra; Zlib supplies codec and allocation state,
and Spike 5 exercises both accepted compression and exact zero-capacity resource exhaustion through
runnable verified targets.

Keep domain obligations in the domain state or error.  A count snapshot does not prove resource
identity, unique reclamation, cleanup, or terminal ownership.  Preserve operational cost as well as
extensional equality when replacing production code: Zlib's first equivalent bridge used repeated
left append and was quadratic, while the landed realization carries a difference-list output and
materializes it once.  When rewriting beneath the fold result match stalls, split the recursive fold
result and legacy result, use associativity on accepted branches, and eliminate impossible failure
equalities.

## Iterate certificates, not evaluators

For a bounded production loop, expose the mathematical bound, prove one pass, carry its invariant,
and compose exact prefix and fuel certificates before discharging the platform wrapper.  Spike 2
uses `Stdlib.Fmt.UInt64DecimalSchedule` for the one-to-twenty-digit bound,
`Gasm.Targets.X86_64.DecimalPass` for one-pass machine effects,
`Gasm.Targets.X86_64.DecimalSchedule` for two-phase composition, and
`Gasm.Targets.X86_64.EventfulSegment` for production-prefix composition; instruction semantics and
artifact authority remain with their target owners.  Reducing the closed 50,000-step native run
with `native_decide` instead caused pathological time and memory use while hiding this induction.
Optimize total proof-delivery cost first: an independently compiled `decide +kernel` proof can be
the right completion for an exact closed proposition even when a structural library would be
cleaner.  Build such memory-heavy proofs sequentially, extract the generic certificate bridge from
working consumers afterward, and introduce semantic chunks only if one proof exceeds the resource
envelope on its own.

Keep the reusable one-pass facts below the schedule-composition boundary.  The x86 decimal path
compiles raw instruction projections in `DecimalStepFacts`, packages the seven- and five-step
contracts in `DecimalPass`, and leaves only bounded two-phase composition in `DecimalSchedule`.
In particular, store safety and placement in a selected pass and derive its architectural effect;
do not store the same large dependent effect proposition a second time.  This keeps layout and
runtime consumers cached when only schedule composition changes.

Make the composed quantitative bound a theorem of that owning schedule.  Canonical
`UInt64DecimalScheduleRealization.selectedPrefix_bounded` derives a real selected production prefix
with fuel at most `12 * decimalDigitCount value`: seven transitions per extraction pass plus five
per reverse-write pass.  Commit `7088d9d` moved the 38-line phase reconstruction out of Spike 2;
the consumer now applies the owner theorem directly.  This is a mathematical/operational transition
bound derived from the phase certificates, not permission to infer runtime resource authority or to
hide arbitrary proof-search fuel.

When a fixed suffix follows a variable-length producer, state its frame against the producer's
abstract endpoint rather than one concrete pass count.  Canonical `9bcb4f2` makes the Spike 2 Linux
19-transition line/write/recurrence tail parametric in the formatted state, then composes a fixed
26-transition opening, the bounded decimal schedule, and that tail.  The resulting continuing-row
prefix has required fuel at most `45 + 12 * decimalDigitCount current`.  Exact syscall lookup,
interception, live-register frames, and the back edge remain in the Spike 2 owner.  This demonstrates
endpoint-parametric certificate composition; it does not establish the whole 90-row termination
theorem or justify a new target-independent variable-fuel framework.

Carry the successor's typed boundary through that composition instead of making the successor
rediscover it from the final machine state.  Canonical `866e7c6a` has the fixed recurrence tail
re-establish `Spike2LinuxRowEntry` from three explicit counter/current/next projections and its
local frame.  The arbitrary-digit row producer preserves those projections across the decimal
schedule and returns the next entry beside the exact selected-prefix certificate.  Keeping the
projections explicit avoids unfolding the large dependent producer merely to recover register
equalities.  This is the seam needed by a future structural row iterator; it does not itself prove
the 90-row iteration or termination theorem.

Canonical `896e2fa4` and `72adfc09` consume that seam by separating three proof dimensions.  A
projection-only `TwoDigitIterationInvariant` carries the next typed row entry; the generic bounded
iterator composes exact selected prefixes with a per-pass ceiling of `285` and an aggregate
eighty-pass bound of `80 * 285` without reopening instruction semantics; target-owned
`TwoDigitRowEvidence` supplies each physical decimal
realization explicitly.  Compose the non-uniform row 90 and typed exit once as an outer tail, not as
another case in every loop step.  The resulting theorem requires the load-through-row-9 prefix,
per-row evidence, and the full bound `initialFuel + 80 * 285 + 285 + 5 ≤ 50000`.  It is therefore a
conditional termination constructor, not closed behavior equivalence, artifact authority, or a
completed `VerifiedProgram`.

The measured invalidation boundary is part of the evidence.  On `25a375f`, a representative warm
edit frontier fell from 12.64 seconds and seven rebuilt modules to 5.54 seconds and three modules on
Polonius; the pass module fell from 1.5 seconds to 0.761 seconds, with no semantic or proof-authority
change.  A facts-only extraction that retained the old dependency direction took 12.65 seconds
versus 12.64 seconds: effectively no gain.  Use the same consumer-observation audit for cached
`does_not_use_memory`/register-frame facts and jump or syscall boundary summaries; theorem movement
without a narrower import frontier is not an optimization.

Changing the evaluator does not rescue a proposition whose proof term is itself monolithic.  On the
exact 90-row Spike 2 Windows certificate, `decide +kernel` exceeded 60 GB without producing an
`.olean`; do not rerun that shape.  A 52-step first-row producer took about 19 seconds, while a
consumer of its opaque certificate took about 2 seconds but still paid roughly 851 MiB of import
floor.  The useful boundary therefore exports only the next control point, recurrence and ABI
registers, event delta, fault status, and the smallest output-memory frame, with the exact production
prefix retained behind an opaque projection.  Prove one parameterized row step and compose it by
structural induction; copying one opaque consumer per concrete row merely moves the scaling defect.

Measure the exact closed proposition before choosing kernel decision.  Canonical `51a8c766`
replaces `native_decide` with `decide +kernel` for Spike 3 Linux's empty-input trace regression;
that small theorem remains a pointwise regression, not a universal theorem or `VerifiedProgram`.
Applying the same proof shape to the canonical trace exceeded its resource envelope and was stopped
and reverted.
When a closed evaluator proof leaves its resource envelope, retain exact production semantics but
switch the proof shape to selected-prefix or phase certificates and structural composition.

## Cache exact producers behind narrow typed boundaries

When an exact production certificate is expensive to elaborate, keep it in the module that proves
the concrete execution and export a second theorem containing only the observations needed by its
successor.  Spike 2's accepted Linux Row 8 slice proves the exact 64-transition `SelectedPrefix`,
including `Fib(8) = 21\r\n`, the selected write event, and the recurrence step.  Its separate
data-only boundary exposes the next RIP, recurrence registers `(9, 34, 55)`, preserved stack
pointer, and absence of fault without importing or unfolding the prefix certificate.  A clean build
spends roughly 24--37 seconds producing/opening the exact boundary but about 1.6 seconds on final
composition.

The boundary is a cache line for proof terms, not a weaker semantics.  Reproduce generated inputs,
retain the exact production prefix in the producer, and make the consumer interface no wider than
its next proof obligation.  This pattern establishes forward fact transfer across one typed
boundary; it does not yet supply generic forward/backward CFG contract derivation, loop-invariant
discovery, termination, or final artifact authority.

## Classify exact outcomes before platform admission

Keep a constructive prefix-chain theorem focused on one exact typed execution outcome.  At the
platform boundary, classify that abstract `NativeRunOutcome` with a cheap proposition, then apply a
named theorem such as `...Admissible_of_execution` that consumes both the exact-outcome equality
and its classification.  Spike 2 Windows commits `75d01c8` and `f90bfc9` use this shape to avoid
eliminating a large dependent prefix witness directly into the platform's admissibility predicate.

The failed alternatives are useful controls.  Projecting `run.isAdmissible` directly from the
dependent execution witness, or invoking a general fuel-recursive admissibility theorem at a
concrete 50,000-step budget, forced weak-head normalization of the runner; attempts timed out and
one Lean process reached approximately 19.2 GiB before cancellation.  With exact execution hidden
behind an opaque theorem and classification kept independent, the focused final equivalence target
built in approximately 4.4 seconds warm.  The classification theorem preserves the exact execution
claim while moving only the small platform-admission delta to the layer that owns it.

Host-runtime typeclass instances used by this boundary must be module-local or indexed by the
platform.  A high-priority global x86 interceptor silently contaminated Linux and generic proofs.
Instance search may deliver a stable proof dictionary, but it must not select an unrequested host
semantic model.

When a certificate API becomes more honest, migrate authority and regression evidence separately.
Current entry certificates make entry establishment an explicit input to admissibility and behavior;
the final `VerifiedProgram` still composes the authority-bearing layers.  Conversely, Spike 3's two
closed stdin vectors remain useful regression theorems and executable tests, but their Bool-indexed
`VerifiedProgram` facade was removed because two vectors do not establish arbitrary-stdin behavior.
Preserve the tests; delete the false authority surface and its exception ledger.  Canonical repairs
`03d22d6`, `17539b0`, and `01c5b0d` demonstrate the entry-certificate migration and regression-only
retention across hosted and bare-metal spikes.

## Prove layers, then compose

Separate logical transformation, physical representation, algorithmic progress, host interaction,
and final artifact connection.  Give each layer a small contract and a frame law.  For streaming
systems, prove chunk composition independently of chunk boundaries.  For sorting, keep immutable
line contents separate from the mutable permutation and algorithm-specific ordered region.

When a consumer needs a small observation refinement from a large evaluator, define the refinement
over an abstract observation and prove its constructor equations once.  Canonical `a10c2700` makes
WASI successful-exit normalization preserve completed, trapped, nonzero-exit, and memory-exhausted
outcomes, while the consumer supplies only the exact successful payload and an explicit no-fuel
premise.  Spike 3 then applies that theorem without unfolding the computation that produced the
observation.  The refinement changes neither the evaluator nor final proof authority.

For stable sorting by a projected preorder, state stability as equality of the filtered sequence for
every mutual-preorder key class.  This observes the exact order of distinct records sharing a key,
unlike permutation or sorting untagged values.  Canonical `ddab78cb` proves ordering, permutation,
and `Stdlib.Sort.insertionSort_stableOn` independently, then uses tagged equal-key records separated
by a smaller key as a nonvacuous regression.  The pure sorting laws do not establish target
execution or artifact authority.

## Compose generated bodies with tiny authority tails

Keep a generated straight-line body behind its local certificate, then connect it to the production
runner with exact contextual placement and runtime-silence evidence.  State the small handwritten
ABI and terminal suffix as a separate named typed slice.  Carry only the exact RIP, fault, frame,
low-memory, and result facts that cross the join; discharge placement and terminal classification at
that boundary.  Compose the pieces only in the production runner and the final
`VerifiedProgram.compose` value.

The Windows compiler-bulk spike at `8b39389` follows this pattern: its arbitrary-environment body
theorem is algebraic, not a fabricated process-entry ABI; a separate three-instruction tail reserves
40 bytes of call space, moves RAX to RCX, and reaches the exact linked `ExitProcess` provider.  Linux
Spike 2 commits `e741e96` and `4a3b394` use named terminal-tail and structural-prefix slices rather
than unfolding the whole runner.  Neither a successful local fold nor executing the tail proves ABI
placement, termination, artifact identity, or admission by itself.  Native exit 42 is regression
evidence, not proof authority.  Empty exports are honest for these process-entry executables, but do
not demonstrate a callable library boundary.

## Keep finite search subordinate to the model

At the memory-model presentation layer, prove that every enumerated seed and successor belongs to
the normative relation; `Gasm.MemoryModel.FiniteSearch` then lifts those facts to bounded-search
soundness.  Reverse completeness is a separate obligation, required only when a concrete tool
advertises complete enumeration for its stated finite scope.

## Close tiny carrier controls without equality instances

For a small private finite-carrier fixture, do not add `DecidableEq` to a public type merely so
`simp` can prove constructor inequality or `List.Nodup`.  Independently reviewed, isolated M0
envelope checkpoint `ecd5f9e` constructs `List.Nodup.cons` and `List.Mem` witnesses explicitly and
closes impossible constructor equalities by inductive no-confusion (`cases equality`).  Reviewer
rebuilt both Envelope modules together in about 1.35 seconds.  This is a fixture technique, not a
current-main API or evidence for a new finite-set library abstraction.

## Lift target steps through small generic algebras

When two targets repeat only the list induction around their own one-step facts, keep those semantic
facts target-owned and lift them through `Gasm.Proof.LocalExecution`.  The x86-64 and AArch64 macro
assemblers use the same append and frame algebra while retaining different instruction classes,
clobber definitions, contracts, and production runners.  This centralized two append proofs and
six AArch64 frame inductions, and removed x86-64's manual composed-frame bookkeeping; each target
retains only a small fold-alignment proof so its established public definition keeps the same
reduction behavior.  Generalize the algebraic shell only; instruction safety, control flow, fuel,
faults, host effects, and artifact identity stay with the layer that defines them.

For that alignment proof, expose one recursive layer with `change` and apply the induction
hypothesis directly.  A broad `simp` over the fold can unfold a target's large step semantics: in
this extraction the direct proof reduced the focused rebuild from about 97 seconds to 5 seconds.

## Derive repeated store frames from exact effects

When two instruction forms have the same single-store semantic shape, derive their frame laws from
plain theorems over the exact descriptor and step result rather than enumerating each written byte
inside both consumers.  Require equality to one `.store` descriptor and exact post-step memory
equality to the corresponding write into pre-memory; these premises prevent a convenient parallel
effect from laundering an instruction-specific proof.  Derive outside-footprint preservation over
the write operation's exact modular address list, without adding a no-wrap premise that the memory
semantics does not need.

For read dependence, keep effective-address, stored-value, and post-step non-memory projection
congruence as consumer premises.  `StoreAgreeOn` then follows from the inside-write byte lemma, while
the exact store descriptor makes the load footprint empty.  Canonical `4c6fbf4c` applies the same
`singleStore_writesWithin`/`singleStore_readsWithin` signature to x86 W32 and W64 MOV stores without
changing their public theorem types or compiled frame audits.  Repeated consumer theorem text fell
from 61 lines to 44; that 28 percent reduction is comparative evidence, not a target or acceptance
gate.  Instruction admission, concurrency, platform behavior, and artifact authority stay outside
this frame algebra.

## Factor a load frame through one declared read

For an exact singleton load, factor the instruction step through the one width-indexed declared
read and make the remaining post-state transformer parametric under `agreeOutsideMemory`.  Prove the
effective address stable, use `agreeOn` with `X86_64Mem.read_congr'` to equate the declared values,
and let the empty store footprint discharge `StoreAgreeOn`.  Do not add memory preservation to this
read-frame helper: reuse the instruction's separately audited no-write theorem so each obligation is
proved once by its owning layer.

The negative control must exercise an additional dependency, not substitute one load for another.
Canonical `aa80e2b1` uses a hostile step whose observable RAX materially combines declared `[rdi]`
and hidden `[rsi]`, then holds the declared value fixed while varying only the hidden value.  This
refutes every proposed one-read factorization with a memory-insensitive post transformer.  The
blocked predecessor `58a624ff` ignored the declared value and therefore tested only a wholly
misdeclared load.  Exact factorization and a dual-dependent control make the helper reusable for the
two accepted x86 load consumers; they do not establish admission, concurrency, platform behavior,
or artifact authority.

## Make control-flow obligations local

At the core CFG layer, use typed block-entry contracts as invariant transfer points and close every
possible successor statically, while charging path-local entry facts only to the edge selected at
runtime; `Gasm.Core.CFG` demonstrates this split with `targetsInGraph` and `SelectedEdge`.  Prove
straight-line production prefixes once and compose loops with an explicit measure or bound.  Do not
replace a production-runner proof with replay of a second evaluator.

Use the same named boundaries in both directions during proof design.  Forward propagation derives
the strongest useful reachable and ghost facts; backward propagation derives the weakest entry
requirements implied by exits and the caller's goal.  Refine joins and loop invariants in both
directions until their contracts stabilize.  An unknown block body is then a local implementation
hole with an explicit contract: discharge it when the body arrives, and use one closed-graph
composition theorem after every hole is filled.  This is currently a search discipline, not a
prescribed deterministic tactic or an established generic fixed-point library.

Keep each boundary projected to what its neighbors observe: control location, live data, relational
ghost state, and outstanding obligations.  The closed-graph theorem should quantify only over
selected, reachable block contracts; an unselected feature or edge must add no premise.  A failed
forward/postcondition or backward/precondition inclusion belongs at that exact edge, rather than in
a later whole-path replay.  The Spike 2 Linux write-setup/syscall bridge is the current proving ground
for this discipline; wait for its accepted join/loop evidence before extracting generic iteration or
fixed-point combinators.

For an x86 body hole, `Gasm.Targets.X86_64.LocalBlockDischarge` is the accepted local mechanism.  It
carries only the canonical selected-production-prefix cutpoint, strengthens entries and weakens
exits with the usual contract variance, and composes adjacent runs through the exact middle machine,
event, and ghost state.  Its result is a caller-logical phase classification; native termination,
CFG identity, placement, and final artifact authority remain separate obligations.

The Spike 3 SortLines proof spine (`533d22f` through `5ae2b6b`) applies the same discipline to a
larger relational proof: prove each selected local block or cutpoint with an exact pre/post
ghost-world handoff, then make the program theorem a fold over those typed boundaries.  Do not
reconstruct ghost ownership from bytes between blocks, and do not let an intermediate phase result
stand in for a runnable `VerifiedProgram` connection.

## Frame external inputs once

When a runner is parametric in stdin, incoming requests, or other unrelated environment state,
prove the `withExternalInputs` commutation and observation laws at the machine/platform layer once.
Then transport an exact closed execution through those laws.  Spike 1 and Spike 2 equivalence
proofs reuse target-owned `withExternalInputs` laws for events, observables, and admissibility
instead of replaying the implementation for each environment.  This is a frame theorem: it does
not permit dropping an input that the selected host transition actually observes.

## Preserve exact dependent CFG definitions

At the CFG authoring and lowering layer, composition or nominal-ID remapping must preserve the whole
dependent block definition, not merely its name or entry.  `Gasm.Compiler.TypedCFG` proves exact
same-index lowered definitions and remapping commutation; a matching name or entry alone is not
evidence that one block may substitute for another.

## Try independent decompositions for hard proofs

When the invariant is unclear, obtain independent proposals: algebraic induction, ghost refinement,
library factoring, or differential transport.  Compare them by soundness, universality,
composability, consumer proof burden, and build cost.  Test the winning idea with one decisive
kernel-checked lemma before expanding it.  A counterexample vetoes a proposal; this is not majority
voting.

## Reuse proofs property by property

For an optimized or relaid-out implementation, identify the exact semantic delta and the properties
that observe it.  Retain source, CFG, frame, or layout proofs that are unaffected; re-prove only the
selected contracts changed by the replacement.  Final certificates must still identify the exact
implementation and artifact being emitted.

At the compiler-frontend lowering layer, `Gasm.Compiler.TypedCFG.ProgramPlan.loweredBlock` is the
accepted differential pattern: retain source entry and topology properties, and re-prove only the
dimensions changed by structural terminator replacement.

The AArch64 and Microsoft x64 straight-line backends now demonstrate the target-body form of this
pattern.  Each target-owned `FunctionalDelta` relates one exact replacement body to a compiler
certificate only through the selected result observation.  X64 additionally requires an explicit
memory-preservation premise from the replacement segment contract.  AArch64 instead admits a list
of its frame-preserving macro `Instruction`s and derives memory, SP, NZCV, fault, and termination
frames structurally.  Each `FunctionalDelta.realize` transports the source-result theorem while
regenerating that target's replacement instructions, bytes, fallthrough, frames, clobbers, and
control-flow classification.  It deliberately does not inherit baseline input-register
preservation.  Canonical x64 bridge `8485743` is exercised end to end by `88edac5`, which proves
placement, runtime silence, terminal outcome, artifact connection, admission, and the sole
`VerifiedProgram` separately for the exact one-instruction replacement.  A property not selected by
the consumer is neither inherited nor silently claimed.

## Charge proofs where the risk appears

Callers prove facts that vary at the call site.  Libraries prove their transition laws once;
targets prove instruction and calling-convention facts; linkers prove layout and joint
admissibility.  A feature absent from a path imposes no obligation on that path.  Proof economy may
move and reuse a necessary fact, but never omit it.
