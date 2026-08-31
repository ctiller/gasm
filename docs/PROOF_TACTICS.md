# Practical proof tactics

This is a short working guide, not a mandatory proof framework.  It records approaches that have
made real Gasm proofs smaller or more honest.  Add abstractions only after repeated use.

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

## Design relational ghost state

Separate immutable logical facts from evolving progress, resources, phases, and obligations.  Relate
physical state to ghost state with a relation: ghost ownership, generations, and nominal identities
need not be reconstructible from machine bytes.  Transfer this state at typed calls and jumps, and
frame components a step does not affect.  Prefer several composable layers over one monolithic ghost
record.

## Consider every bound

For the selected routine and property, inventory applicable numeric ranges, input and output sizes,
loop counts, buffer capacity, allocation, stack, fragmentation, and execution work.  For each
material bound, either prove it, derive it, request it as a capability, eliminate it by streaming,
or specify failure and recovery.  Do not add ledgers for quantities the routine never uses.  Keep
proof fuel distinct from a resource enforced by emitted code.  A useful bound often supplies the
induction measure: `UInt64` decimal length is at most 20 and determines formatter capacity,
iterations, and work.

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

## Prove layers, then compose

Separate logical transformation, physical representation, algorithmic progress, host interaction,
and final artifact connection.  Give each layer a small contract and a frame law.  For streaming
systems, prove chunk composition independently of chunk boundaries.  For sorting, keep immutable
line contents separate from the mutable permutation and algorithm-specific ordered region.

## Keep finite search subordinate to the model

At the memory-model presentation layer, prove that every enumerated seed and successor belongs to
the normative relation; `Gasm.MemoryModel.FiniteSearch` then lifts those facts to bounded-search
soundness.  Reverse completeness is a separate obligation, required only when a concrete tool
advertises complete enumeration for its stated finite scope.

Test reverse completeness by widening the normative transition relation with one valid edge the
enumerator omits.  The private positive control in `2059cd3` consumes actual `ReachesAt` evidence and
the exact step relation, so this mutation breaks its proof.  A theorem that only shows
`state ≤ fuel → reported` and survives the mutation has characterized an encoding or index, not
normative reachability.

## Minimize premises around one semantic witness

When stronger evidence already entails a premise, derive it inside the reusable theorem instead of
charging every caller.  When several stable consequences depend on the same existential witness,
package them together so consumers destruct that witness once.  The accepted from-read and atomic
read-source helpers (`4433e1d`, `4c980cf`) centralize endpoint, source, value, coherence, and
adjacency consequences this way; `e4857567` similarly reuses the canonical premise-free
program-order transitivity law.  Do not bundle unrelated facts simply to make a larger theorem.

## Close tiny carrier controls without equality instances

For a small private finite-carrier fixture, do not add `DecidableEq` to a public type merely so
`simp` can prove constructor inequality or `List.Nodup`.  M0 envelope checkpoint `ecd5f9e` constructs
`List.Nodup.cons` and `List.Mem` witnesses explicitly and closes impossible constructor equalities by
inductive no-confusion (`cases equality`).  The dependency-free focused build remained under two
seconds.  This is a fixture technique, not evidence for a new finite-set library abstraction.

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

## Charge proofs where the risk appears

Callers prove facts that vary at the call site.  Libraries prove their transition laws once;
targets prove instruction and calling-convention facts; linkers prove layout and joint
admissibility.  A feature absent from a path imposes no obligation on that path.  Proof economy may
move and reuse a necessary fact, but never omit it.
