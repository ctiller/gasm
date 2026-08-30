# Practical proof tactics

This is a short working guide, not a mandatory proof framework.  It records approaches that have
made real Gasm proofs smaller or more honest.  Add abstractions only after repeated use.

For a need-oriented map from these tactics to checked declarations, consumers, and deliberate
negative boundaries, see the [proof machinery index](PROOF_MACHINERY_INDEX.md).

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

Inventory numeric ranges, input and output sizes, loop counts, buffer capacity, allocation, stack,
fragmentation, and execution work.  For each bound, either prove it, derive it, request it as a
capability, eliminate it by streaming, or specify failure and recovery.  Keep proof fuel distinct
from a resource enforced by emitted code.  A useful bound often supplies the induction measure:
`UInt64` decimal length is at most 20 and determines formatter capacity, iterations, and work.

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

For an x86 body hole, `Gasm.Targets.X86_64.LocalBlockDischarge` is the accepted local mechanism.  It
carries only the canonical selected-production-prefix cutpoint, strengthens entries and weakens
exits with the usual contract variance, and composes adjacent runs through the exact middle machine,
event, and ghost state.  Its result is a caller-logical phase classification; native termination,
CFG identity, placement, and final artifact authority remain separate obligations.

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
