# Practical proof tactics

This is a short working guide, not a mandatory proof framework.  It records approaches that have
made real Gasm proofs smaller or more honest.  Add abstractions only after repeated use.

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

## Prove layers, then compose

Separate logical transformation, physical representation, algorithmic progress, host interaction,
and final artifact connection.  Give each layer a small contract and a frame law.  For streaming
systems, prove chunk composition independently of chunk boundaries.  For sorting, keep immutable
line contents separate from the mutable permutation and algorithm-specific ordered region.

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

Use typed block-entry contracts as invariant transfer points.  Prove straight-line production
prefixes once, require only the dynamically selected conditional edge at runtime, and compose loops
with an explicit measure or bound.  Do not replace a production-runner proof with replay of a second
evaluator.

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

## Charge proofs where the risk appears

Callers prove facts that vary at the call site.  Libraries prove their transition laws once;
targets prove instruction and calling-convention facts; linkers prove layout and joint
admissibility.  A feature absent from a path imposes no obligation on that path.  Proof economy may
move and reuse a necessary fact, but never omit it.

