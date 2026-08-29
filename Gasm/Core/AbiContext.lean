/-
Copyright 2026 Craig Tiller

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Lean

namespace Gasm.Core

/-!
This module contains staging vocabulary for the ABI-context design.  It deliberately does not
define a Boolean link gate or a whole-program callability theorem.  In particular, constructing
one of these descriptive values is not authority to emit a `VerifiedProgram`.  The missing target
realization and whole-program connection proofs are tracked in `docs/ABI_CONTEXT.md`.
-/

/- REF: docs/ABI_CONTEXT.md#3-placement-free-logical-contracts -/
/-- Whether a logical context is erased or must have a runtime realization. -/
inductive ContextMateriality where
  | erasedGhost
  | runtime
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#3-placement-free-logical-contracts -/
/-- The authority a callee requests over a logical resource. -/
inductive ContextAccess where
  | observe
  | mutate
  | consume
  | provide
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#3-placement-free-logical-contracts -/
/-- Logical extent is independent of where a runtime binding is stored. -/
inductive ContextExtent where
  | call
  | lexical
  | request
  | task
  | thread
  | process
  | object
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#3-placement-free-logical-contracts -/
/-- How a binding may cross a child or nested execution boundary. -/
inductive ContextPropagation where
  | borrow
  | copy
  | move
  | inherit
  | doNotPropagate
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#3-placement-free-logical-contracts -/
/-- Whether the binding may follow work between execution agents. -/
inductive ContextScheduling where
  | pinned
  | migratable
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#3-placement-free-logical-contracts -/
/-- Exit classes for which a context contract must define cleanup. -/
inductive ContextTeardown where
  | normalReturn
  | failure
  | cancellation
  | executorDestruction
  | callback
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#3-placement-free-logical-contracts -/
/-- A placement-free logical requirement. `Key` and `Protocol` are type-level identities, not
    forgeable string names. `valid` and `establishes` connect a runtime value to boundary state;
    they are the proof source for a binding. -/
structure LogicalContextRequirement (Key Resource Protocol State : Type) where
  materiality : ContextMateriality
  access : ContextAccess
  extent : ContextExtent
  propagation : ContextPropagation
  scheduling : ContextScheduling
  teardown : List ContextTeardown
  valid : Protocol → State → Resource → Prop
  establishes : Protocol → State → Resource → State → Prop

/- REF: docs/ABI_CONTEXT.md#4-establishment-and-satisfaction -/
/-- Evidence for one exact requirement.  Lifecycle, representation, and protocol cannot be dropped
    by a string comparison because the complete requirement and its types index the evidence. -/
structure EstablishedContextBinding
    (requirement : LogicalContextRequirement Key Resource Protocol State)
    (protocol : Protocol) (before after : State) where
  value : Resource
  established : requirement.establishes protocol before value after
  validAfter : requirement.valid protocol after value

/- REF: docs/ABI_CONTEXT.md#4-establishment-and-satisfaction -/
/-- A protocol upgrade is explicit proof-producing data.  Keeping a diagnostic name while changing
    a protocol does not create this value. -/
structure ContextProtocolRefinement
    (OldResource OldProtocol NewResource NewProtocol : Type)
    (oldValid : OldProtocol → OldResource → Prop)
    (newValid : NewProtocol → NewResource → Prop) where
  adaptResource : OldResource → NewResource
  adaptProtocol : OldProtocol → NewProtocol
  preserves : ∀ protocol resource,
    oldValid protocol resource → newValid (adaptProtocol protocol) (adaptResource resource)

/- REF: docs/ABI_CONTEXT.md#5-target-realization -/
/-- Calls, callbacks, signals, and interrupts may select different conventions on the same target. -/
inductive BoundaryEntryKind where
  | ordinaryCall
  | callback
  | signal
  | interrupt
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#5-target-realization -/
/-- A target supplies canonical physical locations and a hardware-aware alias relation.  Locations
    therefore cannot be raw register names or unqualified TLS/table indices. -/
class PhysicalLocationModel (Target : Type) where
  Location : Type
  overlaps : Location → Location → Prop
  overlaps_refl : ∀ location, overlaps location location
  overlaps_symm : ∀ {left right}, overlaps left right → overlaps right left

abbrev PhysicalLocation (Target : Type) [model : PhysicalLocationModel Target] := model.Location

/- REF: docs/ABI_CONTEXT.md#6-resolved-footprints-and-conflicts -/
inductive PhysicalAccessMode where
  | read
  | write
  | clobber
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#6-resolved-footprints-and-conflicts -/
structure PhysicalAccess (Target : Type) [PhysicalLocationModel Target] where
  location : PhysicalLocation Target
  mode : PhysicalAccessMode

/- REF: docs/ABI_CONTEXT.md#6-resolved-footprints-and-conflicts -/
def PhysicalAccess.Conflicts [model : PhysicalLocationModel Target]
    (left right : PhysicalAccess Target) : Prop :=
  model.overlaps left.location right.location ∧
    ¬(left.mode = .read ∧ right.mode = .read)

/- REF: docs/ABI_CONTEXT.md#6-resolved-footprints-and-conflicts -/
/-- The resolved footprint includes setup, access, body preservation, and teardown work. -/
structure PhysicalFootprint (Target : Type) [PhysicalLocationModel Target] where
  accesses : List (PhysicalAccess Target)

/- REF: docs/ABI_CONTEXT.md#6-resolved-footprints-and-conflicts -/
def PhysicalFootprint.Compatible [PhysicalLocationModel Target]
    (left right : PhysicalFootprint Target) : Prop :=
  ∀ l ∈ left.accesses, ∀ r ∈ right.accesses, ¬l.Conflicts r

/- REF: docs/ABI_CONTEXT.md#6-resolved-footprints-and-conflicts -/
/-- A realized boundary checks context footprints against the convention's complete classified
    signature footprint and against one another.  There is intentionally no untyped Boolean
    `firstConflict`: a target proof supplies physical non-interference. -/
structure RealizedBoundary (Target Signature : Type) [PhysicalLocationModel Target] where
  signature : Signature
  entryKind : BoundaryEntryKind
  conventionFootprint : PhysicalFootprint Target
  contextFootprints : List (PhysicalFootprint Target)
  conventionCompatible :
    ∀ context ∈ contextFootprints, conventionFootprint.Compatible context
  contextsPairwiseCompatible : contextFootprints.Pairwise PhysicalFootprint.Compatible

end Gasm.Core
