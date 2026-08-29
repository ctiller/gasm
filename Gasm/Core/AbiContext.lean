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

/- REF: docs/ABI_CONTEXT.md#1-requirements-and-placements -/
/-- Concrete placements available to a boundary-local context requirement. -/
inductive AbiContextPlacement where
  | erasedGhost
  | explicitArgument (index : Nat)
  | tlsSlot (index : Nat)
  | dedicatedRegister (name : String)
  | capabilityTableSlot (index : Nat)
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#1-requirements-and-placements -/
/-- Lifetime of a context binding. -/
inductive AbiContextLifecycle where
  | perCall
  | requestScoped
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#1-requirements-and-placements -/
/-- A typed boundary-local resource demand.  `resourceKey` is the link-time identity used to
    compare independently compiled requirements; the Lean parameter keeps the binding itself
    statically typed. -/
structure AbiContextRequirement (Resource : Type) where
  resourceKey : String
  placement : AbiContextPlacement
  lifecycle : AbiContextLifecycle
  deriving Repr

/- REF: docs/ABI_CONTEXT.md#2-binding-provenance-and-composition -/
/-- Origin evidence for a concrete context binding. -/
structure AbiContextProvenance where
  establishedBy : String
  boundaryName : String
  resourceKey : String
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#2-binding-provenance-and-composition -/
/-- A typed binding.  Ghost bindings are erased protocol witnesses; every other constructor is a
    concrete runtime binding at the declared placement. -/
inductive AbiContextBinding (Resource : Type) where
  | ghost (value : Resource) : AbiContextBinding Resource
  | explicitArgument (index : Nat) (value : Resource) (provenance : AbiContextProvenance) : AbiContextBinding Resource
  | tlsSlot (index : Nat) (value : Resource) (provenance : AbiContextProvenance) : AbiContextBinding Resource
  | dedicatedRegister (name : String) (value : Resource) (provenance : AbiContextProvenance) : AbiContextBinding Resource
  | capabilityTableSlot (index : Nat) (value : Resource) (provenance : AbiContextProvenance) : AbiContextBinding Resource

/- REF: docs/ABI_CONTEXT.md#2-binding-provenance-and-composition -/
/-- A binding satisfies a requirement exactly when its placement and lifecycle-visible provenance
    are established at the call boundary.  Ghost requirements have no runtime setup path. -/
def AbiContextBinding.Satisfies (requirement : AbiContextRequirement Resource) :
    AbiContextBinding Resource → Prop
  | .ghost _ => requirement.placement = .erasedGhost
  | .explicitArgument index _ provenance =>
      requirement.placement = .explicitArgument index ∧ provenance.resourceKey = requirement.resourceKey
  | .tlsSlot index _ provenance =>
      requirement.placement = .tlsSlot index ∧ provenance.resourceKey = requirement.resourceKey
  | .dedicatedRegister name _ provenance =>
      requirement.placement = .dedicatedRegister name ∧ provenance.resourceKey = requirement.resourceKey
  | .capabilityTableSlot index _ provenance =>
      requirement.placement = .capabilityTableSlot index ∧ provenance.resourceKey = requirement.resourceKey

/- REF: docs/ABI_CONTEXT.md#2-binding-provenance-and-composition -/
/-- Callability evidence for a boundary using a typed context capability. -/
structure AbiContextCallable (requirement : AbiContextRequirement Resource)
    (binding : AbiContextBinding Resource) : Prop where
  satisfied : binding.Satisfies requirement

/- REF: docs/ABI_CONTEXT.md#2-binding-provenance-and-composition -/
/-- Erased ghost requirements impose no concrete calling convention setup. -/
theorem AbiContextCallable.ghost_erases (requirement : AbiContextRequirement Resource) (value : Resource)
    (h : requirement.placement = .erasedGhost) :
    AbiContextCallable requirement (.ghost value) := ⟨h⟩

/- REF: docs/ABI_CONTEXT.md#2-binding-provenance-and-composition -/
/-- Untyped link-time descriptor used only to detect physical-placement conflicts across different
    resource types. -/
structure AbiContextDescriptor where
  resourceKey : String
  placement : AbiContextPlacement
  lifecycle : AbiContextLifecycle
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#2-binding-provenance-and-composition -/
def AbiContextRequirement.descriptor (requirement : AbiContextRequirement Resource) : AbiContextDescriptor :=
  { resourceKey := requirement.resourceKey, placement := requirement.placement, lifecycle := requirement.lifecycle }

/- REF: docs/ABI_CONTEXT.md#2-binding-provenance-and-composition -/
/-- Whether two requirements use the same concrete physical placement.  Ghost requirements never
    conflict because they carry no runtime representation. -/
def AbiContextDescriptor.overlaps (left right : AbiContextDescriptor) : Bool :=
  match left.placement, right.placement with
  | .erasedGhost, _ => false
  | _, .erasedGhost => false
  | .explicitArgument a, .explicitArgument b => a == b
  | .tlsSlot a, .tlsSlot b => a == b
  | .dedicatedRegister a, .dedicatedRegister b => a == b
  | .capabilityTableSlot a, .capabilityTableSlot b => a == b
  | _, _ => false

/- REF: docs/ABI_CONTEXT.md#2-binding-provenance-and-composition -/
/-- A concrete overlap is compatible only when resource identity and lifecycle agree. -/
def AbiContextDescriptor.compatible (left right : AbiContextDescriptor) : Bool :=
  !left.overlaps right || (left.resourceKey == right.resourceKey && left.lifecycle == right.lifecycle)

/- REF: docs/ABI_CONTEXT.md#2-binding-provenance-and-composition -/
structure AbiContextConflict where
  left : AbiContextDescriptor
  right : AbiContextDescriptor
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#2-binding-provenance-and-composition -/
/-- Detects a composition conflict.  An adapter must resolve any returned conflict; composition
    cannot silently choose one resource for a shared slot/register. -/
def AbiContextDescriptor.firstConflict (left : List AbiContextDescriptor)
    (right : List AbiContextDescriptor) : Option AbiContextConflict :=
  left.findSome? fun l => right.findSome? fun r =>
    if l.compatible r then none else some { left := l, right := r }

/- REF: docs/ABI_CONTEXT.md#3-scoped-tls-and-recovery -/
/-- Typed TLS state for one resource family.  Different resource families are composed through
    their descriptors at the ABI boundary, not stored in an untyped global map. -/
abbrev AbiTls (Resource : Type) := Nat → Option Resource

/- REF: docs/ABI_CONTEXT.md#3-scoped-tls-and-recovery -/
structure AbiTlsScope (Resource : Type) where
  slot : Nat
  prior : Option Resource
  active : AbiTls Resource

/- REF: docs/ABI_CONTEXT.md#3-scoped-tls-and-recovery -/
/-- Enters a TLS-bound context, saving the immediately prior binding for nesting. -/
def AbiTlsScope.enter (tls : AbiTls Resource) (slot : Nat) (value : Resource) : AbiTlsScope Resource :=
  { slot := slot, prior := tls slot, active := fun index => if index = slot then some value else tls index }

/- REF: docs/ABI_CONTEXT.md#3-scoped-tls-and-recovery -/
/-- Restores the saved TLS binding.  The same operation is used for success, failure, and
    cancellation exits. -/
def AbiTlsScope.restore (scope : AbiTlsScope Resource) (tls : AbiTls Resource) : AbiTls Resource :=
  fun index => if index = scope.slot then scope.prior else tls index

/- REF: docs/ABI_CONTEXT.md#3-scoped-tls-and-recovery -/
theorem AbiTlsScope.restore_slot (scope : AbiTlsScope Resource) (tls : AbiTls Resource) :
    scope.restore tls scope.slot = scope.prior := by simp [AbiTlsScope.restore]

/- REF: docs/ABI_CONTEXT.md#4-cancellation -/
/-- Caller-owned monotonic cancellation state. -/
inductive CancellationToken where
  | active
  | cancelled
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#4-cancellation -/
def CancellationToken.cancel : CancellationToken → CancellationToken
  | .active => .cancelled
  | .cancelled => .cancelled

/- REF: docs/ABI_CONTEXT.md#4-cancellation -/
theorem CancellationToken.cannotClearParent (token : CancellationToken) :
    token.cancel = .cancelled := by cases token <;> rfl

/- REF: docs/ABI_CONTEXT.md#4-cancellation -/
/-- Explicit cooperative-call result.  A callee can return cancellation only at its declared
    safe point; non-cancellable functions simply do not carry this context requirement. -/
inductive CooperativeOutcome (Result : Type) where
  | completed (value : Result)
  | cancelled
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#4-cancellation -/
/-- Checks a declared cancellation safe point without changing the caller-owned token. -/
def cancellationSafePoint (token : CancellationToken) (value : Result) : CooperativeOutcome Result :=
  match token with
  | .active => .completed value
  | .cancelled => .cancelled

/- REF: docs/ABI_CONTEXT.md#4-cancellation -/
theorem cancellationSafePoint_preserves_token (token : CancellationToken) (value : Result) :
    (match cancellationSafePoint token value with
      | .completed _ => token
      | .cancelled => token) = token := by cases token <;> rfl

/- REF: docs/ABI_CONTEXT.md#4-cancellation -/
/-- Leaves a TLS-scoped cooperative boundary.  Cleanup is unconditional: cancellation changes the
    returned request outcome, never the restoration obligation. -/
def finishCooperativeScope (scope : AbiTlsScope Resource) (tls : AbiTls Resource)
    (token : CancellationToken) (value : Result) : CooperativeOutcome Result × AbiTls Resource :=
  (cancellationSafePoint token value, scope.restore tls)

/- REF: docs/ABI_CONTEXT.md#4-cancellation -/
theorem finishCooperativeScope_restores_tls (scope : AbiTlsScope Resource) (tls : AbiTls Resource)
    (token : CancellationToken) (value : Result) :
    (finishCooperativeScope scope tls token value).2 scope.slot = scope.prior := by
  simp [finishCooperativeScope, AbiTlsScope.restore]

end Gasm.Core
