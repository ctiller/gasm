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
import Gasm.Core.Types

namespace Gasm.Core

/- REF: docs/PROOF_CARRYING_ASSEMBLY.md#1-capability-based-discrete-memory-permissions -/
/-- Fractional/typestate permissions for memory locations. -/
inductive PermissionShare where
  | ReadOnly   -- Shared read capability (fractional read access)
  | Exclusive  -- Full write/read capability (exclusive ownership)
  | Locked     -- Synchronized / atomic typestate capability
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/PROOF_CARRYING_ASSEMBLY.md#1-capability-based-discrete-memory-permissions -/
/-- Linear proof-carrying capability token granting access to a memory slice. -/
structure MemoryPerm (base : Address) (len : Nat) (share : PermissionShare) : Type where
  validRange : base.toNat + len ≤ 18446744073709551616
  nonEmpty   : len > 0

/- REF: docs/PROOF_CARRYING_ASSEMBLY.md#11-capability-splitting-and-joining-laws -/
/-- Spatial capability splitting relation: separates [base, base + len) into [base, base + k) and [base + k, base + len). -/
def MemoryPerm.split {base : Address} {len : Nat} {share : PermissionShare}
    (p : MemoryPerm base len share) (k : Nat) (h_k : 0 < k ∧ k < len)
    (h_wrap : (base + k.toUInt64).toNat = base.toNat + k) :
    MemoryPerm base k share × MemoryPerm (base + k.toUInt64) (len - k) share :=
  have h_valid1 : base.toNat + k ≤ 18446744073709551616 := by
    have h1 := p.validRange
    omega
  have h_valid2 : (base + k.toUInt64).toNat + (len - k) ≤ 18446744073709551616 := by
    have h1 := p.validRange
    rw [h_wrap]
    omega
  (⟨h_valid1, h_k.1⟩, ⟨h_valid2, by omega⟩)

/- REF: docs/PROOF_CARRYING_ASSEMBLY.md#1-capability-based-discrete-memory-permissions -/
/-- Non-overlapping disjointness condition for two memory slices. -/
def DisjointRanges (a₁ : Address) (l₁ : Nat) (a₂ : Address) (l₂ : Nat) : Prop :=
  a₁.toNat + l₁ ≤ a₂.toNat ∨ a₂.toNat + l₂ ≤ a₁.toNat

/- REF: docs/PROOF_CARRYING_ASSEMBLY.md#1-capability-based-discrete-memory-permissions -/
/-- Pairwise-disjointness invariant for memory capability token lists. -/
def DisjointTokens (tokens : List (Address × Nat × PermissionShare)) : Prop :=
  ∀ (i j : Nat), (hi : i < tokens.length) → (hj : j < tokens.length) → i ≠ j →
    let t₁ := tokens.get ⟨i, hi⟩
    let t₂ := tokens.get ⟨j, hj⟩
    DisjointRanges t₁.1 t₁.2.1 t₂.1 t₂.2.1

/- REF: docs/PROOF_CARRYING_ASSEMBLY.md#1-capability-based-discrete-memory-permissions -/
/-- Active memory capability permissions container with non-overlapping range invariant. -/
structure MemoryPermissions (Arch : Type) where
  tokens   : List (Address × Nat × PermissionShare)
  disjoint : DisjointTokens tokens := by intros _ _ _ _ _; trivial

end Gasm.Core
