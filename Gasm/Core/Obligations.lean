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

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#1-the-linear-obligation-ledger -/
/-- Open linear obligation registration typeclass. -/
class IsObligation (α : Type) where
  obligationKind : α → String
  isLinear       : α → Bool := fun _ => true

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#1-the-linear-obligation-ledger -/
/-- First-class linear obligation capability token with resource-tracking identifier. -/
structure ObligationToken where
  id                : Nat
  kind              : String
  isDroppableOnExit : Bool := false
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#1-the-linear-obligation-ledger -/
/-- Constructs a legacy value-level token accepted by `isValidAtExit`.
This marker neither performs resource cleanup nor proves process-scoped discharge. -/
def ObligationToken.mkProcessScoped (id : Nat) (kind : String) : ObligationToken :=
  ⟨id, kind, true⟩

/- REF: docs/MEMORY_PROVENANCE.md#1-core-principles-of-memory-provenance -/
/-- Root backing allocation from OS page provider (e.g. VirtualAlloc / mmap) with active child borrow tracking. -/
structure ArenaPageToken where
  arenaId       : Nat
  baseAddress   : Address
  sizeBytes     : Nat
  activeBorrows : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_PROVENANCE.md#1-core-principles-of-memory-provenance -/
/-- Safety precondition for releasing an arena page: all active child sub-allocations must be discharged. -/
def ArenaPageToken.isSafeToRelease (t : ArenaPageToken) : Bool :=
  t.activeBorrows == 0

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#11-multiset-obligation-subtraction-listeraseall -/
/-- Erases all occurrences of elements in `toRemove` from `xs`. -/
def List.eraseAll {α : Type} [DecidableEq α] (xs : List α) (toRemove : List α) : List α :=
  toRemove.foldl (fun acc x => acc.erase x) xs

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#11-multiset-obligation-subtraction-listeraseall -/
/-- Strict linear discharge checking requiring constructive membership for every discharged token. -/
def eraseAllChecked {α : Type} [DecidableEq α] (xs : List α) (toRemove : List α) : Option (List α) :=
  toRemove.foldlM (fun acc x =>
    if x ∈ acc then some (acc.erase x) else none) xs

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#1-the-linear-obligation-ledger -/
/-- Linear typestate obligation ledger. -/
structure ObligationLedger where
  tokens : List ObligationToken
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#1-the-linear-obligation-ledger -/
/-- Invariant enforcing that all obligations in the ledger are consumed upon procedure return. -/
def ObligationLedger.isEmpty (l : ObligationLedger) : Bool :=
  l.tokens.isEmpty

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#21-function-returns-cputerminatorret -/
/-- Validity invariant upon procedure return: strictly zero outstanding obligations. -/
def ObligationLedger.isValidAtReturn (l : ObligationLedger) : Bool :=
  l.tokens.isEmpty

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#22-unconditional-exits-cputerminatorsysexit -/
/-- Legacy exit predicate: every remaining token must carry the exit marker.
It does not consume tokens, identify a process, or prove any resource teardown. -/
def ObligationLedger.isValidAtExit (l : ObligationLedger) : Bool :=
  l.tokens.all (fun t => t.isDroppableOnExit)

end Gasm.Core
