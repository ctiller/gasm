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
import Gasm.Core.Arch
import Gasm.Core.State

namespace Gasm.Core

/- REF: docs/API_STATE_MODELS.md#2-the-indexed-typestate-monad-blockm -/
/-- Indexed Typestate Monad: Transforms typestate from S₁ to S₂ while tracking concrete ComposedState. -/
def BlockM (Arch : Type) [TargetArch Arch] (S₁ S₂ : Type) (α : Type) : Type :=
  ComposedState Arch S₁ → (α × ComposedState Arch S₂)

namespace BlockM

/- REF: docs/API_STATE_MODELS.md#2-the-indexed-typestate-monad-blockm -/
/-- Pure value embedding in the indexed monad. -/
def pure {Arch : Type} [TargetArch Arch] {S : Type} {α : Type} (a : α) : BlockM Arch S S α :=
  fun s => (a, s)

/- REF: docs/API_STATE_MODELS.md#2-the-indexed-typestate-monad-blockm -/
/-- Monadic sequence / bind operation for indexed typestate transitions. -/
def bind {Arch : Type} [TargetArch Arch] {S₁ S₂ S₃ : Type} {α β : Type}
    (m : BlockM Arch S₁ S₂ α)
    (f : α → BlockM Arch S₂ S₃ β) :
    BlockM Arch S₁ S₃ β :=
  fun s =>
    let (a, s') := m s
    f a s'

/- REF: docs/API_STATE_MODELS.md#2-the-indexed-typestate-monad-blockm -/
/-- State retrieval inside the indexed monad. -/
def get {Arch : Type} [TargetArch Arch] {S : Type} : BlockM Arch S S (ComposedState Arch S) :=
  fun s => (s, s)

/- REF: docs/API_STATE_MODELS.md#2-the-indexed-typestate-monad-blockm -/
/-- State modification inside the indexed monad. -/
def set {Arch : Type} [TargetArch Arch] {S₁ S₂ : Type} (s' : ComposedState Arch S₂) : BlockM Arch S₁ S₂ Unit :=
  fun _ => ((), s')

end BlockM

end Gasm.Core
