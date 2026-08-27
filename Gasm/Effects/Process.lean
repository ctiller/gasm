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
import Gasm.Effects.Inject

namespace Gasm.Effects

/- REF: docs/SYSTEM_EFFECTS.md#23-monadprocess-lifecycle-environment -/
/-- Strongly-typed process lifecycle event. -/
inductive ProcessEvent where
  | exit (code : UInt32)
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/SYSTEM_EFFECTS.md#11-core-effect-typeclass-hierarchy-gasmeffects -/
instance : IsEvent ProcessEvent where
  domain := "Process"
  format := fun
    | .exit c => s!"exit({c})"

/- REF: docs/SYSTEM_EFFECTS.md#23-monadprocess-lifecycle-environment -/
/-- Portable effect typeclass for process lifecycle and execution environment. -/
class MonadProcess (m : Type → Type) [Monad m] where
  exitProcess : ∀ {α : Type}, UInt32 → m α
  getEnvVar   : String → m (Option String)

end Gasm.Effects
