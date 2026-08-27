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

namespace Gasm.Effects

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- Coproduct injection typeclass embedding a sub-domain effect into a composite event universe. -/
class Inject (SubEvent Event : Type) where
  inject : SubEvent → Event

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
instance : Inject E E where
  inject e := e

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
instance : Inject E₁ (E₁ ⊕ E₂) where
  inject e := Sum.inl e

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
instance : Inject E₂ (E₁ ⊕ E₂) where
  inject e := Sum.inr e

/- REF: docs/SYSTEM_EFFECTS.md#11-core-effect-typeclass-hierarchy-gasmeffects -/
/-- Open typeclass for verified observable machine and system effects. -/
class IsEvent (ε : Type) where
  domain : String
  format : ε → String

/- REF: docs/SYSTEM_EFFECTS.md#11-core-effect-typeclass-hierarchy-gasmeffects -/
/-- Universal, open event container with decidable kernel equivalence. -/
structure AnyEvent where
  domain  : String
  payload : String
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/SYSTEM_EFFECTS.md#11-core-effect-typeclass-hierarchy-gasmeffects -/
/-- Constructs an AnyEvent from any type implementing IsEvent. -/
def AnyEvent.of {ε : Type} [IsEvent ε] (e : ε) : AnyEvent :=
  ⟨IsEvent.domain (ε := ε), IsEvent.format e⟩

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- Universal automatic injection: any type implementing IsEvent automatically injects into AnyEvent. -/
instance {ε : Type} [IsEvent ε] : Inject ε AnyEvent where
  inject e := AnyEvent.of e

end Gasm.Effects
