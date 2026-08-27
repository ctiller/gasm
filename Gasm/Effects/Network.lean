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
import Gasm.Effects.Inject

namespace Gasm.Effects

open Gasm.Core

/- REF: docs/SYSTEM_EFFECTS.md#11-core-effect-typeclass-hierarchy-gasmeffects -/
/-- Pure domain event for network socket interactions. -/
inductive NetEvent where
  | listen (port : UInt16)
  | accept (client : String)
  | recv   (data : String)
  | send   (data : String)
  | close  (sock : Nat)
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/SYSTEM_EFFECTS.md#11-core-effect-typeclass-hierarchy-gasmeffects -/
instance : IsEvent NetEvent where
  domain := "Network"
  format := fun
    | .listen p => s!"listen({p})"
    | .accept c => s!"accept({c})"
    | .recv d   => s!"recv({d})"
    | .send d   => s!"send({d})"
    | .close s  => s!"close({s})"

/- REF: docs/SYSTEM_EFFECTS.md#2-portable-effect-typeclass-specifications -/
/-- Portable typeclass abstraction for TCP network socket operations. -/
class MonadNetwork (m : Type → Type) where
  listen : UInt16 → m (Option Nat)
  accept : Nat → m (Option Nat)
  recv   : Nat → Nat → m (Option String)
  send   : Nat → String → m Bool
  close  : Nat → m Unit

end Gasm.Effects
