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
/-- Pure domain event for standard console interactions. -/
inductive ConsoleEvent where
  | out (text : String)
  | err (text : String)
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/SYSTEM_EFFECTS.md#11-core-effect-typeclass-hierarchy-gasmeffects -/
instance : IsEvent ConsoleEvent where
  domain := "Console"
  format := fun
    | .out s => s!"out({s})"
    | .err s => s!"err({s})"

/- REF: docs/SYSTEM_EFFECTS.md#21-monadconsole-standard-io -/
/-- Portable typeclass abstraction for standard input/output console interactions. -/
class MonadConsole (m : Type → Type) where
  printStr  : String → m Unit
  printLine : String → m Unit := fun s => printStr (s ++ "\r\n")
  readLine  : m (Option String)

end Gasm.Effects
