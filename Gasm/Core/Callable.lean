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
import Gasm.Core.Obligations
import Gasm.Core.CFG

namespace Gasm.Core

/- REF: docs/ARCHITECTURE.md#2-the-core-verification-flow -/
/-- Operational single-step execution relation on target-native machine state. -/
def MachineStep (Arch : Type) [TargetArch Arch] (instr : TargetArch.Instruction Arch) (s₁ s₂ : TargetArch.MachineState Arch) : Prop :=
  s₂ = TargetArch.stepPure instr s₁

/- REF: docs/API_STATE_MODELS.md#3-the-callable-typeclass-automatic-derivation -/
/-- Universal contract for invocations across internal blocks, symbols, and OS boundaries. -/
class Callable (Arch : Type) [TargetArch Arch] (Target : Type) (InState : outParam Type) (OutState : outParam Type) where
  Precondition          : ComposedState Arch InState → Prop
  validTransition       : Target → InState → TargetArch.MachineState Arch → OutState → Prop
  pushedObligations     : Target → TargetArch.MachineState Arch → List ObligationToken
  dischargedObligations : Target → ComposedState Arch InState → List ObligationToken
  causalEffects         : Target → ComposedState Arch InState → List (EventTag × EventTag)
  update                : Target → ComposedState Arch InState → ComposedState Arch OutState
  emitInstruction       : Target → TargetArch.Instruction Arch
  soundness             : ∀ (target : Target) (s : ComposedState Arch InState),
                          Precondition s →
                          MachineStep Arch (emitInstruction target) s.machine (update target s).machine ∧
                          validTransition target s.api (update target s).machine (update target s).api ∧
                          eraseAllChecked (s.obligations ++ pushedObligations target (update target s).machine) (dischargedObligations target s) = some (update target s).obligations ∧
                          (∀ (e₁ e₂ : EventTag), (e₁, e₂) ∈ causalEffects target s → 
                            VectorClock.happensBefore (s.eventHistory e₁) ((update target s).eventHistory e₂))

end Gasm.Core
