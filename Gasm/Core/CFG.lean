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
import Gasm.Core.BlockM

namespace Gasm.Core

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Target register model parameterized by architecture and bit width. -/
structure Register (Arch : Type) (width : Nat) where
  id : Nat
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/API_STATE_MODELS.md#4-basicblock-structure-target-parametric-terminators -/
/-- Architectural condition codes for branching. -/
inductive ConditionCode (Arch : Type) where
  | ZeroFlag
  | NonZeroFlag
  | CarryFlag
  | SignFlag
  | Always
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/STACK_DISCIPLINE.md#2-multi-abi-calling-conventions-stack-restoration-laws -/
/-- Current minimal callee stack-clean predicate.
It contains no register-preservation or external-boundary/link certificate by itself. -/
structure CalleeDiscipline (Arch : Type) [TargetArch Arch] {S : Type} (s : ComposedState Arch S) : Prop where
  stack_clean : s.stackDepth = 0

/- REF: docs/API_STATE_MODELS.md#4-basicblock-structure-target-parametric-terminators -/
/-- Architecture-defined control-flow terminator family indexed over the terminal state. -/
inductive CpuTerminator (Arch : Type) [TargetArch Arch] {S : Type} (s_exit : ComposedState Arch S) where
  | jmp   (targetLabel : String) (targetDepth : Nat)
          (h_depth : targetDepth = s_exit.stackDepth) : CpuTerminator Arch s_exit
  | jcc   (cond : ConditionCode Arch)
          (targetTrue targetFalse : String)
          (targetDepth : Nat)
          (h_depth : targetDepth = s_exit.stackDepth) : CpuTerminator Arch s_exit
  | ret   (exportedObligations : List ObligationToken) (bytesToPop : UInt16 := 0)
          (h_zero      : s_exit.stackDepth = 0)
          (h_match     : s_exit.obligations = exportedObligations)
          (h_callee    : CalleeDiscipline Arch s_exit) : CpuTerminator Arch s_exit
  | sysExit (exitCode  : UInt8)
            (h_droppable : ∀ o ∈ s_exit.obligations, o.isDroppableOnExit) : CpuTerminator Arch s_exit
  | halt    (h_droppable : ∀ o ∈ s_exit.obligations, o.isDroppableOnExit) : CpuTerminator Arch s_exit

/- REF: docs/API_STATE_MODELS.md#4-basicblock-structure-target-parametric-terminators -/
/-- Single-entry basic block with typed entry preconditions and monadic body. -/
structure BasicBlock (Arch : Type) [TargetArch Arch] (InState : Type) where
  label         : String
  expectedDepth : Nat
  entryProof    : ComposedState Arch InState → Prop
  body          : Σ (S_exit : Type), ComposedState Arch InState → (Σ (s_exit : ComposedState Arch S_exit), CpuTerminator Arch s_exit)

end Gasm.Core
