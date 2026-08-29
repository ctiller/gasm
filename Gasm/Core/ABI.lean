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
import Gasm.Core.Arch
import Gasm.Core.CFG

namespace Gasm.Core

/- REF: docs/STACK_DISCIPLINE.md#2-multi-abi-calling-conventions-stack-restoration-laws -/
/-- Partial structural vocabulary for a selected ABI.
It is not by itself an M1/M2-B relational entry/exit, admissibility, or artifact/link certificate. -/
class AbiDiscipline (Arch : Type) (ABI : Type) [TargetArch Arch] where
  callerSavedRegs      : List (Register Arch (TargetArch.wordWidth Arch))
  calleeSavedRegs      : List (Register Arch (TargetArch.wordWidth Arch))
  shadowSpaceRequired  : Nat
  stackAlignment       : Nat
  argumentRegisters    : List (Register Arch (TargetArch.wordWidth Arch))
  returnRegister       : Register Arch (TargetArch.wordWidth Arch)

end Gasm.Core
