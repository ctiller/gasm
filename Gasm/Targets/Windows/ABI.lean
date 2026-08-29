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
import Gasm.Core.ABI
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base

namespace Gasm.Targets.Windows

open Gasm.Core
open Gasm.Targets.X86_64

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Microsoft x64 Fastcall ABI type tag. -/
structure WindowsFastcall

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Implementation of MS x64 Fastcall calling convention discipline for x86-64. -/
instance : AbiDiscipline X86_64 WindowsFastcall where
  callerSavedRegs      := [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨8⟩, ⟨9⟩, ⟨10⟩, ⟨11⟩] -- RAX, RCX, RDX, R8-R11
  calleeSavedRegs      := [⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨12⟩, ⟨13⟩, ⟨14⟩, ⟨15⟩] -- RBX, RSP, RBP, RSI, RDI, R12-R15
  shadowSpaceRequired  := 32
  stackAlignment       := 16
  argumentRegisters    := [⟨1⟩, ⟨2⟩, ⟨8⟩, ⟨9⟩] -- RCX, RDX, R8, R9
  returnRegister       := ⟨0⟩ -- RAX

end Gasm.Targets.Windows
