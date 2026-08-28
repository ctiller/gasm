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

namespace Gasm.Targets.Linux

open Gasm.Core
open Gasm.Targets.X86_64

/- REF: docs/TARGETS/LINUX.md#11-system-v-amd64-function-calling-convention -/
/-- System V AMD64 ABI type tag. -/
structure SystemVAMD64

/- REF: docs/TARGETS/LINUX.md#11-system-v-amd64-function-calling-convention -/
/-- Implementation of System V AMD64 calling convention discipline for x86-64. -/
instance : AbiDiscipline X86_64 SystemVAMD64 where
  callerSavedRegs      := [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩, ⟨9⟩, ⟨10⟩, ⟨11⟩] -- RAX, RCX, RDX, RSI, RDI, R8, R9, R10, R11
  calleeSavedRegs      := [⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨12⟩, ⟨13⟩, ⟨14⟩, ⟨15⟩] -- RBX, RSP, RBP, R12, R13, R14, R15
  shadowSpaceRequired  := 0
  stackAlignment       := 16
  argumentRegisters    := [⟨7⟩, ⟨6⟩, ⟨2⟩, ⟨1⟩, ⟨8⟩, ⟨9⟩] -- RDI, RSI, RDX, RCX, R8, R9
  returnRegister       := ⟨0⟩ -- RAX
  calleePreservesStack := by
    intro S s_post h_callee
    exact h_callee.stack_clean

/- REF: docs/TARGETS/LINUX.md#12-system-call-abis-across-architectures -/
/-- Linux x86-64 System Call ABI descriptor. -/
structure LinuxSyscallABI where
  syscallNumberReg : Reg64 := .rax
  argRegisters     : List Reg64 := [.rdi, .rsi, .rdx, .r10, .r8, .r9]
  returnRegister   : Reg64 := .rax
  clobberedRegs    : List Reg64 := [.rcx, .r11]

/- REF: docs/TARGETS/LINUX.md#12-system-call-abis-across-architectures -/
/-- Standard Linux x86-64 syscall ABI instance. -/
def standardLinuxSyscallABI : LinuxSyscallABI := {}

end Gasm.Targets.Linux
