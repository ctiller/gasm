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
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base

namespace Gasm.Targets.X86_64.Instructions

open Gasm.Core
open Gasm.Targets.X86_64

/- REF: intel-sdm#vol=2;instr=SYSCALL;part=description -/
/-- Simulated kernel syscall entry point VMA (IA32_LSTAR model). -/
def linuxSyscallEntry : Address := 0x80000000

/- REF: intel-sdm#vol=2;instr=SYSCALL;part=description -/
/-- SYSCALL instruction: fast system call transition to privilege level 0. -/
structure SyscallOp where
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SYSCALL;part=operation -/
instance : X86_64Instruction SyscallOp where
  encode _ := ByteArray.mk #[0x0F, 0x05]

  step _ s :=
    let nextRip := s.rip + 2
    { (s.setGpr64 .rcx nextRip).setGpr64 .r11 s.flags with rip := linuxSyscallEntry }

  toUops _ := [
    { mnemonic := "SYSCALL.trap", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 20, reciprocalThroughput := 20.0 }
  ]
  toNASM _ := "syscall"
  toLean _ := "syscall_op"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "SYSCALL invokes an OS-defined kernel-mode transition; the harness has no syscall-trapping or sandboxing support -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := [SyscallOp.mk]

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- SYSCALL helper. -/
def syscall_op : AnyX86_64Instruction :=
  ⟨SyscallOp.mk⟩

end Gasm.Targets.X86_64.Instructions
