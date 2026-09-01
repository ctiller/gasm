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
import Gasm.Targets.X86_64.MemCostModel

namespace Gasm.Targets.X86_64.Instructions

open Gasm.Core
open Gasm.Targets.X86_64

/- REF: intel-sdm#vol=2;instr=POP;part=description -/
/-- POP r64: Pops a 64-bit general-purpose register from the stack. -/
structure PopR64 where
  reg : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- `PopR64`'s declared memory access, hoisted to a top-level `def` and shared by both
    `memAccesses` and `toUops` below (via `memUops`) -- see `Mov.lean`'s
    `movRspDispByteAccesses` doc comment for why. -/
@[simp] def popR64Accesses (_ : PopR64) : List MemAccessSpec :=
  [⟨.load, .w64, ⟨some .rsp, none, 0⟩⟩]

/- REF: intel-sdm#vol=2;instr=POP;part=operation -/
instance : X86_64Instruction PopR64 where
  encode i :=
    let (code, ext) := reg64Code i.reg
    let opcode := 0x58 + code
    if ext then
      ByteArray.mk #[0x41, opcode]
    else
      ByteArray.mk #[opcode]

  step i s :=
    let (_, ext) := reg64Code i.reg
    let len := if ext then 2 else 1
    let (val, s') := s.pop64
    let s'' := s'.setGpr64 i.reg val
    { s'' with rip := s.rip + len }

  toUops i := derivedMemUops (popR64Accesses i) defaultMemCostModel
  toNASM i := s!"pop {i.reg}"
  toLean i := s!"pop_r64 .{i.reg}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "POP modifies RSP directly; HardwareHarness's VEH-based fault recovery and result capture rely on RSP staying harness-controlled (see hwSafeReg64's own doc comment) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := allReg64List.map PopR64.mk
  memAccesses := popR64Accesses

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- POP r64 helper. -/
def pop_r64 (r : Reg64) : AnyX86_64Instruction :=
  ⟨PopR64.mk r⟩

private def popRule (regCode : UInt8) : DecodeRule := {
  opcode := .one (0x58 + regCode),
  builder := fun ctx =>
    let r := codeToReg64 regCode ctx.rexB
    .ok (pop_r64 r, ctx.opcodePos - ctx.startOffset)
}

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Declarative decoding rules for the POP family: `0x58 .. 0x5F` (POP r64). -/
def popDecodeRules : List DecodeRule := [
  popRule 0, popRule 1, popRule 2, popRule 3,
  popRule 4, popRule 5, popRule 6, popRule 7
]

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the POP family, evaluating its declarative rules. -/
def popTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  tryDecodeWithRules popDecodeRules bytes offset

end Gasm.Targets.X86_64.Instructions
