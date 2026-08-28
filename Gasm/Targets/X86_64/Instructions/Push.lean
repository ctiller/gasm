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

/- REF: intel-sdm#vol=2;instr=PUSH;part=description -/
/-- PUSH r64: Pushes a 64-bit general-purpose register onto the stack. -/
structure PushR64 where
  reg : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=PUSH;part=operation -/
instance : X86_64Instruction PushR64 where
  encode i :=
    let (code, ext) := reg64Code i.reg
    let opcode := 0x50 + code
    if ext then
      ByteArray.mk #[0x41, opcode]
    else
      ByteArray.mk #[opcode]

  step i s :=
    let (_, ext) := reg64Code i.reg
    let len := if ext then 2 else 1
    let val := s.gprs i.reg
    let s' := s.push64 val
    { s' with rip := s.rip + len }

  toUops _ := [
    { mnemonic := "PUSH.storeAddr", uopClass := .storeAddr, eligiblePorts := [.p2, .p3, .p7, .p8], latencyCycles := 1, reciprocalThroughput := 0.5 },
    { mnemonic := "PUSH.storeData", uopClass := .storeData, eligiblePorts := [.p4, .p9], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM i := s!"push {i.reg}"
  toLean i := s!"push_r64 .{i.reg}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "PUSH modifies RSP directly; HardwareHarness's VEH-based fault recovery and result capture rely on RSP staying harness-controlled (see hwSafeReg64's own doc comment) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := allReg64List.map PushR64.mk
  memAccesses _ := [⟨.store, .w64, ⟨some .rsp, none, -8⟩⟩]

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- PUSH r64 helper. -/
def push_r64 (r : Reg64) : AnyX86_64Instruction :=
  ⟨PushR64.mk r⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the PUSH family: `0x50 .. 0x57` (PUSH r64). Errors for any other byte
    pattern. -/
def pushTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (_, _, _, _, rexB, opcode, pos) =>
    if opcode >= 0x50 && opcode <= 0x57 then
      let r := codeToReg64 (opcode - 0x50) rexB
      .ok (push_r64 r, pos - offset)
    else
      .error s!"pushTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not PUSH"

end Gasm.Targets.X86_64.Instructions
