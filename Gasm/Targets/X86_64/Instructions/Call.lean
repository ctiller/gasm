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

/- REF: intel-sdm#vol=2;instr=CALL;part=description -/
/-- CALL [RIP + disp32] instruction: indirect near call through memory displacement. -/
structure CallRipRel where
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CALL;part=operation -/
instance : X86_64Instruction CallRipRel where
  encode i :=
    ByteArray.mk #[0xFF, 0x15] ++ int32ToLittleEndian i.disp

  step i s :=
    let nextRip := s.rip + 6
    let targetIat := nextRip + signExtend32To64 i.disp
    let targetFunc := s.read64 targetIat
    { (s.push64 nextRip) with rip := targetFunc }

  toUops _ := [
    { mnemonic := "CALL.loadTarget", uopClass := .load, eligiblePorts := [.p2, .p3], latencyCycles := 4, reciprocalThroughput := 0.5 },
    { mnemonic := "CALL.storeAddr", uopClass := .storeAddr, eligiblePorts := [.p2, .p3, .p7, .p8], latencyCycles := 1, reciprocalThroughput := 0.5 },
    { mnemonic := "CALL.storeData", uopClass := .storeData, eligiblePorts := [.p4, .p9], latencyCycles := 1, reciprocalThroughput := 0.5 },
    { mnemonic := "CALL.branch", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM i := s!"call [rel $+6 {formatDisp32 i.disp}]"
  toLean i := s!"call_rip ({i.disp})"
  canFuzzHardware _ := false
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedInt32Cases.map CallRipRel.mk

/- REF: intel-sdm#vol=2;instr=CALL;part=description -/
/-- CALL rel32 instruction: direct near relative call. -/
structure CallRel32 where
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CALL;part=operation -/
instance : X86_64Instruction CallRel32 where
  encode i :=
    ByteArray.mk #[0xE8] ++ int32ToLittleEndian i.disp

  step i s :=
    let nextRip := s.rip + 5
    let target := nextRip + signExtend32To64 i.disp
    { (s.push64 nextRip) with rip := target }

  toUops _ := [
    { mnemonic := "CALL.storeAddr", uopClass := .storeAddr, eligiblePorts := [.p2, .p3, .p7, .p8], latencyCycles := 1, reciprocalThroughput := 0.5 },
    { mnemonic := "CALL.storeData", uopClass := .storeData, eligiblePorts := [.p4, .p9], latencyCycles := 1, reciprocalThroughput := 0.5 },
    { mnemonic := "CALL.branch", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM i := s!"call {formatDisp32 i.disp}"
  toLean i := s!"call_rel32 ({i.disp})"
  canFuzzHardware _ := false
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedInt32Cases.map CallRel32.mk

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CALL [RIP + disp32] helper. -/
def call_rip (disp : Int32) : AnyX86_64Instruction :=
  ⟨CallRipRel.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CALL rel32 helper. -/
def call_rel32 (disp : Int32) : AnyX86_64Instruction :=
  ⟨CallRel32.mk disp⟩

end Gasm.Targets.X86_64.Instructions
