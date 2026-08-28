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

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=description -/
/-- CMOVE / CMOVZ r64, r64: Conditional move if zero / equal (ZF = 1). -/
structure CmoveR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=operation -/
instance : X86_64Instruction CmoveR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true dstExt false srcExt, 0x0F, 0x44, makeModRM 3 dstCode srcCode]

  step i s :=
    let s' := if s.zf then s.setGpr64 i.dst (s.gprs i.src) else s
    { s' with rip := s.rip + 4 }

  toUops _ := [{ mnemonic := "CMOVE.alu", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"cmove {i.dst}, {i.src}"
  toLean i := s!"cmove_r64 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (CmoveR64R64.mk · .rax)) ++ (allReg64List.map (CmoveR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => CmoveR64R64.mk p.1 p.2)

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=description -/
/-- CMOVNE / CMOVNZ r64, r64: Conditional move if not zero / not equal (ZF = 0). -/
structure CmovneR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=operation -/
instance : X86_64Instruction CmovneR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true dstExt false srcExt, 0x0F, 0x45, makeModRM 3 dstCode srcCode]

  step i s :=
    let s' := if !s.zf then s.setGpr64 i.dst (s.gprs i.src) else s
    { s' with rip := s.rip + 4 }

  toUops _ := [{ mnemonic := "CMOVNE.alu", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"cmovne {i.dst}, {i.src}"
  toLean i := s!"cmovne_r64 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (CmovneR64R64.mk · .rax)) ++ (allReg64List.map (CmovneR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => CmovneR64R64.mk p.1 p.2)

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=description -/
/-- CMOVL / CMOVNGE r64, r64: Conditional move if less (SF != OF). -/
structure CmovlR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=operation -/
instance : X86_64Instruction CmovlR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true dstExt false srcExt, 0x0F, 0x4C, makeModRM 3 dstCode srcCode]

  step i s :=
    let s' := if s.sf != s.of_ then s.setGpr64 i.dst (s.gprs i.src) else s
    { s' with rip := s.rip + 4 }

  toUops _ := [{ mnemonic := "CMOVL.alu", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"cmovl {i.dst}, {i.src}"
  toLean i := s!"cmovl_r64 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (CmovlR64R64.mk · .rax)) ++ (allReg64List.map (CmovlR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => CmovlR64R64.mk p.1 p.2)

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=description -/
/-- CMOVLE / CMOVNG r64, r64: Conditional move if less or equal (ZF = 1 or SF != OF). -/
structure CmovleR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=operation -/
instance : X86_64Instruction CmovleR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true dstExt false srcExt, 0x0F, 0x4E, makeModRM 3 dstCode srcCode]

  step i s :=
    let s' := if s.zf || s.sf != s.of_ then s.setGpr64 i.dst (s.gprs i.src) else s
    { s' with rip := s.rip + 4 }

  toUops _ := [{ mnemonic := "CMOVLE.alu", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"cmovle {i.dst}, {i.src}"
  toLean i := s!"cmovle_r64 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (CmovleR64R64.mk · .rax)) ++ (allReg64List.map (CmovleR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => CmovleR64R64.mk p.1 p.2)

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=description -/
/-- CMOVG / CMOVNLE r64, r64: Conditional move if greater (ZF = 0 and SF = OF). -/
structure CmovgR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=operation -/
instance : X86_64Instruction CmovgR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true dstExt false srcExt, 0x0F, 0x4F, makeModRM 3 dstCode srcCode]

  step i s :=
    let s' := if !s.zf && s.sf == s.of_ then s.setGpr64 i.dst (s.gprs i.src) else s
    { s' with rip := s.rip + 4 }

  toUops _ := [{ mnemonic := "CMOVG.alu", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"cmovg {i.dst}, {i.src}"
  toLean i := s!"cmovg_r64 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (CmovgR64R64.mk · .rax)) ++ (allReg64List.map (CmovgR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => CmovgR64R64.mk p.1 p.2)

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=description -/
/-- CMOVGE / CMOVNL r64, r64: Conditional move if greater or equal (SF = OF). -/
structure CmovgeR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=operation -/
instance : X86_64Instruction CmovgeR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true dstExt false srcExt, 0x0F, 0x4D, makeModRM 3 dstCode srcCode]

  step i s :=
    let s' := if s.sf == s.of_ then s.setGpr64 i.dst (s.gprs i.src) else s
    { s' with rip := s.rip + 4 }

  toUops _ := [{ mnemonic := "CMOVGE.alu", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"cmovge {i.dst}, {i.src}"
  toLean i := s!"cmovge_r64 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (CmovgeR64R64.mk · .rax)) ++ (allReg64List.map (CmovgeR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => CmovgeR64R64.mk p.1 p.2)

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=description -/
/-- CMOVB / CMOVC r64, r64: Conditional move if below / carry (CF = 1). -/
structure CmovbR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=operation -/
instance : X86_64Instruction CmovbR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true dstExt false srcExt, 0x0F, 0x42, makeModRM 3 dstCode srcCode]

  step i s :=
    let s' := if s.cf then s.setGpr64 i.dst (s.gprs i.src) else s
    { s' with rip := s.rip + 4 }

  toUops _ := [{ mnemonic := "CMOVB.alu", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"cmovb {i.dst}, {i.src}"
  toLean i := s!"cmovb_r64 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (CmovbR64R64.mk · .rax)) ++ (allReg64List.map (CmovbR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => CmovbR64R64.mk p.1 p.2)

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=description -/
/-- CMOVAE / CMOVNC r64, r64: Conditional move if above or equal / not carry (CF = 0). -/
structure CmovaeR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMOVcc;part=operation -/
instance : X86_64Instruction CmovaeR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true dstExt false srcExt, 0x0F, 0x43, makeModRM 3 dstCode srcCode]

  step i s :=
    let s' := if !s.cf then s.setGpr64 i.dst (s.gprs i.src) else s
    { s' with rip := s.rip + 4 }

  toUops _ := [{ mnemonic := "CMOVAE.alu", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"cmovae {i.dst}, {i.src}"
  toLean i := s!"cmovae_r64 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (CmovaeR64R64.mk · .rax)) ++ (allReg64List.map (CmovaeR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => CmovaeR64R64.mk p.1 p.2)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CMOVE r64, r64 helper. -/
def cmove_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨CmoveR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CMOVNE r64, r64 helper. -/
def cmovne_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨CmovneR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CMOVL r64, r64 helper. -/
def cmovl_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨CmovlR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CMOVLE r64, r64 helper. -/
def cmovle_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨CmovleR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CMOVG r64, r64 helper. -/
def cmovg_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨CmovgR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CMOVGE r64, r64 helper. -/
def cmovge_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨CmovgeR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CMOVB r64, r64 helper. -/
def cmovb_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨CmovbR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CMOVAE r64, r64 helper. -/
def cmovae_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨CmovaeR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the CMOV family: `0x0F 0x42/0x43/0x44/0x45/0x4C/0x4D/0x4E/0x4F`
    (CMOVB/CMOVAE/CMOVE/CMOVNE/CMOVL/CMOVGE/CMOVLE/CMOVG r64, r64). Errors for any other byte
    pattern. -/
def cmovTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  -- NOTE: nested `match`, not `do` — see `addTryDecode`'s comment for why.
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (_, _, rexR, _, rexB, opcode, opOffset) =>
    if opcode == 0x0F then
      match readUInt8 bytes opOffset with
      | .error e => .error e
      | .ok op2 =>
        if op2 == 0x42 || op2 == 0x43 || op2 == 0x44 || op2 == 0x45 ||
           op2 == 0x4C || op2 == 0x4D || op2 == 0x4E || op2 == 0x4F then
          match readModRM bytes (opOffset + 1) with
          | .error e => .error e
          | .ok (_, reg, rm, pos) =>
            let dst := codeToReg64 reg rexR
            let src := codeToReg64 rm rexB
            let len := pos - offset
            if op2 == 0x42 then .ok (cmovb_r64 dst src, len)
            else if op2 == 0x43 then .ok (cmovae_r64 dst src, len)
            else if op2 == 0x44 then .ok (cmove_r64 dst src, len)
            else if op2 == 0x45 then .ok (cmovne_r64 dst src, len)
            else if op2 == 0x4C then .ok (cmovl_r64 dst src, len)
            else if op2 == 0x4D then .ok (cmovge_r64 dst src, len)
            else if op2 == 0x4E then .ok (cmovle_r64 dst src, len)
            else .ok (cmovg_r64 dst src, len)
        else
          .error "cmovTryDecode: 0x0F sub-opcode is not CMOV"
    else
      .error s!"cmovTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not CMOV"

end Gasm.Targets.X86_64.Instructions
