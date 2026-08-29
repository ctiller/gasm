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

/- REF: intel-sdm#vol=2;instr=JMP;part=description -/
/-- JMP rel8: Unconditional direct relative short jump. -/
structure JmpRel8 where
  disp : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=JMP;part=operation -/
instance : X86_64Instruction JmpRel8 where
  encode i := ByteArray.mk #[0xEB, i.disp]
  step i s :=
    let target := s.rip + 2 + signExtend8To64 i.disp
    { s with rip := target }
  toUops _ := [{ mnemonic := "JMP.rel8", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"jmp short $+2 {formatDisp8 i.disp}"
  toLean i := s!"jmp_rel8 {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedUInt8Cases.map JmpRel8.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=JMP;part=description -/
/-- JMP rel32: Unconditional direct relative near jump. -/
structure JmpRel32 where
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=JMP;part=operation -/
instance : X86_64Instruction JmpRel32 where
  encode i := ByteArray.mk #[0xE9] ++ int32ToLittleEndian i.disp
  step i s :=
    let target := s.rip + 5 + signExtend32To64 i.disp
    { s with rip := target }
  toUops _ := [{ mnemonic := "JMP.rel32", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"jmp near $+5 {formatDisp32 i.disp}"
  toLean i := s!"jmp_rel32 ({i.disp})"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedInt32Cases.map JmpRel32.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JE / JZ rel8: Jump short if equal / zero (ZF = 1). -/
structure JeRel8 where
  disp : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JeRel8 where
  encode i := ByteArray.mk #[0x74, i.disp]
  step i s :=
    let nextRip := s.rip + 2
    let target := if s.zf then nextRip + signExtend8To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JE.rel8", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"je short $+2 {formatDisp8 i.disp}"
  toLean i := s!"je_rel8 {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedUInt8Cases.map JeRel8.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JE / JZ rel32: Jump near if equal / zero (ZF = 1). -/
structure JeRel32 where
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JeRel32 where
  encode i := ByteArray.mk #[0x0F, 0x84] ++ int32ToLittleEndian i.disp
  step i s :=
    let nextRip := s.rip + 6
    let target := if s.zf then nextRip + signExtend32To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JE.rel32", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"je near $+6 {formatDisp32 i.disp}"
  toLean i := s!"je_rel32 ({i.disp})"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedInt32Cases.map JeRel32.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JNE / JNZ rel8: Jump short if not equal / not zero (ZF = 0). -/
structure JneRel8 where
  disp : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JneRel8 where
  encode i := ByteArray.mk #[0x75, i.disp]
  step i s :=
    let nextRip := s.rip + 2
    let target := if !s.zf then nextRip + signExtend8To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JNE.rel8", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"jne short $+2 {formatDisp8 i.disp}"
  toLean i := s!"jne_rel8 {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedUInt8Cases.map JneRel8.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JNE / JNZ rel32: Jump near if not equal / not zero (ZF = 0). -/
structure JneRel32 where
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JneRel32 where
  encode i := ByteArray.mk #[0x0F, 0x85] ++ int32ToLittleEndian i.disp
  step i s :=
    let nextRip := s.rip + 6
    let target := if !s.zf then nextRip + signExtend32To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JNE.rel32", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"jne near $+6 {formatDisp32 i.disp}"
  toLean i := s!"jne_rel32 ({i.disp})"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedInt32Cases.map JneRel32.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JL / JNGE rel8: Jump short if less / not greater or equal (SF != OF). -/
structure JlRel8 where
  disp : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JlRel8 where
  encode i := ByteArray.mk #[0x7C, i.disp]
  step i s :=
    let nextRip := s.rip + 2
    let target := if s.sf != s.of_ then nextRip + signExtend8To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JL.rel8", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"jl short $+2 {formatDisp8 i.disp}"
  toLean i := s!"jl_rel8 {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedUInt8Cases.map JlRel8.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JLE / JNG rel8: Jump short if less or equal / not greater (ZF = 1 or SF != OF). -/
structure JleRel8 where
  disp : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JleRel8 where
  encode i := ByteArray.mk #[0x7E, i.disp]
  step i s :=
    let nextRip := s.rip + 2
    let target := if s.zf || (s.sf != s.of_) then nextRip + signExtend8To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JLE.rel8", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"jle short $+2 {formatDisp8 i.disp}"
  toLean i := s!"jle_rel8 {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedUInt8Cases.map JleRel8.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JG / JNLE rel8: Jump short if greater / not less or equal (ZF = 0 and SF = OF). -/
structure JgRel8 where
  disp : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JgRel8 where
  encode i := ByteArray.mk #[0x7F, i.disp]
  step i s :=
    let nextRip := s.rip + 2
    let target := if !s.zf && (s.sf == s.of_) then nextRip + signExtend8To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JG.rel8", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"jg short $+2 {formatDisp8 i.disp}"
  toLean i := s!"jg_rel8 {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedUInt8Cases.map JgRel8.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JGE / JNL rel8: Jump short if greater or equal / not less (SF = OF). -/
structure JgeRel8 where
  disp : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JgeRel8 where
  encode i := ByteArray.mk #[0x7D, i.disp]
  step i s :=
    let nextRip := s.rip + 2
    let target := if s.sf == s.of_ then nextRip + signExtend8To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JGE.rel8", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"jge short $+2 {formatDisp8 i.disp}"
  toLean i := s!"jge_rel8 {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedUInt8Cases.map JgeRel8.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JGE / JNL rel32: Jump near if greater or equal (SF = OF). -/
structure JgeRel32 where
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JgeRel32 where
  encode i := ByteArray.mk #[0x0F, 0x8D] ++ int32ToLittleEndian i.disp
  step i s :=
    let nextRip := s.rip + 6
    let target := if s.sf == s.of_ then nextRip + signExtend32To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JGE.rel32", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"jge near $+6 {formatDisp32 i.disp}"
  toLean i := s!"jge_rel32 ({i.disp})"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedInt32Cases.map JgeRel32.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JB / JNAE / JC rel8: Jump short if below / not above or equal / carry (CF = 1). -/
structure JbRel8 where
  disp : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JbRel8 where
  encode i := ByteArray.mk #[0x72, i.disp]
  step i s :=
    let nextRip := s.rip + 2
    let target := if s.cf then nextRip + signExtend8To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JB.rel8", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"jb short $+2 {formatDisp8 i.disp}"
  toLean i := s!"jb_rel8 {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedUInt8Cases.map JbRel8.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JAE / JNB / JNC rel8: Jump short if above or equal / not below / not carry (CF = 0). -/
structure JaeRel8 where
  disp : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JaeRel8 where
  encode i := ByteArray.mk #[0x73, i.disp]
  step i s :=
    let nextRip := s.rip + 2
    let target := if !s.cf then nextRip + signExtend8To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JAE.rel8", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"jae short $+2 {formatDisp8 i.disp}"
  toLean i := s!"jae_rel8 {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedUInt8Cases.map JaeRel8.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JAE / JNB / JNC rel32: Jump near if above or equal / not below / not carry (CF = 0). -/
structure JaeRel32 where
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JaeRel32 where
  encode i := ByteArray.mk #[0x0F, 0x83] ++ int32ToLittleEndian i.disp
  step i s :=
    let nextRip := s.rip + 6
    let target := if !s.cf then nextRip + signExtend32To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JAE.rel32", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"jae near $+6 {formatDisp32 i.disp}"
  toLean i := s!"jae_rel32 ({i.disp})"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedInt32Cases.map JaeRel32.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JA / JNBE rel8: Jump short if above / not below or equal (CF = 0 and ZF = 0). -/
structure JaRel8 where
  disp : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JaRel8 where
  encode i := ByteArray.mk #[0x77, i.disp]
  step i s :=
    let nextRip := s.rip + 2
    let target := if !s.cf && !s.zf then nextRip + signExtend8To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JA.rel8", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"ja short $+2 {formatDisp8 i.disp}"
  toLean i := s!"ja_rel8 {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedUInt8Cases.map JaRel8.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JBE / JNA rel8: Jump short if below or equal / not above (CF = 1 or ZF = 1). -/
structure JbeRel8 where
  disp : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JbeRel8 where
  encode i := ByteArray.mk #[0x76, i.disp]
  step i s :=
    let nextRip := s.rip + 2
    let target := if s.cf || s.zf then nextRip + signExtend8To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JBE.rel8", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"jbe short $+2 {formatDisp8 i.disp}"
  toLean i := s!"jbe_rel8 {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedUInt8Cases.map JbeRel8.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JLE / JNG rel32: Jump near if less or equal (ZF = 1 or SF != OF). -/
structure JleRel32 where
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JleRel32 where
  encode i := ByteArray.mk #[0x0F, 0x8E] ++ int32ToLittleEndian i.disp
  step i s :=
    let nextRip := s.rip + 6
    let target := if s.zf || (s.sf != s.of_) then nextRip + signExtend32To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JLE.rel32", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"jle near $+6 {formatDisp32 i.disp}"
  toLean i := s!"jle_rel32 ({i.disp})"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedInt32Cases.map JleRel32.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JB / JC rel32: Jump near if below / carry (CF = 1). -/
structure JbRel32 where
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JbRel32 where
  encode i := ByteArray.mk #[0x0F, 0x82] ++ int32ToLittleEndian i.disp
  step i s :=
    let nextRip := s.rip + 6
    let target := if s.cf then nextRip + signExtend32To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JB.rel32", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"jb near $+6 {formatDisp32 i.disp}"
  toLean i := s!"jb_rel32 ({i.disp})"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedInt32Cases.map JbRel32.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=Jcc;part=description -/
/-- JA / JNBE rel32: Jump near if above (CF = 0 and ZF = 0). -/
structure JaRel32 where
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
instance : X86_64Instruction JaRel32 where
  encode i := ByteArray.mk #[0x0F, 0x87] ++ int32ToLittleEndian i.disp
  step i s :=
    let nextRip := s.rip + 6
    let target := if !s.cf && !s.zf then nextRip + signExtend32To64 i.disp else nextRip
    { s with rip := target }
  toUops _ := [{ mnemonic := "JA.rel32", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"ja near $+6 {formatDisp32 i.disp}"
  toLean i := s!"ja_rel32 ({i.disp})"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "Jcc/JMP transfers control (RIP); HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedInt32Cases.map JaRel32.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JMP rel8 helper. -/
def jmp_rel8 (disp : UInt8) : AnyX86_64Instruction := ⟨JmpRel8.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JMP rel32 helper. -/
def jmp_rel32 (disp : Int32) : AnyX86_64Instruction := ⟨JmpRel32.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JE rel8 helper. -/
def je_rel8 (disp : UInt8) : AnyX86_64Instruction := ⟨JeRel8.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JE rel32 helper. -/
def je_rel32 (disp : Int32) : AnyX86_64Instruction := ⟨JeRel32.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JNE rel8 helper. -/
def jne_rel8 (disp : UInt8) : AnyX86_64Instruction := ⟨JneRel8.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JNE rel32 helper. -/
def jne_rel32 (disp : Int32) : AnyX86_64Instruction := ⟨JneRel32.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JL rel8 helper. -/
def jl_rel8 (disp : UInt8) : AnyX86_64Instruction := ⟨JlRel8.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JLE rel8 helper. -/
def jle_rel8 (disp : UInt8) : AnyX86_64Instruction := ⟨JleRel8.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JLE rel32 helper. -/
def jle_rel32 (disp : Int32) : AnyX86_64Instruction := ⟨JleRel32.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JG rel8 helper. -/
def jg_rel8 (disp : UInt8) : AnyX86_64Instruction := ⟨JgRel8.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JGE rel8 helper. -/
def jge_rel8 (disp : UInt8) : AnyX86_64Instruction := ⟨JgeRel8.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JGE rel32 helper. -/
def jge_rel32 (disp : Int32) : AnyX86_64Instruction := ⟨JgeRel32.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JB rel8 helper. -/
def jb_rel8 (disp : UInt8) : AnyX86_64Instruction := ⟨JbRel8.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JB rel32 helper. -/
def jb_rel32 (disp : Int32) : AnyX86_64Instruction := ⟨JbRel32.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JAE rel8 helper. -/
def jae_rel8 (disp : UInt8) : AnyX86_64Instruction := ⟨JaeRel8.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JAE rel32 helper. -/
def jae_rel32 (disp : Int32) : AnyX86_64Instruction := ⟨JaeRel32.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JA rel8 helper. -/
def ja_rel8 (disp : UInt8) : AnyX86_64Instruction := ⟨JaRel8.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JA rel32 helper. -/
def ja_rel32 (disp : Int32) : AnyX86_64Instruction := ⟨JaRel32.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- JBE rel8 helper. -/
def jbe_rel8 (disp : UInt8) : AnyX86_64Instruction := ⟨JbeRel8.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the JMP/Jcc family: `0xEB`/`0xE9` (unconditional JMP rel8/rel32), the
    short conditional jumps (`0x72..0x77`, `0x7C..0x7F`), and the near conditional jumps reachable
    through the `0x0F` two-byte escape (`0x82..0x8E`, only the subset this codebase's encoders
    emit). Errors for any other byte pattern. -/
def jccTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  -- NOTE: nested `match` (not `do`, see `addTryDecode`'s comment) via two small local closures
  -- (`rel8`/`rel32At`) that read a displacement and apply the given constructor, since almost
  -- every branch of this family has that exact shape.
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (_, _, _, _, _, opcode, opOffset) =>
    let rel8 (mk : UInt8 → AnyX86_64Instruction) : Except String (AnyX86_64Instruction × Nat) :=
      match readUInt8 bytes opOffset with
      | .error e => .error e
      | .ok disp8 => .ok (mk disp8, (opOffset + 1) - offset)
    let rel32At (pos : Nat) (mk : Int32 → AnyX86_64Instruction) :
        Except String (AnyX86_64Instruction × Nat) :=
      match readInt32LE bytes pos with
      | .error e => .error e
      | .ok disp32 => .ok (mk disp32, (pos + 4) - offset)
    if opcode == 0xEB then rel8 jmp_rel8
    else if opcode == 0xE9 then rel32At opOffset jmp_rel32
    else if opcode == 0x72 then rel8 jb_rel8
    else if opcode == 0x73 then rel8 jae_rel8
    else if opcode == 0x74 then rel8 je_rel8
    else if opcode == 0x75 then rel8 jne_rel8
    else if opcode == 0x7C then rel8 jl_rel8
    else if opcode == 0x7D then rel8 jge_rel8
    else if opcode == 0x7E then rel8 jle_rel8
    else if opcode == 0x7F then rel8 jg_rel8
    else if opcode == 0x76 then rel8 jbe_rel8
    else if opcode == 0x77 then rel8 ja_rel8
    else if opcode == 0x0F then
      match readUInt8 bytes opOffset with
      | .error e => .error e
      | .ok op2 =>
        let modPos := opOffset + 1
        if op2 == 0x82 then rel32At modPos jb_rel32
        else if op2 == 0x83 then rel32At modPos jae_rel32
        else if op2 == 0x84 then rel32At modPos je_rel32
        else if op2 == 0x85 then rel32At modPos jne_rel32
        else if op2 == 0x87 then rel32At modPos ja_rel32
        else if op2 == 0x8D then rel32At modPos jge_rel32
        else if op2 == 0x8E then rel32At modPos jle_rel32
        else .error "jccTryDecode: 0x0F sub-opcode is not a near Jcc this codebase emits"
    else
      .error s!"jccTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not JMP/Jcc"

end Gasm.Targets.X86_64.Instructions
