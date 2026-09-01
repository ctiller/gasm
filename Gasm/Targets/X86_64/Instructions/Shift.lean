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

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
/-- Fuzz state generator for r64, cl shift variants: varies the CL count across the documented
    undefined-flag boundaries (0, 1, 2, 3, and the mid/high end of the masked 0..63 range)
    crossed with curated destination values and flag seeds, since the CL count is only known
    at runtime (unlike imm8, `generateStandardFuzzStatesForImm` alone would leave RCX pinned
    at zero and never exercise the AF/OF-undefined counts this instance's mask covers). -/
def generateShiftClFuzzStates (dst : Reg64) (rng : FuzzerRng) (randCount : Nat := 8) : List X86_64MachineState × FuzzerRng := Id.run do
  let mut states : List X86_64MachineState := []
  let counts : List UInt64 := [0, 1, 2, 3, 31, 32, 63]
  for count in counts do
    for v in curated64BitValues.take 6 do
      for flg in curatedFlagValues.take 3 do
        let s : X86_64MachineState := default
        let s := s.setGpr64 dst v
        let s := if dst = Reg64.rcx then s else s.setGpr64 .rcx count
        let s := { s with flags := flg }
        states := states ++ [s]
  let mut curRng := rng
  for _ in [0:randCount] do
    let (s, nextRng) := generateRandomMachineState curRng
    states := states ++ [s]
    curRng := nextRng
  (states, curRng)

-- ============================================================================
-- 64-BIT SHIFT INSTRUCTIONS
-- ============================================================================

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHL r64, imm8: Shifts bits in destination 64-bit register to the left by count (masked to 6 bits 0..63), filling shifted-in bits with zeros. -/
structure ShlR64Imm8 where
  dst : Reg64
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShlR64Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0xC1, makeModRM 3 4 dstCode, i.imm]
  step i s :=
    let dVal := s.gprs i.dst
    let count := (i.imm &&& 0x3F).toUInt64
    let res := dVal <<< count
    let cfBit := if count > 0 && count <= 64 then (dVal >>> (64 - count)) &&& 1 else 0
    let ofBit := if count == 1 then ((res >>> 63) ^^^ cfBit) else 0
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsShift64 res cfBit ofBit (i.imm &&& 0x3F)
    { s'' with rip := s.rip + 4 }
  toUops _ := [{ mnemonic := "SHL.alu", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shl {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"shl_r64_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask i := (if (i.imm &&& 0x3F) == 0 then 0 else 16 ||| (if (i.imm &&& 0x3F) == 1 then 0 else 2048))
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (ShlR64Imm8.mk · 1)) ++ ([(0 : UInt8), 1, 7, 31, 63].map (ShlR64Imm8.mk .rax ·)) ++
    ([(0 : UInt8), 1, 7, 31, 63].map (ShlR64Imm8.mk .r15 ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHL r64, 1: Shifts bits in destination 64-bit register to the left by 1. -/
structure ShlR64One where
  dst : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShlR64One where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0xD1, makeModRM 3 4 dstCode]
  step i s :=
    let dVal := s.gprs i.dst
    let count := (1 : UInt64)
    let res := dVal <<< count
    let cfBit := (dVal >>> 63) &&& 1
    let ofBit := (res >>> 63) ^^^ cfBit
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsShift64 res cfBit ofBit 1
    { s'' with rip := s.rip + 3 }
  toUops _ := [{ mnemonic := "SHL.alu", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shl {i.dst}, 1"
  toLean i := s!"shl_r64_one .{i.dst}"
  undefinedFlagsMask _ := 16
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases := allReg64List.map ShlR64One.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHL r64, cl: Shifts bits in destination 64-bit register to the left by count in CL (masked to 6 bits 0..63). -/
structure ShlR64Cl where
  dst : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShlR64Cl where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0xD3, makeModRM 3 4 dstCode]
  step i s :=
    let dVal := s.gprs i.dst
    let count := s.gprs .rcx &&& 0x3F
    let res := dVal <<< count
    let cfBit := if count > 0 && count <= 64 then (dVal >>> (64 - count)) &&& 1 else 0
    let ofBit := if count == 1 then ((res >>> 63) ^^^ cfBit) else 0
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsShift64 res cfBit ofBit (s.gprs .rcx &&& 0x3F).toUInt8
    { s'' with rip := s.rip + 3 }
  toUops _ := [{ mnemonic := "SHL.cl", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shl {i.dst}, cl"
  toLean i := s!"shl_r64_cl .{i.dst}"
  undefinedFlagsMask _ := 16 ||| 2048
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateShiftClFuzzStates i.dst rng
  roundtripCases := allReg64List.map ShlR64Cl.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHR r64, imm8: Shifts bits in destination 64-bit register to the right by count (masked to 6 bits 0..63), filling shifted-in bits with zeros. -/
structure ShrR64Imm8 where
  dst : Reg64
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShrR64Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0xC1, makeModRM 3 5 dstCode, i.imm]
  step i s :=
    let dVal := s.gprs i.dst
    let count := (i.imm &&& 0x3F).toUInt64
    let res := dVal >>> count
    let cfBit := if count > 0 && count <= 64 then (dVal >>> (count - 1)) &&& 1 else 0
    let ofBit := if count == 1 then (dVal >>> 63) &&& 1 else 0
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsShift64 res cfBit ofBit (i.imm &&& 0x3F)
    { s'' with rip := s.rip + 4 }
  toUops _ := [{ mnemonic := "SHR.alu", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shr {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"shr_r64_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask i := (if (i.imm &&& 0x3F) == 0 then 0 else 16 ||| (if (i.imm &&& 0x3F) == 1 then 0 else 2048))
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (ShrR64Imm8.mk · 1)) ++ ([(0 : UInt8), 1, 7, 31, 63].map (ShrR64Imm8.mk .rax ·)) ++
    ([(0 : UInt8), 1, 7, 31, 63].map (ShrR64Imm8.mk .r15 ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHR r64, 1: Shifts bits in destination 64-bit register to the right by 1. -/
structure ShrR64One where
  dst : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShrR64One where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0xD1, makeModRM 3 5 dstCode]
  step i s :=
    let dVal := s.gprs i.dst
    let count := (1 : UInt64)
    let res := dVal >>> count
    let cfBit := dVal &&& 1
    let ofBit := (dVal >>> 63) &&& 1
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsShift64 res cfBit ofBit 1
    { s'' with rip := s.rip + 3 }
  toUops _ := [{ mnemonic := "SHR.alu", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shr {i.dst}, 1"
  toLean i := s!"shr_r64_one .{i.dst}"
  undefinedFlagsMask _ := 16
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases := allReg64List.map ShrR64One.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHR r64, cl: Shifts bits in destination 64-bit register to the right by count in CL (masked to 6 bits 0..63). -/
structure ShrR64Cl where
  dst : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShrR64Cl where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0xD3, makeModRM 3 5 dstCode]
  step i s :=
    let dVal := s.gprs i.dst
    let count := s.gprs .rcx &&& 0x3F
    let res := dVal >>> count
    let cfBit := if count > 0 && count <= 64 then (dVal >>> (count - 1)) &&& 1 else 0
    let ofBit := if count == 1 then (dVal >>> 63) &&& 1 else 0
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsShift64 res cfBit ofBit (s.gprs .rcx &&& 0x3F).toUInt8
    { s'' with rip := s.rip + 3 }
  toUops _ := [{ mnemonic := "SHR.cl", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shr {i.dst}, cl"
  toLean i := s!"shr_r64_cl .{i.dst}"
  undefinedFlagsMask _ := 16 ||| 2048
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateShiftClFuzzStates i.dst rng
  roundtripCases := allReg64List.map ShrR64Cl.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SAR r64, imm8: Arithmetic right shift of destination 64-bit register by count (masked to 6 bits 0..63), preserving sign bit. -/
structure SarR64Imm8 where
  dst : Reg64
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction SarR64Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0xC1, makeModRM 3 7 dstCode, i.imm]
  step i s :=
    let dVal := s.gprs i.dst
    let count := (i.imm &&& 0x3F).toUInt64
    let signBit := (dVal >>> 63) == 1
    let signExtendMask := if signBit && count > 0 then ~~~(0xFFFFFFFFFFFFFFFF >>> count) else 0
    let res := (dVal >>> count) ||| signExtendMask
    let cfBit := if count > 0 && count <= 64 then (dVal >>> (count - 1)) &&& 1 else 0
    let ofBit := 0
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsShift64 res cfBit ofBit (i.imm &&& 0x3F)
    { s'' with rip := s.rip + 4 }
  toUops _ := [{ mnemonic := "SAR.alu", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"sar {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"sar_r64_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask i := (if (i.imm &&& 0x3F) == 0 then 0 else 16 ||| (if (i.imm &&& 0x3F) == 1 then 0 else 2048))
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (SarR64Imm8.mk · 1)) ++ ([(0 : UInt8), 1, 7, 31, 63].map (SarR64Imm8.mk .rax ·)) ++
    ([(0 : UInt8), 1, 7, 31, 63].map (SarR64Imm8.mk .r15 ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SAR r64, 1: Arithmetic right shift of destination 64-bit register by 1. -/
structure SarR64One where
  dst : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction SarR64One where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0xD1, makeModRM 3 7 dstCode]
  step i s :=
    let dVal := s.gprs i.dst
    let signBit := (dVal >>> 63) == 1
    let signExtendMask : UInt64 := if signBit then 0x8000000000000000 else 0
    let res := (dVal >>> 1) ||| signExtendMask
    let cfBit := dVal &&& 1
    let ofBit := 0
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsShift64 res cfBit ofBit 1
    { s'' with rip := s.rip + 3 }
  toUops _ := [{ mnemonic := "SAR.alu", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"sar {i.dst}, 1"
  toLean i := s!"sar_r64_one .{i.dst}"
  undefinedFlagsMask _ := 16
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases := allReg64List.map SarR64One.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SAR r64, cl: Arithmetic right shift of destination 64-bit register by count in CL (masked to 6 bits 0..63). -/
structure SarR64Cl where
  dst : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction SarR64Cl where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0xD3, makeModRM 3 7 dstCode]
  step i s :=
    let dVal := s.gprs i.dst
    let count := s.gprs .rcx &&& 0x3F
    let signBit := (dVal >>> 63) == 1
    let signExtendMask := if signBit && count > 0 then ~~~(0xFFFFFFFFFFFFFFFF >>> count) else 0
    let res := (dVal >>> count) ||| signExtendMask
    let cfBit := if count > 0 && count <= 64 then (dVal >>> (count - 1)) &&& 1 else 0
    let ofBit := 0
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsShift64 res cfBit ofBit (s.gprs .rcx &&& 0x3F).toUInt8
    { s'' with rip := s.rip + 3 }
  toUops _ := [{ mnemonic := "SAR.cl", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"sar {i.dst}, cl"
  toLean i := s!"sar_r64_cl .{i.dst}"
  undefinedFlagsMask _ := 16 ||| 2048
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateShiftClFuzzStates i.dst rng
  roundtripCases := allReg64List.map SarR64Cl.mk
  memAccesses _ := []

-- ============================================================================
-- 32-BIT SHIFT INSTRUCTIONS
-- ============================================================================

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHL r32, imm8: Shifts 32-bit register left by imm8 (masked to 5 bits 0..31), zero-extending destination to 64 bits. -/
structure ShlR32Imm8 where
  dst : Reg32
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShlR32Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xC1, makeModRM 3 4 dstCode, i.imm]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let count := (i.imm &&& 0x1F).toUInt32
    let res := dVal <<< count
    let cfBit := if count > 0 && count <= 32 then ((dVal >>> (32 - count)) &&& 1).toUInt64 else 0
    let ofBit := if count == 1 then (((res >>> 31) ^^^ (cfBit.toUInt32)) &&& 1).toUInt64 else 0
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsShift32 res cfBit ofBit (i.imm &&& 0x1F)
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHL.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shl {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"shl_r32_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask i := (let c := i.imm &&& 0x1F; if c == 0 then 0 else 16 ||| (if c == 1 then 0 else 2048))
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases :=
    (allReg32List.map (ShlR32Imm8.mk · 1)) ++ ([(0 : UInt8), 1, 7, 31].map (ShlR32Imm8.mk .eax ·)) ++
    ([(0 : UInt8), 1, 7, 31].map (ShlR32Imm8.mk .r15d ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHL r32, 1: Shifts 32-bit register left by 1, zero-extending destination to 64 bits. -/
structure ShlR32One where
  dst : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShlR32One where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xD1, makeModRM 3 4 dstCode]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let res := dVal <<< 1
    let cfBit : UInt64 := ((dVal >>> 31) &&& 1).toUInt64
    let ofBit : UInt64 := (((res >>> 31) ^^^ (cfBit.toUInt32)) &&& 1).toUInt64
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsShift32 res cfBit ofBit 1
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHL.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shl {i.dst}, 1"
  toLean i := s!"shl_r32_one .{i.dst}"
  undefinedFlagsMask _ := 16
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases := allReg32List.map ShlR32One.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHL r32, cl: Shifts 32-bit register left by count in CL (masked to 5 bits 0..31), zero-extending destination to 64 bits. -/
structure ShlR32Cl where
  dst : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShlR32Cl where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xD3, makeModRM 3 4 dstCode]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let count := (s.readGpr8 .cl &&& 0x1F).toUInt32
    let res := dVal <<< count
    let cfBit := if count > 0 && count <= 32 then ((dVal >>> (32 - count)) &&& 1).toUInt64 else 0
    let ofBit := if count == 1 then (((res >>> 31) ^^^ (cfBit.toUInt32)) &&& 1).toUInt64 else 0
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsShift32 res cfBit ofBit (s.readGpr8 .cl &&& 0x1F)
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHL.cl32", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shl {i.dst}, cl"
  toLean i := s!"shl_r32_cl .{i.dst}"
  undefinedFlagsMask _ := 16 ||| 2048
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateShiftClFuzzStates (reg32To64 i.dst) rng
  roundtripCases := allReg32List.map ShlR32Cl.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHR r32, imm8: Logical right shift of 32-bit register by imm8 (masked to 5 bits 0..31), zero-extending destination to 64 bits. -/
structure ShrR32Imm8 where
  dst : Reg32
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShrR32Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xC1, makeModRM 3 5 dstCode, i.imm]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let count := (i.imm &&& 0x1F).toUInt32
    let res := dVal >>> count
    let cfBit := if count > 0 && count <= 32 then ((dVal >>> (count - 1)) &&& 1).toUInt64 else 0
    let ofBit := if count == 1 then ((dVal >>> 31) &&& 1).toUInt64 else 0
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsShift32 res cfBit ofBit (i.imm &&& 0x1F)
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHR.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shr {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"shr_r32_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask i := (let c := i.imm &&& 0x1F; if c == 0 then 0 else 16 ||| (if c == 1 then 0 else 2048))
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases :=
    (allReg32List.map (ShrR32Imm8.mk · 1)) ++ ([(0 : UInt8), 1, 7, 31].map (ShrR32Imm8.mk .eax ·)) ++
    ([(0 : UInt8), 1, 7, 31].map (ShrR32Imm8.mk .r15d ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHR r32, 1: Logical right shift of 32-bit register by 1, zero-extending destination to 64 bits. -/
structure ShrR32One where
  dst : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShrR32One where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xD1, makeModRM 3 5 dstCode]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let res := dVal >>> 1
    let cfBit : UInt64 := (dVal &&& 1).toUInt64
    let ofBit : UInt64 := ((dVal >>> 31) &&& 1).toUInt64
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsShift32 res cfBit ofBit 1
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHR.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shr {i.dst}, 1"
  toLean i := s!"shr_r32_one .{i.dst}"
  undefinedFlagsMask _ := 16
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases := allReg32List.map ShrR32One.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHR r32, cl: Logical right shift of 32-bit register by count in CL (masked to 5 bits 0..31), zero-extending destination to 64 bits. -/
structure ShrR32Cl where
  dst : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShrR32Cl where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xD3, makeModRM 3 5 dstCode]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let count := (s.readGpr8 .cl &&& 0x1F).toUInt32
    let res := dVal >>> count
    let cfBit := if count > 0 && count <= 32 then ((dVal >>> (count - 1)) &&& 1).toUInt64 else 0
    let ofBit := if count == 1 then ((dVal >>> 31) &&& 1).toUInt64 else 0
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsShift32 res cfBit ofBit (s.readGpr8 .cl &&& 0x1F)
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHR.cl32", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shr {i.dst}, cl"
  toLean i := s!"shr_r32_cl .{i.dst}"
  undefinedFlagsMask _ := 16 ||| 2048
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateShiftClFuzzStates (reg32To64 i.dst) rng
  roundtripCases := allReg32List.map ShrR32Cl.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SAR r32, imm8: Arithmetic right shift of 32-bit register by imm8 (masked to 5 bits 0..31), zero-extending destination to 64 bits. -/
structure SarR32Imm8 where
  dst : Reg32
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction SarR32Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xC1, makeModRM 3 7 dstCode, i.imm]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let count := (i.imm &&& 0x1F).toUInt32
    let signBit := (dVal >>> 31) == 1
    let signExtendMask := if signBit && count > 0 then ~~~(0xFFFFFFFF >>> count) else 0
    let res := (dVal >>> count) ||| signExtendMask
    let cfBit := if count > 0 && count <= 32 then ((dVal >>> (count - 1)) &&& 1).toUInt64 else 0
    let ofBit := 0
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsShift32 res cfBit ofBit (i.imm &&& 0x1F)
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SAR.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"sar {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"sar_r32_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask i := (let c := i.imm &&& 0x1F; if c == 0 then 0 else 16 ||| (if c == 1 then 0 else 2048))
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases :=
    (allReg32List.map (SarR32Imm8.mk · 1)) ++ ([(0 : UInt8), 1, 7, 31].map (SarR32Imm8.mk .eax ·)) ++
    ([(0 : UInt8), 1, 7, 31].map (SarR32Imm8.mk .r15d ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SAR r32, 1: Arithmetic right shift of 32-bit register by 1, zero-extending destination to 64 bits. -/
structure SarR32One where
  dst : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction SarR32One where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xD1, makeModRM 3 7 dstCode]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let signBit := (dVal >>> 31) == 1
    let signExtendMask : UInt32 := if signBit then 0x80000000 else 0
    let res := (dVal >>> 1) ||| signExtendMask
    let cfBit : UInt64 := (dVal &&& 1).toUInt64
    let ofBit : UInt64 := 0
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsShift32 res cfBit ofBit 1
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SAR.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"sar {i.dst}, 1"
  toLean i := s!"sar_r32_one .{i.dst}"
  undefinedFlagsMask _ := 16
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases := allReg32List.map SarR32One.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SAR r32, cl: Arithmetic right shift of 32-bit register by count in CL (masked to 5 bits 0..31), zero-extending destination to 64 bits. -/
structure SarR32Cl where
  dst : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction SarR32Cl where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xD3, makeModRM 3 7 dstCode]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let count := (s.readGpr8 .cl &&& 0x1F).toUInt32
    let signBit := (dVal >>> 31) == 1
    let signExtendMask := if signBit && count > 0 then ~~~(0xFFFFFFFF >>> count) else 0
    let res := (dVal >>> count) ||| signExtendMask
    let cfBit := if count > 0 && count <= 32 then ((dVal >>> (count - 1)) &&& 1).toUInt64 else 0
    let ofBit := 0
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsShift32 res cfBit ofBit (s.readGpr8 .cl &&& 0x1F)
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SAR.cl32", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"sar {i.dst}, cl"
  toLean i := s!"sar_r32_cl .{i.dst}"
  undefinedFlagsMask _ := 16 ||| 2048
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateShiftClFuzzStates (reg32To64 i.dst) rng
  roundtripCases := allReg32List.map SarR32Cl.mk
  memAccesses _ := []

-- ============================================================================
-- 16-BIT SHIFT INSTRUCTIONS
-- ============================================================================

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHL r16, imm8: Shifts 16-bit register left by imm8 (masked to 5 bits 0..31), preserving upper 48 bits. -/
structure ShlR16Imm8 where
  dst : Reg16
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShlR16Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexPrefix ++ #[0xC1, makeModRM 3 4 dstCode, i.imm])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let count := (i.imm &&& 0x1F).toUInt16
    let res := if count > 16 then 0 else dVal <<< count
    let cfBit :=
      if count > 0 && count <= 16 then ((dVal >>> (16 - count)) &&& 1).toUInt64
      else 0
    let ofBit := if count == 1 then (((res >>> 15) ^^^ (cfBit.toUInt16)) &&& 1).toUInt64 else 0
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsShift16 res cfBit ofBit (i.imm &&& 0x1F)
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHL.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shl {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"shl_r16_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask i := (let c := i.imm &&& 0x1F; if c == 0 then 0 else 16 ||| (if c == 1 then 0 else 2048))
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases :=
    (allReg16List.map (ShlR16Imm8.mk · 1)) ++ ([(0 : UInt8), 1, 7, 15, 31].map (ShlR16Imm8.mk .ax ·)) ++
    ([(0 : UInt8), 1, 7, 15, 31].map (ShlR16Imm8.mk .r15w ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHL r16, 1: Shifts 16-bit register left by 1, preserving upper 48 bits. -/
structure ShlR16One where
  dst : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShlR16One where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexPrefix ++ #[0xD1, makeModRM 3 4 dstCode])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let res := dVal <<< 1
    let cfBit : UInt64 := ((dVal >>> 15) &&& 1).toUInt64
    let ofBit : UInt64 := (((res >>> 15) ^^^ (cfBit.toUInt16)) &&& 1).toUInt64
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsShift16 res cfBit ofBit 1
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHL.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shl {i.dst}, 1"
  toLean i := s!"shl_r16_one .{i.dst}"
  undefinedFlagsMask _ := 16
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases := allReg16List.map ShlR16One.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHL r16, cl: Shifts 16-bit register left by count in CL (masked to 5 bits 0..31), preserving upper 48 bits. -/
structure ShlR16Cl where
  dst : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShlR16Cl where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexPrefix ++ #[0xD3, makeModRM 3 4 dstCode])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let count := (s.readGpr8 .cl &&& 0x1F).toUInt16
    let res := if count > 16 then 0 else dVal <<< count
    let cfBit :=
      if count > 0 && count <= 16 then ((dVal >>> (16 - count)) &&& 1).toUInt64
      else 0
    let ofBit := if count == 1 then (((res >>> 15) ^^^ (cfBit.toUInt16)) &&& 1).toUInt64 else 0
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsShift16 res cfBit ofBit (s.readGpr8 .cl &&& 0x1F)
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHL.cl16", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shl {i.dst}, cl"
  toLean i := s!"shl_r16_cl .{i.dst}"
  undefinedFlagsMask _ := 16 ||| 2048
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateShiftClFuzzStates (reg16To64 i.dst) rng
  roundtripCases := allReg16List.map ShlR16Cl.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHR r16, imm8: Logical right shift of 16-bit register by imm8 (masked to 5 bits 0..31), preserving upper 48 bits. -/
structure ShrR16Imm8 where
  dst : Reg16
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShrR16Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexPrefix ++ #[0xC1, makeModRM 3 5 dstCode, i.imm])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let count := (i.imm &&& 0x1F).toUInt16
    let res := if count > 16 then 0 else dVal >>> count
    let cfBit :=
      if count > 0 && count <= 16 then ((dVal >>> (count - 1)) &&& 1).toUInt64
      else 0
    let ofBit := if count == 1 then ((dVal >>> 15) &&& 1).toUInt64 else 0
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsShift16 res cfBit ofBit (i.imm &&& 0x1F)
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHR.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shr {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"shr_r16_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask i := (let c := i.imm &&& 0x1F; if c == 0 then 0 else 16 ||| (if c == 1 then 0 else 2048))
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases :=
    (allReg16List.map (ShrR16Imm8.mk · 1)) ++ ([(0 : UInt8), 1, 7, 15, 31].map (ShrR16Imm8.mk .ax ·)) ++
    ([(0 : UInt8), 1, 7, 15, 31].map (ShrR16Imm8.mk .r15w ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHR r16, 1: Logical right shift of 16-bit register by 1, preserving upper 48 bits. -/
structure ShrR16One where
  dst : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShrR16One where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexPrefix ++ #[0xD1, makeModRM 3 5 dstCode])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let res := dVal >>> 1
    let cfBit : UInt64 := (dVal &&& 1).toUInt64
    let ofBit : UInt64 := ((dVal >>> 15) &&& 1).toUInt64
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsShift16 res cfBit ofBit 1
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHR.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shr {i.dst}, 1"
  toLean i := s!"shr_r16_one .{i.dst}"
  undefinedFlagsMask _ := 16
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases := allReg16List.map ShrR16One.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHR r16, cl: Logical right shift of 16-bit register by count in CL (masked to 5 bits 0..31), preserving upper 48 bits. -/
structure ShrR16Cl where
  dst : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShrR16Cl where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexPrefix ++ #[0xD3, makeModRM 3 5 dstCode])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let count := (s.readGpr8 .cl &&& 0x1F).toUInt16
    let res := if count > 16 then 0 else dVal >>> count
    let cfBit :=
      if count > 0 && count <= 16 then ((dVal >>> (count - 1)) &&& 1).toUInt64
      else 0
    let ofBit := if count == 1 then ((dVal >>> 15) &&& 1).toUInt64 else 0
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsShift16 res cfBit ofBit (s.readGpr8 .cl &&& 0x1F)
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHR.cl16", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shr {i.dst}, cl"
  toLean i := s!"shr_r16_cl .{i.dst}"
  undefinedFlagsMask _ := 16 ||| 2048
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateShiftClFuzzStates (reg16To64 i.dst) rng
  roundtripCases := allReg16List.map ShrR16Cl.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SAR r16, imm8: Arithmetic right shift of 16-bit register by imm8 (masked to 5 bits 0..31), preserving upper 48 bits. -/
structure SarR16Imm8 where
  dst : Reg16
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction SarR16Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexPrefix ++ #[0xC1, makeModRM 3 7 dstCode, i.imm])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let count := (i.imm &&& 0x1F).toUInt16
    let signBit := (dVal >>> 15) == 1
    let res : UInt16 :=
      if count > 16 then (if signBit then 0xFFFF else 0)
      else
        let signExtendMask : UInt16 := if signBit && count > 0 then ~~~(0xFFFF >>> count) else 0
        (dVal >>> count) ||| signExtendMask
    let cfBit :=
      if count > 0 && count <= 16 then ((dVal >>> (count - 1)) &&& 1).toUInt64
      else if count > 16 then (if signBit then 1 else 0)
      else 0
    let ofBit := 0
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsShift16 res cfBit ofBit (i.imm &&& 0x1F)
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SAR.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"sar {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"sar_r16_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask i := (let c := i.imm &&& 0x1F; if c == 0 then 0 else 16 ||| (if c == 1 then 0 else 2048))
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases :=
    (allReg16List.map (SarR16Imm8.mk · 1)) ++ ([(0 : UInt8), 1, 7, 15, 31].map (SarR16Imm8.mk .ax ·)) ++
    ([(0 : UInt8), 1, 7, 15, 31].map (SarR16Imm8.mk .r15w ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SAR r16, 1: Arithmetic right shift of 16-bit register by 1, preserving upper 48 bits. -/
structure SarR16One where
  dst : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction SarR16One where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexPrefix ++ #[0xD1, makeModRM 3 7 dstCode])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let signBit := (dVal >>> 15) == 1
    let signExtendMask : UInt16 := if signBit then 0x8000 else 0
    let res := (dVal >>> 1) ||| signExtendMask
    let cfBit : UInt64 := (dVal &&& 1).toUInt64
    let ofBit : UInt64 := 0
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsShift16 res cfBit ofBit 1
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SAR.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"sar {i.dst}, 1"
  toLean i := s!"sar_r16_one .{i.dst}"
  undefinedFlagsMask _ := 16
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases := allReg16List.map SarR16One.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SAR r16, cl: Arithmetic right shift of 16-bit register by count in CL (masked to 5 bits 0..31), preserving upper 48 bits. -/
structure SarR16Cl where
  dst : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction SarR16Cl where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexPrefix ++ #[0xD3, makeModRM 3 7 dstCode])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let count := (s.readGpr8 .cl &&& 0x1F).toUInt16
    let signBit := (dVal >>> 15) == 1
    let res : UInt16 :=
      if count > 16 then (if signBit then 0xFFFF else 0)
      else
        let signExtendMask : UInt16 := if signBit && count > 0 then ~~~(0xFFFF >>> count) else 0
        (dVal >>> count) ||| signExtendMask
    let cfBit :=
      if count > 0 && count <= 16 then ((dVal >>> (count - 1)) &&& 1).toUInt64
      else if count > 16 then (if signBit then 1 else 0)
      else 0
    let ofBit := 0
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsShift16 res cfBit ofBit (s.readGpr8 .cl &&& 0x1F)
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SAR.cl16", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"sar {i.dst}, cl"
  toLean i := s!"sar_r16_cl .{i.dst}"
  undefinedFlagsMask _ := 16 ||| 2048
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateShiftClFuzzStates (reg16To64 i.dst) rng
  roundtripCases := allReg16List.map SarR16Cl.mk
  memAccesses _ := []

-- ============================================================================
-- 8-BIT SHIFT INSTRUCTIONS
-- ============================================================================

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHL r8, imm8: Shifts 8-bit register left by imm8 (masked to 5 bits 0..31), preserving upper 56 bits. -/
structure ShlR8Imm8 where
  dst : Reg8
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShlR8Imm8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xC0, makeModRM 3 4 dstCode, i.imm]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let count := i.imm &&& 0x1F
    let res := if count > 8 then 0 else dVal <<< count
    let cfBit :=
      if count > 0 && count <= 8 then ((dVal >>> (8 - count)) &&& 1).toUInt64
      else 0
    let ofBit := if count == 1 then (((res >>> 7) ^^^ (cfBit.toUInt8)) &&& 1).toUInt64 else 0
    let s' := s.setGpr8 i.dst res
    let s'' := s'.setFlagsShift8 res cfBit ofBit (i.imm &&& 0x1F)
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHL.alu8", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shl {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"shl_r8_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask i := (let c := i.imm &&& 0x1F; if c == 0 then 0 else 16 ||| (if c == 1 then 0 else 2048))
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg8To64 i.dst) rng
  roundtripCases :=
    (allReg8List.map (ShlR8Imm8.mk · 1)) ++ ([(0 : UInt8), 1, 7, 31].map (ShlR8Imm8.mk .al ·)) ++
    ([(0 : UInt8), 1, 7, 31].map (ShlR8Imm8.mk .r15b ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHL r8, 1: Shifts 8-bit register left by 1, preserving upper 56 bits. -/
structure ShlR8One where
  dst : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShlR8One where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xD0, makeModRM 3 4 dstCode]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let res := dVal <<< 1
    let cfBit : UInt64 := ((dVal >>> 7) &&& 1).toUInt64
    let ofBit : UInt64 := (((res >>> 7) ^^^ (cfBit.toUInt8)) &&& 1).toUInt64
    let s' := s.setGpr8 i.dst res
    let s'' := s'.setFlagsShift8 res cfBit ofBit 1
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHL.alu8", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shl {i.dst}, 1"
  toLean i := s!"shl_r8_one .{i.dst}"
  undefinedFlagsMask _ := 16
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg8To64 i.dst) rng
  roundtripCases := allReg8List.map ShlR8One.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHL r8, cl: Shifts 8-bit register left by count in CL (masked to 5 bits 0..31), preserving upper 56 bits. -/
structure ShlR8Cl where
  dst : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShlR8Cl where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xD2, makeModRM 3 4 dstCode]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let count := s.readGpr8 .cl &&& 0x1F
    let res := if count > 8 then 0 else dVal <<< count
    let cfBit :=
      if count > 0 && count <= 8 then ((dVal >>> (8 - count)) &&& 1).toUInt64
      else 0
    let ofBit := if count == 1 then (((res >>> 7) ^^^ (cfBit.toUInt8)) &&& 1).toUInt64 else 0
    let s' := s.setGpr8 i.dst res
    let s'' := s'.setFlagsShift8 res cfBit ofBit (s.readGpr8 .cl &&& 0x1F)
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHL.cl8", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shl {i.dst}, cl"
  toLean i := s!"shl_r8_cl .{i.dst}"
  undefinedFlagsMask _ := 16 ||| 2048
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateShiftClFuzzStates (reg8To64 i.dst) rng
  roundtripCases := allReg8List.map ShlR8Cl.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHR r8, imm8: Logical right shift of 8-bit register by imm8 (masked to 5 bits 0..31), preserving upper 56 bits. -/
structure ShrR8Imm8 where
  dst : Reg8
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShrR8Imm8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xC0, makeModRM 3 5 dstCode, i.imm]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let count := i.imm &&& 0x1F
    let res := if count > 8 then 0 else dVal >>> count
    let cfBit :=
      if count > 0 && count <= 8 then ((dVal >>> (count - 1)) &&& 1).toUInt64
      else 0
    let ofBit := if count == 1 then ((dVal >>> 7) &&& 1).toUInt64 else 0
    let s' := s.setGpr8 i.dst res
    let s'' := s'.setFlagsShift8 res cfBit ofBit (i.imm &&& 0x1F)
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHR.alu8", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shr {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"shr_r8_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask i := (let c := i.imm &&& 0x1F; if c == 0 then 0 else 16 ||| (if c == 1 then 0 else 2048))
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg8To64 i.dst) rng
  roundtripCases :=
    (allReg8List.map (ShrR8Imm8.mk · 1)) ++ ([(0 : UInt8), 1, 7, 31].map (ShrR8Imm8.mk .al ·)) ++
    ([(0 : UInt8), 1, 7, 31].map (ShrR8Imm8.mk .r15b ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHR r8, 1: Logical right shift of 8-bit register by 1, preserving upper 56 bits. -/
structure ShrR8One where
  dst : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShrR8One where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xD0, makeModRM 3 5 dstCode]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let res := dVal >>> 1
    let cfBit : UInt64 := (dVal &&& 1).toUInt64
    let ofBit : UInt64 := ((dVal >>> 7) &&& 1).toUInt64
    let s' := s.setGpr8 i.dst res
    let s'' := s'.setFlagsShift8 res cfBit ofBit 1
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHR.alu8", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shr {i.dst}, 1"
  toLean i := s!"shr_r8_one .{i.dst}"
  undefinedFlagsMask _ := 16
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg8To64 i.dst) rng
  roundtripCases := allReg8List.map ShrR8One.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SHR r8, cl: Logical right shift of 8-bit register by count in CL (masked to 5 bits 0..31), preserving upper 56 bits. -/
structure ShrR8Cl where
  dst : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction ShrR8Cl where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xD2, makeModRM 3 5 dstCode]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let count := s.readGpr8 .cl &&& 0x1F
    let res := if count > 8 then 0 else dVal >>> count
    let cfBit :=
      if count > 0 && count <= 8 then ((dVal >>> (count - 1)) &&& 1).toUInt64
      else 0
    let ofBit := if count == 1 then ((dVal >>> 7) &&& 1).toUInt64 else 0
    let s' := s.setGpr8 i.dst res
    let s'' := s'.setFlagsShift8 res cfBit ofBit (s.readGpr8 .cl &&& 0x1F)
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SHR.cl8", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"shr {i.dst}, cl"
  toLean i := s!"shr_r8_cl .{i.dst}"
  undefinedFlagsMask _ := 16 ||| 2048
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateShiftClFuzzStates (reg8To64 i.dst) rng
  roundtripCases := allReg8List.map ShrR8Cl.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SAR r8, imm8: Arithmetic right shift of 8-bit register by imm8 (masked to 5 bits 0..31), preserving upper 56 bits. -/
structure SarR8Imm8 where
  dst : Reg8
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction SarR8Imm8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xC0, makeModRM 3 7 dstCode, i.imm]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let count := i.imm &&& 0x1F
    let signBit := (dVal >>> 7) == 1
    let res : UInt8 :=
      if count > 8 then (if signBit then 0xFF else 0)
      else
        let signExtendMask : UInt8 := if signBit && count > 0 then ~~~(0xFF >>> count) else 0
        (dVal >>> count) ||| signExtendMask
    let cfBit :=
      if count > 0 && count <= 8 then ((dVal >>> (count - 1)) &&& 1).toUInt64
      else if count > 8 then (if signBit then 1 else 0)
      else 0
    let ofBit := 0
    let s' := s.setGpr8 i.dst res
    let s'' := s'.setFlagsShift8 res cfBit ofBit (i.imm &&& 0x1F)
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SAR.alu8", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"sar {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"sar_r8_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask i := (let c := i.imm &&& 0x1F; if c == 0 then 0 else 16 ||| (if c == 1 then 0 else 2048))
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg8To64 i.dst) rng
  roundtripCases :=
    (allReg8List.map (SarR8Imm8.mk · 1)) ++ ([(0 : UInt8), 1, 7, 31].map (SarR8Imm8.mk .al ·)) ++
    ([(0 : UInt8), 1, 7, 31].map (SarR8Imm8.mk .r15b ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SAR r8, 1: Arithmetic right shift of 8-bit register by 1, preserving upper 56 bits. -/
structure SarR8One where
  dst : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction SarR8One where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xD0, makeModRM 3 7 dstCode]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let signBit := (dVal >>> 7) == 1
    let signExtendMask : UInt8 := if signBit then 0x80 else 0
    let res := (dVal >>> 1) ||| signExtendMask
    let cfBit : UInt64 := (dVal &&& 1).toUInt64
    let ofBit : UInt64 := 0
    let s' := s.setGpr8 i.dst res
    let s'' := s'.setFlagsShift8 res cfBit ofBit 1
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SAR.alu8", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"sar {i.dst}, 1"
  toLean i := s!"sar_r8_one .{i.dst}"
  undefinedFlagsMask _ := 16
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg8To64 i.dst) rng
  roundtripCases := allReg8List.map SarR8One.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=description -/
/-- SAR r8, cl: Arithmetic right shift of 8-bit register by count in CL (masked to 5 bits 0..31), preserving upper 56 bits. -/
structure SarR8Cl where
  dst : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SAL_SAR_SHL_SHR;part=operation -/
instance : X86_64Instruction SarR8Cl where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xD2, makeModRM 3 7 dstCode]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let count := s.readGpr8 .cl &&& 0x1F
    let signBit := (dVal >>> 7) == 1
    let res : UInt8 :=
      if count > 8 then (if signBit then 0xFF else 0)
      else
        let signExtendMask : UInt8 := if signBit && count > 0 then ~~~(0xFF >>> count) else 0
        (dVal >>> count) ||| signExtendMask
    let cfBit :=
      if count > 0 && count <= 8 then ((dVal >>> (count - 1)) &&& 1).toUInt64
      else if count > 8 then (if signBit then 1 else 0)
      else 0
    let ofBit := 0
    let s' := s.setGpr8 i.dst res
    let s'' := s'.setFlagsShift8 res cfBit ofBit (s.readGpr8 .cl &&& 0x1F)
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "SAR.cl8", uopClass := .intALU, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"sar {i.dst}, cl"
  toLean i := s!"sar_r8_cl .{i.dst}"
  undefinedFlagsMask _ := 16 ||| 2048
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateShiftClFuzzStates (reg8To64 i.dst) rng
  roundtripCases := allReg8List.map SarR8Cl.mk
  memAccesses _ := []

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
def shl_r64_imm8 (dst : Reg64) (imm : UInt8) : AnyX86_64Instruction := ⟨ShlR64Imm8.mk dst imm⟩
def shl_r64_one (dst : Reg64) : AnyX86_64Instruction := ⟨ShlR64One.mk dst⟩
def shl_r64_cl (dst : Reg64) : AnyX86_64Instruction := ⟨ShlR64Cl.mk dst⟩

def shr_r64_imm8 (dst : Reg64) (imm : UInt8) : AnyX86_64Instruction := ⟨ShrR64Imm8.mk dst imm⟩
def shr_r64_one (dst : Reg64) : AnyX86_64Instruction := ⟨ShrR64One.mk dst⟩
def shr_r64_cl (dst : Reg64) : AnyX86_64Instruction := ⟨ShrR64Cl.mk dst⟩

def sar_r64_imm8 (dst : Reg64) (imm : UInt8) : AnyX86_64Instruction := ⟨SarR64Imm8.mk dst imm⟩
def sar_r64_one (dst : Reg64) : AnyX86_64Instruction := ⟨SarR64One.mk dst⟩
def sar_r64_cl (dst : Reg64) : AnyX86_64Instruction := ⟨SarR64Cl.mk dst⟩

def shl_r32_imm8 (dst : Reg32) (imm : UInt8) : AnyX86_64Instruction := ⟨ShlR32Imm8.mk dst imm⟩
def shl_r32_one (dst : Reg32) : AnyX86_64Instruction := ⟨ShlR32One.mk dst⟩
def shl_r32_cl (dst : Reg32) : AnyX86_64Instruction := ⟨ShlR32Cl.mk dst⟩

def shr_r32_imm8 (dst : Reg32) (imm : UInt8) : AnyX86_64Instruction := ⟨ShrR32Imm8.mk dst imm⟩
def shr_r32_one (dst : Reg32) : AnyX86_64Instruction := ⟨ShrR32One.mk dst⟩
def shr_r32_cl (dst : Reg32) : AnyX86_64Instruction := ⟨ShrR32Cl.mk dst⟩

def sar_r32_imm8 (dst : Reg32) (imm : UInt8) : AnyX86_64Instruction := ⟨SarR32Imm8.mk dst imm⟩
def sar_r32_one (dst : Reg32) : AnyX86_64Instruction := ⟨SarR32One.mk dst⟩
def sar_r32_cl (dst : Reg32) : AnyX86_64Instruction := ⟨SarR32Cl.mk dst⟩

def shl_r16_imm8 (dst : Reg16) (imm : UInt8) : AnyX86_64Instruction := ⟨ShlR16Imm8.mk dst imm⟩
def shl_r16_one (dst : Reg16) : AnyX86_64Instruction := ⟨ShlR16One.mk dst⟩
def shl_r16_cl (dst : Reg16) : AnyX86_64Instruction := ⟨ShlR16Cl.mk dst⟩

def shr_r16_imm8 (dst : Reg16) (imm : UInt8) : AnyX86_64Instruction := ⟨ShrR16Imm8.mk dst imm⟩
def shr_r16_one (dst : Reg16) : AnyX86_64Instruction := ⟨ShrR16One.mk dst⟩
def shr_r16_cl (dst : Reg16) : AnyX86_64Instruction := ⟨ShrR16Cl.mk dst⟩

def sar_r16_imm8 (dst : Reg16) (imm : UInt8) : AnyX86_64Instruction := ⟨SarR16Imm8.mk dst imm⟩
def sar_r16_one (dst : Reg16) : AnyX86_64Instruction := ⟨SarR16One.mk dst⟩
def sar_r16_cl (dst : Reg16) : AnyX86_64Instruction := ⟨SarR16Cl.mk dst⟩

def shl_r8_imm8 (dst : Reg8) (imm : UInt8) : AnyX86_64Instruction := ⟨ShlR8Imm8.mk dst imm⟩
def shl_r8_one (dst : Reg8) : AnyX86_64Instruction := ⟨ShlR8One.mk dst⟩
def shl_r8_cl (dst : Reg8) : AnyX86_64Instruction := ⟨ShlR8Cl.mk dst⟩

def shr_r8_imm8 (dst : Reg8) (imm : UInt8) : AnyX86_64Instruction := ⟨ShrR8Imm8.mk dst imm⟩
def shr_r8_one (dst : Reg8) : AnyX86_64Instruction := ⟨ShrR8One.mk dst⟩
def shr_r8_cl (dst : Reg8) : AnyX86_64Instruction := ⟨ShrR8Cl.mk dst⟩

def sar_r8_imm8 (dst : Reg8) (imm : UInt8) : AnyX86_64Instruction := ⟨SarR8Imm8.mk dst imm⟩
def sar_r8_one (dst : Reg8) : AnyX86_64Instruction := ⟨SarR8One.mk dst⟩
def sar_r8_cl (dst : Reg8) : AnyX86_64Instruction := ⟨SarR8Cl.mk dst⟩

-- ============================================================================
-- CO-LOCATED DECODER
-- ============================================================================

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
def shiftTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  match parsePrefixesAndOpcode bytes offset with
  | .error e => .error e
  | .ok (has0x66, _, rexW, _, _, rexB, opcode, opOffset) =>
    if has0x66 then
      if opcode == 0xC1 then
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (_, reg, rm, modPos) =>
          let dst := codeToReg16 rm rexB
          match readUInt8 bytes modPos with
          | .error e => .error e
          | .ok imm8 =>
            let pos := modPos + 1
            if reg == 4 then .ok (shl_r16_imm8 dst imm8, pos - offset)
            else if reg == 5 then .ok (shr_r16_imm8 dst imm8, pos - offset)
            else if reg == 7 then .ok (sar_r16_imm8 dst imm8, pos - offset)
            else .error "shiftTryDecode: 0xC1 sub-opcode is not SHIFT"
      else if opcode == 0xD1 then
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (_, reg, rm, pos) =>
          let dst := codeToReg16 rm rexB
          if reg == 4 then .ok (shl_r16_one dst, pos - offset)
          else if reg == 5 then .ok (shr_r16_one dst, pos - offset)
          else if reg == 7 then .ok (sar_r16_one dst, pos - offset)
          else .error "shiftTryDecode: 0xD1 sub-opcode is not SHIFT"
      else if opcode == 0xD3 then
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (_, reg, rm, pos) =>
          let dst := codeToReg16 rm rexB
          if reg == 4 then .ok (shl_r16_cl dst, pos - offset)
          else if reg == 5 then .ok (shr_r16_cl dst, pos - offset)
          else if reg == 7 then .ok (sar_r16_cl dst, pos - offset)
          else .error "shiftTryDecode: 0xD3 sub-opcode is not SHIFT"
      else
        .error s!"shiftTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} with 0x66 prefix is not SHIFT"
    else if opcode == 0xC0 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        let dst := codeToReg8 rm rexB
        match readUInt8 bytes modPos with
        | .error e => .error e
        | .ok imm8 =>
          let pos := modPos + 1
          if reg == 4 then .ok (shl_r8_imm8 dst imm8, pos - offset)
          else if reg == 5 then .ok (shr_r8_imm8 dst imm8, pos - offset)
          else if reg == 7 then .ok (sar_r8_imm8 dst imm8, pos - offset)
          else .error "shiftTryDecode: 0xC0 sub-opcode is not SHIFT"
    else if opcode == 0xD0 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        let dst := codeToReg8 rm rexB
        if reg == 4 then .ok (shl_r8_one dst, pos - offset)
        else if reg == 5 then .ok (shr_r8_one dst, pos - offset)
        else if reg == 7 then .ok (sar_r8_one dst, pos - offset)
        else .error "shiftTryDecode: 0xD0 sub-opcode is not SHIFT"
    else if opcode == 0xD2 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        let dst := codeToReg8 rm rexB
        if reg == 4 then .ok (shl_r8_cl dst, pos - offset)
        else if reg == 5 then .ok (shr_r8_cl dst, pos - offset)
        else if reg == 7 then .ok (sar_r8_cl dst, pos - offset)
        else .error "shiftTryDecode: 0xD2 sub-opcode is not SHIFT"
    else if opcode == 0xC1 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        match readUInt8 bytes modPos with
        | .error e => .error e
        | .ok imm8 =>
          let pos := modPos + 1
          if rexW then
            let dst := codeToReg64 rm rexB
            if reg == 4 then .ok (shl_r64_imm8 dst imm8, pos - offset)
            else if reg == 5 then .ok (shr_r64_imm8 dst imm8, pos - offset)
            else if reg == 7 then .ok (sar_r64_imm8 dst imm8, pos - offset)
            else .error "shiftTryDecode: 0xC1 sub-opcode is not SHIFT"
          else
            let dst := codeToReg32 rm rexB
            if reg == 4 then .ok (shl_r32_imm8 dst imm8, pos - offset)
            else if reg == 5 then .ok (shr_r32_imm8 dst imm8, pos - offset)
            else if reg == 7 then .ok (sar_r32_imm8 dst imm8, pos - offset)
            else .error "shiftTryDecode: 0xC1 sub-opcode is not SHIFT"
    else if opcode == 0xD1 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        if rexW then
          let dst := codeToReg64 rm rexB
          if reg == 4 then .ok (shl_r64_one dst, pos - offset)
          else if reg == 5 then .ok (shr_r64_one dst, pos - offset)
          else if reg == 7 then .ok (sar_r64_one dst, pos - offset)
          else .error "shiftTryDecode: 0xD1 sub-opcode is not SHIFT"
        else
          let dst := codeToReg32 rm rexB
          if reg == 4 then .ok (shl_r32_one dst, pos - offset)
          else if reg == 5 then .ok (shr_r32_one dst, pos - offset)
          else if reg == 7 then .ok (sar_r32_one dst, pos - offset)
          else .error "shiftTryDecode: 0xD1 sub-opcode is not SHIFT"
    else if opcode == 0xD3 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        if rexW then
          let dst := codeToReg64 rm rexB
          if reg == 4 then .ok (shl_r64_cl dst, pos - offset)
          else if reg == 5 then .ok (shr_r64_cl dst, pos - offset)
          else if reg == 7 then .ok (sar_r64_cl dst, pos - offset)
          else .error "shiftTryDecode: 0xD3 sub-opcode is not SHIFT"
        else
          let dst := codeToReg32 rm rexB
          if reg == 4 then .ok (shl_r32_cl dst, pos - offset)
          else if reg == 5 then .ok (shr_r32_cl dst, pos - offset)
          else if reg == 7 then .ok (sar_r32_cl dst, pos - offset)
          else .error "shiftTryDecode: 0xD3 sub-opcode is not SHIFT"
    else
      .error s!"shiftTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not SHIFT"

end Gasm.Targets.X86_64.Instructions
