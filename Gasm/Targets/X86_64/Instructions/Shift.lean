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
  undefinedFlagsMask i := (if (i.imm &&& 0x3F) == 0 then 0 else 16 ||| (if (i.imm &&& 0x3F) == 1 then 0 else 2048)) -- AF is undefined for shift count != 0, OF is undefined for count > 1 (count is imm masked to 6 bits, so imm=0x40 etc. must not over-mask)
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (ShlR64Imm8.mk · 1)) ++ ([(0 : UInt8), 1, 7, 31, 63].map (ShlR64Imm8.mk .rax ·)) ++
    ([(0 : UInt8), 1, 7, 31, 63].map (ShlR64Imm8.mk .r15 ·))
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
  undefinedFlagsMask i := (if (i.imm &&& 0x3F) == 0 then 0 else 16 ||| (if (i.imm &&& 0x3F) == 1 then 0 else 2048)) -- AF is undefined for shift count != 0, OF is undefined for count > 1 (count is imm masked to 6 bits, so imm=0x40 etc. must not over-mask)
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (ShrR64Imm8.mk · 1)) ++ ([(0 : UInt8), 1, 7, 31, 63].map (ShrR64Imm8.mk .rax ·)) ++
    ([(0 : UInt8), 1, 7, 31, 63].map (ShrR64Imm8.mk .r15 ·))
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
  undefinedFlagsMask i := (if (i.imm &&& 0x3F) == 0 then 0 else 16 ||| (if (i.imm &&& 0x3F) == 1 then 0 else 2048)) -- count is imm masked to 6 bits, so imm=0x40 etc. must not over-mask
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (SarR64Imm8.mk · 1)) ++ ([(0 : UInt8), 1, 7, 31, 63].map (SarR64Imm8.mk .rax ·)) ++
    ([(0 : UInt8), 1, 7, 31, 63].map (SarR64Imm8.mk .r15 ·))
  memAccesses _ := []

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
  undefinedFlagsMask _ := 16 ||| 2048 -- count comes from CL at runtime (any value 0..63): AF is undefined whenever count != 0, OF undefined whenever count != 1, so both must be masked conservatively for every count
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateShiftClFuzzStates i.dst rng
  roundtripCases := allReg64List.map ShlR64Cl.mk
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
  undefinedFlagsMask _ := 16 ||| 2048 -- count comes from CL at runtime (any value 0..63): AF is undefined whenever count != 0, OF undefined whenever count != 1, so both must be masked conservatively for every count
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateShiftClFuzzStates i.dst rng
  roundtripCases := allReg64List.map ShrR64Cl.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- SHL r64, imm8 helper. -/
def shl_r64_imm8 (dst : Reg64) (imm : UInt8) : AnyX86_64Instruction :=
  ⟨ShlR64Imm8.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- SHL r64, cl helper. -/
def shl_r64_cl (dst : Reg64) : AnyX86_64Instruction :=
  ⟨ShlR64Cl.mk dst⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- SHR r64, imm8 helper. -/
def shr_r64_imm8 (dst : Reg64) (imm : UInt8) : AnyX86_64Instruction :=
  ⟨ShrR64Imm8.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- SHR r64, cl helper. -/
def shr_r64_cl (dst : Reg64) : AnyX86_64Instruction :=
  ⟨ShrR64Cl.mk dst⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- SAR r64, imm8 helper. -/
def sar_r64_imm8 (dst : Reg64) (imm : UInt8) : AnyX86_64Instruction :=
  ⟨SarR64Imm8.mk dst imm⟩

private def shiftImm8Rule (reg : UInt8) (mk : Reg64 → UInt8 → AnyX86_64Instruction) : DecodeRule := {
  opcode := .one 0xC1,
  modrmReg := some reg,
  builder := fun ctx =>
    match ctx.modrm with
    | none => .error "shift imm8: missing ModR/M byte"
    | some m =>
      let dst := codeToReg64 m.rm ctx.rexB
      match readUInt8 ctx.bytes m.pos with
      | .error e => .error e
      | .ok imm8 => .ok (mk dst imm8, (m.pos + 1) - ctx.startOffset)
}

private def shiftClRule (reg : UInt8) (mk : Reg64 → AnyX86_64Instruction) : DecodeRule := {
  opcode := .one 0xD3,
  modrmReg := some reg,
  builder := fun ctx =>
    match ctx.modrm with
    | none => .error "shift cl: missing ModR/M byte"
    | some m =>
      let dst := codeToReg64 m.rm ctx.rexB
      .ok (mk dst, m.pos - ctx.startOffset)
}

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Declarative decoding rules for the SHIFT family. -/
def shiftDecodeRules : List DecodeRule := [
  shiftImm8Rule 4 shl_r64_imm8,
  shiftImm8Rule 5 shr_r64_imm8,
  shiftImm8Rule 7 sar_r64_imm8,
  shiftClRule 4 shl_r64_cl,
  shiftClRule 5 shr_r64_cl
]

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the SHIFT family, evaluating its declarative rules. -/
def shiftTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  tryDecodeWithRules shiftDecodeRules bytes offset

end Gasm.Targets.X86_64.Instructions
