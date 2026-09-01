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

/- REF: intel-sdm#vol=2;instr=DIV;part=description -/
/-- DIV r64: Unsigned divide RDX:RAX by 64-bit general-purpose register. -/
structure DivR64 where
  divisor : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=DIV;part=operation -/
instance : X86_64Instruction DivR64 where
  encode i :=
    let (code, ext) := reg64Code i.divisor
    let rex := makeRex true false false ext
    let modrm := makeModRM 3 6 code
    ByteArray.mk #[rex, 0xF7, modrm]
  step i s :=
    let divisorVal := s.gprs i.divisor
    if divisorVal == 0 then
      -- #DE (Divide Error Exception) - fault retains the faulting instruction RIP
      { s with fault := some .divideError }
    else
      let dividendNat : Nat := (s.gprs .rdx).toNat * 18446744073709551616 + (s.gprs .rax).toNat
      let divisorNat : Nat := divisorVal.toNat
      let quotNat := dividendNat / divisorNat
      let remNat := dividendNat % divisorNat
      if quotNat > 0xFFFFFFFFFFFFFFFF then
        -- #DE (Quotient Overflow Exception) - fault retains the faulting instruction RIP
        { s with fault := some .divideError }
      else
        let s' := s.setGpr64 .rax (UInt64.ofNat quotNat)
        let s'' := s'.setGpr64 .rdx (UInt64.ofNat remNat)
        { s'' with rip := s.rip + 3 }
  toUops _ := [
    { mnemonic := "DIV.prep", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "DIV.intDiv", uopClass := .intDiv, eligiblePorts := [.p0], latencyCycles := 14, reciprocalThroughput := 10.0 },
    { mnemonic := "DIV.splitQuot", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "DIV.splitRem", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "DIV.flags", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"div {i.divisor}"
  toLean i := s!"div_r64 .{i.divisor}"
  undefinedFlagsMask _ := arithmeticStatusMask -- All status flags are undefined after DIV according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.divisor
  validationOracle i := if hwSafeReg64 i.divisor then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := Id.run do
    let mut states : List X86_64MachineState := []
    let divisors : List UInt64 := [0, 1, 2, 3, 5, 7, 0x10, 0x100, 0x7FFF, 0x8000, 0xFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF]
    let dividends : List UInt64 := [0, 1, 2, 10, 100, 0x1000, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]
    for d in divisors do
      if d != 0 then
        let s : X86_64MachineState := default
        let s := s.setGpr64 .rax 0
        let s := s.setGpr64 .rdx d
        let s := s.setGpr64 i.divisor d
        states := states ++ [s]
    for rdxVal in ([1, 0xFFFFFFFFFFFFFFFF] : List UInt64) do
      let s : X86_64MachineState := default
      let s := s.setGpr64 .rax 123
      let s := s.setGpr64 .rdx rdxVal
      let s := s.setGpr64 i.divisor 0
      states := states ++ [s]
    for d in divisors do
      for a in dividends do
        let s : X86_64MachineState := default
        let s := s.setGpr64 .rax a
        let s := s.setGpr64 .rdx 0
        let s := s.setGpr64 i.divisor d
        states := states ++ [s]
    (states, rng)
  roundtripCases := allReg64List.map DivR64.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- DIV r64 helper. -/
def div_r64 (r : Reg64) : AnyX86_64Instruction :=
  ⟨DivR64.mk r⟩

/- REF: intel-sdm#vol=2;instr=DIV;part=description -/
/-- DIV r32: Unsigned divide EDX:EAX by 32-bit general-purpose register. -/
structure DivR32 where
  divisor : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=DIV;part=operation -/
instance : X86_64Instruction DivR32 where
  encode i :=
    let (code, ext) := reg32Code i.divisor
    let rex := if ext then #[makeRex false false false ext] else #[]
    ByteArray.mk (rex ++ #[0xF7, makeModRM 3 6 code])
  step i s :=
    let divisorVal := (s.gprs (reg32To64 i.divisor)).toUInt32
    if divisorVal == 0 then
      { s with fault := some .divideError }
    else
      let dividendNat : Nat := (s.gprs .rdx).toUInt32.toNat * 0x100000000 + (s.gprs .rax).toUInt32.toNat
      let divisorNat : Nat := divisorVal.toNat
      let quotNat := dividendNat / divisorNat
      let remNat := dividendNat % divisorNat
      if quotNat > 0xFFFFFFFF then
        { s with fault := some .divideError }
      else
        let s' := s.setGpr32 .eax (UInt32.ofNat quotNat)
        let s'' := s'.setGpr32 .edx (UInt32.ofNat remNat)
        let len : UInt64 := (if (reg32Code i.divisor).2 then 1 else 0) + 2
        { s'' with rip := s.rip + len }
  toUops _ := [
    { mnemonic := "DIV.prep", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "DIV.intDiv", uopClass := .intDiv, eligiblePorts := [.p0], latencyCycles := 14, reciprocalThroughput := 10.0 },
    { mnemonic := "DIV.splitQuot", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "DIV.splitRem", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "DIV.flags", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"div {i.divisor}"
  toLean i := s!"div_r32 .{i.divisor}"
  undefinedFlagsMask _ := arithmeticStatusMask
  canFuzzHardware i := hwSafeReg32 i.divisor
  validationOracle i := if hwSafeReg32 i.divisor then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := Id.run do
    let mut states : List X86_64MachineState := []
    let divisors : List UInt32 := [0, 1, 2, 3, 5, 7, 0x10, 0x100, 0x7FFF, 0x8000, 0x7FFFFFFF, 0xFFFFFFFF]
    let dividends : List UInt32 := [0, 1, 2, 10, 100, 0x1000, 0x7FFFFFFF, 0xFFFFFFFF]
    for d in divisors do
      if d != 0 then
        let s : X86_64MachineState := default
        let s := s.setGpr32 .eax 0
        let s := s.setGpr32 .edx d
        let s := s.setGpr32 i.divisor d
        states := states ++ [s]
    for rdxVal in ([1, 0xFFFFFFFF] : List UInt32) do
      let s : X86_64MachineState := default
      let s := s.setGpr32 .eax 123
      let s := s.setGpr32 .edx rdxVal
      let s := s.setGpr32 i.divisor 0
      states := states ++ [s]
    for d in divisors do
      for a in dividends do
        let s : X86_64MachineState := default
        let s := s.setGpr32 .eax a
        let s := s.setGpr32 .edx 0
        let s := s.setGpr32 i.divisor d
        states := states ++ [s]
    (states, rng)
  roundtripCases := allReg32List.map DivR32.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- DIV r32 helper. -/
def div_r32 (r : Reg32) : AnyX86_64Instruction :=
  ⟨DivR32.mk r⟩

/- REF: intel-sdm#vol=2;instr=DIV;part=description -/
/-- DIV r16: Unsigned divide DX:AX by 16-bit general-purpose register. -/
structure DivR16 where
  divisor : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=DIV;part=operation -/
instance : X86_64Instruction DivR16 where
  encode i :=
    let (code, ext) := reg16Code i.divisor
    let rex := if ext then #[makeRex false false false ext] else #[]
    ByteArray.mk (#[0x66] ++ rex ++ #[0xF7, makeModRM 3 6 code])
  step i s :=
    let divisorVal := (s.gprs (reg16To64 i.divisor)).toUInt16
    if divisorVal == 0 then
      { s with fault := some .divideError }
    else
      let dividendNat : Nat := (s.gprs .rdx).toUInt16.toNat * 0x10000 + (s.gprs .rax).toUInt16.toNat
      let divisorNat : Nat := divisorVal.toNat
      let quotNat := dividendNat / divisorNat
      let remNat := dividendNat % divisorNat
      if quotNat > 0xFFFF then
        { s with fault := some .divideError }
      else
        let s' := s.setGpr16 .ax (UInt16.ofNat quotNat)
        let s'' := s'.setGpr16 .dx (UInt16.ofNat remNat)
        let len : UInt64 := 1 + (if (reg16Code i.divisor).2 then 1 else 0) + 2
        { s'' with rip := s.rip + len }
  toUops _ := [
    { mnemonic := "DIV.prep", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "DIV.intDiv", uopClass := .intDiv, eligiblePorts := [.p0], latencyCycles := 14, reciprocalThroughput := 10.0 },
    { mnemonic := "DIV.splitQuot", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "DIV.splitRem", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "DIV.flags", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"div {i.divisor}"
  toLean i := s!"div_r16 .{i.divisor}"
  undefinedFlagsMask _ := arithmeticStatusMask
  canFuzzHardware i := hwSafeReg16 i.divisor
  validationOracle i := if hwSafeReg16 i.divisor then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := Id.run do
    let mut states : List X86_64MachineState := []
    let divisors : List UInt16 := [0, 1, 2, 3, 5, 7, 0x10, 0x100, 0x7FFF, 0x8000, 0xFFFF]
    let dividends : List UInt16 := [0, 1, 2, 10, 100, 0x1000, 0x7FFF, 0xFFFF]
    for d in divisors do
      if d != 0 then
        let s : X86_64MachineState := default
        let s := s.setGpr16 .ax 0
        let s := s.setGpr16 .dx d
        let s := s.setGpr16 i.divisor d
        states := states ++ [s]
    for rdxVal in ([1, 0xFFFF] : List UInt16) do
      let s : X86_64MachineState := default
      let s := s.setGpr16 .ax 123
      let s := s.setGpr16 .dx rdxVal
      let s := s.setGpr16 i.divisor 0
      states := states ++ [s]
    for d in divisors do
      for a in dividends do
        let s : X86_64MachineState := default
        let s := s.setGpr16 .ax a
        let s := s.setGpr16 .dx 0
        let s := s.setGpr16 i.divisor d
        states := states ++ [s]
    (states, rng)
  roundtripCases := allReg16List.map DivR16.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- DIV r16 helper. -/
def div_r16 (r : Reg16) : AnyX86_64Instruction :=
  ⟨DivR16.mk r⟩

/- REF: intel-sdm#vol=2;instr=DIV;part=description -/
/-- DIV r8: Unsigned divide AX by 8-bit general-purpose register. -/
structure DivR8 where
  divisor : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=DIV;part=operation -/
instance : X86_64Instruction DivR8 where
  encode i :=
    let (code, ext, mandatory) := reg8Code i.divisor
    let rex := if ext || mandatory then #[makeRex false false false ext] else #[]
    ByteArray.mk (rex ++ #[0xF6, makeModRM 3 6 code])
  step i s :=
    let divisorVal := (s.gprs (reg8To64 i.divisor)).toUInt8
    if divisorVal == 0 then
      { s with fault := some .divideError }
    else
      let dividendNat : Nat := (s.gprs .rax).toUInt16.toNat
      let divisorNat : Nat := divisorVal.toNat
      let quotNat := dividendNat / divisorNat
      let remNat := dividendNat % divisorNat
      if quotNat > 0xFF then
        { s with fault := some .divideError }
      else
        let quotVal := UInt16.ofNat quotNat
        let remVal := UInt16.ofNat remNat
        let axVal : UInt16 := (remVal <<< 8) ||| quotVal
        let s' := s.setGpr16 .ax axVal
        let len : UInt64 := (if (reg8Code i.divisor).2.1 || (reg8Code i.divisor).2.2 then 1 else 0) + 2
        { s' with rip := s.rip + len }
  toUops _ := [
    { mnemonic := "DIV.prep", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "DIV.intDiv", uopClass := .intDiv, eligiblePorts := [.p0], latencyCycles := 14, reciprocalThroughput := 10.0 },
    { mnemonic := "DIV.splitQuot", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "DIV.splitRem", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "DIV.flags", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"div {i.divisor}"
  toLean i := s!"div_r8 .{i.divisor}"
  undefinedFlagsMask _ := arithmeticStatusMask
  canFuzzHardware i := hwSafeReg8 i.divisor
  validationOracle i := if hwSafeReg8 i.divisor then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := Id.run do
    let mut states : List X86_64MachineState := []
    let divisors : List UInt8 := [0, 1, 2, 3, 5, 7, 0x10, 0x7F, 0x80, 0xFF]
    let dividends : List UInt16 := [0, 1, 2, 10, 100, 0x7F, 0xFF, 0x100, 0xFFFF]
    for d in divisors do
      if d != 0 then
        let s : X86_64MachineState := default
        let s := s.setGpr16 .ax (d.toUInt16 <<< 8)
        let s := s.setGpr8 i.divisor d
        states := states ++ [s]
    for d in divisors do
      for a in dividends do
        let s : X86_64MachineState := default
        let s := s.setGpr16 .ax a
        let s := s.setGpr8 i.divisor d
        states := states ++ [s]
    (states, rng)
  roundtripCases := allReg8List.map DivR8.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- DIV r8 helper. -/
def div_r8 (r : Reg8) : AnyX86_64Instruction :=
  ⟨DivR8.mk r⟩

/- REF: intel-sdm#vol=2;instr=IDIV;part=description -/
/-- IDIV r64: Signed divide RDX:RAX by 64-bit general-purpose register. -/
structure IdivR64 where
  divisor : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IDIV;part=operation -/
instance : X86_64Instruction IdivR64 where
  encode i :=
    let (code, ext) := reg64Code i.divisor
    let rex := makeRex true false false ext
    let modrm := makeModRM 3 7 code
    ByteArray.mk #[rex, 0xF7, modrm]
  step i s :=
    let dVal := s.gprs i.divisor
    let divisorInt : Int := if (dVal >>> 63) == 1 then -(0x10000000000000000 - dVal.toNat : Int) else (dVal.toNat : Int)
    if divisorInt == 0 then
      { s with fault := some .divideError }
    else
      let rdxVal := s.gprs .rdx
      let raxVal := s.gprs .rax
      let u128 : Nat := rdxVal.toNat * 0x10000000000000000 + raxVal.toNat
      let dividendInt : Int := if (rdxVal >>> 63) == 1 then -(0x100000000000000000000000000000000 - u128 : Int) else (u128 : Int)
      let quotInt := dividendInt.tdiv divisorInt
      let remInt := dividendInt.tmod divisorInt
      let minQuot : Int := -0x8000000000000000
      let maxQuot : Int := 0x7FFFFFFFFFFFFFFF
      if quotInt < minQuot || quotInt > maxQuot then
        { s with fault := some .divideError }
      else
        let quotVal : UInt64 := UInt64.ofNat (quotInt % 18446744073709551616).toNat
        let remVal : UInt64 := UInt64.ofNat (remInt % 18446744073709551616).toNat
        let s' := s.setGpr64 .rax quotVal
        let s'' := s'.setGpr64 .rdx remVal
        { s'' with rip := s.rip + 3 }
  toUops _ := [
    { mnemonic := "IDIV.prep", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "IDIV.intDiv", uopClass := .intDiv, eligiblePorts := [.p0], latencyCycles := 14, reciprocalThroughput := 10.0 },
    { mnemonic := "IDIV.splitQuot", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "IDIV.splitRem", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "IDIV.flags", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"idiv {i.divisor}"
  toLean i := s!"idiv_r64 .{i.divisor}"
  undefinedFlagsMask _ := arithmeticStatusMask
  canFuzzHardware i := hwSafeReg64 i.divisor
  validationOracle i := if hwSafeReg64 i.divisor then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := Id.run do
    let mut states : List X86_64MachineState := []
    let divisors : List UInt64 := [0, 1, 2, 3, 5, 0x10, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF]
    let dividends : List UInt64 := [0, 1, 2, 10, 100, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF]
    for d in divisors do
      if d != 0 then
        let s : X86_64MachineState := default
        let s := s.setGpr64 .rax 0
        let s := s.setGpr64 .rdx d
        let s := s.setGpr64 i.divisor d
        states := states ++ [s]
    for d in divisors do
      for a in dividends do
        let s : X86_64MachineState := default
        let s := s.setGpr64 .rax a
        let s := s.setGpr64 .rdx 0
        let s := s.setGpr64 i.divisor d
        states := states ++ [s]
    (states, rng)
  roundtripCases := allReg64List.map IdivR64.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IDIV r64 helper. -/
def idiv_r64 (r : Reg64) : AnyX86_64Instruction :=
  ⟨IdivR64.mk r⟩

/- REF: intel-sdm#vol=2;instr=IDIV;part=description -/
/-- IDIV r32: Signed divide EDX:EAX by 32-bit general-purpose register. -/
structure IdivR32 where
  divisor : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IDIV;part=operation -/
instance : X86_64Instruction IdivR32 where
  encode i :=
    let (code, ext) := reg32Code i.divisor
    let rex := if ext then #[makeRex false false false ext] else #[]
    ByteArray.mk (rex ++ #[0xF7, makeModRM 3 7 code])
  step i s :=
    let dVal := (s.gprs (reg32To64 i.divisor)).toUInt32
    let divisorInt : Int := if (dVal >>> 31) == 1 then -(0x100000000 - dVal.toNat : Int) else (dVal.toNat : Int)
    if divisorInt == 0 then
      { s with fault := some .divideError }
    else
      let edxVal := (s.gprs .rdx).toUInt32
      let eaxVal := (s.gprs .rax).toUInt32
      let u64 : Nat := edxVal.toNat * 0x100000000 + eaxVal.toNat
      let dividendInt : Int := if (edxVal >>> 31) == 1 then -(0x10000000000000000 - u64 : Int) else (u64 : Int)
      let quotInt := dividendInt.tdiv divisorInt
      let remInt := dividendInt.tmod divisorInt
      let minQuot : Int := -0x80000000
      let maxQuot : Int := 0x7FFFFFFF
      if quotInt < minQuot || quotInt > maxQuot then
        { s with fault := some .divideError }
      else
        let quotVal : UInt32 := UInt32.ofNat (quotInt % 4294967296).toNat
        let remVal : UInt32 := UInt32.ofNat (remInt % 4294967296).toNat
        let s' := s.setGpr32 .eax quotVal
        let s'' := s'.setGpr32 .edx remVal
        let len : UInt64 := (if (reg32Code i.divisor).2 then 1 else 0) + 2
        { s'' with rip := s.rip + len }
  toUops _ := [
    { mnemonic := "IDIV.prep", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "IDIV.intDiv", uopClass := .intDiv, eligiblePorts := [.p0], latencyCycles := 14, reciprocalThroughput := 10.0 },
    { mnemonic := "IDIV.splitQuot", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "IDIV.splitRem", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "IDIV.flags", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"idiv {i.divisor}"
  toLean i := s!"idiv_r32 .{i.divisor}"
  undefinedFlagsMask _ := arithmeticStatusMask
  canFuzzHardware i := hwSafeReg32 i.divisor
  validationOracle i := if hwSafeReg32 i.divisor then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := Id.run do
    let mut states : List X86_64MachineState := []
    let divisors : List UInt32 := [0, 1, 2, 3, 5, 0x10, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]
    let dividends : List UInt32 := [0, 1, 2, 10, 100, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]
    for d in divisors do
      if d != 0 then
        let s : X86_64MachineState := default
        let s := s.setGpr32 .eax 0
        let s := s.setGpr32 .edx d
        let s := s.setGpr32 i.divisor d
        states := states ++ [s]
    for d in divisors do
      for a in dividends do
        let s : X86_64MachineState := default
        let s := s.setGpr32 .eax a
        let s := s.setGpr32 .edx 0
        let s := s.setGpr32 i.divisor d
        states := states ++ [s]
    (states, rng)
  roundtripCases := allReg32List.map IdivR32.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IDIV r32 helper. -/
def idiv_r32 (r : Reg32) : AnyX86_64Instruction :=
  ⟨IdivR32.mk r⟩

/- REF: intel-sdm#vol=2;instr=IDIV;part=description -/
/-- IDIV r16: Signed divide DX:AX by 16-bit general-purpose register. -/
structure IdivR16 where
  divisor : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IDIV;part=operation -/
instance : X86_64Instruction IdivR16 where
  encode i :=
    let (code, ext) := reg16Code i.divisor
    let rex := if ext then #[makeRex false false false ext] else #[]
    ByteArray.mk (#[0x66] ++ rex ++ #[0xF7, makeModRM 3 7 code])
  step i s :=
    let dVal := (s.gprs (reg16To64 i.divisor)).toUInt16
    let divisorInt : Int := if (dVal >>> 15) == 1 then -(0x10000 - dVal.toNat : Int) else (dVal.toNat : Int)
    if divisorInt == 0 then
      { s with fault := some .divideError }
    else
      let dxVal := (s.gprs .rdx).toUInt16
      let axVal := (s.gprs .rax).toUInt16
      let u32 : Nat := dxVal.toNat * 0x10000 + axVal.toNat
      let dividendInt : Int := if (dxVal >>> 15) == 1 then -(0x100000000 - u32 : Int) else (u32 : Int)
      let quotInt := dividendInt.tdiv divisorInt
      let remInt := dividendInt.tmod divisorInt
      let minQuot : Int := -0x8000
      let maxQuot : Int := 0x7FFF
      if quotInt < minQuot || quotInt > maxQuot then
        { s with fault := some .divideError }
      else
        let quotVal : UInt16 := UInt16.ofNat (quotInt % 65536).toNat
        let remVal : UInt16 := UInt16.ofNat (remInt % 65536).toNat
        let s' := s.setGpr16 .ax quotVal
        let s'' := s'.setGpr16 .dx remVal
        let len : UInt64 := 1 + (if (reg16Code i.divisor).2 then 1 else 0) + 2
        { s'' with rip := s.rip + len }
  toUops _ := [
    { mnemonic := "IDIV.prep", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "IDIV.intDiv", uopClass := .intDiv, eligiblePorts := [.p0], latencyCycles := 14, reciprocalThroughput := 10.0 },
    { mnemonic := "IDIV.splitQuot", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "IDIV.splitRem", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "IDIV.flags", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"idiv {i.divisor}"
  toLean i := s!"idiv_r16 .{i.divisor}"
  undefinedFlagsMask _ := arithmeticStatusMask
  canFuzzHardware i := hwSafeReg16 i.divisor
  validationOracle i := if hwSafeReg16 i.divisor then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := Id.run do
    let mut states : List X86_64MachineState := []
    let divisors : List UInt16 := [0, 1, 2, 3, 5, 0x10, 0x7FFF, 0x8000, 0xFFFF]
    let dividends : List UInt16 := [0, 1, 2, 10, 100, 0x7FFF, 0x8000, 0xFFFF]
    for d in divisors do
      if d != 0 then
        let s : X86_64MachineState := default
        let s := s.setGpr16 .ax 0
        let s := s.setGpr16 .dx d
        let s := s.setGpr16 i.divisor d
        states := states ++ [s]
    for d in divisors do
      for a in dividends do
        let s : X86_64MachineState := default
        let s := s.setGpr16 .ax a
        let s := s.setGpr16 .dx 0
        let s := s.setGpr16 i.divisor d
        states := states ++ [s]
    (states, rng)
  roundtripCases := allReg16List.map IdivR16.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IDIV r16 helper. -/
def idiv_r16 (r : Reg16) : AnyX86_64Instruction :=
  ⟨IdivR16.mk r⟩

/- REF: intel-sdm#vol=2;instr=IDIV;part=description -/
/-- IDIV r8: Signed divide AX by 8-bit general-purpose register. -/
structure IdivR8 where
  divisor : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IDIV;part=operation -/
instance : X86_64Instruction IdivR8 where
  encode i :=
    let (code, ext, mandatory) := reg8Code i.divisor
    let rex := if ext || mandatory then #[makeRex false false false ext] else #[]
    ByteArray.mk (rex ++ #[0xF6, makeModRM 3 7 code])
  step i s :=
    let dVal := (s.gprs (reg8To64 i.divisor)).toUInt8
    let divisorInt : Int := if (dVal >>> 7) == 1 then -(0x100 - dVal.toNat : Int) else (dVal.toNat : Int)
    if divisorInt == 0 then
      { s with fault := some .divideError }
    else
      let axVal := (s.gprs .rax).toUInt16
      let dividendInt : Int := if (axVal >>> 15) == 1 then -(0x10000 - axVal.toNat : Int) else (axVal.toNat : Int)
      let quotInt := dividendInt.tdiv divisorInt
      let remInt := dividendInt.tmod divisorInt
      let minQuot : Int := -0x80
      let maxQuot : Int := 0x7F
      if quotInt < minQuot || quotInt > maxQuot then
        { s with fault := some .divideError }
      else
        let quotVal : UInt8 := UInt8.ofNat (quotInt % 256).toNat
        let remVal : UInt8 := UInt8.ofNat (remInt % 256).toNat
        let axRes : UInt16 := (remVal.toUInt16 <<< 8) ||| quotVal.toUInt16
        let s' := s.setGpr16 .ax axRes
        let len : UInt64 := (if (reg8Code i.divisor).2.1 || (reg8Code i.divisor).2.2 then 1 else 0) + 2
        { s' with rip := s.rip + len }
  toUops _ := [
    { mnemonic := "IDIV.prep", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "IDIV.intDiv", uopClass := .intDiv, eligiblePorts := [.p0], latencyCycles := 14, reciprocalThroughput := 10.0 },
    { mnemonic := "IDIV.splitQuot", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "IDIV.splitRem", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "IDIV.flags", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"idiv {i.divisor}"
  toLean i := s!"idiv_r8 .{i.divisor}"
  undefinedFlagsMask _ := arithmeticStatusMask
  canFuzzHardware i := hwSafeReg8 i.divisor
  validationOracle i := if hwSafeReg8 i.divisor then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := Id.run do
    let mut states : List X86_64MachineState := []
    let divisors : List UInt8 := [0, 1, 2, 3, 5, 0x10, 0x7F, 0x80, 0xFF]
    let dividends : List UInt16 := [0, 1, 2, 10, 100, 0x7F, 0x80, 0xFF, 0x7FFF, 0x8000, 0xFFFF]
    for d in divisors do
      if d != 0 then
        let s : X86_64MachineState := default
        let s := s.setGpr16 .ax (d.toUInt16 <<< 8)
        let s := s.setGpr8 i.divisor d
        states := states ++ [s]
    for d in divisors do
      for a in dividends do
        let s : X86_64MachineState := default
        let s := s.setGpr16 .ax a
        let s := s.setGpr8 i.divisor d
        states := states ++ [s]
    (states, rng)
  roundtripCases := allReg8List.map IdivR8.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IDIV r8 helper. -/
def idiv_r8 (r : Reg8) : AnyX86_64Instruction :=
  ⟨IdivR8.mk r⟩

/- REF: intel-sdm#vol=2;instr=MUL;part=description -/
/-- MUL r64: Unsigned multiply RAX by 64-bit general-purpose register, storing result in RDX:RAX. -/
structure MulR64 where
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MUL;part=operation -/
instance : X86_64Instruction MulR64 where
  encode i :=
    let (code, ext) := reg64Code i.src
    let rex := makeRex true false false ext
    ByteArray.mk #[rex, 0xF7, makeModRM 3 4 code]
  step i s :=
    let aVal := s.gprs .rax
    let sVal := s.gprs i.src
    let prodNat : Nat := aVal.toNat * sVal.toNat
    let lo64 : UInt64 := UInt64.ofNat prodNat
    let hi64 : UInt64 := UInt64.ofNat (prodNat / 0x10000000000000000)
    let s' := s.setGpr64 .rax lo64
    let s'' := s'.setGpr64 .rdx hi64
    let cf_of : UInt64 := if hi64 != 0 then (((1 : UInt64) <<< 0) ||| ((1 : UInt64) <<< 11)) else 0
    let s''' := { s'' with flags := (s''.flags &&& ~~~arithmeticStatusMask) ||| cf_of }
    { s''' with rip := s.rip + 3 }
  toUops _ := [
    { mnemonic := "MUL.alu", uopClass := .intALU, eligiblePorts := [.p1, .p5], latencyCycles := 3, reciprocalThroughput := 1.0 },
    { mnemonic := "MUL.flags", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"mul {i.src}"
  toLean i := s!"mul_r64 .{i.src}"
  undefinedFlagsMask _ := 0xD4
  canFuzzHardware i := hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng :=
    if i.src == .rax then generateStandardFuzzStatesFor1Reg .rax rng
    else generateStandardFuzzStatesFor2Regs .rax i.src rng
  roundtripCases := allReg64List.map MulR64.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MUL r64 helper. -/
def mul_r64 (r : Reg64) : AnyX86_64Instruction :=
  ⟨MulR64.mk r⟩

/- REF: intel-sdm#vol=2;instr=MUL;part=description -/
/-- MUL r32: Unsigned multiply EAX by 32-bit general-purpose register, storing result in EDX:EAX. -/
structure MulR32 where
  src : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MUL;part=operation -/
instance : X86_64Instruction MulR32 where
  encode i :=
    let (code, ext) := reg32Code i.src
    let rex := if ext then #[makeRex false false false ext] else #[]
    ByteArray.mk (rex ++ #[0xF7, makeModRM 3 4 code])
  step i s :=
    let aVal := s.readGpr32 .eax
    let sVal := s.readGpr32 i.src
    let prodNat : Nat := aVal.toNat * sVal.toNat
    let lo32 : UInt32 := UInt32.ofNat prodNat
    let hi32 : UInt32 := UInt32.ofNat (prodNat / 0x100000000)
    let s' := s.setGpr32 .eax lo32
    let s'' := s'.setGpr32 .edx hi32
    let cf_of : UInt64 := if hi32 != 0 then (((1 : UInt64) <<< 0) ||| ((1 : UInt64) <<< 11)) else 0
    let s''' := { s'' with flags := (s''.flags &&& ~~~arithmeticStatusMask) ||| cf_of }
    let len : UInt64 := (if (reg32Code i.src).2 then 1 else 0) + 2
    { s''' with rip := s.rip + len }
  toUops _ := [
    { mnemonic := "MUL.alu", uopClass := .intALU, eligiblePorts := [.p1, .p5], latencyCycles := 3, reciprocalThroughput := 1.0 },
    { mnemonic := "MUL.flags", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"mul {i.src}"
  toLean i := s!"mul_r32 .{i.src}"
  undefinedFlagsMask _ := 0xD4
  canFuzzHardware i := hwSafeReg32 i.src
  validationOracle i := if hwSafeReg32 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng :=
    if i.src == .eax then generateStandardFuzzStatesFor1Reg .rax rng
    else generateStandardFuzzStatesFor2Regs .rax (reg32To64 i.src) rng
  roundtripCases := allReg32List.map MulR32.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MUL r32 helper. -/
def mul_r32 (r : Reg32) : AnyX86_64Instruction :=
  ⟨MulR32.mk r⟩

/- REF: intel-sdm#vol=2;instr=MUL;part=description -/
/-- MUL r16: Unsigned multiply AX by 16-bit general-purpose register, storing result in DX:AX. -/
structure MulR16 where
  src : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MUL;part=operation -/
instance : X86_64Instruction MulR16 where
  encode i :=
    let (code, ext) := reg16Code i.src
    let rex := if ext then #[makeRex false false false ext] else #[]
    ByteArray.mk (#[0x66] ++ rex ++ #[0xF7, makeModRM 3 4 code])
  step i s :=
    let aVal := s.readGpr16 .ax
    let sVal := s.readGpr16 i.src
    let prodNat : Nat := aVal.toNat * sVal.toNat
    let lo16 : UInt16 := UInt16.ofNat prodNat
    let hi16 : UInt16 := UInt16.ofNat (prodNat / 0x10000)
    let s' := s.setGpr16 .ax lo16
    let s'' := s'.setGpr16 .dx hi16
    let cf_of : UInt64 := if hi16 != 0 then (((1 : UInt64) <<< 0) ||| ((1 : UInt64) <<< 11)) else 0
    let s''' := { s'' with flags := (s''.flags &&& ~~~arithmeticStatusMask) ||| cf_of }
    let len : UInt64 := 1 + (if (reg16Code i.src).2 then 1 else 0) + 2
    { s''' with rip := s.rip + len }
  toUops _ := [
    { mnemonic := "MUL.alu", uopClass := .intALU, eligiblePorts := [.p1, .p5], latencyCycles := 3, reciprocalThroughput := 1.0 },
    { mnemonic := "MUL.flags", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"mul {i.src}"
  toLean i := s!"mul_r16 .{i.src}"
  undefinedFlagsMask _ := 0xD4
  canFuzzHardware i := hwSafeReg16 i.src
  validationOracle i := if hwSafeReg16 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng :=
    if i.src == .ax then generateStandardFuzzStatesFor1Reg .rax rng
    else generateStandardFuzzStatesFor2Regs .rax (reg16To64 i.src) rng
  roundtripCases := allReg16List.map MulR16.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MUL r16 helper. -/
def mul_r16 (r : Reg16) : AnyX86_64Instruction :=
  ⟨MulR16.mk r⟩

/- REF: intel-sdm#vol=2;instr=MUL;part=description -/
/-- MUL r8: Unsigned multiply AL by 8-bit general-purpose register, storing result in AX. -/
structure MulR8 where
  src : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MUL;part=operation -/
instance : X86_64Instruction MulR8 where
  encode i :=
    let (code, ext, mandatory) := reg8Code i.src
    let rex := if ext || mandatory then #[makeRex false false false ext] else #[]
    ByteArray.mk (rex ++ #[0xF6, makeModRM 3 4 code])
  step i s :=
    let aVal := s.readGpr8 .al
    let sVal := s.readGpr8 i.src
    let prodNat : Nat := aVal.toNat * sVal.toNat
    let axVal : UInt16 := UInt16.ofNat prodNat
    let s' := s.setGpr16 .ax axVal
    let hi8 : UInt8 := UInt8.ofNat (prodNat / 0x100)
    let cf_of : UInt64 := if hi8 != 0 then (((1 : UInt64) <<< 0) ||| ((1 : UInt64) <<< 11)) else 0
    let s'' := { s' with flags := (s'.flags &&& ~~~arithmeticStatusMask) ||| cf_of }
    let len : UInt64 := (if (reg8Code i.src).2.1 || (reg8Code i.src).2.2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [
    { mnemonic := "MUL.alu", uopClass := .intALU, eligiblePorts := [.p1, .p5], latencyCycles := 3, reciprocalThroughput := 1.0 },
    { mnemonic := "MUL.flags", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"mul {i.src}"
  toLean i := s!"mul_r8 .{i.src}"
  undefinedFlagsMask _ := 0xD4
  canFuzzHardware i := hwSafeReg8 i.src
  validationOracle i := if hwSafeReg8 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng :=
    if i.src == .al then generateStandardFuzzStatesFor1Reg .rax rng
    else generateStandardFuzzStatesFor2Regs .rax (reg8To64 i.src) rng
  roundtripCases := allReg8List.map MulR8.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MUL r8 helper. -/
def mul_r8 (r : Reg8) : AnyX86_64Instruction :=
  ⟨MulR8.mk r⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
def divDecodeRules : List DecodeRule := [
  -- MUL /4
  { opcode := .one 0xF7, has0x66 := some true, modrmReg := some 4,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "mul_r16: missing ModR/M byte"
      | some m => if m.mod != 3 then .error "divTryDecode: memory operand unsupported" else
        let r := codeToReg16 m.rm ctx.rexB
        .ok (mul_r16 r, m.pos - ctx.startOffset)
  },
  { opcode := .one 0xF6, has0x66 := some false, modrmReg := some 4,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "mul_r8: missing ModR/M byte"
      | some m => if m.mod != 3 then .error "divTryDecode: memory operand unsupported" else
        let r := codeToReg8 m.rm ctx.rexB
        .ok (mul_r8 r, m.pos - ctx.startOffset)
  },
  { opcode := .one 0xF7, has0x66 := some false, rexW := some true, modrmReg := some 4,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "mul_r64: missing ModR/M byte"
      | some m => if m.mod != 3 then .error "divTryDecode: memory operand unsupported" else
        let r := codeToReg64 m.rm ctx.rexB
        .ok (mul_r64 r, m.pos - ctx.startOffset)
  },
  { opcode := .one 0xF7, has0x66 := some false, rexW := some false, modrmReg := some 4,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "mul_r32: missing ModR/M byte"
      | some m => if m.mod != 3 then .error "divTryDecode: memory operand unsupported" else
        let r := codeToReg32 m.rm ctx.rexB
        .ok (mul_r32 r, m.pos - ctx.startOffset)
  },
  -- DIV /6
  { opcode := .one 0xF7, has0x66 := some true, modrmReg := some 6,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "div_r16: missing ModR/M byte"
      | some m => if m.mod != 3 then .error "divTryDecode: memory operand unsupported" else
        let r := codeToReg16 m.rm ctx.rexB
        .ok (div_r16 r, m.pos - ctx.startOffset)
  },
  { opcode := .one 0xF6, has0x66 := some false, modrmReg := some 6,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "div_r8: missing ModR/M byte"
      | some m => if m.mod != 3 then .error "divTryDecode: memory operand unsupported" else
        let r := codeToReg8 m.rm ctx.rexB
        .ok (div_r8 r, m.pos - ctx.startOffset)
  },
  { opcode := .one 0xF7, has0x66 := some false, rexW := some true, modrmReg := some 6,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "div_r64: missing ModR/M byte"
      | some m => if m.mod != 3 then .error "divTryDecode: memory operand unsupported" else
        let r := codeToReg64 m.rm ctx.rexB
        .ok (div_r64 r, m.pos - ctx.startOffset)
  },
  { opcode := .one 0xF7, has0x66 := some false, rexW := some false, modrmReg := some 6,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "div_r32: missing ModR/M byte"
      | some m => if m.mod != 3 then .error "divTryDecode: memory operand unsupported" else
        let r := codeToReg32 m.rm ctx.rexB
        .ok (div_r32 r, m.pos - ctx.startOffset)
  },
  -- IDIV /7
  { opcode := .one 0xF7, has0x66 := some true, modrmReg := some 7,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "idiv_r16: missing ModR/M byte"
      | some m => if m.mod != 3 then .error "divTryDecode: memory operand unsupported" else
        let r := codeToReg16 m.rm ctx.rexB
        .ok (idiv_r16 r, m.pos - ctx.startOffset)
  },
  { opcode := .one 0xF6, has0x66 := some false, modrmReg := some 7,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "idiv_r8: missing ModR/M byte"
      | some m => if m.mod != 3 then .error "divTryDecode: memory operand unsupported" else
        let r := codeToReg8 m.rm ctx.rexB
        .ok (idiv_r8 r, m.pos - ctx.startOffset)
  },
  { opcode := .one 0xF7, has0x66 := some false, rexW := some true, modrmReg := some 7,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "idiv_r64: missing ModR/M byte"
      | some m => if m.mod != 3 then .error "divTryDecode: memory operand unsupported" else
        let r := codeToReg64 m.rm ctx.rexB
        .ok (idiv_r64 r, m.pos - ctx.startOffset)
  },
  { opcode := .one 0xF7, has0x66 := some false, rexW := some false, modrmReg := some 7,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "idiv_r32: missing ModR/M byte"
      | some m => if m.mod != 3 then .error "divTryDecode: memory operand unsupported" else
        let r := codeToReg32 m.rm ctx.rexB
        .ok (idiv_r32 r, m.pos - ctx.startOffset)
  }
]

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the DIV family, evaluating its declarative rules. -/
def divTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  tryDecodeWithRules divDecodeRules bytes offset

end Gasm.Targets.X86_64.Instructions
