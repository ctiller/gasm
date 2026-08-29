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
import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.Addressing
import Gasm.Targets.AArch64.Machine
import Gasm.Targets.AArch64.Uop

namespace Gasm.Targets.AArch64.Instructions

open Gasm.Core
open Gasm.Targets.AArch64

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Extracts bitfield [hi:lo] from a UInt32 word. -/
def extractBits (w : UInt32) (hi lo : Nat) : UInt32 :=
  (w >>> lo.toUInt32) &&& (((1 : UInt32) <<< (hi - lo + 1).toUInt32) - 1)

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Extracts single bit at position `bit` from a UInt32 word. -/
def extractBit (w : UInt32) (bit : Nat) : Bool :=
  ((w >>> bit.toUInt32) &&& 1) == 1

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Sign-extends an unsigned bitfield of width `bits` to a signed Int64. -/
def signExtendToInt64 (val : UInt64) (bits : Nat) : Int64 :=
  let signBit := (val >>> (bits - 1).toUInt64) &&& 1
  if signBit == 1 then
    let mask := (0xFFFFFFFFFFFFFFFF <<< bits.toUInt64)
    Int64.ofUInt64 (val ||| mask)
  else
    Int64.ofUInt64 val

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Converts ShiftType to its 2-bit instruction encoding code. -/
def shiftTypeCode (st : ShiftType) : UInt32 :=
  match st with
  | .LSL => 0
  | .LSR => 1
  | .ASR => 2
  | .ROR => 3

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Decodes 2-bit instruction field to ShiftType. -/
def shiftTypeOfCode (code : UInt32) : ShiftType :=
  match code &&& 3 with
  | 0 => .LSL
  | 1 => .LSR
  | 2 => .ASR
  | _ => .ROR

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Converts ExtendType to its 3-bit instruction encoding code. -/
def extendTypeCode (et : ExtendType) : UInt32 :=
  match et with
  | .UXTB => 0 | .UXTH => 1 | .UXTW => 2 | .UXTX => 3
  | .SXTB => 4 | .SXTH => 5 | .SXTW => 6 | .SXTX => 7

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Decodes 3-bit instruction field to ExtendType. -/
def extendTypeOfCode (code : UInt32) : ExtendType :=
  match code &&& 7 with
  | 0 => .UXTB | 1 => .UXTH | 2 => .UXTW | 3 => .UXTX
  | 4 => .SXTB | 5 => .SXTH | 6 => .SXTW | _ => .SXTX

/- REF: docs/TARGETS/ARM64.md#instruction-surface-15-core-instruction-families -/
/-- Formats a Reg64 as 64-bit (x0..x30, sp, xzr) or 32-bit (w0..w30, wsp, wzr). -/
def formatReg (is64 : Bool) (r : Reg64) : String :=
  if is64 then r.toString else (reg64To32 r).toString

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Universe-polymorphic typeclass interface for AArch64 machine instruction semantics,
    binary encoding, micro-op decomposition, assembly formatting, and verification metadata. -/
class AArch64Instruction (ι : Type u) where
  encodeWord       : ι → UInt32
  encode           : ι → ByteArray := fun i =>
    let w := encodeWord i
    ByteArray.mk #[
      (w &&& 0xFF).toUInt8,
      ((w >>> 8) &&& 0xFF).toUInt8,
      ((w >>> 16) &&& 0xFF).toUInt8,
      ((w >>> 24) &&& 0xFF).toUInt8
    ]
  step             : ι → AArch64MachineState → AArch64MachineState
  toUops           : ι → List AArch64Uop
  toAssembly       : ι → String
  roundtripCases   : List ι
  validationOracle : ι → AArch64ValidationOracle
  costProvenance   : ι → CoefficientProvenance

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Open existential instruction container packing any type implementing AArch64Instruction. -/
structure AnyAArch64Instruction where
  {α : Type}
  [inst : AArch64Instruction α]
  instr : α

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
instance : AArch64Instruction AnyAArch64Instruction where
  encodeWord pkg := @AArch64Instruction.encodeWord pkg.α pkg.inst pkg.instr
  encode pkg := @AArch64Instruction.encode pkg.α pkg.inst pkg.instr
  step pkg s := @AArch64Instruction.step pkg.α pkg.inst pkg.instr s
  toUops pkg := @AArch64Instruction.toUops pkg.α pkg.inst pkg.instr
  toAssembly pkg := @AArch64Instruction.toAssembly pkg.α pkg.inst pkg.instr
  roundtripCases := []
  validationOracle pkg := @AArch64Instruction.validationOracle pkg.α pkg.inst pkg.instr
  costProvenance pkg := @AArch64Instruction.costProvenance pkg.α pkg.inst pkg.instr

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
instance : ToString AnyAArch64Instruction where
  toString pkg := AArch64Instruction.toAssembly pkg

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
instance : BEq AnyAArch64Instruction where
  beq a b :=
    AArch64Instruction.encodeWord a == AArch64Instruction.encodeWord b &&
    AArch64Instruction.toAssembly a == AArch64Instruction.toAssembly b

end Gasm.Targets.AArch64.Instructions

namespace Gasm.Targets.AArch64

open Gasm.Targets.AArch64.Instructions

/- REF: docs/TARGETS/ARM64.md#instruction-surface-15-core-instruction-families -/
/-- Standard AArch64 instruction typeclass alias. -/
abbrev AArch64Instruction := Gasm.Targets.AArch64.Instructions.AArch64Instruction

/- REF: docs/TARGETS/ARM64.md#instruction-surface-15-core-instruction-families -/
/-- Standard AArch64 open existential instruction container alias. -/
abbrev AnyAArch64Instruction := Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction

/- REF: docs/TARGETS/ARM64.md#instruction-surface-15-core-instruction-families -/
/-- AArch64 instruction alias shorthand. -/
abbrev AArch64Instr := AnyAArch64Instruction

end Gasm.Targets.AArch64
