/-
Copyright 2026 Google LLC

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
import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.Addressing
import Gasm.Targets.AArch64.Instructions

namespace Gasm.Targets.AArch64

open Gasm.Core
open Gasm.Targets.AArch64.Instructions

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Encodes an AArch64 instruction into a 32-bit machine word via typeclass dispatch. -/
def encodeWord (i : AnyAArch64Instruction) : UInt32 :=
  AArch64Instruction.encodeWord i

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Decodes a 32-bit machine word into an AArch64 instruction, packed in an open existential. -/
def decodeWord (w : UInt32) : Option AnyAArch64Instruction :=
  -- B / BL: bits 30:26 = 00101
  if (w &&& 0x7C000000) == 0x14000000 then
    let isBl := extractBit w 31
    let rawImm26 := (w &&& 0x3FFFFFF).toUInt64
    let simm26 := signExtendToInt64 (rawImm26 <<< 2) 28
    if isBl then some ⟨Bl.mk simm26⟩ else some ⟨B.mk simm26⟩

  -- B.cond: bits 31:24 = 0x54, bit 4 = 0
  else if (w &&& 0xFF000010) == 0x54000000 then
    let cond := Cond.ofCode (w.toUInt8 &&& 0xF)
    let rawImm19 := ((w >>> 5) &&& 0x7FFFF).toUInt64
    let simm19 := signExtendToInt64 (rawImm19 <<< 2) 21
    some ⟨BCond.mk cond simm19⟩

  -- RET: bits 31:10 = 0xD65F08, bits 4:0 = 0
  else if (w &&& 0xFFFFFC1F) == 0xD65F0800 then
    let rn := decodeReg64Data (((w >>> 5) &&& 0x1F).toUInt8)
    some ⟨Ret.mk rn⟩

  -- SVC: bits 31:21 = 0x6A0, bits 4:0 = 0x01
  else if (w &&& 0xFFE0001F) == 0xD4000001 then
    let imm16 := ((w >>> 5) &&& 0xFFFF).toUInt16
    some ⟨Svc.mk imm16⟩

  -- HLT: bits 31:21 = 0x6A2, bits 4:0 = 0x00
  else if (w &&& 0xFFE0001F) == 0xD4400000 then
    let imm16 := ((w >>> 5) &&& 0xFFFF).toUInt16
    some ⟨Hlt.mk imm16⟩

  -- NOP
  else if w == 0xD503201F then
    some ⟨Nop.mk⟩

  -- ADR / ADRP: bits 28:24 = 10000
  else if (w &&& 0x1F000000) == 0x10000000 then
    let isAdrp := extractBit w 31
    let immlo := (w >>> 29) &&& 3
    let immhi := (w >>> 5) &&& 0x7FFFF
    let imm21 := ((immhi <<< 2) ||| immlo).toUInt64
    let rd := decodeReg64Data (w.toUInt8 &&& 0x1F)
    if isAdrp then
      let offset := signExtendToInt64 (imm21 <<< 12) 33
      some ⟨Adrp.mk rd offset⟩
    else
      let offset := signExtendToInt64 imm21 21
      some ⟨Adr.mk rd offset⟩

  -- MoveWide (MOVN, MOVZ, MOVK): bits 28:23 = 100101
  else if (w &&& 0x1F800000) == 0x12800000 then
    let is64 := extractBit w 31
    let opc := (w >>> 29) &&& 3
    let hw := ((w >>> 21) &&& 3).toUInt8
    let imm16 := ((w >>> 5) &&& 0xFFFF).toUInt16
    let rd := decodeReg64Data (w.toUInt8 &&& 0x1F)
    match opc with
    | 0 => some ⟨Movn.mk is64 rd imm16 hw⟩
    | 2 => some ⟨Movz.mk is64 rd imm16 hw⟩
    | 3 => some ⟨Movk.mk is64 rd imm16 hw⟩
    | _ => none

  -- LogicalImm: bits 28:23 = 100100
  else if (w &&& 0x1F800000) == 0x12000000 then
    let is64 := extractBit w 31
    let opc := (w >>> 29) &&& 3
    let n := extractBit w 22
    let immr := ((w >>> 16) &&& 0x3F).toUInt8
    let imms := ((w >>> 10) &&& 0x3F).toUInt8
    let rn := decodeReg64Data (((w >>> 5) &&& 0x1F).toUInt8)
    let rd := decodeReg64Data (w.toUInt8 &&& 0x1F)
    match opc with
    | 0 => some ⟨AndImm.mk is64 false rd rn n immr imms⟩
    | 1 => some ⟨OrrImm.mk is64 rd rn n immr imms⟩
    | 2 => some ⟨EorImm.mk is64 rd rn n immr imms⟩
    | 3 => some ⟨AndImm.mk is64 true rd rn n immr imms⟩
    | _ => none

  -- AddSubImm: bits 28:24 = 10001
  else if (w &&& 0x1F000000) == 0x11000000 then
    let is64 := extractBit w 31
    let isSub := extractBit w 30
    let setFlags := extractBit w 29
    let shift12 := extractBit w 22
    let imm12 := ((w >>> 10) &&& 0xFFF).toUInt64
    let rn := decodeReg64Sp (((w >>> 5) &&& 0x1F).toUInt8)
    let rd := if setFlags then decodeReg64Data (w.toUInt8 &&& 0x1F) else decodeReg64Sp (w.toUInt8 &&& 0x1F)
    if isSub then
      some ⟨SubImm.mk is64 setFlags rd rn imm12 shift12⟩
    else
      some ⟨AddImm.mk is64 setFlags rd rn imm12 shift12⟩

  -- AddSubReg / AddSubExt: bits 28:24 = 01011
  else if (w &&& 0x1F000000) == 0x0B000000 then
    let is64 := extractBit w 31
    let isSub := extractBit w 30
    let setFlags := extractBit w 29
    let isExt := extractBit w 21
    let rm := decodeReg64Data (((w >>> 16) &&& 0x1F).toUInt8)
    let rn := if isExt then decodeReg64Sp (((w >>> 5) &&& 0x1F).toUInt8) else decodeReg64Data (((w >>> 5) &&& 0x1F).toUInt8)
    let rd := if setFlags then decodeReg64Data (w.toUInt8 &&& 0x1F) else if isExt then decodeReg64Sp (w.toUInt8 &&& 0x1F) else decodeReg64Data (w.toUInt8 &&& 0x1F)
    if isExt then
      let ext := extendTypeOfCode ((w >>> 13) &&& 7)
      let amt := ((w >>> 10) &&& 7).toUInt8
      if isSub then
        some ⟨SubExt.mk is64 setFlags rd rn rm ext amt⟩
      else
        some ⟨AddExt.mk is64 setFlags rd rn rm ext amt⟩
    else
      let sh := shiftTypeOfCode ((w >>> 22) &&& 3)
      let amt := ((w >>> 10) &&& 0x3F).toUInt8
      if isSub then
        some ⟨SubReg.mk is64 setFlags rd rn rm sh amt⟩
      else
        some ⟨AddReg.mk is64 setFlags rd rn rm sh amt⟩

  -- LogicalReg: bits 28:24 = 01010
  else if (w &&& 0x1F000000) == 0x0A000000 then
    let is64 := extractBit w 31
    let opc := (w >>> 29) &&& 3
    let sh := shiftTypeOfCode ((w >>> 22) &&& 3)
    let invert := extractBit w 21
    let rm := decodeReg64Data (((w >>> 16) &&& 0x1F).toUInt8)
    let amt := ((w >>> 10) &&& 0x3F).toUInt8
    let rn := decodeReg64Data (((w >>> 5) &&& 0x1F).toUInt8)
    let rd := decodeReg64Data (w.toUInt8 &&& 0x1F)
    if opc == 1 && rn == .xzr && sh == .LSL && amt == 0 && !invert then
      some ⟨MovReg.mk is64 rd rm⟩
    else match opc with
    | 0 => some ⟨AndReg.mk is64 false rd rn rm sh amt invert⟩
    | 1 => some ⟨OrrReg.mk is64 rd rn rm sh amt invert⟩
    | 2 => some ⟨EorReg.mk is64 rd rn rm sh amt invert⟩
    | 3 => some ⟨AndReg.mk is64 true rd rn rm sh amt invert⟩
    | _ => none

  -- LoadStorePair: bits 29:25 = 10100
  else if (w &&& 0x3E000000) == 0x28000000 then
    let opc := (w >>> 30) &&& 3
    let is64 := opc == 2
    let mode := (w >>> 23) &&& 3
    let isLoad := extractBit w 22
    let rawImm7 := ((w >>> 15) &&& 0x7F).toUInt64
    let scale : UInt64 := if is64 then 8 else 4
    let simm7 := signExtendToInt64 (rawImm7 * scale) (7 + if is64 then 3 else 2)
    let rt2 := decodeReg64Data (((w >>> 10) &&& 0x1F).toUInt8)
    let rn := decodeReg64Sp (((w >>> 5) &&& 0x1F).toUInt8)
    let rt1 := decodeReg64Data (w.toUInt8 &&& 0x1F)
    match mode with
    | 1 => if isLoad then some ⟨LdpPost.mk is64 rt1 rt2 rn simm7⟩ else some ⟨StpPost.mk is64 rt1 rt2 rn simm7⟩
    | 2 => if isLoad then some ⟨LdpOffset.mk is64 rt1 rt2 rn simm7⟩ else some ⟨StpOffset.mk is64 rt1 rt2 rn simm7⟩
    | 3 => if isLoad then some ⟨LdpPre.mk is64 rt1 rt2 rn simm7⟩ else some ⟨StpPre.mk is64 rt1 rt2 rn simm7⟩
    | _ => none

  -- LoadStore Literal: bits 29:24 = 011000
  else if (w &&& 0x3F000000) == 0x18000000 then
    let is64 := extractBit w 30
    let rawImm19 := ((w >>> 5) &&& 0x7FFFF).toUInt64
    let simm19 := signExtendToInt64 (rawImm19 <<< 2) 21
    let rt := decodeReg64Data (w.toUInt8 &&& 0x1F)
    some ⟨LdrLit.mk is64 rt simm19⟩

  -- LoadStore Unsigned Imm: bits 29:24 = 111001
  else if (w &&& 0x3F000000) == 0x39000000 then
    let size := (w >>> 30) &&& 3
    let isLoad := extractBit w 22
    let imm12 := ((w >>> 10) &&& 0xFFF).toUInt64
    let rn := decodeReg64Sp (((w >>> 5) &&& 0x1F).toUInt8)
    let rt := decodeReg64Data (w.toUInt8 &&& 0x1F)
    match size with
    | 0 => if isLoad then some ⟨LdrbImm.mk rt rn imm12⟩ else some ⟨StrbImm.mk rt rn imm12⟩
    | 1 => if isLoad then some ⟨LdrhImm.mk rt rn (imm12 * 2)⟩ else some ⟨StrhImm.mk rt rn (imm12 * 2)⟩
    | 2 => if isLoad then some ⟨LdrImm.mk false rt rn (imm12 * 4)⟩ else some ⟨StrImm.mk false rt rn (imm12 * 4)⟩
    | 3 => if isLoad then some ⟨LdrImm.mk true rt rn (imm12 * 8)⟩ else some ⟨StrImm.mk true rt rn (imm12 * 8)⟩
    | _ => none

  -- LoadStore Unscaled / Pre / Post: bits 29:24 = 111000
  else if (w &&& 0x3F000000) == 0x38000000 then
    let size := (w >>> 30) &&& 3
    let is64 := size == 3
    let isLoad := extractBit w 22
    let rawImm9 := ((w >>> 12) &&& 0x1FF).toUInt64
    let simm9 := signExtendToInt64 rawImm9 9
    let mode := (w >>> 10) &&& 3
    let rn := decodeReg64Sp (((w >>> 5) &&& 0x1F).toUInt8)
    let rt := decodeReg64Data (w.toUInt8 &&& 0x1F)
    match mode with
    | 1 => if isLoad then some ⟨LdrPost.mk is64 rt rn simm9⟩ else some ⟨StrPost.mk is64 rt rn simm9⟩
    | 3 => if isLoad then some ⟨LdrPre.mk is64 rt rn simm9⟩ else some ⟨StrPre.mk is64 rt rn simm9⟩
    | _ => none

  -- MoveWide variants: movn (opc 0), movz (opc 2), movk (opc 3)
  -- Load/Store scaling factors: offset / scale on encode, imm12 * scale on decode
  else
    none

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Encodes an AArch64 instruction AST into a 4-byte ByteArray (little-endian). -/
def encode (i : AnyAArch64Instruction) : ByteArray :=
  let w := encodeWord i
  ByteArray.mk #[
    (w &&& 0xFF).toUInt8,
    ((w >>> 8) &&& 0xFF).toUInt8,
    ((w >>> 16) &&& 0xFF).toUInt8,
    ((w >>> 24) &&& 0xFF).toUInt8
  ]

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Decodes an AArch64 instruction from a ByteArray at byte offset `offset`.
    Returns the decoded instruction and the 4 bytes consumed. -/
def decode (bytes : ByteArray) (offset : Nat := 0) : Option (AnyAArch64Instruction × Nat) :=
  if offset + 4 <= bytes.size then
    let b0 := (bytes.get! offset).toUInt32
    let b1 := (bytes.get! (offset + 1)).toUInt32
    let b2 := (bytes.get! (offset + 2)).toUInt32
    let b3 := (bytes.get! (offset + 3)).toUInt32
    let word := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
    match decodeWord word with
    | some instr => some (instr, 4)
    | none => none
  else
    none

end Gasm.Targets.AArch64
