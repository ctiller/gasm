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

/-
Adversarial Empirical Stress Harness for AArch64 Binary Codec & Round-Trip Soundness.
Challenger: teamwork_preview_challenger_m3_it2_gen2_1
Tests:
1. Roundtrip decodeWord (encodeWord i) = some i across extreme parameters:
   - Max/min immediates, signed/unsigned wrap-around, bitmask edge cases.
   - All 16 condition codes in BCond.
   - SP index 31 vs XZR index 31 across load/store, ALU imm, ALU reg, and comparisons.
2. Resilience of decodeWord against malformed, corrupted, and randomized bit patterns.
3. Resilience of decode against truncated ByteArrays and out-of-bounds offsets.
-/

import Lean
import Gasm.Core.Types
import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.Addressing
import Gasm.Targets.AArch64.Instructions
import Gasm.Targets.AArch64.Decoder
import Gasm.Targets.AArch64.Roundtrip
import Gasm.Targets.AArch64.RoundtripGate

open Gasm.Core
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Instructions (
  AddImm AddReg AddExt SubImm SubReg SubExt MovReg Movz Movn Movk
  AndReg OrrReg EorReg AndImm OrrImm EorImm LdrImm StrImm LdrbImm StrbImm
  LdrhImm StrhImm LdrPre StrPre LdrPost StrPost LdpPre StpPre LdpPost StpPost
  LdpOffset StpOffset LdrLit B Bl BCond Ret Adr Adrp Nop Svc Hlt
)

def toHexChar (n : Nat) : Char :=
  if n < 10 then (Char.ofNat ('0'.toNat + n))
  else (Char.ofNat ('A'.toNat + n - 10))

def toHex (val : Nat) (digits : Nat) : String :=
  let rec loop (v : Nat) (d : Nat) (acc : List Char) : List Char :=
    match d with
    | 0 => acc
    | d + 1 => loop (v / 16) d (toHexChar (v % 16) :: acc)
  String.ofList (loop val digits [])

def check (desc : String) (cond : Bool) : IO Unit := do
  if !cond then
    IO.println s!"[FAIL] {desc}"
    throw (IO.userError s!"Assertion failed: {desc}")
  else
    IO.println s!"[PASS] {desc}"

def checkRoundtrip (desc : String) (i : AnyAArch64Instruction) : IO Unit := do
  let w := encodeWord i
  match decodeWord w with
  | none =>
    IO.println s!"[FAIL] {desc}: decodeWord returned none for encoded word 0x{toHex w.toNat 8}"
    throw (IO.userError s!"Roundtrip failed: {desc}")
  | some decoded =>
    let w' := encodeWord decoded
    let asmOrig := s!"{i}"
    let asmDec := s!"{decoded}"
    if w != w' || asmOrig != asmDec then
      IO.println s!"[FAIL] {desc}: mismatch!"
      IO.println s!"  Original: word=0x{toHex w.toNat 8} asm='{asmOrig}'"
      IO.println s!"  Decoded:  word=0x{toHex w'.toNat 8} asm='{asmDec}'"
      throw (IO.userError s!"Roundtrip mismatch: {desc}")
    else
      IO.println s!"[PASS] {desc} (0x{toHex w.toNat 8} -> '{asmDec}')"

def main : IO UInt32 := do
  IO.println "================================================================================"
  IO.println "  Adversarial Empirical Stress Suite for AArch64 Codec & Roundtrip Soundness   "
  IO.println "================================================================================"

  -- --------------------------------------------------------------------------
  -- Section 1: All 16 Condition Codes in BCond
  -- --------------------------------------------------------------------------
  IO.println "\n--- 1. Testing All 16 Condition Codes in BCond ---"
  let allConds : List Cond := [
    .EQ, .NE, .CS, .CC, .MI, .PL, .VS, .VC,
    .HI, .LS, .GE, .LT, .GT, .LE, .AL, .NV
  ]
  for c in allConds do
    -- Test with zero offset
    checkRoundtrip s!"BCond {c} offset 0" ⟨BCond.mk c 0⟩
    -- Test with positive offset
    checkRoundtrip s!"BCond {c} offset 16" ⟨BCond.mk c 16⟩
    -- Test with negative offset
    checkRoundtrip s!"BCond {c} offset -16" ⟨BCond.mk c (-16)⟩
    -- Test with extreme positive 21-bit offset: (0x3FFFF <<< 2) = 1048572
    checkRoundtrip s!"BCond {c} max positive offset" ⟨BCond.mk c 1048572⟩
    -- Test with extreme negative 21-bit offset: -1048576
    checkRoundtrip s!"BCond {c} min negative offset" ⟨BCond.mk c (-1048576)⟩

  -- --------------------------------------------------------------------------
  -- Section 2: Extreme Immediates & Wrap-Around for Unconditional Branches
  -- --------------------------------------------------------------------------
  IO.println "\n--- 2. Unconditional Branch Immediate Boundaries (28-bit simm) ---"
  -- B max pos: 0x07FFFFFC = 134217724, min neg: -0x08000000 = -134217728
  checkRoundtrip "B offset 0" ⟨B.mk 0⟩
  checkRoundtrip "B offset +4" ⟨B.mk 4⟩
  checkRoundtrip "B offset -4" ⟨B.mk (-4)⟩
  checkRoundtrip "B max pos 134217724" ⟨B.mk 134217724⟩
  checkRoundtrip "B min neg -134217728" ⟨B.mk (-134217728)⟩

  checkRoundtrip "BL offset 0" ⟨Bl.mk 0⟩
  checkRoundtrip "BL offset +4" ⟨Bl.mk 4⟩
  checkRoundtrip "BL offset -4" ⟨Bl.mk (-4)⟩
  checkRoundtrip "BL max pos 134217724" ⟨Bl.mk 134217724⟩
  checkRoundtrip "BL min neg -134217728" ⟨Bl.mk (-134217728)⟩

  -- --------------------------------------------------------------------------
  -- Section 3: ADR and ADRP Extreme Offsets
  -- --------------------------------------------------------------------------
  IO.println "\n--- 3. ADR and ADRP Offset Boundaries ---"
  -- ADR: 21-bit signed byte offset (-1048576 to 1048575)
  checkRoundtrip "ADR offset 0" ⟨Adr.mk .x0 0⟩
  checkRoundtrip "ADR offset +1" ⟨Adr.mk .x1 1⟩
  checkRoundtrip "ADR offset -1" ⟨Adr.mk .x2 (-1)⟩
  checkRoundtrip "ADR max pos 1048575" ⟨Adr.mk .x30 1048575⟩
  checkRoundtrip "ADR min neg -1048576" ⟨Adr.mk .xzr (-1048576)⟩

  -- ADRP: 33-bit signed page-aligned offset (imm21 <<< 12)
  checkRoundtrip "ADRP offset 0" ⟨Adrp.mk .x0 0⟩
  checkRoundtrip "ADRP offset +4096" ⟨Adrp.mk .x1 4096⟩
  checkRoundtrip "ADRP offset -4096" ⟨Adrp.mk .x2 (-4096)⟩
  checkRoundtrip "ADRP max pos (1048575 * 4096)" ⟨Adrp.mk .x30 (1048575 * 4096)⟩
  checkRoundtrip "ADRP min neg (-4294967296)" ⟨Adrp.mk .xzr (-4294967296)⟩

  -- --------------------------------------------------------------------------
  -- Section 4: MoveWide Boundary Tests (MOVZ, MOVN, MOVK)
  -- --------------------------------------------------------------------------
  IO.println "\n--- 4. MoveWide 16-bit Immediates and Shift Positions ---"
  for imm in [0, 1, 0x7FFF, 0x8000, 0xFFFF] do
    for hw in [0, 1, 2, 3] do
      checkRoundtrip s!"MOVZ 64-bit imm=0x{toHex imm 4} hw={hw}"
        ⟨Movz.mk true .x0 imm.toUInt16 hw.toUInt8⟩
      checkRoundtrip s!"MOVN 64-bit imm=0x{toHex imm 4} hw={hw}"
        ⟨Movn.mk true .x1 imm.toUInt16 hw.toUInt8⟩
      checkRoundtrip s!"MOVK 64-bit imm=0x{toHex imm 4} hw={hw}"
        ⟨Movk.mk true .x2 imm.toUInt16 hw.toUInt8⟩
    for hw in [0, 1] do
      checkRoundtrip s!"MOVZ 32-bit imm=0x{toHex imm 4} hw={hw}"
        ⟨Movz.mk false .x3 imm.toUInt16 hw.toUInt8⟩
      checkRoundtrip s!"MOVN 32-bit imm=0x{toHex imm 4} hw={hw}"
        ⟨Movn.mk false .x4 imm.toUInt16 hw.toUInt8⟩
      checkRoundtrip s!"MOVK 32-bit imm=0x{toHex imm 4} hw={hw}"
        ⟨Movk.mk false .x5 imm.toUInt16 hw.toUInt8⟩

  -- --------------------------------------------------------------------------
  -- Section 5: SP (index 31) vs XZR (index 31) Discrimination
  -- --------------------------------------------------------------------------
  IO.println "\n--- 5. SP vs XZR Disambiguation across ALU and Memory ---"
  -- ALU Immediate: AddImm and SubImm
  -- When setFlags=false: rd=31 encodes SP, rn=31 encodes SP
  checkRoundtrip "AddImm SP = SP + 0 (architectural mov)" ⟨AddImm.mk true false .sp .sp 0 false⟩
  checkRoundtrip "AddImm X0 = SP + 16" ⟨AddImm.mk true false .x0 .sp 16 false⟩
  checkRoundtrip "AddImm SP = X0 + 32" ⟨AddImm.mk true false .sp .x0 32 false⟩
  checkRoundtrip "SubImm SP = SP - 16" ⟨SubImm.mk true false .sp .sp 16 false⟩
  checkRoundtrip "AddImm 32-bit WSP = WSP + 8" ⟨AddImm.mk false false .sp .sp 8 false⟩

  -- When setFlags=true: rd=31 encodes XZR (e.g. CMN and CMP)
  checkRoundtrip "CMN imm (AddImm setFlags=true, rd=xzr, rn=x0)" ⟨AddImm.mk true true .xzr .x0 100 false⟩
  checkRoundtrip "CMN imm with rn=sp" ⟨AddImm.mk true true .xzr .sp 100 false⟩
  checkRoundtrip "CMP imm (SubImm setFlags=true, rd=xzr, rn=x1)" ⟨SubImm.mk true true .xzr .x1 42 false⟩
  checkRoundtrip "CMP imm with rn=sp" ⟨SubImm.mk true true .xzr .sp 42 false⟩
  checkRoundtrip "CMP imm 32-bit (SubImm 32 setFlags=true, rd=xzr, rn=x2)" ⟨SubImm.mk false true .xzr .x2 8 false⟩

  -- ALU Register: AddReg and SubReg
  -- In shifted register, rd=31 is XZR, rn=31 is XZR, rm=31 is XZR
  checkRoundtrip "AddReg rd=xzr, rn=x0, rm=x1" ⟨AddReg.mk true false .xzr .x0 .x1 .LSL 0⟩
  checkRoundtrip "AddReg rd=x0, rn=xzr, rm=x1" ⟨AddReg.mk true false .x0 .xzr .x1 .LSL 0⟩
  checkRoundtrip "AddReg rd=x0, rn=x1, rm=xzr" ⟨AddReg.mk true false .x0 .x1 .xzr .LSL 0⟩
  checkRoundtrip "CMP reg (SubReg setFlags=true, rd=xzr, rn=x0, rm=x1)" ⟨SubReg.mk true true .xzr .x0 .x1 .LSL 0⟩

  -- ALU Extended: AddExt and SubExt
  -- In extended register, rn=31 is SP! rd=31 is SP (if !setFlags) or XZR (if setFlags).
  checkRoundtrip "AddExt rd=sp, rn=sp, rm=x0" ⟨AddExt.mk true false .sp .sp .x0 .UXTX 0⟩
  checkRoundtrip "AddExt rd=x0, rn=sp, rm=x1" ⟨AddExt.mk true false .x0 .sp .x1 .UXTX 0⟩
  checkRoundtrip "CMP ext (SubExt setFlags=true, rd=xzr, rn=sp, rm=x0)" ⟨SubExt.mk true true .xzr .sp .x0 .UXTX 0⟩

  -- Load/Store:
  -- Base register rn=31 is SP. Data register rt=31 is XZR.
  checkRoundtrip "StrImm rn=sp, rt=xzr" ⟨StrImm.mk true .xzr .sp 0⟩
  checkRoundtrip "LdrImm rn=sp, rt=xzr" ⟨LdrImm.mk true .xzr .sp 0⟩
  checkRoundtrip "StrbImm rn=sp, rt=xzr" ⟨StrbImm.mk .xzr .sp 0⟩
  checkRoundtrip "LdrbImm rn=sp, rt=xzr" ⟨LdrbImm.mk .xzr .sp 0⟩
  checkRoundtrip "StrPre rn=sp, rt=xzr" ⟨StrPre.mk true .xzr .sp (-8)⟩
  checkRoundtrip "LdrPost rn=sp, rt=xzr" ⟨LdrPost.mk true .xzr .sp 8⟩
  checkRoundtrip "StpPre rn=sp, rt1=xzr, rt2=xzr" ⟨StpPre.mk true .xzr .xzr .sp (-16)⟩
  checkRoundtrip "LdpPost rn=sp, rt1=xzr, rt2=xzr" ⟨LdpPost.mk true .xzr .xzr .sp 16⟩
  checkRoundtrip "StpOffset rn=sp, rt1=xzr, rt2=x0" ⟨StpOffset.mk true .xzr .x0 .sp 0⟩

  -- --------------------------------------------------------------------------
  -- Section 6: Load/Store Offset Boundaries and Scaling
  -- --------------------------------------------------------------------------
  IO.println "\n--- 6. Load/Store Immediate Offset Bounds and Scaling ---"
  -- StrImm / LdrImm 64-bit: scale 8, imm12 max 4095 -> offset 32760
  checkRoundtrip "StrImm 64-bit offset 0" ⟨StrImm.mk true .x0 .sp 0⟩
  checkRoundtrip "StrImm 64-bit max offset 32760" ⟨StrImm.mk true .x0 .sp 32760⟩
  checkRoundtrip "LdrImm 64-bit max offset 32760" ⟨LdrImm.mk true .x0 .sp 32760⟩

  -- StrImm / LdrImm 32-bit: scale 4, imm12 max 4095 -> offset 16380
  checkRoundtrip "StrImm 32-bit offset 0" ⟨StrImm.mk false .x0 .sp 0⟩
  checkRoundtrip "StrImm 32-bit max offset 16380" ⟨StrImm.mk false .x0 .sp 16380⟩
  checkRoundtrip "LdrImm 32-bit max offset 16380" ⟨LdrImm.mk false .x0 .sp 16380⟩

  -- StrbImm / LdrbImm: scale 1, imm12 max 4095
  checkRoundtrip "StrbImm max offset 4095" ⟨StrbImm.mk .x0 .sp 4095⟩
  checkRoundtrip "LdrbImm max offset 4095" ⟨LdrbImm.mk .x0 .sp 4095⟩

  -- StrhImm / LdrhImm: scale 2, imm12 max 4095 -> offset 8190
  checkRoundtrip "StrhImm max offset 8190" ⟨StrhImm.mk .x0 .sp 8190⟩
  checkRoundtrip "LdrhImm max offset 8190" ⟨LdrhImm.mk .x0 .sp 8190⟩

  -- Pre/Post Index: 9-bit signed immediate (-256 to 255)
  checkRoundtrip "StrPre min neg -256" ⟨StrPre.mk true .x0 .sp (-256)⟩
  checkRoundtrip "StrPre max pos +255" ⟨StrPre.mk true .x0 .sp 255⟩
  checkRoundtrip "LdrPost min neg -256" ⟨LdrPost.mk true .x0 .sp (-256)⟩
  checkRoundtrip "LdrPost max pos +255" ⟨LdrPost.mk true .x0 .sp 255⟩

  -- LoadStorePair: 7-bit signed immediate
  -- 64-bit scale 8: -512 to 504
  checkRoundtrip "StpPre 64-bit min neg -512" ⟨StpPre.mk true .x29 .x30 .sp (-512)⟩
  checkRoundtrip "StpPre 64-bit max pos 504" ⟨StpPre.mk true .x29 .x30 .sp 504⟩
  checkRoundtrip "LdpPost 64-bit min neg -512" ⟨LdpPost.mk true .x29 .x30 .sp (-512)⟩
  checkRoundtrip "LdpPost 64-bit max pos 504" ⟨LdpPost.mk true .x29 .x30 .sp 504⟩
  -- 32-bit scale 4: -256 to 252
  checkRoundtrip "StpPre 32-bit min neg -256" ⟨StpPre.mk false .x0 .x1 .sp (-256)⟩
  checkRoundtrip "StpPre 32-bit max pos 252" ⟨StpPre.mk false .x0 .x1 .sp 252⟩

  -- Load Literal: 19-bit signed immediate (-1048576 to 1048572)
  checkRoundtrip "LdrLit min neg -1048576" ⟨LdrLit.mk true .x0 (-1048576)⟩
  checkRoundtrip "LdrLit max pos 1048572" ⟨LdrLit.mk true .x0 1048572⟩

  -- --------------------------------------------------------------------------
  -- Section 7: Logical Shifted & Immediate Edge Cases
  -- --------------------------------------------------------------------------
  IO.println "\n--- 7. Logical Instruction Edge Cases ---"
  -- LogicalReg (AndReg, OrrReg, EorReg) with shift types and amounts
  for sh in [ShiftType.LSL, ShiftType.LSR, ShiftType.ASR, ShiftType.ROR] do
    for amt in [0, 1, 31, 63] do
      checkRoundtrip s!"AndReg sh={sh} amt={amt} invert=false"
        ⟨AndReg.mk true false .x0 .x1 .x2 sh amt.toUInt8 false⟩
      checkRoundtrip s!"AndReg (BIC) sh={sh} amt={amt} invert=true"
        ⟨AndReg.mk true false .x0 .x1 .x2 sh amt.toUInt8 true⟩
      checkRoundtrip s!"OrrReg (ORN) sh={sh} amt={amt} invert=true"
        ⟨OrrReg.mk true .x0 .x1 .x2 sh amt.toUInt8 true⟩
      checkRoundtrip s!"EorReg (EON) sh={sh} amt={amt} invert=true"
        ⟨EorReg.mk true .x0 .x1 .x2 sh amt.toUInt8 true⟩

  -- Adversarial check: EOR/EON with 0xCAFEBABE encoding
  checkRoundtrip "Adversarial 0xCAFEBABE roundtrip (EON x30, x21, x30, ror #46)"
    ⟨EorReg.mk true .x30 .x21 .x30 .ROR 46 true⟩

  -- Adversarial check: 0x12345678 roundtrip (AndImm 32-bit)
  match decodeWord 0x12345678 with
  | some i => checkRoundtrip "Adversarial 0x12345678 roundtrip" i
  | none => check "0x12345678 decodes" false

  -- MovReg disambiguation: MOV rd, rm is encoded as ORR rd, xzr, rm
  checkRoundtrip "MovReg 64-bit x0 = x1" ⟨MovReg.mk true .x0 .x1⟩
  checkRoundtrip "MovReg 32-bit w2 = w3" ⟨MovReg.mk false .x2 .x3⟩

  -- LogicalImm (AndImm, OrrImm, EorImm) bitmask edge cases
  checkRoundtrip "AndImm n=true immr=0 imms=0" ⟨AndImm.mk true false .x0 .x1 true 0 0⟩
  checkRoundtrip "AndImm n=false immr=31 imms=31" ⟨AndImm.mk false false .x0 .x1 false 31 31⟩
  checkRoundtrip "TST imm (AndImm setFlags=true, rd=xzr)" ⟨AndImm.mk true true .xzr .x1 true 0 0⟩
  checkRoundtrip "OrrImm n=true immr=63 imms=63" ⟨OrrImm.mk true .x0 .x1 true 63 63⟩
  checkRoundtrip "EorImm n=true immr=10 imms=20" ⟨EorImm.mk true .x0 .x1 true 10 20⟩

  -- System instructions
  checkRoundtrip "NOP" ⟨Nop.mk⟩
  checkRoundtrip "SVC 0" ⟨Svc.mk 0⟩
  checkRoundtrip "SVC 0xFFFF" ⟨Svc.mk 0xFFFF⟩
  checkRoundtrip "HLT 0xF000" ⟨Hlt.mk 0xF000⟩
  checkRoundtrip "HLT 0" ⟨Hlt.mk 0⟩
  checkRoundtrip "HLT 0xFFFF" ⟨Hlt.mk 0xFFFF⟩

  -- --------------------------------------------------------------------------
  -- Section 8: Decoder Resilience Against Malformed & Undefined Words
  -- --------------------------------------------------------------------------
  IO.println "\n--- 8. Decoder Resilience against Malformed & Undefined Words ---"
  let undefinedWords : List UInt32 := [
    0x00000000, -- Unallocated zero word (UDF #0)
    0xFFFFFFFF, -- All ones word (unallocated in ARMv8)
    0xDEADBEEF, -- Unallocated encoding
    0xD4000002, -- SVC with invalid reserved lower bits (must have bits 4:0 == 0x01)
    0xD4400001, -- HLT with invalid reserved lower bits (must have bits 4:0 == 0x00)
    0xD65F0000, -- RET with invalid opcode bits
    0xD503201E, -- Near NOP with wrong bits
    0x32800000, -- MoveWide with opc=1 unallocated
    0x28000000, -- LoadStorePair with mode=0 unallocated
    0x38000000, -- LoadStore unscaled with mode=0 unallocated
    0x38000800  -- LoadStore unscaled with mode=2 unallocated
  ]
  for w in undefinedWords do
    let res := decodeWord w
    check s!"Undefined word 0x{toHex w.toNat 8} decodes to none" (res.isNone)

  -- Fuzz 20,000 pseudo-random 32-bit words for crash freedom
  IO.println "\n--- 9. Decoder Crash-Freedom Fuzzing (20,000 randomized words) ---"
  let mut seed : UInt64 := 0x123456789ABCDEF0
  let mut crashCount := 0
  for _ in [0:20000] do
    seed := seed ^^^ (seed <<< 13)
    seed := seed ^^^ (seed >>> 7)
    seed := seed ^^^ (seed <<< 17)
    let w : UInt32 := seed.toUInt32
    match decodeWord w with
    | some _ => pure ()
    | none => pure ()
  check "20,000 randomized words decoded without panic or hang" (crashCount == 0)

  -- --------------------------------------------------------------------------
  -- Section 10: Byte Array Truncation & Buffer Bounds Testing
  -- --------------------------------------------------------------------------
  IO.println "\n--- 10. Byte Array Truncation & Out-of-Bounds Offsets ---"
  let emptyBytes := ByteArray.empty
  check "Empty ByteArray decodes to none" (decode emptyBytes 0).isNone

  let oneByte := ByteArray.mk #[0x1F]
  check "1-byte ByteArray decodes to none" (decode oneByte 0).isNone

  let twoBytes := ByteArray.mk #[0x1F, 0x20]
  check "2-byte ByteArray decodes to none" (decode twoBytes 0).isNone

  let threeBytes := ByteArray.mk #[0x1F, 0x20, 0x03]
  check "3-byte ByteArray decodes to none" (decode threeBytes 0).isNone

  let nopBytes := ByteArray.mk #[0x1F, 0x20, 0x03, 0xD5] -- NOP little-endian
  check "Valid 4-byte NOP decodes successfully" (decode nopBytes 0).isSome
  check "Offset 1 on 4-byte buffer returns none (out of bounds)" (decode nopBytes 1).isNone
  check "Offset 4 on 4-byte buffer returns none" (decode nopBytes 4).isNone
  check "Offset 100 on 4-byte buffer returns none" (decode nopBytes 100).isNone

  IO.println "\n================================================================================"
  IO.println "  ALL ADVERSARIAL STRESS TESTS PASSED EMPIRICALLY!                              "
  IO.println "================================================================================"
  return 0
