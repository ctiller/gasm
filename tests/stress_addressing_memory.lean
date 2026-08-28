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

import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.MemoryCell
import Gasm.Targets.AArch64.Addressing
import Gasm.Targets.AArch64.Machine

open Gasm.Targets.AArch64
open Gasm.Core

structure TestSuiteState where
  total : Nat := 0
  passed : Nat := 0
  failed : Nat := 0
  failures : List String := []

def check (name : String) (cond : Bool) (detail : String := "") (st : TestSuiteState) : TestSuiteState :=
  let total := st.total + 1
  if cond then
    { st with total := total, passed := st.passed + 1 }
  else
    let msg := s!"FAIL: [{name}] {detail}"
    { st with total := total, failed := st.failed + 1, failures := msg :: st.failures }

def runAddressingStressTests (st : TestSuiteState) : IO TestSuiteState := do
  let mut s := st

  -- ---------------------------------------------------------------------------
  -- 1. Addressing Mode: Boundary Immediate Offsets & Negative Offsets
  -- ---------------------------------------------------------------------------

  -- Test 1.1: Immediate offset 0
  let m0 := AArch64AddrMode.immOffset .x0 (int64OfInt 0)
  let (ea0, wb0) := evalAddr m0 (fun r => if r == .x0 then 0x1000 else 0) 0x5000
  s := check "addr_imm_zero" (ea0 == 0x1000 && wb0 == none) s!"ea={ea0}, wb={wb0.isSome}" s

  -- Test 1.2: Positive immediate offset +1
  let m1 := AArch64AddrMode.immOffset .x0 (int64OfInt 1)
  let (ea1, wb1) := evalAddr m1 (fun r => if r == .x0 then 0x1000 else 0) 0x5000
  s := check "addr_imm_pos_1" (ea1 == 0x1001 && wb1 == none) s!"ea={ea1}" s

  -- Test 1.3: Negative immediate offset -1
  let m_neg1 := AArch64AddrMode.immOffset .x0 (int64OfInt (-1))
  let (ea_neg1, wb_neg1) := evalAddr m_neg1 (fun r => if r == .x0 then 0x1000 else 0) 0x5000
  s := check "addr_imm_neg_1" (ea_neg1 == 0x0FFF && wb_neg1 == none) s!"ea={ea_neg1}" s

  -- Test 1.4: 9-bit signed boundaries: +255 and -256
  let m_pos255 := AArch64AddrMode.immOffset .x0 (int64OfInt 255)
  let (ea_pos255, _) := evalAddr m_pos255 (fun r => if r == .x0 then 0x2000 else 0) 0
  s := check "addr_imm_pos_255" (ea_pos255 == (0x2000 : UInt64) + 255) s!"ea={ea_pos255}" s

  let m_neg256 := AArch64AddrMode.immOffset .x0 (int64OfInt (-256))
  let (ea_neg256, _) := evalAddr m_neg256 (fun r => if r == .x0 then 0x2000 else 0) 0
  s := check "addr_imm_neg_256" (ea_neg256 == (0x2000 : UInt64) - 256) s!"ea={ea_neg256}" s

  -- Test 1.5: Out-of-9-bit signed boundaries: +256 and -257
  let m_pos256 := AArch64AddrMode.immOffset .x0 (int64OfInt 256)
  let (ea_pos256, _) := evalAddr m_pos256 (fun r => if r == .x0 then 0x2000 else 0) 0
  s := check "addr_imm_pos_256" (ea_pos256 == (0x2000 : UInt64) + 256) s!"ea={ea_pos256}" s

  let m_neg257 := AArch64AddrMode.immOffset .x0 (int64OfInt (-257))
  let (ea_neg257, _) := evalAddr m_neg257 (fun r => if r == .x0 then 0x2000 else 0) 0
  s := check "addr_imm_neg_257" (ea_neg257 == (0x2000 : UInt64) - 257) s!"ea={ea_neg257}" s

  -- Test 1.6: 12-bit unsigned boundaries: 4095 and scaled 32760
  let m_4095 := AArch64AddrMode.immOffset .x0 (int64OfInt 4095)
  let (ea_4095, _) := evalAddr m_4095 (fun r => if r == .x0 then 0x10000 else 0) 0
  s := check "addr_imm_4095" (ea_4095 == (0x10000 : UInt64) + 4095) s!"ea={ea_4095}" s

  let m_32760 := AArch64AddrMode.immOffset .x0 (int64OfInt 32760)
  let (ea_32760, _) := evalAddr m_32760 (fun r => if r == .x0 then 0x10000 else 0) 0
  s := check "addr_imm_32760" (ea_32760 == (0x10000 : UInt64) + 32760) s!"ea={ea_32760}" s

  -- Test 1.7: 64-bit wrap-around at upper boundary (0xFFFFFFFFFFFFFFFF + 1 = 0)
  let m_wrap_pos := AArch64AddrMode.immOffset .x0 (int64OfInt 1)
  let (ea_wrap_pos, _) := evalAddr m_wrap_pos (fun r => if r == .x0 then 0xFFFFFFFFFFFFFFFF else 0) 0
  s := check "addr_imm_wrap_pos" (ea_wrap_pos == 0) s!"ea={ea_wrap_pos}" s

  -- Test 1.8: 64-bit wrap-around at lower boundary (0 - 1 = 0xFFFFFFFFFFFFFFFF)
  let m_wrap_neg := AArch64AddrMode.immOffset .x0 (int64OfInt (-1))
  let (ea_wrap_neg, _) := evalAddr m_wrap_neg (fun r => if r == .x0 then 0 else 0) 0
  s := check "addr_imm_wrap_neg" (ea_wrap_neg == 0xFFFFFFFFFFFFFFFF) s!"ea={ea_wrap_neg}" s

  -- Test 1.9: Extreme 64-bit boundary immediates: Int64 min and max
  let imm_max := int64OfUInt64 0x7FFFFFFFFFFFFFFF
  let (ea_imm_max, _) := evalAddr (AArch64AddrMode.immOffset .x0 imm_max) (fun r => if r == .x0 then 10 else 0) 0
  s := check "addr_imm_max64" (ea_imm_max == (10 : UInt64) + 0x7FFFFFFFFFFFFFFF) s!"ea={ea_imm_max}" s

  let imm_min := int64OfUInt64 0x8000000000000000
  let (ea_imm_min, _) := evalAddr (AArch64AddrMode.immOffset .x0 imm_min) (fun r => if r == .x0 then 10 else 0) 0
  s := check "addr_imm_min64" (ea_imm_min == (10 : UInt64) + 0x8000000000000000) s!"ea={ea_imm_min}" s

  -- ---------------------------------------------------------------------------
  -- 2. Addressing Mode: Pre-Index & Post-Index Writebacks
  -- ---------------------------------------------------------------------------

  -- Test 2.1: Pre-index writeback with SP and negative offset (typical stack push: [SP, #-16]!)
  let pre_sp := AArch64AddrMode.preIndex .sp (int64OfInt (-16))
  let (pre_ea, pre_wb) := evalAddr pre_sp (fun r => if r == .sp then 0x7FFFFFFF0000 else 0) 0
  s := check "pre_index_sp_neg16_ea" (pre_ea == 0x7FFFFFFEFFF0) s!"pre_ea={pre_ea}" s
  s := check "pre_index_sp_neg16_wb" (pre_wb == some (.sp, 0x7FFFFFFEFFF0)) s!"pre_wb={repr pre_wb}" s
  s := check "pre_index_predicate" (AArch64AddrMode.isPreIndexed pre_sp && AArch64AddrMode.hasWriteback pre_sp) "" s

  -- Apply writeback to AArch64MachineState
  let ms0 : AArch64MachineState := { sp := 0x7FFFFFFF0000 }
  let ms1 := match pre_wb with
    | some (reg, val) => ms0.setReg64 reg val
    | none => ms0
  s := check "pre_index_state_update_sp" (ms1.sp == (0x7FFFFFFEFFF0 : UInt64)) s!"ms1.sp={ms1.sp}" s

  -- Test 2.2: Post-index writeback with SP and positive offset (typical stack pop: [SP], #16)
  let post_sp := AArch64AddrMode.postIndex .sp (int64OfInt 16)
  let (post_ea, post_wb) := evalAddr post_sp (fun r => if r == .sp then 0x7FFFFFFEFFF0 else 0) 0
  -- Post-index effective address must be initial SP (before addition)
  s := check "post_index_sp_pos16_ea" (post_ea == 0x7FFFFFFEFFF0) s!"post_ea={post_ea}" s
  -- Writeback target must be updated SP (after addition)
  s := check "post_index_sp_pos16_wb" (post_wb == some (.sp, 0x7FFFFFFF0000)) s!"post_wb={repr post_wb}" s
  s := check "post_index_predicate" (AArch64AddrMode.isPostIndexed post_sp && AArch64AddrMode.hasWriteback post_sp) "" s

  let ms2 := match post_wb with
    | some (reg, val) => ms1.setReg64 reg val
    | none => ms1
  s := check "post_index_state_update_sp" (ms2.sp == (0x7FFFFFFF0000 : UInt64)) s!"ms2.sp={ms2.sp}" s

  -- Test 2.3: Pre-index and post-index on general registers X0, X1, X29, X30
  let checkReg (reg : Reg64) (st_acc : TestSuiteState) : TestSuiteState :=
    let pre_reg := AArch64AddrMode.preIndex reg (int64OfInt 8)
    let (p_ea, p_wb) := evalAddr pre_reg (fun r => if r == reg then 0x4000 else 0) 0
    let s' := check s!"pre_index_{reg}_ea" (p_ea == 0x4008) s!"ea={p_ea}" st_acc
    let s'' := check s!"pre_index_{reg}_wb" (p_wb == some (reg, 0x4008)) s!"wb={repr p_wb}" s'

    let post_reg := AArch64AddrMode.postIndex reg (int64OfInt (-8))
    let (po_ea, po_wb) := evalAddr post_reg (fun r => if r == reg then 0x4008 else 0) 0
    let s''' := check s!"post_index_{reg}_ea" (po_ea == 0x4008) s!"ea={po_ea}" s''
    check s!"post_index_{reg}_wb" (po_wb == some (reg, 0x4000)) s!"wb={repr po_wb}" s'''

  s := checkReg .x0 s
  s := checkReg .x1 s
  s := checkReg .x29 s
  s := checkReg .x30 s

  -- Test 2.4: Writeback to XZR (architecture specifies XZR discarded)
  let pre_xzr := AArch64AddrMode.preIndex .xzr (int64OfInt 16)
  let (xzr_ea, xzr_wb) := evalAddr pre_xzr (fun r => if r == .xzr then 0 else 0) 0
  s := check "pre_index_xzr_ea" (xzr_ea == 16) s!"ea={xzr_ea}" s
  s := check "pre_index_xzr_wb" (xzr_wb == some (.xzr, 16)) s!"wb={repr xzr_wb}" s
  -- Updating machine state with xzr writeback must be NO-OP
  let ms_xzr : AArch64MachineState := default
  let ms_xzr_updated := match xzr_wb with
    | some (r, v) => ms_xzr.setReg64 r v
    | none => ms_xzr
  s := check "pre_index_xzr_discarded" (ms_xzr_updated.getReg64 .xzr == (0 : UInt64)) "" s

  -- ---------------------------------------------------------------------------
  -- 3. Register Offset Addressing with Shift
  -- ---------------------------------------------------------------------------

  -- Test 3.1: Register offset with no shift
  let ro_no_shift := AArch64AddrMode.regOffset .x1 .x2 none
  let (ro_ea1, ro_wb1) := evalAddr ro_no_shift (fun r => if r == .x1 then 0x1000 else if r == .x2 then 0x20 else 0) 0
  s := check "reg_offset_no_shift" (ro_ea1 == 0x1020 && ro_wb1 == none) s!"ea={ro_ea1}" s

  -- Test 3.2: Register offset with LSL #0, #1, #2, #3
  for shiftAmt in [0, 1, 2, 3] do
    let ro_lsl := AArch64AddrMode.regOffset .x1 .x2 (some (.LSL, shiftAmt))
    let (ro_ea, _) := evalAddr ro_lsl (fun r => if r == .x1 then 0x1000 else if r == .x2 then 0x10 else 0) 0
    let expected : UInt64 := (0x1000 : UInt64) + ((0x10 : UInt64) <<< shiftAmt.toUInt64)
    s := check s!"reg_offset_lsl_{shiftAmt}" (ro_ea == expected) s!"ea={ro_ea}, exp={expected}" s

  -- Test 3.3: Register offset with ASR on negative index value
  let ro_asr := AArch64AddrMode.regOffset .x1 .x2 (some (.ASR, 2))
  -- 0xFFFFFFFFFFFFFFF0 is -16. ASR #2 should give 0xFFFFFFFFFFFFFFFC (-4).
  let (ro_ea_asr, _) := evalAddr ro_asr (fun r => if r == .x1 then 0x1000 else if r == .x2 then 0xFFFFFFFFFFFFFFF0 else 0) 0
  s := check "reg_offset_asr_neg" (ro_ea_asr == (0x1000 : UInt64) + 0xFFFFFFFFFFFFFFFC) s!"ea={ro_ea_asr}" s

  -- Test 3.4: Register offset boundary shift >= 64
  let ro_lsl_64 := AArch64AddrMode.regOffset .x1 .x2 (some (.LSL, 64))
  let (ro_ea_64, _) := evalAddr ro_lsl_64 (fun r => if r == .x1 then 0x1000 else if r == .x2 then 0x1234 else 0) 0
  s := check "reg_offset_lsl_64_zeroes" (ro_ea_64 == 0x1000) s!"ea={ro_ea_64}" s

  -- ---------------------------------------------------------------------------
  -- 4. PC-Relative Literal Addressing
  -- ---------------------------------------------------------------------------
  let lit_pos := AArch64AddrMode.literal (int64OfInt 0x100)
  let (lit_ea_pos, lit_wb_pos) := evalAddr lit_pos (fun _ => 0) 0x4000
  s := check "literal_pos" (lit_ea_pos == 0x4100 && lit_wb_pos == none) s!"ea={lit_ea_pos}" s

  let lit_neg := AArch64AddrMode.literal (int64OfInt (-0x100))
  let (lit_ea_neg, lit_wb_neg) := evalAddr lit_neg (fun _ => 0) 0x4000
  s := check "literal_neg" (lit_ea_neg == 0x3F00 && lit_wb_neg == none) s!"ea={lit_ea_neg}" s

  return s

def runMemoryCellStressTests (st : TestSuiteState) : IO TestSuiteState := do
  let mut s := st

  -- ---------------------------------------------------------------------------
  -- 5. Little-Endian Byte Ordering: 16, 32, and 64-bit Reads/Writes
  -- ---------------------------------------------------------------------------

  -- Test 5.1: 16-bit Little-Endian Exact Byte Decomposition
  -- Value 0x1234 stored at 0x1000:
  -- byte at 0x1000 must be 0x34 (LSB)
  -- byte at 0x1001 must be 0x12 (MSB)
  let mem0 := AArch64Mem.zero
  let mem_w16 := AArch64Mem.write .w16 0x1000 0x1234 mem0
  let b0 := AArch64Mem.readByte mem_w16 0x1000
  let b1 := AArch64Mem.readByte mem_w16 0x1001
  let r16 := AArch64Mem.read .w16 0x1000 mem_w16
  s := check "w16_le_byte0" (b0 == 0x34) s!"b0={b0}" s
  s := check "w16_le_byte1" (b1 == 0x12) s!"b1={b1}" s
  s := check "w16_read_roundtrip" (r16 == 0x1234) s!"r16={r16}" s

  -- Test 5.2: 32-bit Little-Endian Exact Byte Decomposition
  -- Value 0xDEADBEEF stored at 0x2000:
  -- bytes: [0xEF, 0xBE, 0xAD, 0xDE]
  let mem_w32 := AArch64Mem.write .w32 0x2000 0xDEADBEEF mem0
  let b32_0 := AArch64Mem.readByte mem_w32 0x2000
  let b32_1 := AArch64Mem.readByte mem_w32 0x2001
  let b32_2 := AArch64Mem.readByte mem_w32 0x2002
  let b32_3 := AArch64Mem.readByte mem_w32 0x2003
  let r32 := AArch64Mem.read .w32 0x2000 mem_w32
  s := check "w32_le_byte0" (b32_0 == 0xEF) s!"b0={b32_0}" s
  s := check "w32_le_byte1" (b32_1 == 0xBE) s!"b1={b32_1}" s
  s := check "w32_le_byte2" (b32_2 == 0xAD) s!"b2={b32_2}" s
  s := check "w32_le_byte3" (b32_3 == 0xDE) s!"b3={b32_3}" s
  s := check "w32_read_roundtrip" (r32 == 0xDEADBEEF) s!"r32={r32}" s

  -- Test 5.3: 64-bit Little-Endian Exact Byte Decomposition
  -- Value 0x0123456789ABCDEF stored at 0x3000:
  -- bytes: [0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01]
  let val64 : UInt64 := 0x0123456789ABCDEF
  let mem_w64 := AArch64Mem.write .w64 0x3000 val64 mem0
  let expectedBytes : List UInt8 := [0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01]
  let readBytes := (List.range 8).map (fun i => AArch64Mem.readByte mem_w64 (0x3000 + i.toUInt64))
  s := check "w64_le_bytes" (readBytes == expectedBytes) s!"bytes={repr readBytes}" s
  let r64 := AArch64Mem.read .w64 0x3000 mem_w64
  s := check "w64_read_roundtrip" (r64 == val64) s!"r64={r64}" s

  -- Test 5.4: Cross-width sub-reading of 64-bit value
  -- Reading two 32-bit values from 64-bit store:
  -- lower 32 bits: 0x89ABCDEF
  -- upper 32 bits: 0x01234567
  let r32_low := AArch64Mem.read .w32 0x3000 mem_w64
  let r32_high := AArch64Mem.read .w32 0x3004 mem_w64
  s := check "w64_split_32_low" (r32_low == 0x89ABCDEF) s!"low={r32_low}" s
  s := check "w64_split_32_high" (r32_high == 0x01234567) s!"high={r32_high}" s

  -- Reading four 16-bit values from 64-bit store:
  let r16_0 := AArch64Mem.read .w16 0x3000 mem_w64
  let r16_1 := AArch64Mem.read .w16 0x3002 mem_w64
  let r16_2 := AArch64Mem.read .w16 0x3004 mem_w64
  let r16_3 := AArch64Mem.read .w16 0x3006 mem_w64
  s := check "w64_split_16_0" (r16_0 == 0xCDEF) s!"r16_0={r16_0}" s
  s := check "w64_split_16_1" (r16_1 == 0x89AB) s!"r16_1={r16_1}" s
  s := check "w64_split_16_2" (r16_2 == 0x4567) s!"r16_2={r16_2}" s
  s := check "w64_split_16_3" (r16_3 == 0x0123) s!"r16_3={r16_3}" s

  -- Test 5.5: Overlapping Writes (Sub-register write integrity)
  -- Write 64-bit 0xFFFFFFFFFFFFFFFF, then write 16-bit 0x0000 at offset +2
  let mem_overlap := AArch64Mem.write .w16 0x3002 0x0000 mem_w64
  let r64_overlap := AArch64Mem.read .w64 0x3000 mem_overlap
  -- Bytes originally: [0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01]
  -- Offset 2 & 3 replaced with 0x00, 0x00:
  -- Bytes now: [0xEF, 0xCD, 0x00, 0x00, 0x67, 0x45, 0x23, 0x01]
  -- Expected 64-bit integer: 0x012345670000CDEF
  s := check "overlap_w16_in_w64" (r64_overlap == 0x012345670000CDEF) s!"r64_overlap={r64_overlap}" s

  -- Test 5.6: Extreme Bit Patterns
  for pat in [0x0000000000000000, 0xFFFFFFFFFFFFFFFF, 0xAAAAAAAAAAAAAAAA, 0x5555555555555555, 0x8000000000000000, 0x0000000000000001] do
    let m_pat := AArch64Mem.write .w64 0x4000 pat mem0
    let r_pat := AArch64Mem.read .w64 0x4000 m_pat
    s := check s!"pattern_64_{pat}" (r_pat == pat) s!"got={r_pat}" s

  -- ---------------------------------------------------------------------------
  -- 6. Alignment Predicates & Natural Alignment
  -- ---------------------------------------------------------------------------

  -- Test 6.1: 8-bit Alignment (all addresses aligned)
  for a in [0x1000, 0x1001, 0x1002, 0x1003, 0x1007, 0xFFFFFFFFFFFFFFFF] do
    s := check s!"isAligned_w8_{a}" (isAligned a .w8 == true) "" s

  -- Test 6.2: 16-bit Alignment (even addresses aligned, odd unaligned)
  s := check "isAligned_w16_even" (isAligned 0x1000 .w16 == true && isAligned 0x1002 .w16 == true) "" s
  s := check "isAligned_w16_odd" (isAligned 0x1001 .w16 == false && isAligned 0x1003 .w16 == false) "" s

  -- Test 6.3: 32-bit Alignment (multiples of 4 aligned)
  s := check "isAligned_w32_aligned" (isAligned 0x1000 .w32 == true && isAligned 0x1004 .w32 == true) "" s
  s := check "isAligned_w32_unaligned" (isAligned 0x1001 .w32 == false && isAligned 0x1002 .w32 == false && isAligned 0x1003 .w32 == false) "" s

  -- Test 6.4: 64-bit Alignment (multiples of 8 aligned)
  s := check "isAligned_w64_aligned" (isAligned 0x1000 .w64 == true && isAligned 0x1008 .w64 == true) "" s
  for offset in [1, 2, 3, 4, 5, 6, 7] do
    let unaligned_addr : UInt64 := (0x1000 : UInt64) + offset.toUInt64
    s := check s!"isAligned_w64_unaligned_{offset}" (isAligned unaligned_addr .w64 == false) "" s

  -- Test 6.5: Stack Pointer 16-byte Alignment Predicate (AAPCS64 invariant)
  s := check "isSpAligned_0" (isSpAligned 0 == true) "" s
  s := check "isSpAligned_16" (isSpAligned 16 == true && isSpAligned 0x7FFFFFFF0000 == true) "" s
  for sp_offset in [1, 2, 4, 8, 12, 14, 15] do
    let bad_sp : UInt64 := (0x7FFFFFFF0000 : UInt64) + sp_offset.toUInt64
    s := check s!"isSpAligned_bad_{sp_offset}" (isSpAligned bad_sp == false) "" s

  -- Test 6.6: MachineState SP Alignment Predicate
  let ms_good_sp : AArch64MachineState := { sp := 0x7FFFFFFF0000 }
  s := check "ms_isSpAligned_pass" (ms_good_sp.isSpAligned == true && ms_good_sp.checkSpAlignment == true) "" s

  let ms_bad_sp : AArch64MachineState := { sp := 0x7FFFFFFF0008 }
  s := check "ms_isSpAligned_fail" (ms_bad_sp.isSpAligned == false && ms_bad_sp.checkSpAlignment == false) "" s

  -- ---------------------------------------------------------------------------
  -- 7. Unaligned Memory Accesses in Machine Model
  -- ---------------------------------------------------------------------------
  -- Test 7.1: Unaligned 16-bit read/write at odd address (0x1001)
  let mem_unaligned_16 := AArch64Mem.write .w16 0x1001 0xABCD mem0
  let r16_unaligned := AArch64Mem.read .w16 0x1001 mem_unaligned_16
  s := check "unaligned_16_roundtrip" (r16_unaligned == 0xABCD) s!"r16={r16_unaligned}" s
  s := check "unaligned_16_byte0" (AArch64Mem.readByte mem_unaligned_16 0x1001 == 0xCD) "" s
  s := check "unaligned_16_byte1" (AArch64Mem.readByte mem_unaligned_16 0x1002 == 0xAB) "" s

  -- Test 7.2: Unaligned 32-bit read/write at offset +1 (0x1001)
  let mem_unaligned_32 := AArch64Mem.write .w32 0x1001 0x11223344 mem0
  let r32_unaligned := AArch64Mem.read .w32 0x1001 mem_unaligned_32
  s := check "unaligned_32_roundtrip" (r32_unaligned == 0x11223344) s!"r32={r32_unaligned}" s

  -- Test 7.3: Unaligned 64-bit read/write at offset +3 (0x1003)
  let val_unaligned_64 : UInt64 := 0xFEDCBA9876543210
  let mem_unaligned_64 := AArch64Mem.write .w64 0x1003 val_unaligned_64 mem0
  let r64_unaligned := AArch64Mem.read .w64 0x1003 mem_unaligned_64
  s := check "unaligned_64_roundtrip" (r64_unaligned == val_unaligned_64) s!"r64={r64_unaligned}" s

  -- ---------------------------------------------------------------------------
  -- 8. Memory Straddling 64-bit Address Space Wrap-around Boundary
  -- ---------------------------------------------------------------------------
  -- Test 8.1: Write 16-bit value at 0xFFFFFFFFFFFFFFFF (byte 0 at MAX, byte 1 at 0)
  let mem_wrap_16 := AArch64Mem.write .w16 0xFFFFFFFFFFFFFFFF 0xA55A mem0
  let b_max := AArch64Mem.readByte mem_wrap_16 0xFFFFFFFFFFFFFFFF
  let b_zero := AArch64Mem.readByte mem_wrap_16 0
  let r16_wrap := AArch64Mem.read .w16 0xFFFFFFFFFFFFFFFF mem_wrap_16
  s := check "wrap_16_byte_max" (b_max == 0x5A) s!"b_max={b_max}" s
  s := check "wrap_16_byte_zero" (b_zero == 0xA5) s!"b_zero={b_zero}" s
  s := check "wrap_16_read_roundtrip" (r16_wrap == 0xA55A) s!"r16={r16_wrap}" s

  -- Test 8.2: Write 64-bit value straddling the boundary at 0xFFFFFFFFFFFFFFFE (bytes at MAX-1, MAX, 0, 1, 2, 3, 4, 5)
  let val_wrap_64 : UInt64 := 0x0102030405060708
  let mem_wrap_64 := AArch64Mem.write .w64 0xFFFFFFFFFFFFFFFE val_wrap_64 mem0
  let r64_wrap := AArch64Mem.read .w64 0xFFFFFFFFFFFFFFFE mem_wrap_64
  s := check "wrap_64_read_roundtrip" (r64_wrap == val_wrap_64) s!"r64={r64_wrap}" s
  s := check "wrap_64_byte_max_minus_1" (AArch64Mem.readByte mem_wrap_64 0xFFFFFFFFFFFFFFFE == 0x08) "" s
  s := check "wrap_64_byte_max" (AArch64Mem.readByte mem_wrap_64 0xFFFFFFFFFFFFFFFF == 0x07) "" s
  s := check "wrap_64_byte_0" (AArch64Mem.readByte mem_wrap_64 0 == 0x06) "" s
  s := check "wrap_64_byte_5" (AArch64Mem.readByte mem_wrap_64 5 == 0x01) "" s

  -- ---------------------------------------------------------------------------
  -- 9. Memory Access Footprints & Invariants
  -- ---------------------------------------------------------------------------
  let spec_store : AArch64MemAccessSpec := {
    kind := .store,
    width := .w64,
    mode := AArch64AddrMode.preIndex .sp (int64OfInt (-16))
  }
  let fp_addrs := spec_store.addresses (fun r => if r == .sp then 0x7FFFFFFF0000 else 0) 0
  s := check "footprint_store_len" (fp_addrs.length == 8) s!"len={fp_addrs.length}" s
  s := check "footprint_store_start" (fp_addrs[0]! == (0x7FFFFFFEFFF0 : UInt64)) "" s
  s := check "footprint_store_end" (fp_addrs[7]! == (0x7FFFFFFEFFF7 : UInt64)) "" s

  let specs : List AArch64MemAccessSpec := [
    spec_store,
    { kind := .load, width := .w32, mode := AArch64AddrMode.immOffset .x0 (int64OfInt 0x20) }
  ]
  let sf := storeFootprint specs (fun r => if r == .sp then 0x7FFFFFFF0000 else if r == .x0 then 0x1000 else 0) 0
  let lf := loadFootprint specs (fun r => if r == .sp then 0x7FFFFFFF0000 else if r == .x0 then 0x1000 else 0) 0
  s := check "storeFootprint_filter" (sf.length == 8) s!"len={sf.length}" s
  s := check "loadFootprint_filter" (lf.length == 4 && lf[0]! == (0x1020 : UInt64)) s!"len={lf.length}" s

  -- ---------------------------------------------------------------------------
  -- 10. Assembly Formatting & String Representations
  -- ---------------------------------------------------------------------------
  let s_imm0 := toString (AArch64AddrMode.immOffset .x0 (int64OfInt 0))
  s := check "toString_imm0" (s_imm0 == "[x0]") s!"got={s_imm0}" s

  let s_imm_pos := toString (AArch64AddrMode.immOffset .x1 (int64OfInt 16))
  s := check "toString_imm_pos" (s_imm_pos == "[x1, #16]") s!"got={s_imm_pos}" s

  let s_imm_neg := toString (AArch64AddrMode.immOffset .sp (int64OfInt (-16)))
  s := check "toString_imm_neg" (s_imm_neg == "[sp, #-16]") s!"got={s_imm_neg}" s

  let s_pre := toString (AArch64AddrMode.preIndex .sp (int64OfInt (-16)))
  s := check "toString_pre" (s_pre == "[sp, #-16]!") s!"got={s_pre}" s

  let s_post := toString (AArch64AddrMode.postIndex .sp (int64OfInt 16))
  s := check "toString_post" (s_post == "[sp], #16") s!"got={s_post}" s

  let s_reg_noshift := toString (AArch64AddrMode.regOffset .x1 .x2 none)
  s := check "toString_reg_noshift" (s_reg_noshift == "[x1, x2]") s!"got={s_reg_noshift}" s

  let s_reg_shift := toString (AArch64AddrMode.regOffset .x1 .x2 (some (.LSL, 3)))
  s := check "toString_reg_shift" (s_reg_shift == "[x1, x2, lsl #3]") s!"got={s_reg_shift}" s

  let s_lit := toString (AArch64AddrMode.literal (int64OfInt 64))
  s := check "toString_lit" (s_lit == "[pc, #64]") s!"got={s_lit}" s

  -- ---------------------------------------------------------------------------
  -- 11. ExtendType and ShiftType Operations
  -- ---------------------------------------------------------------------------
  s := check "ext_uxtb" (ExtendType.UXTB.apply 0x123456789ABCDEF0 == 0xF0) "" s
  s := check "ext_uxth" (ExtendType.UXTH.apply 0x123456789ABCDEF0 == 0xDEF0) "" s
  s := check "ext_uxtw" (ExtendType.UXTW.apply 0x123456789ABCDEF0 == 0x9ABCDEF0) "" s
  s := check "ext_uxtx" (ExtendType.UXTX.apply 0x123456789ABCDEF0 == 0x123456789ABCDEF0) "" s

  s := check "ext_sxtb_pos" (ExtendType.SXTB.apply 0x7F == 0x7F) "" s
  s := check "ext_sxtb_neg" (ExtendType.SXTB.apply 0x80 == 0xFFFFFFFFFFFFFF80) "" s
  s := check "ext_sxth_pos" (ExtendType.SXTH.apply 0x7FFF == 0x7FFF) "" s
  s := check "ext_sxth_neg" (ExtendType.SXTH.apply 0x8000 == 0xFFFFFFFFFFFF8000) "" s
  s := check "ext_sxtw_pos" (ExtendType.SXTW.apply 0x7FFFFFFF == 0x7FFFFFFF) "" s
  s := check "ext_sxtw_neg" (ExtendType.SXTW.apply 0x80000000 == 0xFFFFFFFF80000000) "" s
  s := check "ext_sxtx" (ExtendType.SXTX.apply 0x8000000000000000 == 0x8000000000000000) "" s

  -- ROR rotation checks
  s := check "ror_0" (ShiftType.ROR.apply 0x0123456789ABCDEF 0 == 0x0123456789ABCDEF) "" s
  s := check "ror_64" (ShiftType.ROR.apply 0x0123456789ABCDEF 64 == 0x0123456789ABCDEF) "" s
  s := check "ror_8" (ShiftType.ROR.apply 0x0123456789ABCDEF 8 == 0xEF0123456789ABCD) "" s

  return s

def main : IO Unit := do
  IO.println "================================================================================"
  IO.println "  AArch64 Addressing Modes & Memory Model Adversarial Stress Test Suite"
  IO.println "================================================================================"

  let st0 : TestSuiteState := {}
  let st1 ← runAddressingStressTests st0
  let st2 ← runMemoryCellStressTests st1

  IO.println "--------------------------------------------------------------------------------"
  IO.println s!"Total Assertions Executed: {st2.total}"
  IO.println s!"Passed:                   {st2.passed}"
  IO.println s!"Failed:                   {st2.failed}"

  if st2.failed > 0 then
    IO.println "Failures encountered:"
    for f in st2.failures do
      IO.println f
    IO.Process.exit 1
  else
    IO.println "All empirical stress tests PASSED successfully!"
    IO.Process.exit 0
