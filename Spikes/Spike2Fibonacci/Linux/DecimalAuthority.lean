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

import Spikes.Spike2Fibonacci.Linux.DecimalPhases

/-!
# Text authority frames for the Spike 2 decimal loops

The decimal loops write only their stack scratch words and caller-owned output bytes.  Linux
text is not an IAT: preserving its eight-byte observations is the physical fact that keeps the
shared x86 dispatcher on the ordinary selected/silent path.  This module records the exact
read-over-write frame needed by the program-owned decimal invariant; it does not grant a
RIP-only shortcut.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.DecimalSegments
open Gasm.Targets.X86_64.DecimalSchedule

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/-- A caller-owned store leaves a lower, non-wrapping eight-byte text observation unchanged. -/
/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
theorem spike2_read64_write_below (width : MemWidth) (memory : X86_64Memory)
    (writeAddress readAddress : UInt64) (value : UInt64)
    (writeNoWrap : writeAddress.toNat + width.bytes ≤ 2 ^ 64)
    (below : readAddress.toNat + 8 ≤ writeAddress.toNat) :
    X86_64Mem.read .w64 readAddress (X86_64Mem.write width writeAddress value memory) =
      X86_64Mem.read .w64 readAddress memory := by
  have offset0 : readAddress.toNat < writeAddress.toNat := by omega
  have offset1 : (readAddress + 1).toNat < writeAddress.toNat := by
    simp [UInt64.toNat_add]
    omega
  have offset2 : (readAddress + 2).toNat < writeAddress.toNat := by
    simp [UInt64.toNat_add]
    omega
  have offset3 : (readAddress + 3).toNat < writeAddress.toNat := by
    simp [UInt64.toNat_add]
    omega
  have offset4 : (readAddress + 4).toNat < writeAddress.toNat := by
    simp [UInt64.toNat_add]
    omega
  have offset5 : (readAddress + 5).toNat < writeAddress.toNat := by
    simp [UInt64.toNat_add]
    omega
  have offset6 : (readAddress + 6).toNat < writeAddress.toNat := by
    simp [UInt64.toNat_add]
    omega
  have offset7 : (readAddress + 7).toNat < writeAddress.toNat := by
    simp [UInt64.toNat_add]
    omega
  unfold X86_64Mem.read
  rw [X86_64Mem.readByte_write_disjoint width writeAddress value memory readAddress writeNoWrap
    (Or.inl offset0)]
  rw [X86_64Mem.readByte_write_disjoint width writeAddress value memory (readAddress + 1) writeNoWrap
    (Or.inl offset1)]
  rw [X86_64Mem.readByte_write_disjoint width writeAddress value memory (readAddress + 2) writeNoWrap
    (Or.inl offset2)]
  rw [X86_64Mem.readByte_write_disjoint width writeAddress value memory (readAddress + 3) writeNoWrap
    (Or.inl offset3)]
  rw [X86_64Mem.readByte_write_disjoint width writeAddress value memory (readAddress + 4) writeNoWrap
    (Or.inl offset4)]
  rw [X86_64Mem.readByte_write_disjoint width writeAddress value memory (readAddress + 5) writeNoWrap
    (Or.inl offset5)]
  rw [X86_64Mem.readByte_write_disjoint width writeAddress value memory (readAddress + 6) writeNoWrap
    (Or.inl offset6)]
  rw [X86_64Mem.readByte_write_disjoint width writeAddress value memory (readAddress + 7) writeNoWrap
    (Or.inl offset7)]

/-- An extraction pass cannot alter an eight-byte text observation below its stack scratch word. -/
/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2_extraction_pass_preserves_text_read64 {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8} {stackLower : UInt64}
    {initial : X86_64MachineState}
    (pass : SelectedExtractionPass (Event := Event) selected indexed backDisp stackLower initial)
    (readAddress : UInt64)
    (writeNoWrap : (initial.rsp - 8).toNat + 8 ≤ 2 ^ 64)
    (below : readAddress.toNat + 8 ≤ (initial.rsp - 8).toNat) :
    (extractionFinal backDisp initial).read64 readAddress = initial.read64 readAddress := by
  change X86_64Mem.read .w64 readAddress (extractionFinal backDisp initial).memory =
    X86_64Mem.read .w64 readAddress initial.memory
  rw [pass.effect.memory]
  apply spike2_read64_write_below .w64 initial.memory (initial.rsp - 8) readAddress
    (UInt64.ofNat ((initial.gprs .rax).toNat % 10) + 0x30)
  · exact writeNoWrap
  · exact below

/-- A reverse-write pass cannot alter an eight-byte text observation below its output byte. -/
/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2_write_pass_preserves_text_read64 {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8}
    {stackUpper outputLimit : UInt64} {initial : X86_64MachineState}
    (pass : SelectedWritePass (Event := Event) selected indexed backDisp stackUpper outputLimit initial)
    (readAddress : UInt64)
    (writeNoWrap : (initial.gprs .rdi).toNat + 1 ≤ 2 ^ 64)
    (below : readAddress.toNat + 8 ≤ (initial.gprs .rdi).toNat) :
    (writeFinal backDisp initial).read64 readAddress = initial.read64 readAddress := by
  change X86_64Mem.read .w64 readAddress (writeFinal backDisp initial).memory =
    X86_64Mem.read .w64 readAddress initial.memory
  rw [pass.effect.memory]
  apply spike2_read64_write_below .w8 initial.memory (initial.gprs .rdi) readAddress
    (initial.read64 initial.rsp).toUInt8.toUInt64
  · exact writeNoWrap
  · exact below

/-- The exact eight-byte observations which keep every decimal-loop control point out of the
Win32-IAT dispatcher path.  This is deliberately a fixed program-owned boundary, not a generic
code-memory abstraction: each field names an actual Linux text coordinate. -/
/- REF: docs/PROOF_TACTICS.md#design-relational-ghost-state -/
structure Spike2DecimalTextAuthority (state : X86_64MachineState) : Prop where
  extractClearHigh : state.read64 (spike2ExtractionAddress .clearHigh) ≠ spike2ExtractionAddress .clearHigh
  extractDivide : state.read64 (spike2ExtractionAddress .divide) ≠ spike2ExtractionAddress .divide
  extractAscii : state.read64 (spike2ExtractionAddress .ascii) ≠ spike2ExtractionAddress .ascii
  extractPush : state.read64 (spike2ExtractionAddress .push) ≠ spike2ExtractionAddress .push
  extractIncrement : state.read64 (spike2ExtractionAddress .increment) ≠ spike2ExtractionAddress .increment
  extractCompare : state.read64 (spike2ExtractionAddress .compare) ≠ spike2ExtractionAddress .compare
  extractBranch : state.read64 (spike2ExtractionAddress .branch) ≠ spike2ExtractionAddress .branch
  extractExit : state.read64 (spike2ExtractionAddress .exit) ≠ spike2ExtractionAddress .exit
  writePop : state.read64 (spike2WriteAddress .pop) ≠ spike2WriteAddress .pop
  writeStore : state.read64 (spike2WriteAddress .store) ≠ spike2WriteAddress .store
  writeAdvance : state.read64 (spike2WriteAddress .advance) ≠ spike2WriteAddress .advance
  writeDecrement : state.read64 (spike2WriteAddress .decrement) ≠ spike2WriteAddress .decrement
  writeBranch : state.read64 (spike2WriteAddress .branch) ≠ spike2WriteAddress .branch
  writeExit : state.read64 (spike2WriteAddress .exit) ≠ spike2WriteAddress .exit

/- The fourteens fields above are intentionally enumerated.  A write can only preserve this
authority if its target is above the entire concrete decimal text range. -/
/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
private theorem spike2_decimal_text_below (upper : Nat) (above : 4198635 ≤ upper) (address : UInt64)
    (member : address = spike2ExtractionAddress .clearHigh ∨ address = spike2ExtractionAddress .divide ∨
      address = spike2ExtractionAddress .ascii ∨ address = spike2ExtractionAddress .push ∨
      address = spike2ExtractionAddress .increment ∨ address = spike2ExtractionAddress .compare ∨
      address = spike2ExtractionAddress .branch ∨ address = spike2ExtractionAddress .exit ∨
      address = spike2WriteAddress .pop ∨ address = spike2WriteAddress .store ∨
      address = spike2WriteAddress .advance ∨ address = spike2WriteAddress .decrement ∨
      address = spike2WriteAddress .branch ∨ address = spike2WriteAddress .exit) :
    address.toNat + 8 ≤ upper := by
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst address <;> simp [spike2ExtractionAddress, spike2WriteAddress] at above ⊢ <;> omega

/- The exact text authority advances through a selected extraction pass. -/
/- REF: docs/PROOF_TACTICS.md#design-relational-ghost-state -/
theorem Spike2DecimalTextAuthority.afterExtraction {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8} {stackLower : UInt64}
    {initial : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority initial)
    (pass : SelectedExtractionPass (Event := Event) selected indexed backDisp stackLower initial)
    (writeNoWrap : (initial.rsp - 8).toNat + 8 ≤ 2 ^ 64)
    (above : 4198635 ≤ (initial.rsp - 8).toNat) :
    Spike2DecimalTextAuthority (extractionFinal backDisp initial) := by
  constructor <;>
    rw [spike2_extraction_pass_preserves_text_read64 pass _ writeNoWrap
      (spike2_decimal_text_below _ above _ (by simp [spike2ExtractionAddress, spike2WriteAddress]))] <;>
    first | exact authority.extractClearHigh | exact authority.extractDivide |
      exact authority.extractAscii | exact authority.extractPush |
      exact authority.extractIncrement | exact authority.extractCompare |
      exact authority.extractBranch | exact authority.extractExit |
      exact authority.writePop | exact authority.writeStore |
      exact authority.writeAdvance | exact authority.writeDecrement |
      exact authority.writeBranch | exact authority.writeExit

/- The exact text authority advances through a selected reverse-write pass. -/
/- REF: docs/PROOF_TACTICS.md#design-relational-ghost-state -/
theorem Spike2DecimalTextAuthority.afterWrite {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8}
    {stackUpper outputLimit : UInt64} {initial : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority initial)
    (pass : SelectedWritePass (Event := Event) selected indexed backDisp stackUpper outputLimit initial)
    (writeNoWrap : (initial.gprs .rdi).toNat + 1 ≤ 2 ^ 64)
    (above : 4198635 ≤ (initial.gprs .rdi).toNat) :
    Spike2DecimalTextAuthority (writeFinal backDisp initial) := by
  constructor <;>
    rw [spike2_write_pass_preserves_text_read64 pass _ writeNoWrap
      (spike2_decimal_text_below _ above _ (by simp [spike2ExtractionAddress, spike2WriteAddress]))] <;>
    first | exact authority.extractClearHigh | exact authority.extractDivide |
      exact authority.extractAscii | exact authority.extractPush |
      exact authority.extractIncrement | exact authority.extractCompare |
      exact authority.extractBranch | exact authority.extractExit |
      exact authority.writePop | exact authority.writeStore |
      exact authority.writeAdvance | exact authority.writeDecrement |
      exact authority.writeBranch | exact authority.writeExit

end Spikes.Spike2Fibonacci.Linux
