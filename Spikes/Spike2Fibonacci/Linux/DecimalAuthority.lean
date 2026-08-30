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

open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
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

/-- The first extraction successor reaches the concrete DIV text instruction without changing
memory, so the program-owned text authority supplies its dispatcher fact. -/
/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
private theorem spike2_extraction_xor_ordinary (initial : X86_64MachineState)
    (entry : initial.rip = spike2ExtractionAddress .clearHigh)
    (authority : Spike2DecimalTextAuthority initial) :
    Spike2OrdinaryCode (extractionStates initial).1 := by
  constructor
  · change initial.rip + 2 ≠ Gasm.Targets.X86_64.Instructions.linuxSyscallEntry
    rw [entry]
    decide
  · rw [show (extractionStates initial).1.rip = initial.rip + 2 by rfl]
    change X86_64Mem.read .w64 (initial.rip + 2) (extractionStates initial).1.memory ≠
      initial.rip + 2
    rw [show (extractionStates initial).1.memory = initial.memory by rfl]
    rw [entry]
    exact authority.extractDivide

/- The DIV instruction has a genuinely conditional core, so its fallthrough uses the explicit
execution-safety evidence rather than assuming that a placed instruction advanced. -/
/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
private theorem spike2_extraction_div_fallthrough (state : X86_64MachineState)
    (safe : (X86_64Instruction.step (div_r64 .r10) state).fault = none) :
    (X86_64Instruction.step (div_r64 .r10) state).rip = state.rip + 3 := by
  let core : X86_64MachineState :=
    { state with stdinBuffer := ByteArray.empty, incomingRequests := [] }
  change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
    { divisor := .r10 } core).fault = none at safe
  change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
    { divisor := .r10 } core).rip = state.rip + 3
  simp only [X86_64Instruction.step] at safe ⊢
  split at safe
  · contradiction
  · rename_i hnonzero
    split at safe
    · contradiction
    · rename_i hfits
      simp [hnonzero, hfits, core]

/- The program-owned link witness turns each non-branch successor into its exact Spike 2 text
coordinate.  This is deliberately local to the decimal authority proof: it does not turn RIP
placement into a dispatcher policy. -/
/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
private theorem spike2_extraction_reached_addresses (initial : X86_64MachineState)
    (entry : initial.rip = spike2ExtractionAddress .clearHigh)
    (safe : ExtractionExecutionSafety 236 initial) :
    (extractionStates initial).1.rip = spike2ExtractionAddress .divide ∧
    (extractionStates initial).2.1.rip = spike2ExtractionAddress .ascii ∧
    (extractionStates initial).2.2.1.rip = spike2ExtractionAddress .push ∧
    (extractionStates initial).2.2.2.1.rip = spike2ExtractionAddress .increment ∧
    (extractionStates initial).2.2.2.2.1.rip = spike2ExtractionAddress .compare ∧
    (extractionStates initial).2.2.2.2.2.rip = spike2ExtractionAddress .branch := by
  have h1 : (extractionStates initial).1.rip = spike2ExtractionAddress .divide := by
    rw [show (extractionStates initial).1.rip = initial.rip + 2 by rfl, entry]
    decide
  have h2 : (extractionStates initial).2.1.rip = spike2ExtractionAddress .ascii := by
    have divSafe : (X86_64Instruction.step (div_r64 .r10) (extractionStates initial).1).fault = none :=
      safe.divSafe
    rw [show (extractionStates initial).2.1.rip =
      (X86_64Instruction.step (div_r64 .r10) (extractionStates initial).1).rip by rfl,
      spike2_extraction_div_fallthrough _ divSafe, h1]
    decide
  have h3 : (extractionStates initial).2.2.1.rip = spike2ExtractionAddress .push := by
    rw [show (extractionStates initial).2.2.1.rip =
      (extractionStates initial).2.1.rip + 4 by rfl, h2]
    decide
  have h4 : (extractionStates initial).2.2.2.1.rip = spike2ExtractionAddress .increment := by
    rw [show (extractionStates initial).2.2.2.1.rip =
      (extractionStates initial).2.2.1.rip + 1 by rfl, h3]
    decide
  have h5 : (extractionStates initial).2.2.2.2.1.rip = spike2ExtractionAddress .compare := by
    rw [show (extractionStates initial).2.2.2.2.1.rip =
      (extractionStates initial).2.2.2.1.rip + 4 by rfl, h4]
    decide
  have h6 : (extractionStates initial).2.2.2.2.2.rip = spike2ExtractionAddress .branch := by
    rw [show (extractionStates initial).2.2.2.2.2.rip =
      (extractionStates initial).2.2.2.2.1.rip + 4 by rfl, h5]
    decide
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/- A reached state with unchanged memory inherits exactly the one named text observation that
belongs to its concrete RIP.  The separate RIP and memory equalities prevent this helper from
being an address-only dispatcher shortcut. -/
/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
private theorem spike2_ordinary_from_initial_memory (initial state : X86_64MachineState)
    (address : UInt64) (rip : state.rip = address) (memory : state.memory = initial.memory)
    (notLinux : address ≠ Gasm.Targets.X86_64.Instructions.linuxSyscallEntry)
    (notIat : initial.read64 address ≠ address) : Spike2OrdinaryCode state := by
  constructor
  · rw [rip]
    exact notLinux
  · rw [rip]
    change X86_64Mem.read .w64 address state.memory ≠ address
    rw [memory]
    exact notIat

/- The PUSH-written stack word is the only extraction memory mutation.  This frame transports a
named lower text observation across that exact write; callers must still provide the concrete
RIP and non-Linux-entry facts. -/
/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
private theorem spike2_ordinary_from_stack_write (initial state : X86_64MachineState)
    (address writeAddress value : UInt64) (rip : state.rip = address)
    (memory : state.memory = X86_64Mem.write .w64 writeAddress value initial.memory)
    (writeNoWrap : writeAddress.toNat + 8 ≤ 2 ^ 64)
    (below : address.toNat + 8 ≤ writeAddress.toNat)
    (notLinux : address ≠ Gasm.Targets.X86_64.Instructions.linuxSyscallEntry)
    (notIat : initial.read64 address ≠ address) : Spike2OrdinaryCode state := by
  constructor
  · rw [rip]
    exact notLinux
  · rw [rip]
    change X86_64Mem.read .w64 address state.memory ≠ address
    rw [memory, spike2_read64_write_below .w64 initial.memory writeAddress address value writeNoWrap below]
    exact notIat

/- The remaining extraction instructions and JNE do not write memory; this ties the PUSH
intermediate observation to the already proved completed extraction effect. -/
/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
private theorem spike2_extraction_push_memory_eq_final (initial : X86_64MachineState) :
    (extractionStates initial).2.2.2.1.memory = (extractionFinal 236 initial).memory := by
  rfl

/-- PUSH reaches the increment coordinate with the exact completed-pass stack-write frame. -/
/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
private theorem spike2_extraction_push_ordinary {stackLower : UInt64}
    (initial : X86_64MachineState) (entry : initial.rip = spike2ExtractionAddress .clearHigh)
    (authority : Spike2DecimalTextAuthority initial) (safety : ExtractionSafety stackLower initial)
    (safe : ExtractionExecutionSafety 236 initial)
    (writeNoWrap : (initial.rsp - 8).toNat + 8 ≤ 2 ^ 64)
    (above : 4198635 ≤ (initial.rsp - 8).toNat) :
    Spike2OrdinaryCode (extractionStates initial).2.2.2.1 := by
  obtain ⟨_, _, _, rip, _, _⟩ := spike2_extraction_reached_addresses initial entry safe
  apply spike2_ordinary_from_stack_write initial _ (spike2ExtractionAddress .increment)
    (initial.rsp - 8) (UInt64.ofNat ((initial.gprs .rax).toNat % 10) + 0x30) rip
  · rw [spike2_extraction_push_memory_eq_final, (extractionPassEffect 236 stackLower initial safety safe).memory]
  · exact writeNoWrap
  · exact spike2_decimal_text_below _ above _ (by simp [spike2ExtractionAddress, spike2WriteAddress])
  · decide
  · exact authority.extractIncrement

/-- The increment successor keeps the completed extraction stack-write frame at CMP. -/
/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
private theorem spike2_extraction_count_ordinary {stackLower : UInt64}
    (initial : X86_64MachineState) (entry : initial.rip = spike2ExtractionAddress .clearHigh)
    (authority : Spike2DecimalTextAuthority initial) (safety : ExtractionSafety stackLower initial)
    (safe : ExtractionExecutionSafety 236 initial)
    (writeNoWrap : (initial.rsp - 8).toNat + 8 ≤ 2 ^ 64)
    (above : 4198635 ≤ (initial.rsp - 8).toNat) :
    Spike2OrdinaryCode (extractionStates initial).2.2.2.2.1 := by
  obtain ⟨_, _, _, _, rip, _⟩ := spike2_extraction_reached_addresses initial entry safe
  apply spike2_ordinary_from_stack_write initial _ (spike2ExtractionAddress .compare)
    (initial.rsp - 8) (UInt64.ofNat ((initial.gprs .rax).toNat % 10) + 0x30) rip
  · rw [show (extractionStates initial).2.2.2.2.1.memory =
      (extractionFinal 236 initial).memory by rfl,
      (extractionPassEffect 236 stackLower initial safety safe).memory]
  · exact writeNoWrap
  · exact spike2_decimal_text_below _ above _ (by simp [spike2ExtractionAddress, spike2WriteAddress])
  · decide
  · exact authority.extractCompare

/-- CMP reaches the linked JNE coordinate without touching the completed extraction frame. -/
/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
private theorem spike2_extraction_cmp_ordinary {stackLower : UInt64}
    (initial : X86_64MachineState) (entry : initial.rip = spike2ExtractionAddress .clearHigh)
    (authority : Spike2DecimalTextAuthority initial) (safety : ExtractionSafety stackLower initial)
    (safe : ExtractionExecutionSafety 236 initial)
    (writeNoWrap : (initial.rsp - 8).toNat + 8 ≤ 2 ^ 64)
    (above : 4198635 ≤ (initial.rsp - 8).toNat) :
    Spike2OrdinaryCode (extractionStates initial).2.2.2.2.2 := by
  obtain ⟨_, _, _, _, _, rip⟩ := spike2_extraction_reached_addresses initial entry safe
  apply spike2_ordinary_from_stack_write initial _ (spike2ExtractionAddress .branch)
    (initial.rsp - 8) (UInt64.ofNat ((initial.gprs .rax).toNat % 10) + 0x30) rip
  · rw [show (extractionStates initial).2.2.2.2.2.memory =
      (extractionFinal 236 initial).memory by rfl,
      (extractionPassEffect 236 stackLower initial safety safe).memory]
  · exact writeNoWrap
  · exact spike2_decimal_text_below _ above _ (by simp [spike2ExtractionAddress, spike2WriteAddress])
  · decide
  · exact authority.extractBranch

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
private theorem spike2_extraction_branch_rip_taken (initial : X86_64MachineState)
    (entry : initial.rip = spike2ExtractionAddress .clearHigh)
    (safe : ExtractionExecutionSafety 236 initial)
    (taken : X86BranchCondition.notEqual.holds (extractionStates initial).2.2.2.2.2) :
    (extractionFinal 236 initial).rip = spike2ExtractionAddress .clearHigh := by
  obtain ⟨_, _, _, _, _, branchRip⟩ := spike2_extraction_reached_addresses initial entry safe
  change (if !(extractionStates initial).2.2.2.2.2.zf then
      (extractionStates initial).2.2.2.2.2.rip + 2 + signExtend8To64 236 else
      (extractionStates initial).2.2.2.2.2.rip + 2) = spike2ExtractionAddress .clearHigh
  change (extractionStates initial).2.2.2.2.2.zf = false at taken
  simp [taken]
  rw [branchRip]
  exact spike2ExtractionLinkedLayout.takenTarget

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
private theorem spike2_extraction_branch_rip_fallthrough (initial : X86_64MachineState)
    (entry : initial.rip = spike2ExtractionAddress .clearHigh)
    (safe : ExtractionExecutionSafety 236 initial)
    (fallthrough : ¬ X86BranchCondition.notEqual.holds (extractionStates initial).2.2.2.2.2) :
    (extractionFinal 236 initial).rip = spike2ExtractionAddress .exit := by
  obtain ⟨_, _, _, _, _, branchRip⟩ := spike2_extraction_reached_addresses initial entry safe
  change (if !(extractionStates initial).2.2.2.2.2.zf then
      (extractionStates initial).2.2.2.2.2.rip + 2 + signExtend8To64 236 else
      (extractionStates initial).2.2.2.2.2.rip + 2) = spike2ExtractionAddress .exit
  change ¬ (extractionStates initial).2.2.2.2.2.zf = false at fallthrough
  have zf : (extractionStates initial).2.2.2.2.2.zf = true := by
    cases h : (extractionStates initial).2.2.2.2.2.zf <;> simp [h] at fallthrough ⊢
  simp [zf]
  rw [branchRip]
  exact spike2ExtractionLinkedLayout.falseFallthrough

/-- The DIV successor is still ordinary Linux code: its read64 observation is the original
ASCII instruction observation, proved via the concrete no-memory-write theorem. -/
/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
private theorem spike2_extraction_div_ordinary (initial : X86_64MachineState)
    (entry : initial.rip = spike2ExtractionAddress .clearHigh)
    (authority : Spike2DecimalTextAuthority initial)
    (safe : ExtractionExecutionSafety 236 initial) :
    Spike2OrdinaryCode (extractionStates initial).2.1 := by
  have rip : (extractionStates initial).2.1.rip = spike2ExtractionAddress .ascii := by
    change (X86_64Instruction.step (div_r64 .r10) (extractionStates initial).1).rip = _
    have divSafe : (X86_64Instruction.step (div_r64 .r10) (extractionStates initial).1).fault = none :=
      safe.divSafe
    have divRip := spike2_extraction_div_fallthrough (extractionStates initial).1 divSafe
    rw [divRip]
    rw [show (extractionStates initial).1.rip = initial.rip + 2 by rfl, entry]
    decide
  constructor
  · rw [rip]
    decide
  · rw [rip]
    change X86_64Mem.read .w64 (spike2ExtractionAddress .ascii)
      (extractionStates initial).2.1.memory ≠ spike2ExtractionAddress .ascii
    rw [extractionAfterDiv_preservesMemory initial]
    exact authority.extractAscii

/-- The ASCII-add successor reaches PUSH with the unchanged concrete Linux text observation. -/
/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
private theorem spike2_extraction_ascii_ordinary (initial : X86_64MachineState)
    (entry : initial.rip = spike2ExtractionAddress .clearHigh)
    (authority : Spike2DecimalTextAuthority initial)
    (safe : ExtractionExecutionSafety 236 initial) :
    Spike2OrdinaryCode (extractionStates initial).2.2.1 := by
  obtain ⟨_, _, rip, _, _, _⟩ := spike2_extraction_reached_addresses initial entry safe
  apply spike2_ordinary_from_initial_memory initial _ (spike2ExtractionAddress .push) rip
  · rw [show (extractionStates initial).2.2.1.memory =
      (extractionStates initial).2.1.memory by rfl]
    exact extractionAfterDiv_preservesMemory initial
  · decide
  · exact authority.extractPush

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2ExtractionOrdinary_of_textAuthority {stackLower : UInt64}
    (initial : X86_64MachineState) (entry : initial.rip = spike2ExtractionAddress .clearHigh)
    (authority : Spike2DecimalTextAuthority initial) (safety : ExtractionSafety stackLower initial)
    (safe : ExtractionExecutionSafety 236 initial)
    (branch : X86BranchCondition.notEqual.holds (extractionStates initial).2.2.2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds (extractionStates initial).2.2.2.2.2)
    (writeNoWrap : (initial.rsp - 8).toNat + 8 ≤ 2 ^ 64)
    (above : 4198635 ≤ (initial.rsp - 8).toNat) : Spike2ExtractionOrdinary 236 initial := by
  refine ⟨spike2_extraction_xor_ordinary initial entry authority,
    spike2_extraction_div_ordinary initial entry authority safe,
    spike2_extraction_ascii_ordinary initial entry authority safe,
    spike2_extraction_push_ordinary initial entry authority safety safe writeNoWrap above,
    spike2_extraction_count_ordinary initial entry authority safety safe writeNoWrap above,
    spike2_extraction_cmp_ordinary initial entry authority safety safe writeNoWrap above, ?_⟩
  have memory := (extractionPassEffect 236 stackLower initial safety safe).memory
  rcases branch with taken | fallthrough
  · exact spike2_ordinary_from_stack_write initial _ (spike2ExtractionAddress .clearHigh)
      (initial.rsp - 8) (UInt64.ofNat ((initial.gprs .rax).toNat % 10) + 0x30)
      (spike2_extraction_branch_rip_taken initial entry safe taken) memory writeNoWrap
      (spike2_decimal_text_below _ above _ (by simp [spike2ExtractionAddress, spike2WriteAddress]))
      (by decide) authority.extractClearHigh
  · exact spike2_ordinary_from_stack_write initial _ (spike2ExtractionAddress .exit)
      (initial.rsp - 8) (UInt64.ofNat ((initial.gprs .rax).toNat % 10) + 0x30)
      (spike2_extraction_branch_rip_fallthrough initial entry safe fallthrough) memory writeNoWrap
      (spike2_decimal_text_below _ above _ (by simp [spike2ExtractionAddress, spike2WriteAddress]))
      (by decide) authority.extractExit

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
private theorem spike2_ordinary_from_output_write (initial state : X86_64MachineState)
    (address writeAddress value : UInt64) (rip : state.rip = address)
    (memory : state.memory = X86_64Mem.write .w8 writeAddress value initial.memory)
    (writeNoWrap : writeAddress.toNat + 1 ≤ 2 ^ 64)
    (below : address.toNat + 8 ≤ writeAddress.toNat)
    (notLinux : address ≠ Gasm.Targets.X86_64.Instructions.linuxSyscallEntry)
    (notIat : initial.read64 address ≠ address) : Spike2OrdinaryCode state := by
  constructor
  · rw [rip]
    exact notLinux
  · rw [rip]
    change X86_64Mem.read .w64 address state.memory ≠ address
    rw [memory, spike2_read64_write_below .w8 initial.memory writeAddress address value writeNoWrap below]
    exact notIat

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
private theorem spike2_write_reached_addresses (initial : X86_64MachineState)
    (entry : initial.rip = spike2WriteAddress .pop) :
    (writeStates initial).1.rip = spike2WriteAddress .store ∧
    (writeStates initial).2.1.rip = spike2WriteAddress .advance ∧
    (writeStates initial).2.2.1.rip = spike2WriteAddress .decrement ∧
    (writeStates initial).2.2.2.rip = spike2WriteAddress .branch := by
  have h1 : (writeStates initial).1.rip = spike2WriteAddress .store := by
    rw [show (writeStates initial).1.rip = initial.rip + 1 by rfl, entry]
    decide
  have h2 : (writeStates initial).2.1.rip = spike2WriteAddress .advance := by
    rw [show (writeStates initial).2.1.rip = (writeStates initial).1.rip + 2 by rfl, h1]
    decide
  have h3 : (writeStates initial).2.2.1.rip = spike2WriteAddress .decrement := by
    rw [show (writeStates initial).2.2.1.rip = (writeStates initial).2.1.rip + 4 by rfl, h2]
    decide
  have h4 : (writeStates initial).2.2.2.rip = spike2WriteAddress .branch := by
    rw [show (writeStates initial).2.2.2.rip = (writeStates initial).2.2.1.rip + 4 by rfl, h3]
    decide
  exact ⟨h1, h2, h3, h4⟩

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
private theorem spike2_write_pop_ordinary (initial : X86_64MachineState)
    (entry : initial.rip = spike2WriteAddress .pop)
    (authority : Spike2DecimalTextAuthority initial) :
    Spike2OrdinaryCode (writeStates initial).1 := by
  obtain ⟨rip, _, _, _⟩ := spike2_write_reached_addresses initial entry
  apply spike2_ordinary_from_initial_memory initial _ (spike2WriteAddress .store) rip
  · rfl
  · decide
  · exact authority.writeStore

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
private theorem spike2_write_store_ordinary {stackUpper outputLimit : UInt64}
    (initial : X86_64MachineState) (entry : initial.rip = spike2WriteAddress .pop)
    (authority : Spike2DecimalTextAuthority initial) (safety : WriteSafety stackUpper outputLimit initial)
    (safe : WriteExecutionSafety 243 initial)
    (writeNoWrap : (initial.gprs .rdi).toNat + 1 ≤ 2 ^ 64)
    (above : 4198635 ≤ (initial.gprs .rdi).toNat) :
    Spike2OrdinaryCode (writeStates initial).2.1 := by
  obtain ⟨_, rip, _, _⟩ := spike2_write_reached_addresses initial entry
  apply spike2_ordinary_from_output_write initial _ (spike2WriteAddress .advance)
    (initial.gprs .rdi) (initial.read64 initial.rsp).toUInt8.toUInt64 rip
  · rw [show (writeStates initial).2.1.memory = (writeFinal 243 initial).memory by rfl,
      (writePassEffect 243 stackUpper outputLimit initial safety safe).memory]
  · exact writeNoWrap
  · exact spike2_decimal_text_below _ above _ (by simp [spike2ExtractionAddress, spike2WriteAddress])
  · decide
  · exact authority.writeAdvance

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
private theorem spike2_write_cursor_ordinary {stackUpper outputLimit : UInt64}
    (initial : X86_64MachineState) (entry : initial.rip = spike2WriteAddress .pop)
    (authority : Spike2DecimalTextAuthority initial) (safety : WriteSafety stackUpper outputLimit initial)
    (safe : WriteExecutionSafety 243 initial) (writeNoWrap : (initial.gprs .rdi).toNat + 1 ≤ 2 ^ 64)
    (above : 4198635 ≤ (initial.gprs .rdi).toNat) : Spike2OrdinaryCode (writeStates initial).2.2.1 := by
  obtain ⟨_, _, rip, _⟩ := spike2_write_reached_addresses initial entry
  apply spike2_ordinary_from_output_write initial _ (spike2WriteAddress .decrement)
    (initial.gprs .rdi) (initial.read64 initial.rsp).toUInt8.toUInt64 rip
  · rw [show (writeStates initial).2.2.1.memory = (writeFinal 243 initial).memory by rfl,
      (writePassEffect 243 stackUpper outputLimit initial safety safe).memory]
  · exact writeNoWrap
  · exact spike2_decimal_text_below _ above _ (by simp [spike2ExtractionAddress, spike2WriteAddress])
  · decide
  · exact authority.writeDecrement

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
private theorem spike2_write_count_ordinary {stackUpper outputLimit : UInt64}
    (initial : X86_64MachineState) (entry : initial.rip = spike2WriteAddress .pop)
    (authority : Spike2DecimalTextAuthority initial) (safety : WriteSafety stackUpper outputLimit initial)
    (safe : WriteExecutionSafety 243 initial) (writeNoWrap : (initial.gprs .rdi).toNat + 1 ≤ 2 ^ 64)
    (above : 4198635 ≤ (initial.gprs .rdi).toNat) : Spike2OrdinaryCode (writeStates initial).2.2.2 := by
  obtain ⟨_, _, _, rip⟩ := spike2_write_reached_addresses initial entry
  apply spike2_ordinary_from_output_write initial _ (spike2WriteAddress .branch)
    (initial.gprs .rdi) (initial.read64 initial.rsp).toUInt8.toUInt64 rip
  · rw [show (writeStates initial).2.2.2.memory = (writeFinal 243 initial).memory by rfl,
      (writePassEffect 243 stackUpper outputLimit initial safety safe).memory]
  · exact writeNoWrap
  · exact spike2_decimal_text_below _ above _ (by simp [spike2ExtractionAddress, spike2WriteAddress])
  · decide
  · exact authority.writeBranch

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
private theorem spike2_write_branch_rip_taken (initial : X86_64MachineState)
    (entry : initial.rip = spike2WriteAddress .pop)
    (taken : X86BranchCondition.notEqual.holds (writeStates initial).2.2.2) :
    (writeFinal 243 initial).rip = spike2WriteAddress .pop := by
  obtain ⟨_, _, _, branchRip⟩ := spike2_write_reached_addresses initial entry
  change (if !(writeStates initial).2.2.2.zf then (writeStates initial).2.2.2.rip + 2 +
      signExtend8To64 243 else (writeStates initial).2.2.2.rip + 2) = spike2WriteAddress .pop
  change (writeStates initial).2.2.2.zf = false at taken
  simp [taken]
  rw [branchRip]
  exact spike2WriteLinkedLayout.takenTarget

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
private theorem spike2_write_branch_rip_fallthrough (initial : X86_64MachineState)
    (entry : initial.rip = spike2WriteAddress .pop)
    (fallthrough : ¬ X86BranchCondition.notEqual.holds (writeStates initial).2.2.2) :
    (writeFinal 243 initial).rip = spike2WriteAddress .exit := by
  obtain ⟨_, _, _, branchRip⟩ := spike2_write_reached_addresses initial entry
  change (if !(writeStates initial).2.2.2.zf then (writeStates initial).2.2.2.rip + 2 +
      signExtend8To64 243 else (writeStates initial).2.2.2.rip + 2) = spike2WriteAddress .exit
  change ¬ (writeStates initial).2.2.2.zf = false at fallthrough
  have zf : (writeStates initial).2.2.2.zf = true := by
    cases h : (writeStates initial).2.2.2.zf <;> simp [h] at fallthrough ⊢
  simp [zf]
  rw [branchRip]
  exact spike2WriteLinkedLayout.falseFallthrough

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2WriteOrdinary_of_textAuthority {stackUpper outputLimit : UInt64}
    (initial : X86_64MachineState) (entry : initial.rip = spike2WriteAddress .pop)
    (authority : Spike2DecimalTextAuthority initial) (safety : WriteSafety stackUpper outputLimit initial)
    (safe : WriteExecutionSafety 243 initial)
    (branch : X86BranchCondition.notEqual.holds (writeStates initial).2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds (writeStates initial).2.2.2)
    (writeNoWrap : (initial.gprs .rdi).toNat + 1 ≤ 2 ^ 64)
    (above : 4198635 ≤ (initial.gprs .rdi).toNat) : Spike2WriteOrdinary 243 initial := by
  refine ⟨spike2_write_pop_ordinary initial entry authority,
    spike2_write_store_ordinary initial entry authority safety safe writeNoWrap above,
    spike2_write_cursor_ordinary initial entry authority safety safe writeNoWrap above,
    spike2_write_count_ordinary initial entry authority safety safe writeNoWrap above, ?_⟩
  have memory := (writePassEffect 243 stackUpper outputLimit initial safety safe).memory
  rcases branch with taken | fallthrough
  · exact spike2_ordinary_from_output_write initial _ (spike2WriteAddress .pop)
      (initial.gprs .rdi) (initial.read64 initial.rsp).toUInt8.toUInt64
      (spike2_write_branch_rip_taken initial entry taken) memory writeNoWrap
      (spike2_decimal_text_below _ above _ (by simp [spike2ExtractionAddress, spike2WriteAddress]))
      (by decide) authority.writePop
  · exact spike2_ordinary_from_output_write initial _ (spike2WriteAddress .exit)
      (initial.gprs .rdi) (initial.read64 initial.rsp).toUInt8.toUInt64
      (spike2_write_branch_rip_fallthrough initial entry fallthrough) memory writeNoWrap
      (spike2_decimal_text_below _ above _ (by simp [spike2ExtractionAddress, spike2WriteAddress]))
      (by decide) authority.writeExit

/- REF: docs/PROOF_TACTICS.md#design-relational-ghost-state -/
structure Spike2ExtractionPhysicalLoopWitness (value stackLower : UInt64)
    (initial : X86_64MachineState) (initialEventsRev : List AnyEvent) : Prop where
  entry : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    (spike2ExtractionIter initial completed).rip = spike2ExtractionAddress .clearHigh
  safety : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    ExtractionSafety stackLower (spike2ExtractionIter initial completed)
  executionSafety : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    ExtractionExecutionSafety 236 (spike2ExtractionIter initial completed)
  branch : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    X86BranchCondition.notEqual.holds (extractionStates (spike2ExtractionIter initial completed)).2.2.2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds (extractionStates (spike2ExtractionIter initial completed)).2.2.2.2.2
  authority : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    Spike2DecimalTextAuthority (spike2ExtractionIter initial completed)
  writeNoWrap : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    ((spike2ExtractionIter initial completed).rsp - 8).toNat + 8 ≤ 2 ^ 64
  above : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    4198635 ≤ ((spike2ExtractionIter initial completed).rsp - 8).toNat

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
theorem Spike2ExtractionPhysicalLoopWitness.toPhaseWitness {value stackLower : UInt64}
    {initial : X86_64MachineState} {initialEventsRev : List AnyEvent}
    (physical : Spike2ExtractionPhysicalLoopWitness value stackLower initial initialEventsRev) :
    Spike2ExtractionLoopWitness value stackLower initial initialEventsRev where
  entry completed within := physical.entry completed within
  safety completed within := physical.safety completed within
  executionSafety completed within := physical.executionSafety completed within
  ordinary completed within := spike2ExtractionOrdinary_of_textAuthority
    _ (physical.entry completed within) (physical.authority completed within)
    (physical.safety completed within) (physical.executionSafety completed within)
    (physical.branch completed within) (physical.writeNoWrap completed within) (physical.above completed within)
  branch completed within := physical.branch completed within

/- REF: docs/PROOF_TACTICS.md#design-relational-ghost-state -/
structure Spike2WritePhysicalLoopWitness (value stackUpper outputLimit : UInt64)
    (initial : X86_64MachineState) (initialEventsRev : List AnyEvent) : Prop where
  entry : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    (spike2WriteIter initial completed).rip = spike2WriteAddress .pop
  safety : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    WriteSafety stackUpper outputLimit (spike2WriteIter initial completed)
  executionSafety : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    WriteExecutionSafety 243 (spike2WriteIter initial completed)
  branch : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    X86BranchCondition.notEqual.holds (writeStates (spike2WriteIter initial completed)).2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds (writeStates (spike2WriteIter initial completed)).2.2.2
  authority : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    Spike2DecimalTextAuthority (spike2WriteIter initial completed)
  writeNoWrap : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    ((spike2WriteIter initial completed).gprs .rdi).toNat + 1 ≤ 2 ^ 64
  above : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    4198635 ≤ ((spike2WriteIter initial completed).gprs .rdi).toNat

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
theorem Spike2WritePhysicalLoopWitness.toPhaseWitness {value stackUpper outputLimit : UInt64}
    {initial : X86_64MachineState} {initialEventsRev : List AnyEvent}
    (physical : Spike2WritePhysicalLoopWitness value stackUpper outputLimit initial initialEventsRev) :
    Spike2WriteLoopWitness value stackUpper outputLimit initial initialEventsRev where
  entry completed within := physical.entry completed within
  safety completed within := physical.safety completed within
  executionSafety completed within := physical.executionSafety completed within
  ordinary completed within := spike2WriteOrdinary_of_textAuthority
    _ (physical.entry completed within) (physical.authority completed within)
    (physical.safety completed within) (physical.executionSafety completed within)
    (physical.branch completed within) (physical.writeNoWrap completed within) (physical.above completed within)
  branch completed within := physical.branch completed within

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
theorem spike2ExtractionPhase_ofPhysicalWitness (value stackLower : UInt64)
    (initial : X86_64MachineState) (initialEventsRev : List AnyEvent)
    (physical : Spike2ExtractionPhysicalLoopWitness value stackLower initial initialEventsRev) :
    DecimalExtractionPhase selectedNonInputPlatformCall spike2Indexed value
      (spike2ExtractionInvariant initial initialEventsRev) :=
  spike2ExtractionPhase value stackLower initial initialEventsRev physical.toPhaseWitness

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
theorem spike2WritePhase_ofPhysicalWitness (value stackUpper outputLimit : UInt64)
    (initial : X86_64MachineState) (initialEventsRev : List AnyEvent)
    (physical : Spike2WritePhysicalLoopWitness value stackUpper outputLimit initial initialEventsRev) :
    DecimalWritePhase selectedNonInputPlatformCall spike2Indexed value
      (spike2WriteInvariant initial initialEventsRev) :=
  spike2WritePhase value stackUpper outputLimit initial initialEventsRev physical.toPhaseWitness

end Spikes.Spike2Fibonacci.Linux
