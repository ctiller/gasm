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
-/import Spikes.Spike2Fibonacci.Windows.RowIndexPath

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Stdlib.Fmt

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

theorem spike2_decimal_slice (completed : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent)
    (hrip : state.rip = 5368713409) (rsp : state.rsp = spike2AfterPrologue.rsp)
    (safe : state.fault = none) (low : Spike2RowLowMemory state)
    (cursorAboveStack : state.rsp.toNat ≤ (state.gprs .rdi).toNat)
    (cursorAbove : spike2RowLowMemoryTop ≤ (state.gprs .rdi).toNat)
    (cursorRoom : (state.gprs .rdi).toNat + 22 < 2 ^ 64)
    (cursor : state.gprs .rdi =
      state.rsp + 64 + UInt64.ofNat (spike2IndexPrefixBytes completed).length)
    (cursorNat : (state.gprs .rdi).toNat =
      (state.rsp + 64).toNat + (spike2IndexPrefixBytes completed).length)
    (prefixBuffer : BufHolds state.memory (state.rsp + 64)
      (spike2IndexPrefixBytes completed)) :
    ∃ fuel final finalEventsRev emitted,
      fuel ≤ 243 ∧
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed fuel
        state eventsRev final finalEventsRev emitted ∧
      Spike2RowRegisterFrame state final ∧
      Spike2FibRegisterFrame state final ∧
      Spike2RowLowMemory final ∧
      BufHolds final.memory (state.rsp + 64)
        (spike2IndexPrefixBytes completed ++
          Stdlib.Fmt.formatDecimal ((spike2AfterDecimalSetup state).gprs .rax).toNat) ∧
      final.gprs .rdi = state.rsp + 64 + UInt64.ofNat
        (spike2IndexPrefixBytes completed ++
          Stdlib.Fmt.formatDecimal ((spike2AfterDecimalSetup state).gprs .rax).toNat).length ∧
      (final.gprs .rdi).toNat = (state.rsp + 64).toNat +
        (spike2IndexPrefixBytes completed ++
          Stdlib.Fmt.formatDecimal ((spike2AfterDecimalSetup state).gprs .rax).toNat).length ∧
      final.rip = 5368713457 ∧
      spike2RowLowMemoryTop ≤ (final.gprs .rdi).toNat ∧
      (final.gprs .rdi).toNat + 2 < 2 ^ 64 := by
  let decimalInitial := spike2AfterDecimalSetup state
  let value := decimalInitial.gprs .rax
  have setupFrame := spike2_decimal_setup_registerFrame state
  have setupSafe : decimalInitial.fault = none := setupFrame.fault.trans safe
  have setupLow := spike2_decimal_setup_lowMemory state low
  have setupRip : decimalInitial.rip = 5368713424 := by
    change state.rip + 3 + 10 + 2 = 5368713424
    rw [hrip]
    rfl
  have text3424 : decimalInitial.read64 5368713424 ≠ 5368713424 := by
    rw [setupLow 5368713424 (by decide)]
    exact spike2_initial_text_3424_not_selfref
  have setupPrefix := spike2_decimal_setup_selected_prefix state eventsRev hrip safe text3424
  have stackBounds := spike2_decimal_stack_bounds value
  have digitsBound := decimalDigitCount_le_twenty value
  have frame : Spike2DecimalFrame value decimalInitial := {
    entry := setupRip
    dividend := rfl
    divisor := by rfl
    count := by
      dsimp [decimalInitial, spike2AfterDecimalSetup]
      simp [step_xor_r32, X86_64MachineState.setGpr32,
        X86_64MachineState.setFlagsLogic, reg32To64]
    fault := setupSafe
    stackRoom := by
      rw [setupFrame.rsp, rsp]
      exact stackBounds.1
    stackTop := by
      rw [setupFrame.rsp, rsp]
      exact stackBounds.2
    bufferAboveStack := by
      change state.rsp.toNat ≤ (state.gprs .rdi).toNat
      exact cursorAboveStack
    bufferTop := by
      change (state.gprs .rdi).toNat + decimalDigitCount value < 2 ^ 64
      omega
    text3424 := text3424
    text3444 := by
      rw [setupLow 5368713444 (by decide)]
      exact spike2_initial_text_3444_not_selfref
    text3457 := by
      rw [setupLow 5368713457 (by decide)]
      exact spike2_initial_text_3457_not_selfref
    text3384 := by
      rw [setupLow 5368713384 (by decide)]
      exact spike2_initial_text_3384_not_selfref
    writeFileIat := by
      rw [setupLow 5368721424 (by decide)]
      exact spike2_after_prologue_writeFileIat
    exitProcessIat := by
      rw [setupLow 5368721432 (by decide)]
      exact spike2_after_prologue_exitProcessIat }
  rcases spike2_uint64_decimal_selected_prefix_bounded value decimalInitial eventsRev frame with
    ⟨decimalFuel, final, finalEventsRev, emitted, decimalBound, decimalPrefix,
      finalRsp, finalRdi, _finalRcx, _formatBytes, _r12, finalR13, finalR14, finalR15, caller⟩
  have decimalRegisters : Spike2RowRegisterFrame decimalInitial final := {
    rsp := finalRsp
    r13 := finalR13
    fault := caller.fault.trans setupSafe.symm }
  have initialRdi : decimalInitial.gprs .rdi = state.gprs .rdi := by rfl
  have noWrap : (decimalInitial.gprs .rdi).toNat + decimalDigitCount value < 2 ^ 64 := by
    rw [initialRdi]
    omega
  have finalRdiNat : (final.gprs .rdi).toNat =
      (decimalInitial.gprs .rdi).toNat + decimalDigitCount value := by
    rw [finalRdi, UInt64.toNat_add]
    simp [Nat.toUInt64, Nat.mod_eq_of_lt noWrap]
  have finalLow : Spike2RowLowMemory final := by
    intro address below
    rw [caller.lowMemory address below]
    exact setupLow address below
  have prefixFinal : BufHolds final.memory (state.rsp + 64)
      (spike2IndexPrefixBytes completed) := by
    apply BufHolds_of_getElem
    intro index within
    have observed := BufHolds_getElem state.memory (state.rsp + 64)
      (spike2IndexPrefixBytes completed) prefixBuffer index within
    let address := state.rsp + 64 + UInt64.ofNat index
    have startNat : (state.rsp + 64).toNat = state.rsp.toNat + 64 := by
      rw [rsp, spike2_after_prologue_rsp_eq]
      decide
    have addressNat : address.toNat = (state.rsp + 64).toNat + index := by
      dsimp [address]
      have room := cursorRoom
      rw [cursorNat] at room
      have indexBound : index < 2 ^ 64 := by omega
      have sumBound : (state.rsp + 64).toNat + index < 2 ^ 64 := by omega
      simp [UInt64.toNat_add, Nat.toUInt64, Nat.mod_eq_of_lt indexBound,
        Nat.mod_eq_of_lt sumBound]
      rw [Nat.mod_eq_of_lt (by omega : state.rsp.toNat + 64 + index < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : state.rsp.toNat + 64 < 2 ^ 64)]
    have above : decimalInitial.rsp.toNat ≤ address.toNat := by
      rw [setupFrame.rsp, addressNat, startNat]
      omega
    have below : address.toNat < (decimalInitial.gprs .rdi).toNat := by
      rw [initialRdi, addressNat, cursorNat]
      omega
    have preserved := caller.beforeBufferMemory address above below
    change X86_64Mem.read .w8 address final.memory = _
    rw [show X86_64Mem.read .w8 address final.memory =
        (X86_64Mem.readByte final.memory address).toUInt64 by rfl,
      preserved]
    change (X86_64Mem.readByte state.memory address).toUInt64 = _
    simpa [address] using congrArg UInt8.toUInt64 observed
  have decimalBuffer : BufHolds final.memory (decimalInitial.gprs .rdi)
      (Stdlib.Fmt.formatDecimal value.toNat) := by
    apply BufHolds_of_decimalBytesAt
    rw [Stdlib.Fmt.formatDecimal_length_eq, ← Stdlib.Fmt.decimalDigitCount_eq_digits_length]
    exact _formatBytes
  have completeBuffer : BufHolds final.memory (state.rsp + 64)
      (spike2IndexPrefixBytes completed ++ Stdlib.Fmt.formatDecimal value.toNat) := by
    rw [BufHolds_append]
    refine ⟨prefixFinal, ?_⟩
    rw [← cursor, ← initialRdi]
    exact decimalBuffer
  have completeCursorNat : (final.gprs .rdi).toNat = (state.rsp + 64).toNat +
      (spike2IndexPrefixBytes completed ++ Stdlib.Fmt.formatDecimal value.toNat).length := by
    rw [finalRdiNat, initialRdi, cursorNat, List.length_append,
      Stdlib.Fmt.formatDecimal_length_eq, ← Stdlib.Fmt.decimalDigitCount_eq_digits_length]
    omega
  have completeCursor : final.gprs .rdi = state.rsp + 64 + UInt64.ofNat
      (spike2IndexPrefixBytes completed ++ Stdlib.Fmt.formatDecimal value.toNat).length := by
    apply UInt64.toNat_inj.mp
    rw [completeCursorNat, rsp, spike2_after_prologue_rsp_eq, UInt64.toNat_add]
    have bound : (state.rsp + 64).toNat +
        (spike2IndexPrefixBytes completed ++ Stdlib.Fmt.formatDecimal value.toNat).length <
        2 ^ 64 := by
      rw [← completeCursorNat]
      exact (final.gprs .rdi).toNat_lt_size
    rw [rsp, spike2_after_prologue_rsp_eq] at bound
    simp [UInt64.toNat_add] at bound ⊢
    simp [Nat.toUInt64, Nat.mod_eq_of_lt bound]
  refine ⟨3 + decimalFuel, final, finalEventsRev, emitted, ?_, setupPrefix.append decimalPrefix,
    setupFrame.trans decimalRegisters,
    { r14 := finalR14
      r15 := finalR15 },
    finalLow, completeBuffer, completeCursor, completeCursorNat, caller.rip, ?_, ?_⟩
  · omega
  · rw [finalRdiNat, initialRdi]
    omega
  · rw [finalRdiNat, initialRdi]
    omega

end Spikes.Spike2Fibonacci.Windows
