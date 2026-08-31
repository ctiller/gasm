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

import Gasm.Targets.X86_64.EventfulSegment
import Gasm.Targets.X86_64.DecimalSegments
import Gasm.Targets.Linux.OutcomeBridge
import Spikes.Spike2Fibonacci.NativeLoop
import Spikes.Spike2Fibonacci.Linux.Program
import Stdlib.Fmt.UInt64DecimalSchedule

/-!
# Eventful production adapter for Linux Spike 2

This module is the platform-specific connection point for the Fibonacci driver's real lowered
instructions.  It constructs only `ProductionPrefix` certificates over the production indexed
runner; it does not replay `runProgramWithLoops` or turn a closed evaluator result into a proof.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.Windows
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Spikes.Spike2Fibonacci

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The exact indexed lowering consumed by the production outcome runner. -/
def spike2Indexed : List (UInt64 × X86_64Instr) :=
  indexInstructions spike2Executable.load.rip spike2Instructions

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The concrete machine state at the native driver's first loop header, expressed by four
    target instruction steps rather than an evaluator run. -/
def spike2AfterPrologue : X86_64MachineState :=
  X86_64Instruction.step (mov_r64_imm64 .r15 1)
    (X86_64Instruction.step (mov_r64_imm64 .r14 1)
      (X86_64Instruction.step (mov_r64_imm64 .r13 1)
        (X86_64Instruction.step (sub_rsp32 136) spike2Executable.load)))

/-- The linked address of the main loop header. -/
def spike2MainLoopRip : UInt64 := spike2AfterPrologue.rip

/-- Exact two-instruction main-header transition on a continuing pass. -/
def spike2AfterMainHeader (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (jge_rel32 259)
    (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state)

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Exact state at the terminal syscall after taking the main-loop exit and setting
    `SYS_exit (0)`.  The syscall itself is deliberately excluded: its process-exit outcome is
    discharged by `SelectedPrefix.selectedExecutionTerminates_of_processExit`. -/
def spike2BeforeExitSyscall (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (mov_r32 .eax 60)
    (X86_64Instruction.step (xor_r32 .edi .edi) (spike2AfterMainHeader state))

private theorem sequentialSubRsp (imm : UInt32) : SequentialInstruction (sub_rsp32 imm) where
  encoding := .subRsp32 imm
  safeFallthrough := by intro state _; rfl

private theorem sequentialMovImm (dst : Reg64) (imm : UInt64) :
    SequentialInstruction (mov_r64_imm64 dst imm) where
  encoding := .loadImm dst imm
  safeFallthrough := by intro state _; rfl

private theorem sequentialCmpCounter : SequentialInstruction (cmp_r64_imm8 .r13 91) where
  encoding := .compareImm8 .r13 91
  safeFallthrough := by intro _ _; rfl

private theorem sequentialXorExitCode : SequentialInstruction (xor_r32 .edi .edi) where
  encoding := .xor32 .edi .edi
  safeFallthrough := by intro _ _; rfl

private theorem sequentialMovExitNumber : SequentialInstruction (mov_r32 .eax 60) where
  encoding := .mov32 .eax 60
  safeFallthrough := by intro _ _; rfl

/- The driver uses signed JGE with nonnegative counters below 128.  The following local facts
   connect the concrete flag implementation to that finite-width signed comparison without
   enumerating the ninety counter values. -/
private theorem stepCmpImm8 (dst : Reg64) (imm : UInt8) (state : X86_64MachineState) :
    X86_64Instruction.step (cmp_r64_imm8 dst imm) state =
      { state.setFlagsCmp64 (state.gprs dst) (signExtend8To64 imm) with
        rip := state.rip + 4 } := rfl

private theorem stepJge32 (disp : Int32) (state : X86_64MachineState) :
    X86_64Instruction.step (jge_rel32 disp) state =
      { state with rip := if state.sf == state.of_ then
          state.rip + 6 + signExtend32To64 disp else state.rip + 6 } := rfl

private theorem stepMovR32Rip (dst : Reg32) (imm : UInt32)
    (state : X86_64MachineState) :
    (X86_64Instruction.step (mov_r32 dst imm) state).rip =
      state.rip + (if (reg32Code dst).2 then 6 else 5) := rfl

private theorem stepMovExitNumber (state : X86_64MachineState) :
    X86_64Instruction.step (mov_r32 .eax 60) state =
      { state.setGpr32 .eax 60 with rip := state.rip + 5 } := rfl

private theorem stepXorExitCode (state : X86_64MachineState) :
    X86_64Instruction.step (xor_r32 .edi .edi) state =
      { (state.setGpr32 .edi
          ((state.gprs .rdi).toUInt32 ^^^ (state.gprs .rdi).toUInt32)).setFlagsLogic 32
            (((state.gprs .rdi).toUInt32 ^^^ (state.gprs .rdi).toUInt32).toUInt64) with
        rip := state.rip + 2 } := rfl

private theorem stepSyscall (state : X86_64MachineState) :
    X86_64Instruction.step syscall_op state =
      { (state.setGpr64 .rcx (state.rip + 2)).setGpr64 .r11 state.flags with
        rip := linuxSyscallEntry } := rfl

private theorem beforeExitRax (state : X86_64MachineState) :
    (spike2BeforeExitSyscall state).gprs .rax = SYS_exit := by
  rw [spike2BeforeExitSyscall, stepMovExitNumber]
  simp [X86_64MachineState.setGpr32, reg32To64, SYS_exit]

private theorem beforeExitRdi (state : X86_64MachineState) :
    (spike2BeforeExitSyscall state).gprs .rdi = 0 := by
  rw [spike2BeforeExitSyscall, stepMovExitNumber, stepXorExitCode]
  simp [X86_64MachineState.setGpr32, X86_64MachineState.setFlagsLogic, reg32To64]

private theorem syscallStepRip (state : X86_64MachineState) :
    (X86_64Instruction.step syscall_op state).rip = linuxSyscallEntry := rfl

private theorem syscallStepRax (state : X86_64MachineState) :
    (X86_64Instruction.step syscall_op state).gprs .rax = state.gprs .rax := by
  rw [stepSyscall]
  simp [X86_64MachineState.setGpr64]

private theorem syscallStepRdi (state : X86_64MachineState) :
    (X86_64Instruction.step syscall_op state).gprs .rdi = state.gprs .rdi := by
  rw [stepSyscall]
  simp [X86_64MachineState.setGpr64]

private theorem andOrDistributes (x y z : UInt64) :
    (x ||| y) &&& z = (x &&& z) ||| (y &&& z) := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_or]
  exact BitVec.and_or_distrib_right ..

private theorem parityClearsBit7 (x : UInt64) :
    computeParity8 x &&& ((1 : UInt64) <<< 7) = 0 := by
  unfold computeParity8
  dsimp only
  split <;> rfl

private theorem parityClearsBit11 (x : UInt64) :
    computeParity8 x &&& ((1 : UInt64) <<< 11) = 0 := by
  unfold computeParity8
  dsimp only
  split <;> rfl

private theorem auxClearsBit7 (a b result : UInt64) :
    computeAuxCarry a b result &&& ((1 : UInt64) <<< 7) = 0 := by
  unfold computeAuxCarry
  split <;> rfl

private theorem auxClearsBit11 (a b result : UInt64) :
    computeAuxCarry a b result &&& ((1 : UInt64) <<< 11) = 0 := by
  unfold computeAuxCarry
  split <;> rfl

private theorem preservedClearsBit7 (flags : UInt64) :
    (flags &&& ~~~arithmeticStatusMask) &&& ((1 : UInt64) <<< 7) = 0 := by
  rw [UInt64.and_assoc,
    show (~~~arithmeticStatusMask) &&& ((1 : UInt64) <<< 7) = 0 by decide,
    UInt64.and_zero]

private theorem preservedClearsBit11 (flags : UInt64) :
    (flags &&& ~~~arithmeticStatusMask) &&& ((1 : UInt64) <<< 11) = 0 := by
  rw [UInt64.and_assoc,
    show (~~~arithmeticStatusMask) &&& ((1 : UInt64) <<< 11) = 0 by decide,
    UInt64.and_zero]

private theorem cmpSignFlag (state : X86_64MachineState) (a b : UInt64) :
    (state.setFlagsCmp64 a b).sf = ((a - b) >>> 63 == 1) := by
  have hz : (if a - b == 0 then ((1 : UInt64) <<< 6) else 0) &&&
      ((1 : UInt64) <<< 7) = 0 := by split <;> rfl
  have hcf : (if a < b then ((1 : UInt64) <<< 0) else 0) &&&
      ((1 : UInt64) <<< 7) = 0 := by split <;> rfl
  have hof : (if ((a ^^^ b) &&& (a ^^^ (a - b)) &&& ((1 : UInt64) <<< 63)) != 0
      then ((1 : UInt64) <<< 11) else 0) &&& ((1 : UInt64) <<< 7) = 0 := by
    split <;> rfl
  unfold X86_64MachineState.setFlagsCmp64 X86_64MachineState.sf
  dsimp only
  simp only [andOrDistributes, preservedClearsBit7, hz, hcf, hof, parityClearsBit7,
    auxClearsBit7, UInt64.zero_or, UInt64.or_zero]
  by_cases hsign : (a - b) >>> 63 = 1 <;> simp [hsign] <;> decide

private theorem cmpOverflowFlag (state : X86_64MachineState) (a b : UInt64) :
    (state.setFlagsCmp64 a b).of_ =
      (((a ^^^ b) &&& (a ^^^ (a - b)) &&& ((1 : UInt64) <<< 63)) != 0) := by
  have hz : (if a - b == 0 then ((1 : UInt64) <<< 6) else 0) &&&
      ((1 : UInt64) <<< 11) = 0 := by split <;> rfl
  have hsf : (if ((a - b) >>> 63) == 1 then ((1 : UInt64) <<< 7) else 0) &&&
      ((1 : UInt64) <<< 11) = 0 := by split <;> rfl
  have hcf : (if a < b then ((1 : UInt64) <<< 0) else 0) &&&
      ((1 : UInt64) <<< 11) = 0 := by split <;> rfl
  unfold X86_64MachineState.setFlagsCmp64 X86_64MachineState.of_
  dsimp only
  simp only [andOrDistributes, preservedClearsBit11, hz, hsf, hcf, parityClearsBit11,
    auxClearsBit11, UInt64.zero_or, UInt64.or_zero]
  by_cases hoverflow : (a ^^^ b) &&& (a ^^^ (a - b)) &&& ((1 : UInt64) <<< 63) != 0 <;>
    simp [hoverflow] <;> decide

private theorem smallXor91ClearsSignBit (n : Nat) (hn : n < 91) :
    (n.toUInt64 ^^^ (91 : UInt64)) &&& ((1 : UInt64) <<< 63) = 0 := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_xor, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_ofNat]
  change (n.toUInt64.toBitVec ^^^ BitVec.ofNat 64 91) &&& BitVec.twoPow 64 63 = 0
  rw [BitVec.and_twoPow]
  have hnmsb : (n.toUInt64).toBitVec.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    change 2 * n.toUInt64.toNat < 2 ^ 64
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [← BitVec.msb_eq_getLsbD_last, BitVec.msb_xor, hnmsb]
  decide

private theorem smallSub91Shift63 (n : Nat) (hn : n < 91) :
    (n.toUInt64 - (91 : UInt64)) >>> (63 : UInt64) = 1 := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change ((n.toUInt64 - (91 : UInt64)) >>> (63 : UInt64)).toNat = 1
  rw [UInt64.toNat_shiftRight, UInt64.toNat_sub]
  simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub,
    Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.add_mod_mod, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private theorem smallXor10ClearsSignBit (n : Nat) (hn : n < 91) :
    (n.toUInt64 ^^^ (10 : UInt64)) &&& ((1 : UInt64) <<< 63) = 0 := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_xor, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_ofNat]
  change (n.toUInt64.toBitVec ^^^ BitVec.ofNat 64 10) &&& BitVec.twoPow 64 63 = 0
  rw [BitVec.and_twoPow]
  have hnmsb : (n.toUInt64).toBitVec.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    change 2 * n.toUInt64.toNat < 2 ^ 64
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [← BitVec.msb_eq_getLsbD_last, BitVec.msb_xor, hnmsb]
  decide

private theorem smallSub10Shift63 (n : Nat) (hn : n < 10) :
    (n.toUInt64 - (10 : UInt64)) >>> (63 : UInt64) = 1 := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change ((n.toUInt64 - (10 : UInt64)) >>> (63 : UInt64)).toNat = 1
  rw [UInt64.toNat_shiftRight, UInt64.toNat_sub]
  simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub,
    Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.add_mod_mod, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private theorem smallGe10Shift63 (n : Nat) (hge : 10 ≤ n) (hn : n < 91) :
    (n.toUInt64 - (10 : UInt64)) >>> (63 : UInt64) = 0 := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change ((n.toUInt64 - (10 : UInt64)) >>> (63 : UInt64)).toNat = 0
  rw [UInt64.toNat_shiftRight, UInt64.toNat_sub]
  simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub,
    Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.add_mod_mod, Nat.shiftRight_eq_div_pow]
  have hsum : 18446744073709551606 + n = 18446744073709551616 + (n - 10) := by omega
  rw [hsum, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem mainLoopContinues (state : X86_64MachineState) (n : Nat) (hn : n < 91)
    (hcounter : state.gprs .r13 = n.toUInt64) :
    ¬ X86BranchCondition.greaterEqual.holds
      (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state) := by
  simp only [X86BranchCondition.holds]
  rw [stepCmpImm8]
  change ¬ (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 91)).sf =
    (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 91)).of_
  rw [hcounter, show signExtend8To64 91 = (91 : UInt64) by decide,
    cmpSignFlag, cmpOverflowFlag]
  have hsf : ((n.toUInt64 - (91 : UInt64)) >>> 63 == 1) = true := by
    rw [smallSub91Shift63 n hn]
    decide
  have hfirst := smallXor91ClearsSignBit n hn
  have hof : (n.toUInt64 ^^^ (91 : UInt64)) &&&
      (n.toUInt64 ^^^ (n.toUInt64 - (91 : UInt64))) &&& ((1 : UInt64) <<< 63) = 0 := by
    calc
      _ = (n.toUInt64 ^^^ (n.toUInt64 - (91 : UInt64))) &&&
          ((n.toUInt64 ^^^ (91 : UInt64)) &&& ((1 : UInt64) <<< 63)) := by ac_rfl
      _ = 0 := by rw [hfirst, UInt64.and_zero]
  rw [hsf, hof]
  decide

/-- At the unique post-loop counter value, the same signed comparison selects the linked exit
    edge.  This is the terminal counterpart of `mainLoopContinues`; it is not a 91st body pass. -/
private theorem mainLoopExits (state : X86_64MachineState)
    (hcounter : state.gprs .r13 = (91 : UInt64)) :
    X86BranchCondition.greaterEqual.holds
      (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state) := by
  simp only [X86BranchCondition.holds]
  rw [stepCmpImm8]
  change (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 91)).sf =
    (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 91)).of_
  rw [hcounter, show signExtend8To64 91 = (91 : UInt64) by decide,
    cmpSignFlag, cmpOverflowFlag]
  decide

private theorem indexOneDigit (state : X86_64MachineState) (n : Nat) (hn : n < 10)
    (hcounter : state.gprs .r13 = n.toUInt64) :
    ¬ X86BranchCondition.greaterEqual.holds
      (X86_64Instruction.step (cmp_r64_imm8 .r13 10) state) := by
  simp only [X86BranchCondition.holds]
  rw [stepCmpImm8]
  change ¬ (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 10)).sf =
    (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 10)).of_
  rw [hcounter, show signExtend8To64 10 = (10 : UInt64) by decide,
    cmpSignFlag, cmpOverflowFlag]
  have hsf : ((n.toUInt64 - (10 : UInt64)) >>> 63 == 1) = true := by
    rw [smallSub10Shift63 n hn]
    decide
  have hfirst := smallXor10ClearsSignBit n (by omega)
  have hof : (n.toUInt64 ^^^ (10 : UInt64)) &&&
      (n.toUInt64 ^^^ (n.toUInt64 - (10 : UInt64))) &&& ((1 : UInt64) <<< 63) = 0 := by
    calc
      _ = (n.toUInt64 ^^^ (n.toUInt64 - (10 : UInt64))) &&&
          ((n.toUInt64 ^^^ (10 : UInt64)) &&& ((1 : UInt64) <<< 63)) := by ac_rfl
      _ = 0 := by rw [hfirst, UInt64.and_zero]
  rw [hsf, hof]
  decide

private theorem indexTwoDigits (state : X86_64MachineState) (n : Nat)
    (hge : 10 ≤ n) (hn : n < 91) (hcounter : state.gprs .r13 = n.toUInt64) :
    X86BranchCondition.greaterEqual.holds
      (X86_64Instruction.step (cmp_r64_imm8 .r13 10) state) := by
  simp only [X86BranchCondition.holds]
  rw [stepCmpImm8]
  change (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 10)).sf =
    (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 10)).of_
  rw [hcounter, show signExtend8To64 10 = (10 : UInt64) by decide,
    cmpSignFlag, cmpOverflowFlag]
  have hsf : ((n.toUInt64 - (10 : UInt64)) >>> 63 == 1) = false := by
    rw [smallGe10Shift63 n hge hn]
    decide
  have hfirst := smallXor10ClearsSignBit n hn
  have hof : (n.toUInt64 ^^^ (10 : UInt64)) &&&
      (n.toUInt64 ^^^ (n.toUInt64 - (10 : UInt64))) &&& ((1 : UInt64) <<< 63) = 0 := by
    calc
      _ = (n.toUInt64 ^^^ (n.toUInt64 - (10 : UInt64))) &&&
          ((n.toUInt64 ^^^ (10 : UInt64)) &&& ((1 : UInt64) <<< 63)) := by ac_rfl
      _ = 0 := by rw [hfirst, UInt64.and_zero]
  rw [hsf, hof]
  decide

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Public projection-only form of the one-digit index branch fact.  Row producers use this
without unfolding either the predecessor state or its memory. -/
theorem spike2_index_one_digit (state : X86_64MachineState) (n : Nat) (hn : n < 10)
    (hcounter : state.gprs .r13 = n.toUInt64) :
    ¬ X86BranchCondition.greaterEqual.holds
      (X86_64Instruction.step (cmp_r64_imm8 .r13 10) state) :=
  indexOneDigit state n hn hcounter

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Public projection-only form of the two-digit index branch fact. -/
theorem spike2_index_two_digits (state : X86_64MachineState) (n : Nat)
    (hge : 10 ≤ n) (hn : n < 91) (hcounter : state.gprs .r13 = n.toUInt64) :
    X86BranchCondition.greaterEqual.holds
      (X86_64Instruction.step (cmp_r64_imm8 .r13 10) state) :=
  indexTwoDigits state n hge hn hcounter

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The linked main header selects the body for every pass `0..89`.  The proof is parameterized by
    `completed`; the signed comparison facts above, rather than ninety concrete reductions, choose
    the JGE fallthrough. -/
theorem spike2_main_header_selected_prefix (completed : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hcompleted : completed < 90)
    (hrip : state.rip = spike2MainLoopRip)
    (hcounter : state.gprs .r13 = (completed + 1).toUInt64)
    (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 2 state eventsRev
      (spike2AfterMainHeader state) eventsRev [] := by
  change ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed (1 + 1) state
    eventsRev (spike2AfterMainHeader state) eventsRev []
  have hcontinue := mainLoopContinues state (completed + 1) (by omega) hcounter
  have hcmpRip : (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state).rip = 4198441 := by
    rw [stepCmpImm8, hrip]
    rfl
  have hbodyRip : (spike2AfterMainHeader state).rip = 4198447 := by
    unfold spike2AfterMainHeader
    simp only [X86BranchCondition.holds] at hcontinue
    rw [stepJge32]
    simp [hcontinue, hcmpRip]
  refine ProductionPrefix.SelectedPrefix.ordinary
    (Event := AnyEvent) (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed)
    sequentialCmpCounter ?_ ?_ ?_ ?_ ?_
  · rw [hrip]
    rfl
  · simp [selectedNonInputPlatformCall, selectedNonInputWin32Call,
      Gasm.Targets.Windows.findIatIndex, hcmpRip, linuxSyscallEntry]
  · change (if (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state).rip ==
        linuxSyscallEntry then
        linuxSyscallIntercept _ _ else Gasm.Targets.Windows.win32Intercept _ _) = none
    rw [hcmpRip]
    simp [linuxSyscallEntry, Gasm.Targets.Windows.win32Intercept,
      Gasm.Targets.Windows.findIatIndex]
  · rw [stepCmpImm8]
    exact hsafe
  · refine ProductionPrefix.SelectedPrefix.conditionalFallthrough
      (Event := AnyEvent) (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed)
      (.jge32 259) hcontinue ?_ ?_ ?_ ?_ ?_
    · rw [hcmpRip]
      rfl
    · change selectedNonInputPlatformCall (spike2AfterMainHeader state).rip
        (spike2AfterMainHeader state) = true
      simp [selectedNonInputPlatformCall, selectedNonInputWin32Call,
        Gasm.Targets.Windows.findIatIndex, hbodyRip, linuxSyscallEntry]
    · change ExternalCallInterceptor.interceptCall X86_64 (spike2AfterMainHeader state).rip
        (spike2AfterMainHeader state) = none
      change (if (spike2AfterMainHeader state).rip == linuxSyscallEntry then
          linuxSyscallIntercept _ _ else Gasm.Targets.Windows.win32Intercept _ _) = none
      rw [hbodyRip]
      simp [linuxSyscallEntry, Gasm.Targets.Windows.win32Intercept,
        Gasm.Targets.Windows.findIatIndex]
    · change state.fault = none
      exact hsafe
    · exact .nil _ _

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The continuing main header's body entry has its fixed linked RIP.  Row certificates consume
    this fact through their typed predecessor boundary rather than reducing a closed prior row
    merely to rediscover the address. -/
theorem spike2_after_main_header_body_rip (completed : Nat) (state : X86_64MachineState)
    (hcompleted : completed < 90)
    (hrip : state.rip = spike2MainLoopRip)
    (hcounter : state.gprs .r13 = (completed + 1).toUInt64) :
    (spike2AfterMainHeader state).rip = 4198447 := by
  have hcontinue := mainLoopContinues state (completed + 1) (by omega) hcounter
  have hcmpRip : (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state).rip = 4198441 := by
    rw [stepCmpImm8, hrip]
    rfl
  unfold spike2AfterMainHeader
  simp only [X86BranchCondition.holds] at hcontinue
  rw [stepJge32]
  simp [hcontinue, hcmpRip]

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The header after exactly ninety completed rows takes the real linked `JGE` edge to the exit
    setup.  Its final state is the same concrete two-step state function used by continuing
    headers, with branch selection determined from `r13 = 91`. -/
theorem spike2_exit_header_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent)
    (hrip : state.rip = spike2MainLoopRip)
    (hcounter : state.gprs .r13 = (91 : UInt64))
    (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 2 state eventsRev
      (spike2AfterMainHeader state) eventsRev [] := by
  change ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed (1 + 1) state
    eventsRev (spike2AfterMainHeader state) eventsRev []
  have hexits := mainLoopExits state hcounter
  have hcmpRip : (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state).rip = 4198441 := by
    rw [stepCmpImm8, hrip]
    rfl
  have hexitRip : (spike2AfterMainHeader state).rip = 4198706 := by
    unfold spike2AfterMainHeader
    simp only [X86BranchCondition.holds] at hexits
    rw [stepJge32]
    simp [hexits, hcmpRip]
    decide
  refine ProductionPrefix.SelectedPrefix.ordinary
    (Event := AnyEvent) (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed)
    sequentialCmpCounter ?_ ?_ ?_ ?_ ?_
  · rw [hrip]
    rfl
  · simp [selectedNonInputPlatformCall, selectedNonInputWin32Call,
      Gasm.Targets.Windows.findIatIndex, hcmpRip, linuxSyscallEntry]
  · change (if (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state).rip ==
        linuxSyscallEntry then
        linuxSyscallIntercept _ _ else Gasm.Targets.Windows.win32Intercept _ _) = none
    rw [hcmpRip]
    simp [linuxSyscallEntry, Gasm.Targets.Windows.win32Intercept,
      Gasm.Targets.Windows.findIatIndex]
  · rw [stepCmpImm8]
    exact hsafe
  · refine ProductionPrefix.SelectedPrefix.conditionalTaken
      (Event := AnyEvent) (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed)
      (.jge32 259) hexits ?_ ?_ ?_ ?_ ?_
    · rw [hcmpRip]
      rfl
    · change selectedNonInputPlatformCall (spike2AfterMainHeader state).rip
        (spike2AfterMainHeader state) = true
      simp [selectedNonInputPlatformCall, selectedNonInputWin32Call,
        Gasm.Targets.Windows.findIatIndex, hexitRip, linuxSyscallEntry]
    · change ExternalCallInterceptor.interceptCall X86_64 (spike2AfterMainHeader state).rip
        (spike2AfterMainHeader state) = none
      change (if (spike2AfterMainHeader state).rip == linuxSyscallEntry then
          linuxSyscallIntercept _ _ else Gasm.Targets.Windows.win32Intercept _ _) = none
      rw [hexitRip]
      simp [linuxSyscallEntry, Gasm.Targets.Windows.win32Intercept,
        Gasm.Targets.Windows.findIatIndex]
    · change state.fault = none
      exact hsafe
    · exact .nil _ _

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The terminal main-header facts projected to the linked exit-setup address.  Keeping this
    projection separate lets the bounded exit-tail adapter consume the header certificate without
    reopening its branch-condition proof. -/
theorem spike2_after_exit_header_rip (state : X86_64MachineState)
    (hrip : state.rip = spike2MainLoopRip)
    (hcounter : state.gprs .r13 = (91 : UInt64)) :
    (spike2AfterMainHeader state).rip = 4198706 := by
  have hexits := mainLoopExits state hcounter
  have hcmpRip : (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state).rip = 4198441 := by
    rw [stepCmpImm8, hrip]
    rfl
  unfold spike2AfterMainHeader
  simp only [X86BranchCondition.holds] at hexits
  rw [stepJge32]
  simp [hexits, hcmpRip]
  decide

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The selected exit setup clears the concrete exit-code register and loads Linux syscall 60.
    The certificate stops at the linked `SYSCALL`, allowing the typed process-exit theorem to
    terminate the unchanged production runner without pretending that exit is a safe prefix. -/
theorem spike2_exit_setup_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent)
    (hrip : (spike2AfterMainHeader state).rip = 4198706)
    (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 2
      (spike2AfterMainHeader state) eventsRev (spike2BeforeExitSyscall state) eventsRev [] := by
  have hxorRip : (X86_64Instruction.step (xor_r32 .edi .edi)
      (spike2AfterMainHeader state)).rip = 4198708 := by
    calc
      _ = (spike2AfterMainHeader state).rip + 2 := by rw [stepXorExitCode]
      _ = 4198708 := by rw [hrip]; decide
  have hmovRip : (spike2BeforeExitSyscall state).rip = 4198713 := by
    unfold spike2BeforeExitSyscall
    rw [stepMovR32Rip, hxorRip]
    decide
  change ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed (1 + 1)
    (spike2AfterMainHeader state) eventsRev (spike2BeforeExitSyscall state) eventsRev []
  refine ProductionPrefix.SelectedPrefix.ordinary
    (Event := AnyEvent) (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed)
    sequentialXorExitCode ?_ ?_ ?_ ?_ ?_
  · rw [hrip]
    rfl
  · rw [hxorRip]
    simp [selectedNonInputPlatformCall, selectedNonInputWin32Call,
      Gasm.Targets.Windows.findIatIndex, linuxSyscallEntry]
  · change (if (X86_64Instruction.step (xor_r32 .edi .edi)
        (spike2AfterMainHeader state)).rip == linuxSyscallEntry then
        linuxSyscallIntercept _ _ else Gasm.Targets.Windows.win32Intercept _ _) = none
    rw [hxorRip]
    simp [linuxSyscallEntry, Gasm.Targets.Windows.win32Intercept,
      Gasm.Targets.Windows.findIatIndex]
  · change state.fault = none
    exact hsafe
  · refine ProductionPrefix.SelectedPrefix.ordinary
      (Event := AnyEvent) (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed)
      sequentialMovExitNumber ?_ ?_ ?_ ?_ ?_
    · rw [hxorRip]
      rfl
    · change selectedNonInputPlatformCall (spike2BeforeExitSyscall state).rip
        (spike2BeforeExitSyscall state) = true
      rw [hmovRip]
      simp [selectedNonInputPlatformCall, selectedNonInputLinuxCall,
        selectedNonInputWin32Call, Gasm.Targets.Windows.findIatIndex, SYS_exit,
        linuxSyscallEntry]
    · change ExternalCallInterceptor.interceptCall X86_64
        (spike2BeforeExitSyscall state).rip (spike2BeforeExitSyscall state) = none
      change (if (spike2BeforeExitSyscall state).rip == linuxSyscallEntry then
          linuxSyscallIntercept _ _ else Gasm.Targets.Windows.win32Intercept _ _) = none
      rw [hmovRip]
      simp [linuxSyscallEntry,
        Gasm.Targets.Windows.win32Intercept, Gasm.Targets.Windows.findIatIndex]
    · change state.fault = none
      exact hsafe
    · exact .nil _ _

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The linked Linux `SYSCALL` is the exact classified terminal step after the
    selected exit setup.  Its raw CPU step is fault-free; only the real Linux
    interceptor supplies the typed process-exit state and event. -/
def spike2_exit_syscall_selected_step (state : X86_64MachineState)
    (hrip : (spike2AfterMainHeader state).rip = 4198706)
    (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix.SelectedProcessExitStep (Event := AnyEvent)
      selectedNonInputPlatformCall spike2Indexed (spike2BeforeExitSyscall state) 0 where
  instruction := syscall_op
  hooked := (sysExitHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op (spike2BeforeExitSyscall state))).1
  event := (sysExitHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op (spike2BeforeExitSyscall state))).2
  encoding := .syscall
  lookup := by
    have hxorRip : (X86_64Instruction.step (xor_r32 .edi .edi)
        (spike2AfterMainHeader state)).rip = 4198708 := by
      calc
        _ = (spike2AfterMainHeader state).rip + 2 := by rw [stepXorExitCode]
        _ = 4198708 := by rw [hrip]; decide
    have hmovRip : (spike2BeforeExitSyscall state).rip = 4198713 := by
      unfold spike2BeforeExitSyscall
      rw [stepMovR32Rip, hxorRip]
      decide
    rw [hmovRip]
    rfl
  selectedAt := by
    change (if (X86_64Instruction.step syscall_op
          (spike2BeforeExitSyscall state)).rip == linuxSyscallEntry then
        selectedNonInputLinuxCall _ _ else selectedNonInputWin32Call _ _) = true
    rw [syscallStepRip]
    simp only [beq_self_eq_true, ↓reduceIte]
    unfold selectedNonInputLinuxCall
    rw [syscallStepRax, beforeExitRax]
    simp [SYS_exit]
  steppedSafe := by
    change state.fault = none
    exact hsafe
  intercept := by
    change (if (X86_64Instruction.step syscall_op
          (spike2BeforeExitSyscall state)).rip == linuxSyscallEntry then
        linuxSyscallIntercept _ _ else Gasm.Targets.Windows.win32Intercept _ _) = _
    rw [syscallStepRip]
    simp only [beq_self_eq_true, ↓reduceIte]
    unfold linuxSyscallIntercept
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [syscallStepRax, beforeExitRax]
    simp [SYS_exit]
  exits := by
    simp [sysExitHook, syscallStepRdi, beforeExitRdi]

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The actual four instruction setup prefix is a safe, silent production prefix.  Each lookup is
    into `spike2Indexed`, so this cannot be disconnected from the linked instruction stream. -/
theorem spike2_prologue_prefix :
    ProductionPrefix spike2Indexed 4 spike2Executable.load ([] : List AnyEvent)
      spike2AfterPrologue [] [] := by
  refine ProductionPrefix.ordinary (sequentialSubRsp 136) ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · refine ProductionPrefix.ordinary (sequentialMovImm .r13 1) ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · refine ProductionPrefix.ordinary (sequentialMovImm .r14 1) ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · refine ProductionPrefix.ordinary (sequentialMovImm .r15 1) ?_ ?_ ?_ ?_
        · rfl
        · rfl
        · rfl
        · exact .nil _ _

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The same linked prologue carries the selected-Linux-call evidence needed to compose it into
    the universal termination certificate.  All four instructions are ordinary fallthrough
    instructions, so they cannot enter a syscall boundary. -/
theorem spike2_prologue_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 4 spike2Executable.load
      ([] : List AnyEvent) spike2AfterPrologue [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary (sequentialSubRsp 136) ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary (sequentialMovImm .r13 1) ?_ ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · rfl
    · refine ProductionPrefix.SelectedPrefix.ordinary (sequentialMovImm .r14 1) ?_ ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · rfl
      · refine ProductionPrefix.SelectedPrefix.ordinary (sequentialMovImm .r15 1) ?_ ?_ ?_ ?_ ?_
        · rfl
        · rfl
        · rfl
        · rfl
        · exact .nil _ _

end Spikes.Spike2Fibonacci.Linux
