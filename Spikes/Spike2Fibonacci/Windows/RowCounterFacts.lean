/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.ExitAdapter
import Spikes.Spike2Fibonacci.Windows.FormatterIndex

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

private theorem stepCmpImm8 (dst : Reg64) (imm : UInt8) (state : X86_64MachineState) :
    X86_64Instruction.step (cmp_r64_imm8 dst imm) state =
      { state.setFlagsCmp64 (state.gprs dst) (signExtend8To64 imm) with
        rip := state.rip + 4 } := rfl

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

/-- Every structurally indexed row counter from one through ninety falls through the main header. -/
theorem spike2_main_counter_continues (state : X86_64MachineState) (completed : Nat)
    (within : completed < 90)
    (counter : state.gprs .r13 = UInt64.ofNat (completed + 1)) :
    ¬ X86BranchCondition.greaterEqual.holds
      (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state) := by
  simp only [X86BranchCondition.holds]
  rw [stepCmpImm8]
  change ¬ (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 91)).sf =
    (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 91)).of_
  rw [counter, show signExtend8To64 91 = (91 : UInt64) by decide,
    cmpSignFlag, cmpOverflowFlag]
  have bound : completed + 1 < 91 := by omega
  have hsf : (((completed + 1).toUInt64 - (91 : UInt64)) >>> 63 == 1) = true := by
    rw [smallSub91Shift63 (completed + 1) bound]
    decide
  have hfirst := smallXor91ClearsSignBit (completed + 1) bound
  have hof : ((completed + 1).toUInt64 ^^^ (91 : UInt64)) &&&
      ((completed + 1).toUInt64 ^^^ ((completed + 1).toUInt64 - (91 : UInt64))) &&&
        ((1 : UInt64) <<< 63) = 0 := by
    calc
      _ = ((completed + 1).toUInt64 ^^^
          ((completed + 1).toUInt64 - (91 : UInt64))) &&&
          (((completed + 1).toUInt64 ^^^ (91 : UInt64)) &&&
            ((1 : UInt64) <<< 63)) := by ac_rfl
      _ = 0 := by rw [hfirst, UInt64.and_zero]
  rw [hsf, hof]
  decide

/-- The first nine rows take the one-digit formatter edge. -/
theorem spike2_index_counter_one_digit (state : X86_64MachineState) (completed : Nat)
    (within : completed < 9)
    (counter : state.gprs .r13 = UInt64.ofNat (completed + 1)) :
    ¬ X86BranchCondition.greaterEqual.holds (spike2AfterIndexCompare state) := by
  simp only [X86BranchCondition.holds]
  unfold spike2AfterIndexCompare
  rw [stepCmpImm8]
  change ¬ (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 10)).sf =
    (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 10)).of_
  rw [counter, show signExtend8To64 10 = (10 : UInt64) by decide,
    cmpSignFlag, cmpOverflowFlag]
  have bound : completed + 1 < 10 := by omega
  have hsf : (((completed + 1).toUInt64 - (10 : UInt64)) >>> 63 == 1) = true := by
    rw [smallSub10Shift63 (completed + 1) bound]
    decide
  have hfirst := smallXor10ClearsSignBit (completed + 1) (by omega)
  have hof : ((completed + 1).toUInt64 ^^^ (10 : UInt64)) &&&
      ((completed + 1).toUInt64 ^^^ ((completed + 1).toUInt64 - (10 : UInt64))) &&&
        ((1 : UInt64) <<< 63) = 0 := by
    calc
      _ = ((completed + 1).toUInt64 ^^^
          ((completed + 1).toUInt64 - (10 : UInt64))) &&&
          (((completed + 1).toUInt64 ^^^ (10 : UInt64)) &&&
            ((1 : UInt64) <<< 63)) := by ac_rfl
      _ = 0 := by rw [hfirst, UInt64.and_zero]
  rw [hsf, hof]
  decide

/-- Rows ten through ninety take the two-digit formatter edge. -/
theorem spike2_index_counter_two_digit (state : X86_64MachineState) (completed : Nat)
    (lower : 9 ≤ completed) (upper : completed < 90)
    (counter : state.gprs .r13 = UInt64.ofNat (completed + 1)) :
    X86BranchCondition.greaterEqual.holds (spike2AfterIndexCompare state) := by
  simp only [X86BranchCondition.holds]
  unfold spike2AfterIndexCompare
  rw [stepCmpImm8]
  change (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 10)).sf =
    (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 10)).of_
  rw [counter, show signExtend8To64 10 = (10 : UInt64) by decide,
    cmpSignFlag, cmpOverflowFlag]
  have lower' : 10 ≤ completed + 1 := by omega
  have upper' : completed + 1 < 91 := by omega
  have hsf : (((completed + 1).toUInt64 - (10 : UInt64)) >>> 63 == 1) = false := by
    rw [smallGe10Shift63 (completed + 1) lower' upper']
    decide
  have hfirst := smallXor10ClearsSignBit (completed + 1) upper'
  have hof : ((completed + 1).toUInt64 ^^^ (10 : UInt64)) &&&
      ((completed + 1).toUInt64 ^^^ ((completed + 1).toUInt64 - (10 : UInt64))) &&&
        ((1 : UInt64) <<< 63) = 0 := by
    calc
      _ = ((completed + 1).toUInt64 ^^^
          ((completed + 1).toUInt64 - (10 : UInt64))) &&&
          (((completed + 1).toUInt64 ^^^ (10 : UInt64)) &&&
            ((1 : UInt64) <<< 63)) := by ac_rfl
      _ = 0 := by rw [hfirst, UInt64.and_zero]
  rw [hsf, hof]
  decide

/-- After ninety rows the counter is exactly ninety-one and the terminal edge is taken. -/
theorem spike2_main_counter_exits (state : X86_64MachineState)
    (counter : state.gprs .r13 = UInt64.ofNat 91) :
    X86BranchCondition.greaterEqual.holds
      (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state) := by
  simp only [X86BranchCondition.holds]
  rw [stepCmpImm8]
  change (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 91)).sf =
    (state.setFlagsCmp64 (state.gprs .r13) (signExtend8To64 91)).of_
  rw [counter, show signExtend8To64 91 = (91 : UInt64) by decide,
    cmpSignFlag, cmpOverflowFlag]
  decide

end Spikes.Spike2Fibonacci.Windows
