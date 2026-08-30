/- Copyright 2026 Craig Tiller -/
import Gasm.Targets.X86_64.DecimalSchedule
import Spikes.Spike2Fibonacci.Windows.FormatterDecimal
import Spikes.Spike2Fibonacci.Windows.FormatterTextFrame
import Spikes.Spike2Fibonacci.Windows.ItoaBridge

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.Windows Gasm.Targets.Linux
open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.DecimalSegments Gasm.Targets.X86_64.DecimalSchedule
open Stdlib.Fmt

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

/-- The physical formatter frame needed in both directions at the extraction/write fixed point. -/
structure Spike2DecimalFrame (value : UInt64) (initial : X86_64MachineState) : Prop where
  entry : initial.rip = 5368713424
  dividend : initial.gprs .rax = value
  divisor : initial.gprs .r10 = 10
  count : initial.gprs .rcx = 0
  fault : initial.fault = none
  stackRoom : 5368713465 + 8 * decimalDigitCount value ≤ initial.rsp.toNat
  stackTop : initial.rsp.toNat < 18446744073709551608
  bufferAboveStack : initial.rsp.toNat ≤ (initial.gprs .rdi).toNat
  bufferTop : (initial.gprs .rdi).toNat + decimalDigitCount value < 2 ^ 64
  text3424 : initial.read64 5368713424 ≠ 5368713424
  text3444 : initial.read64 5368713444 ≠ 5368713444
  text3457 : initial.read64 5368713457 ≠ 5368713457

private theorem extraction_execution_safety (state : X86_64MachineState)
    (divisor : state.gprs .r10 = 10) (fault : state.fault = none) :
    ExtractionExecutionSafety 236 state := by
  let s1 := X86_64Instruction.step (xor_r32 .edx .edx) state
  let s2 := X86_64Instruction.step (div_r64 .r10) s1
  let s3 := X86_64Instruction.step (add_r64_imm8 .rdx 0x30) s2
  let s4 := X86_64Instruction.step (push_r64 .rdx) s3
  let s5 := X86_64Instruction.step (add_r64_imm8 .rcx 1) s4
  let s6 := X86_64Instruction.step (cmp_r64_imm8 .rax 0) s5
  have hs1 : s1.fault = none := by
    dsimp only [s1]
    rw [step_xor_r32]
    exact fault
  have highZero : s1.gprs .rdx = 0 := by
    dsimp only [s1]
    rw [step_xor_r32]
    simp [X86_64MachineState.setGpr32, X86_64MachineState.setFlagsLogic, reg32To64]
  have divisor1 : s1.gprs .r10 = 10 := by
    dsimp only [s1]
    rw [step_xor_r32]
    simpa [X86_64MachineState.setGpr32, X86_64MachineState.setFlagsLogic, reg32To64]
      using divisor
  have hs2 : s2.fault = none := by
    dsimp only [s2]
    rw [step_div_r64_by10 s1 highZero divisor1]
    exact hs1
  have hs3 : s3.fault = none := by
    dsimp only [s3]
    rw [step_add_r64_imm8]
    exact hs2
  have hs4 : s4.fault = none := by
    dsimp only [s4]
    rw [step_push_rdx]
    exact hs3
  have hs5 : s5.fault = none := by
    dsimp only [s5]
    rw [step_add_r64_imm8]
    exact hs4
  have hs6 : s6.fault = none := by
    dsimp only [s6]
    rw [step_cmp_r64_imm8]
    exact hs5
  refine ⟨hs1, hs2, hs3, hs4, hs5, hs6, ?_⟩
  rw [show (extractionStates state).2.2.2.2.2 = s6 by rfl, step_jne_rel8]
  exact hs6

private theorem write_execution_safety (state : X86_64MachineState)
    (fault : state.fault = none) : WriteExecutionSafety 243 state := by
  let s1 := X86_64Instruction.step (pop_r64 .rdx) state
  let s2 := X86_64Instruction.step (mov_mem8 .rdi .rdx) s1
  let s3 := X86_64Instruction.step (add_r64_imm8 .rdi 1) s2
  let s4 := X86_64Instruction.step (sub_r64_imm8 .rcx 1) s3
  have hs1 : s1.fault = none := by
    dsimp only [s1]
    rw [step_pop_rdx]
    exact fault
  have hs2 : s2.fault = none := by
    dsimp only [s2]
    rw [step_mov_mem8_rdi_rdx]
    exact hs1
  have hs3 : s3.fault = none := by
    dsimp only [s3]
    rw [step_add_r64_imm8]
    exact hs2
  have hs4 : s4.fault = none := by
    dsimp only [s4]
    rw [step_sub_r64_imm8]
    exact hs3
  refine ⟨hs1, hs2, hs3, hs4, ?_⟩
  rw [show (writeStates state).2.2.2 = s4 by rfl, step_jne_rel8]
  exact hs4

private theorem extraction_preserves_gpr (state : X86_64MachineState) (r : Reg64)
    (notRax : r ≠ .rax) (notRdx : r ≠ .rdx) (notRcx : r ≠ .rcx) (notRsp : r ≠ .rsp) :
    (extractionFinal 236 state).gprs r = state.gprs r := by
  rw [show (extractionFinal 236 state).gprs r =
    (extractionStates state).2.1.gprs r by
      unfold extractionFinal extractionStates
      simp [step_jne_rel8, step_cmp_r64_imm8, step_add_r64_imm8, step_push_rdx,
        X86_64MachineState.setGpr64, X86_64MachineState.setFlagsAdd64,
        X86_64MachineState.setFlagsCmp64, X86_64MachineState.push64,
        X86_64MachineState.write64, notRdx, notRcx, notRsp]]
  exact extractionAfterDiv_preservesGpr state r notRax notRdx

private theorem write_preserves_gpr (state : X86_64MachineState) (r : Reg64)
    (notRdx : r ≠ .rdx) (notRdi : r ≠ .rdi) (notRcx : r ≠ .rcx) (notRsp : r ≠ .rsp) :
    (writeFinal 243 state).gprs r = state.gprs r := by
  unfold writeFinal writeStates
  simp [step_jne_rel8, step_sub_r64_imm8, step_add_r64_imm8, step_mov_mem8_rdi_rdx,
    step_pop_rdx, X86_64MachineState.setGpr64, X86_64MachineState.pop64,
    X86_64MachineState.setFlagsAdd64, X86_64MachineState.setFlagsSub64,
    X86_64MachineState.setFlagsCmp64, X86_64MachineState.write8,
    notRdx, notRdi, notRcx, notRsp]

private theorem div_r10_fallthrough_local (state : X86_64MachineState)
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
      simp [hnonzero, hfits]
      rfl

private theorem extraction_cmp_rip (state : X86_64MachineState)
    (hrip : state.rip = 5368713424) (safe : ExtractionExecutionSafety 236 state) :
    (extractionStates state).2.2.2.2.2.rip = 5368713442 := by
  have divSafe : (X86_64Instruction.step (div_r64 .r10)
      (X86_64Instruction.step (xor_r32 .edx .edx) state)).fault = none := by
    simpa [extractionStates] using safe.divSafe
  let s1 := X86_64Instruction.step (xor_r32 .edx .edx) state
  let s2 := X86_64Instruction.step (div_r64 .r10) s1
  let s3 := X86_64Instruction.step (add_r64_imm8 .rdx 0x30) s2
  let s4 := X86_64Instruction.step (push_r64 .rdx) s3
  let s5 := X86_64Instruction.step (add_r64_imm8 .rcx 1) s4
  let s6 := X86_64Instruction.step (cmp_r64_imm8 .rax 0) s5
  change s6.rip = 5368713442
  dsimp only [s6]
  rw [step_cmp_r64_imm8, show s5.rip = s4.rip + 4 by rfl,
    show s4.rip = s3.rip + 1 by rfl, show s3.rip = s2.rip + 4 by rfl,
    show s2.rip = s1.rip + 3 by exact div_r10_fallthrough_local _ divSafe,
    show s1.rip = state.rip + 2 by rfl, hrip]
  change 5368713424 + 2 + 3 + 4 + 1 + 4 + 4 = 5368713442
  decide

private theorem write_sub_rip (state : X86_64MachineState)
    (hrip : state.rip = 5368713444) :
    (writeStates state).2.2.2.rip = 5368713455 := by
  let s1 := X86_64Instruction.step (pop_r64 .rdx) state
  let s2 := X86_64Instruction.step (mov_mem8 .rdi .rdx) s1
  let s3 := X86_64Instruction.step (add_r64_imm8 .rdi 1) s2
  let s4 := X86_64Instruction.step (sub_r64_imm8 .rcx 1) s3
  change s4.rip = 5368713455
  rw [show s4.rip = s3.rip + 4 by rfl, show s3.rip = s2.rip + 4 by rfl,
    show s2.rip = s1.rip + 2 by rfl, show s1.rip = state.rip + 1 by rfl, hrip]
  decide

private theorem extraction_branch_iff (state : X86_64MachineState)
    (divisor : state.gprs .r10 = 10) :
    X86BranchCondition.notEqual.holds (extractionStates state).2.2.2.2.2 ↔
      UInt64.ofNat ((state.gprs .rax).toNat / 10) ≠ 0 := by
  let afterDiv := (extractionStates state).2.1
  let beforeCmp := (extractionStates state).2.2.2.2.1
  let afterCmp := (extractionStates state).2.2.2.2.2
  have quotient : afterDiv.gprs .rax = UInt64.ofNat ((state.gprs .rax).toNat / 10) :=
    extractionAfterDiv_quotient state divisor
  have beforeCmpRax : beforeCmp.gprs .rax = afterDiv.gprs .rax := by
    dsimp only [beforeCmp, afterDiv, extractionStates]
    simp [step_add_r64_imm8, step_push_rdx, X86_64MachineState.setGpr64,
      X86_64MachineState.setFlagsAdd64, X86_64MachineState.push64,
      X86_64MachineState.write64]
  have zf : afterCmp.zf = (beforeCmp.gprs .rax == 0) := by
    dsimp only [afterCmp]
    rw [show (extractionStates state).2.2.2.2.2 =
      X86_64Instruction.step (cmp_r64_imm8 .rax 0) beforeCmp by rfl,
      step_cmp_r64_imm8]
    change (beforeCmp.setFlagsCmp64 (beforeCmp.gprs .rax) 0).zf = _
    exact setFlagsCmp64_zero_zf beforeCmp (beforeCmp.gprs .rax)
  simp only [X86BranchCondition.holds]
  rw [show (extractionStates state).2.2.2.2.2 = afterCmp by rfl, zf,
    beforeCmpRax, quotient]
  simp

private theorem write_branch_iff (state : X86_64MachineState) :
    X86BranchCondition.notEqual.holds (writeStates state).2.2.2 ↔
      state.gprs .rcx ≠ 1 := by
  let beforeSub := (writeStates state).2.2.1
  let afterSub := (writeStates state).2.2.2
  have beforeSubRcx : beforeSub.gprs .rcx = state.gprs .rcx := by
    dsimp only [beforeSub, writeStates]
    simp [step_add_r64_imm8, step_mov_mem8_rdi_rdx, step_pop_rdx,
      X86_64MachineState.setGpr64, X86_64MachineState.setFlagsAdd64,
      X86_64MachineState.pop64, X86_64MachineState.write8]
  have zf : afterSub.zf = (beforeSub.gprs .rcx == 1) := by
    dsimp only [afterSub]
    rw [show (writeStates state).2.2.2 =
      X86_64Instruction.step (sub_r64_imm8 .rcx 1) beforeSub by rfl,
      step_sub_r64_imm8]
    change (beforeSub.setFlagsSub64 (beforeSub.gprs .rcx) 1).zf = _
    exact setFlagsSub64_one_zf beforeSub (beforeSub.gprs .rcx)
  simp only [X86BranchCondition.holds]
  rw [show (writeStates state).2.2.2 = afterSub by rfl, zf, beforeSubRcx]
  simp

private theorem extraction_final_rip_taken (state : X86_64MachineState)
    (hrip : state.rip = 5368713424) (safe : ExtractionExecutionSafety 236 state)
    (taken : X86BranchCondition.notEqual.holds (extractionStates state).2.2.2.2.2) :
    (extractionFinal 236 state).rip = 5368713424 := by
  unfold extractionFinal
  rw [step_jne_rel8]
  simp only [X86BranchCondition.holds] at taken
  rw [if_pos (by simpa [taken])]
  rw [extraction_cmp_rip state hrip safe]
  change 5368713442 + 2 + signExtend8To64 236 = 5368713424
  decide

private theorem extraction_final_rip_fallthrough (state : X86_64MachineState)
    (hrip : state.rip = 5368713424) (safe : ExtractionExecutionSafety 236 state)
    (fallthrough : ¬ X86BranchCondition.notEqual.holds
      (extractionStates state).2.2.2.2.2) :
    (extractionFinal 236 state).rip = 5368713444 := by
  unfold extractionFinal
  rw [step_jne_rel8]
  simp only [X86BranchCondition.holds] at fallthrough
  rw [if_neg (by simpa using fallthrough)]
  rw [extraction_cmp_rip state hrip safe]
  change 5368713442 + 2 = 5368713444
  decide

private theorem write_final_rip_taken (state : X86_64MachineState)
    (hrip : state.rip = 5368713444)
    (taken : X86BranchCondition.notEqual.holds (writeStates state).2.2.2) :
    (writeFinal 243 state).rip = 5368713444 := by
  unfold writeFinal
  rw [step_jne_rel8]
  simp only [X86BranchCondition.holds] at taken
  rw [if_pos (by simpa [taken])]
  rw [write_sub_rip state hrip]
  change 5368713455 + 2 + signExtend8To64 243 = 5368713444
  decide

private theorem write_final_rip_fallthrough (state : X86_64MachineState)
    (hrip : state.rip = 5368713444)
    (fallthrough : ¬ X86BranchCondition.notEqual.holds (writeStates state).2.2.2) :
    (writeFinal 243 state).rip = 5368713457 := by
  unfold writeFinal
  rw [step_jne_rel8]
  simp only [X86BranchCondition.holds] at fallthrough
  rw [if_neg (by simpa using fallthrough)]
  rw [write_sub_rip state hrip]
  change 5368713455 + 2 = 5368713457
  decide

private theorem StackHolds_write64_before (memory : X86_64Memory)
    (writeAddress top : UInt64) (word : UInt64) (digits : List UInt8)
    (writeNoWrap : writeAddress.toNat + 8 ≤ 2 ^ 64)
    (before : writeAddress.toNat + 8 ≤ top.toNat)
    (stackNoWrap : top.toNat + 8 * digits.length < 2 ^ 64) :
    StackHolds (X86_64Mem.write .w64 writeAddress word memory) top digits =
      StackHolds memory top digits := by
  induction digits generalizing top with
  | nil => rfl
  | cons digit rest ih =>
    simp only [List.length_cons] at stackNoWrap
    have topWordNoWrap : top.toNat + 8 < 2 ^ 64 := by omega
    have readSame : X86_64Mem.read .w64 top
        (X86_64Mem.write .w64 writeAddress word memory) =
        X86_64Mem.read .w64 top memory := by
      apply X86_64Mem.read_congr
      intro offset offsetBound
      have offsetLt : offset < 8 := by simpa [MemWidth.bytes] using offsetBound
      apply X86_64Mem.readByte_write_disjoint .w64 writeAddress word memory
        (top + offset.toUInt64) writeNoWrap
      right
      have offsetCast : offset.toUInt64.toNat = offset := by
        simp [Nat.toUInt64, Nat.mod_eq_of_lt (by omega : offset < 2 ^ 64)]
      rw [UInt64.toNat_add]
      have topBound : top.toNat + offset < 2 ^ 64 := by omega
      rw [offsetCast, Nat.mod_eq_of_lt topBound]
      simpa [MemWidth.bytes] using
        (Nat.le_trans before (Nat.le_add_right top.toNat offset))
    have topNext : (top + 8).toNat = top.toNat + 8 := by
      rw [UInt64.toNat_add]
      simp [Nat.mod_eq_of_lt topWordNoWrap]
    simp only [StackHolds]
    rw [readSame, ih (top + 8) (by omega) (by rw [topNext]; omega)]

private theorem StackHolds_push (memory : X86_64Memory) (top : UInt64)
    (digit : UInt8) (digits : List UInt8) (room : 8 ≤ top.toNat)
    (stackNoWrap : top.toNat + 8 * digits.length < 2 ^ 64) :
    StackHolds (X86_64Mem.write .w64 (top - 8) digit.toUInt64 memory)
        (top - 8) (digit :: digits) ↔ StackHolds memory top digits := by
  have topBound : top.toNat < 2 ^ 64 := top.toNat_lt_size
  have subNat : (top - 8).toNat = top.toNat - 8 := by
    simp [UInt64.toNat_sub]
    omega
  have writeNoWrap : (top - 8).toNat + 8 ≤ 2 ^ 64 := by rw [subNat]; omega
  have next : top - 8 + 8 = top := by rw [UInt64.sub_add_cancel]
  simp only [StackHolds]
  rw [X86_64Mem.read64_write64_same, next,
    StackHolds_write64_before memory (top - 8) top digit.toUInt64 digits
      writeNoWrap (by rw [subNat]; omega) stackNoWrap]
  simp

private theorem BufHolds_write8_after (memory : X86_64Memory) (start writeAddress : UInt64)
    (byte : UInt64) (written : List UInt8)
    (writeNoWrap : writeAddress.toNat + 1 ≤ 2 ^ 64)
    (after : start.toNat + written.length ≤ writeAddress.toNat)
    (prefixNoWrap : start.toNat + written.length < 2 ^ 64) :
    BufHolds (X86_64Mem.write .w8 writeAddress byte memory) start written =
      BufHolds memory start written := by
  induction written generalizing start with
  | nil => rfl
  | cons digit rest ih =>
    simp only [List.length_cons] at after prefixNoWrap
    have startLt : start.toNat < writeAddress.toNat := by omega
    have readSame := X86_64Mem.readByte_write_disjoint .w8 writeAddress byte memory start
      writeNoWrap (Or.inl startLt)
    have startOne : (start + 1).toNat = start.toNat + 1 := by
      rw [UInt64.toNat_add]
      simp [Nat.mod_eq_of_lt (by omega : start.toNat + 1 < 2 ^ 64)]
    simp only [BufHolds, X86_64Mem.read]
    rw [readSame, ih (start + 1) (by rw [startOne]; omega) (by rw [startOne]; omega)]

private theorem byteOfDigit_cast (digit : Nat) (small : digit < 10) :
    UInt64.ofNat digit + 0x30 = (byteOfDigit digit).toUInt64 :=
  digit_byte_toUInt64 digit small

private theorem toNat_sub_eight (value : UInt64) (room : 8 ≤ value.toNat) :
    (value - 8).toNat = value.toNat - 8 := by
  have upper := value.toNat_lt_size
  change value.toNat < 18446744073709551616 at upper
  have division : (18446744073709551608 + value.toNat) / 18446744073709551616 = 1 := by
    omega
  simp [UInt64.toNat_sub, UInt64.size, division]
  omega

/-- Forward extraction facts and backward write requirements meet in `suffix`: the already
extracted low digits, stored in the exact order in which the write loop will pop them. -/
structure Spike2ExtractionFacts (value : UInt64) (initial : X86_64MachineState)
    (initialEventsRev : List AnyEvent) (completed : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) where
  events : eventsRev = initialEventsRev
  within : completed ≤ decimalDigitCount value
  remaining : Nat
  remainingBound : remaining < 2 ^ 64
  suffix : List UInt8
  suffixLength : suffix.length = completed
  activeDecomposition : completed < decimalDigitCount value →
    formatDecimal value.toNat = formatDecimal remaining ++ suffix
  completedSuffix : completed = decimalDigitCount value → suffix = formatDecimal value.toNat
  rax : state.gprs .rax = UInt64.ofNat remaining
  r10 : state.gprs .r10 = 10
  rcx : state.gprs .rcx = UInt64.ofNat completed
  rspAccounting : state.rsp.toNat + 8 * completed = initial.rsp.toNat
  rdi : state.gprs .rdi = initial.gprs .rdi
  fault : state.fault = none
  stack : StackHolds state.memory state.rsp suffix
  preservesR12 : state.gprs .r12 = initial.gprs .r12
  preservesR13 : state.gprs .r13 = initial.gprs .r13
  preservesR14 : state.gprs .r14 = initial.gprs .r14
  preservesR15 : state.gprs .r15 = initial.gprs .r15
  text3424 : state.read64 5368713424 = initial.read64 5368713424
  text3444 : state.read64 5368713444 = initial.read64 5368713444
  text3457 : state.read64 5368713457 = initial.read64 5368713457
  activeRip : completed < decimalDigitCount value → state.rip = 5368713424
  completedRip : completed = decimalDigitCount value → state.rip = 5368713444

def Spike2ExtractionInvariant (value : UInt64) (initial : X86_64MachineState)
    (initialEventsRev : List AnyEvent) (completed : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) : Prop :=
  Nonempty (Spike2ExtractionFacts value initial initialEventsRev completed state eventsRev)

private theorem formatDecimal_single (n : Nat) (small : n < 10) :
    formatDecimal n = [byteOfDigit n] := by
  unfold formatDecimal
  rw [digits_single n small]
  rfl

private theorem formatDecimal_step (n : Nat) (large : 10 ≤ n) :
    formatDecimal n = formatDecimal (n / 10) ++ [byteOfDigit (n % 10)] := by
  unfold formatDecimal
  rw [show digits n = digits (n / 10) ++ [n % 10] by
    rw [digits]
    simp [show ¬n < 10 by omega]]
  simp

private theorem decimal_full_length (value : UInt64) :
    (formatDecimal value.toNat).length = decimalDigitCount value := by
  rw [formatDecimal_length_eq, ← decimalDigitCount_eq_digits_length]

private theorem extraction_text_frame {value : UInt64} {initial state final : X86_64MachineState}
    {initialEventsRev eventsRev : List AnyEvent} {completed : Nat}
    (frame : Spike2DecimalFrame value initial)
    (holds : Spike2ExtractionFacts value initial initialEventsRev completed state eventsRev)
    (within : completed < decimalDigitCount value)
    (effect : ExtractionPassEffect 236 state final) (address : UInt64)
    (addressBound : address.toNat + 8 ≤ 5368713465) :
    final.read64 address = state.read64 address := by
  have digitsBound := decimalDigitCount_le_twenty value
  have room : 8 ≤ state.rsp.toNat := by
    have := frame.stackRoom
    have := holds.rspAccounting
    omega
  have subNat : (state.rsp - 8).toNat = state.rsp.toNat - 8 := by
    exact toNat_sub_eight state.rsp room
  have noWrap : (state.rsp - 8).toNat + 8 ≤ 2 ^ 64 := by
    rw [subNat]
    change state.rsp.toNat - 8 + 8 ≤ 18446744073709551616
    have upper := state.rsp.toNat_lt_size
    change state.rsp.toNat < 18446744073709551616 at upper
    omega
  have below : address.toNat + 8 ≤ (state.rsp - 8).toNat := by
    rw [subNat]
    have := frame.stackRoom
    have := holds.rspAccounting
    omega
  exact spike2_extraction_preserves_text_word effect address noWrap below

/-- The extraction half, discharged one named body at a time.  No trace of all digits is
evaluated: the pass effect advances the boundary invariant by one quotient/remainder step. -/
theorem spike2_decimal_extraction_phase (value : UInt64) (initial : X86_64MachineState)
    (initialEventsRev : List AnyEvent) (frame : Spike2DecimalFrame value initial) :
    DecimalExtractionPhase selectedNonInputPlatformCall spike2Indexed value
      (Spike2ExtractionInvariant value initial initialEventsRev) where
  run completed state eventsRev within holds := by
    rcases holds with ⟨holds⟩
    have digitsBound := decimalDigitCount_le_twenty value
    have hrip := holds.activeRip within
    have decomposition := holds.activeDecomposition within
    have remainingNat : (state.gprs .rax).toNat = holds.remaining := by
      rw [holds.rax]
      simp [Nat.toUInt64, Nat.mod_eq_of_lt holds.remainingBound]
    have stackCapacity : StackPushCapacity 0 state := by
      unfold StackPushCapacity
      change 8 ≤ state.rsp.toNat
      have := frame.stackRoom
      have := holds.rspAccounting
      omega
    have pre := extractionSafety_of_decimalBound value completed 0 state holds.r10 stackCapacity
      holds.fault holds.rcx within
    have safe := extraction_execution_safety state holds.r10 holds.fault
    have effect := extractionPassEffect 236 0 state pre safe
    let final := extractionFinal 236 state
    have finalText3424 : final.read64 5368713424 = state.read64 5368713424 :=
      extraction_text_frame frame holds within effect 5368713424 (by decide)
    have finalText3444 : final.read64 5368713444 = state.read64 5368713444 :=
      extraction_text_frame frame holds within effect 5368713444 (by decide)
    have finalText3457 : final.read64 5368713457 = state.read64 5368713457 :=
      extraction_text_frame frame holds within effect 5368713457 (by decide)
    have room : 8 ≤ state.rsp.toNat := by
      have := frame.stackRoom
      have := holds.rspAccounting
      omega
    have subNat : (state.rsp - 8).toNat = state.rsp.toNat - 8 := by
      exact toNat_sub_eight state.rsp room
    have currentStackNoWrap : state.rsp.toNat + 8 * holds.suffix.length < 2 ^ 64 := by
      rw [holds.suffixLength, holds.rspAccounting]
      exact Nat.lt_trans frame.stackTop (by decide)
    have finalStack : StackHolds final.memory final.rsp
        (byteOfDigit (holds.remaining % 10) :: holds.suffix) := by
      rw [effect.memory, effect.stackPointer, remainingNat,
        byteOfDigit_cast (holds.remaining % 10) (Nat.mod_lt _ (by omega))]
      exact (StackHolds_push state.memory state.rsp _ holds.suffix room currentStackNoWrap).2
        holds.stack
    have finalRspAccounting : final.rsp.toNat + 8 * (completed + 1) = initial.rsp.toNat := by
      rw [effect.stackPointer, subNat]
      calc
        state.rsp.toNat - 8 + 8 * (completed + 1) = state.rsp.toNat + 8 * completed := by omega
        _ = initial.rsp.toNat := holds.rspAccounting
    have finalRdi : final.gprs .rdi = initial.gprs .rdi := by
      rw [extraction_preserves_gpr state .rdi (by decide) (by decide) (by decide) (by decide),
        holds.rdi]
    have finalR10 : final.gprs .r10 = 10 := by
      rw [extraction_preserves_gpr state .r10 (by decide) (by decide) (by decide) (by decide),
        holds.r10]
    have finalText3424Initial : final.read64 5368713424 = initial.read64 5368713424 :=
      finalText3424.trans holds.text3424
    have finalText3444Initial : final.read64 5368713444 = initial.read64 5368713444 :=
      finalText3444.trans holds.text3444
    have finalText3457Initial : final.read64 5368713457 = initial.read64 5368713457 :=
      finalText3457.trans holds.text3457
    by_cases small : holds.remaining < 10
    · have quotientZero : UInt64.ofNat ((state.gprs .rax).toNat / 10) = 0 := by
        rw [remainingNat]
        simp [Nat.div_eq_of_lt small]
      have fallthrough : ¬X86BranchCondition.notEqual.holds
          (extractionStates state).2.2.2.2.2 := by
        rw [extraction_branch_iff state holds.r10]
        exact not_not_intro quotientZero
      have finalRip := extraction_final_rip_fallthrough state hrip safe fallthrough
      have boundary := spike2_selected_silent_nonIat final 5368713444 finalRip (by decide)
        (by rw [finalText3444Initial]; exact frame.text3444)
      have placement := spike2_extraction_selected_placement state hrip safe
        (by
          have selectedFinal : selectedNonInputPlatformCall final.rip final = true := by
            rw [finalRip]
            exact boundary.1
          simpa only [final, extractionFinal] using selectedFinal)
        (by
          have silentFinal : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
              final.rip final = none := by
            rw [finalRip]
            exact boundary.2
          simpa only [final, extractionFinal] using silentFinal)
      have pass : SelectedExtractionPass (Event := AnyEvent) selectedNonInputPlatformCall
          spike2Indexed 236 0 state :=
        ⟨placement, pre, safe, Or.inr fallthrough, effect⟩
      have oneDigit := formatDecimal_single holds.remaining small
      have nextCompleted : completed + 1 = decimalDigitCount value := by
        have lengths := congrArg List.length decomposition
        rw [oneDigit, List.length_append, holds.suffixLength, decimal_full_length] at lengths
        simp only [List.length_cons, List.length_nil, Nat.add_zero] at lengths
        omega
      have nextSuffix : byteOfDigit (holds.remaining % 10) :: holds.suffix =
          formatDecimal value.toNat := by
        rw [Nat.mod_eq_of_lt small]
        rw [decomposition, oneDigit]
        rfl
      refine ⟨236, 0, pass, ?_⟩
      refine ⟨{
        events := holds.events
        within := by omega
        remaining := 0
        remainingBound := by decide
        suffix := byteOfDigit (holds.remaining % 10) :: holds.suffix
        suffixLength := by simp [holds.suffixLength]
        activeDecomposition := ?_
        completedSuffix := ?_
        rax := by rw [effect.quotient, remainingNat]; simp [Nat.div_eq_of_lt small]
        r10 := finalR10
        rcx := by rw [effect.count, holds.rcx]; simp [Nat.toUInt64]
        rspAccounting := finalRspAccounting
        rdi := finalRdi
        fault := effect.fault
        stack := finalStack
        preservesR12 := effect.preservesR12.trans holds.preservesR12
        preservesR13 := effect.preservesR13.trans holds.preservesR13
        preservesR14 := effect.preservesR14.trans holds.preservesR14
        preservesR15 := effect.preservesR15.trans holds.preservesR15
        text3424 := finalText3424Initial
        text3444 := finalText3444Initial
        text3457 := finalText3457Initial
        activeRip := ?_
        completedRip := ?_ }⟩
      · intro impossible; omega
      · intro _; exact nextSuffix
      · intro impossible; omega
      · intro _; exact finalRip
    · have large : 10 ≤ holds.remaining := by omega
      have quotientPos : 0 < holds.remaining / 10 := Nat.div_pos (by omega) (by omega)
      have quotientBound : holds.remaining / 10 < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) holds.remainingBound
      have taken : X86BranchCondition.notEqual.holds
          (extractionStates state).2.2.2.2.2 := by
        rw [extraction_branch_iff state holds.r10, remainingNat]
        intro zero
        have := congrArg UInt64.toNat zero
        simp [Nat.toUInt64, Nat.mod_eq_of_lt quotientBound] at this
        omega
      have finalRip := extraction_final_rip_taken state hrip safe taken
      have boundary := spike2_selected_silent_nonIat final 5368713424 finalRip (by decide)
        (by rw [finalText3424Initial]; exact frame.text3424)
      have placement := spike2_extraction_selected_placement state hrip safe
        (by
          have selectedFinal : selectedNonInputPlatformCall final.rip final = true := by
            rw [finalRip]
            exact boundary.1
          simpa only [final, extractionFinal] using selectedFinal)
        (by
          have silentFinal : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
              final.rip final = none := by
            rw [finalRip]
            exact boundary.2
          simpa only [final, extractionFinal] using silentFinal)
      have pass : SelectedExtractionPass (Event := AnyEvent) selectedNonInputPlatformCall
          spike2Indexed 236 0 state :=
        ⟨placement, pre, safe, Or.inl taken, effect⟩
      have stepFormat := formatDecimal_step holds.remaining large
      have nextDecomposition : formatDecimal value.toNat =
          formatDecimal (holds.remaining / 10) ++
            (byteOfDigit (holds.remaining % 10) :: holds.suffix) := by
        rw [decomposition, stepFormat, List.append_assoc]
        rfl
      have nextWithin : completed + 1 < decimalDigitCount value := by
        have lengths := congrArg List.length nextDecomposition
        simp only [List.length_append, List.length_cons] at lengths
        rw [holds.suffixLength, decimal_full_length] at lengths
        have nonempty := formatDecimal_ne_nil (holds.remaining / 10)
        have positive : 0 < (formatDecimal (holds.remaining / 10)).length :=
          List.length_pos_iff.mpr nonempty
        omega
      refine ⟨236, 0, pass, ?_⟩
      refine ⟨{
        events := holds.events
        within := by omega
        remaining := holds.remaining / 10
        remainingBound := quotientBound
        suffix := byteOfDigit (holds.remaining % 10) :: holds.suffix
        suffixLength := by simp [holds.suffixLength]
        activeDecomposition := fun _ => nextDecomposition
        completedSuffix := ?_
        rax := by rw [effect.quotient, remainingNat]
        r10 := finalR10
        rcx := by rw [effect.count, holds.rcx]; simp [Nat.toUInt64]
        rspAccounting := finalRspAccounting
        rdi := finalRdi
        fault := effect.fault
        stack := finalStack
        preservesR12 := effect.preservesR12.trans holds.preservesR12
        preservesR13 := effect.preservesR13.trans holds.preservesR13
        preservesR14 := effect.preservesR14.trans holds.preservesR14
        preservesR15 := effect.preservesR15.trans holds.preservesR15
        text3424 := finalText3424Initial
        text3444 := finalText3444Initial
        text3457 := finalText3457Initial
        activeRip := fun _ => finalRip
        completedRip := ?_ }⟩
      · intro impossible; omega
      · intro impossible; omega

/-- The write invariant is the meet point: `written` is the forward buffer fact and `remaining`
is the backward stack requirement. -/
structure Spike2WriteFacts (value : UInt64) (initial : X86_64MachineState)
    (initialEventsRev : List AnyEvent) (completed : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) where
  events : eventsRev = initialEventsRev
  within : completed ≤ decimalDigitCount value
  written : List UInt8
  remaining : List UInt8
  content : written ++ remaining = formatDecimal value.toNat
  writtenLength : written.length = completed
  remainingLength : remaining.length + completed = decimalDigitCount value
  rcx : state.gprs .rcx = UInt64.ofNat remaining.length
  rspAccounting : state.rsp.toNat + 8 * remaining.length = initial.rsp.toNat
  rdi : state.gprs .rdi = initial.gprs .rdi + UInt64.ofNat completed
  rdiNat : (state.gprs .rdi).toNat = (initial.gprs .rdi).toNat + completed
  fault : state.fault = none
  stack : StackHolds state.memory state.rsp remaining
  buffer : BufHolds state.memory (initial.gprs .rdi) written
  preservesR12 : state.gprs .r12 = initial.gprs .r12
  preservesR13 : state.gprs .r13 = initial.gprs .r13
  preservesR14 : state.gprs .r14 = initial.gprs .r14
  preservesR15 : state.gprs .r15 = initial.gprs .r15
  text3424 : state.read64 5368713424 = initial.read64 5368713424
  text3444 : state.read64 5368713444 = initial.read64 5368713444
  text3457 : state.read64 5368713457 = initial.read64 5368713457
  activeRip : completed < decimalDigitCount value → state.rip = 5368713444
  completedRip : completed = decimalDigitCount value → state.rip = 5368713457

def Spike2WriteInvariant (value : UInt64) (initial : X86_64MachineState)
    (initialEventsRev : List AnyEvent) (completed : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) : Prop :=
  Nonempty (Spike2WriteFacts value initial initialEventsRev completed state eventsRev)

structure Spike2DecimalCallerFrame (initial final : X86_64MachineState) : Prop where
  rip : final.rip = 5368713457
  fault : final.fault = none
  r10 : final.gprs .r10 = initial.gprs .r10
  text3424 : final.read64 5368713424 = initial.read64 5368713424
  text3444 : final.read64 5368713444 = initial.read64 5368713444
  text3457 : final.read64 5368713457 = initial.read64 5368713457

private theorem write_text_frame {value : UInt64} {initial state final : X86_64MachineState}
    {initialEventsRev eventsRev : List AnyEvent} {completed : Nat}
    (frame : Spike2DecimalFrame value initial)
    (holds : Spike2WriteFacts value initial initialEventsRev completed state eventsRev)
    (within : completed < decimalDigitCount value)
    (effect : WritePassEffect 243 state final) (address : UInt64)
    (addressBound : address.toNat + 8 ≤ 5368713465) :
    final.read64 address = state.read64 address := by
  have noWrap : (state.gprs .rdi).toNat + 1 ≤ 2 ^ 64 := by
    rw [holds.rdiNat]
    have := frame.bufferTop
    omega
  have below : address.toNat + 8 ≤ (state.gprs .rdi).toNat := by
    rw [holds.rdiNat]
    have := frame.stackRoom
    have := frame.bufferAboveStack
    omega
  exact spike2_write_preserves_text_word effect address noWrap below

private theorem BufHolds_getElem (memory : X86_64Memory) (start : UInt64)
    (bytes : List UInt8) (holds : BufHolds memory start bytes) (index : Nat)
    (within : index < bytes.length) :
    X86_64Mem.readByte memory (start + UInt64.ofNat index) = bytes[index] := by
  induction bytes generalizing start index with
  | nil => simp at within
  | cons byte rest ih =>
    cases index with
    | zero =>
      have head := holds.1
      change (X86_64Mem.readByte memory start).toUInt64 = byte.toUInt64 at head
      have exactByte : X86_64Mem.readByte memory start = byte := by
        exact UInt8.toUInt64_inj.mp head
      simpa using exactByte
    | succ index =>
      have tail := ih (start + 1) holds.2 index (by simpa using within)
      have address : start + 1 + UInt64.ofNat index =
          start + UInt64.ofNat (index + 1) := by
        rw [UInt64.add_assoc]
        congr 1
        rw [UInt64.add_comm]
        simp [Nat.toUInt64]
      rw [address] at tail
      simpa using tail

private theorem decimalBytesAt_eq_of_BufHolds (memory : X86_64Memory) (start : UInt64)
    (bytes : List UInt8) (holds : BufHolds memory start bytes) :
    decimalBytesAt memory start bytes.length = bytes := by
  apply List.ext_getElem
  · simp [decimalBytesAt]
  · intro index left right
    simpa [decimalBytesAt] using BufHolds_getElem memory start bytes holds index right

/-- Reverse-write phase, advancing the stack/buffer cutpoint by one byte. -/
theorem spike2_decimal_write_phase (value : UInt64) (initial : X86_64MachineState)
    (initialEventsRev : List AnyEvent) (frame : Spike2DecimalFrame value initial) :
    DecimalWritePhase selectedNonInputPlatformCall spike2Indexed value
      (Spike2WriteInvariant value initial initialEventsRev) where
  run completed state eventsRev within holds := by
    rcases holds with ⟨holds⟩
    have digitsBound := decimalDigitCount_le_twenty value
    have hrip := holds.activeRip within
    have remainingNonempty : holds.remaining ≠ [] := by
      intro empty
      have accounting := holds.remainingLength
      rw [empty] at accounting
      simp only [List.length_nil, Nat.zero_add] at accounting
      omega
    rcases remainingCons : holds.remaining with _ | ⟨byte, rest⟩
    · exact (remainingNonempty remainingCons).elim
    · have remainingLength : holds.remaining.length = rest.length + 1 := by
        rw [remainingCons]
        simp
      have restAccounting : rest.length + 1 + completed = decimalDigitCount value := by
        have accounting := holds.remainingLength
        rw [remainingCons] at accounting
        simpa only [List.length_cons] using accounting
      have rspAccountingCons : state.rsp.toNat + 8 * (rest.length + 1) =
          initial.rsp.toNat := by
        have accounting := holds.rspAccounting
        rw [remainingCons] at accounting
        simpa only [List.length_cons] using accounting
      have stackCons : StackHolds state.memory state.rsp (byte :: rest) := by
        simpa only [remainingCons] using holds.stack
      have rspPlusEight : (state.rsp + 8).toNat = state.rsp.toNat + 8 := by
        rw [UInt64.toNat_add]
        have bound : state.rsp.toNat + 8 < 2 ^ 64 := by
          have := rspAccountingCons
          have := frame.stackTop
          omega
        simp [Nat.mod_eq_of_lt bound]
      have stackCapacity : StackPopCapacity initial.rsp state := by
        unfold StackPopCapacity
        have := rspAccountingCons
        omega
      have bufferLimitNat : (UInt64.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := by
        simp [Nat.toUInt64, Nat.mod_eq_of_lt (by omega : 2 ^ 64 - 1 < 2 ^ 64)]
      have bufferCapacity : BufferWriteCapacity (UInt64.ofNat (2 ^ 64 - 1)) state := by
        unfold BufferWriteCapacity
        rw [bufferLimitNat, holds.rdiNat]
        have := frame.bufferTop
        omega
      have countPositive : state.gprs .rcx ≠ 0 := by
        rw [holds.rcx, remainingLength]
        intro zero
        have zeroNat := congrArg UInt64.toNat zero
        have restBound : rest.length + 1 < 2 ^ 64 := by omega
        simp [Nat.toUInt64, Nat.mod_eq_of_lt restBound] at zeroNat
      have pre : WriteSafety initial.rsp (UInt64.ofNat (2 ^ 64 - 1)) state :=
        ⟨stackCapacity, bufferCapacity, countPositive, holds.fault⟩
      have safe := write_execution_safety state holds.fault
      have effect := writePassEffect 243 initial.rsp (UInt64.ofNat (2 ^ 64 - 1)) state pre safe
      let final := writeFinal 243 state
      have finalText3424 : final.read64 5368713424 = state.read64 5368713424 :=
        write_text_frame frame holds within effect 5368713424 (by decide)
      have finalText3444 : final.read64 5368713444 = state.read64 5368713444 :=
        write_text_frame frame holds within effect 5368713444 (by decide)
      have finalText3457 : final.read64 5368713457 = state.read64 5368713457 :=
        write_text_frame frame holds within effect 5368713457 (by decide)
      have finalText3424Initial : final.read64 5368713424 = initial.read64 5368713424 :=
        finalText3424.trans holds.text3424
      have finalText3444Initial : final.read64 5368713444 = initial.read64 5368713444 :=
        finalText3444.trans holds.text3444
      have finalText3457Initial : final.read64 5368713457 = initial.read64 5368713457 :=
        finalText3457.trans holds.text3457
      have cursorNoWrap : (state.gprs .rdi).toNat + 1 ≤ 2 ^ 64 := by
        rw [holds.rdiNat]
        have := frame.bufferTop
        omega
      have stackTail : StackHolds state.memory (state.rsp + 8) rest := by
        exact stackCons.2
      have stackDisjoint : (state.gprs .rdi).toNat ≥
          (state.rsp + 8).toNat + 8 * rest.length := by
        rw [rspPlusEight, holds.rdiNat]
        have := rspAccountingCons
        have := frame.bufferAboveStack
        omega
      have finalStack : StackHolds final.memory final.rsp rest := by
        rw [effect.memory, effect.stackPointer]
        rw [StackHolds_write8_disjoint state.memory (state.rsp + 8) (state.gprs .rdi)
          (state.read64 state.rsp).toUInt8.toUInt64 rest stackDisjoint]
        exact stackTail
      have cursorAddress : initial.gprs .rdi + UInt64.ofNat holds.written.length =
          state.gprs .rdi := by
        rw [holds.writtenLength, holds.rdi]
      have prefixPreserved : BufHolds final.memory (initial.gprs .rdi) holds.written =
          BufHolds state.memory (initial.gprs .rdi) holds.written := by
        rw [effect.memory]
        apply BufHolds_write8_after
        · exact cursorNoWrap
        · rw [holds.writtenLength, holds.rdiNat]
          exact Nat.le_refl _
        · rw [holds.writtenLength]
          have := frame.bufferTop
          omega
      have writtenByte : X86_64Mem.read .w8 (state.gprs .rdi) final.memory = byte.toUInt64 := by
        rw [effect.memory]
        have stackHead : state.read64 state.rsp = byte.toUInt64 := by
          exact stackCons.1
        rw [stackHead]
        simp [X86_64Mem.read, X86_64Mem.write]
      have finalBuffer : BufHolds final.memory (initial.gprs .rdi)
          (holds.written ++ [byte]) := by
        rw [BufHolds_append]
        constructor
        · rw [prefixPreserved]
          exact holds.buffer
        · rw [cursorAddress]
          exact ⟨writtenByte, trivial⟩
      have finalRspAccounting : final.rsp.toNat + 8 * rest.length = initial.rsp.toNat := by
        rw [effect.stackPointer, rspPlusEight]
        omega
      have finalRdiNat : (final.gprs .rdi).toNat =
          (initial.gprs .rdi).toNat + (completed + 1) := by
        rw [effect.cursor, UInt64.toNat_add]
        have bound : (state.gprs .rdi).toNat + 1 < 2 ^ 64 := by
          rw [holds.rdiNat]
          have := frame.bufferTop
          omega
        rw [show (1 : UInt64).toNat = 1 by decide, Nat.mod_eq_of_lt bound, holds.rdiNat]
        omega
      have finalRdi : final.gprs .rdi =
          initial.gprs .rdi + UInt64.ofNat (completed + 1) := by
        apply UInt64.toNat_inj.mp
        rw [finalRdiNat, UInt64.toNat_add]
        have bound : (initial.gprs .rdi).toNat + (completed + 1) < 2 ^ 64 := by
          have := frame.bufferTop
          omega
        simp [Nat.toUInt64, Nat.mod_eq_of_lt bound]
      have finalContent : holds.written ++ [byte] ++ rest = formatDecimal value.toNat := by
        simpa [remainingCons, List.append_assoc] using holds.content
      have finalRcx : final.gprs .rcx = UInt64.ofNat rest.length := by
        rw [effect.count, holds.rcx, remainingLength]
        simp [Nat.toUInt64]
      by_cases restEmpty : rest = []
      · have fallthrough : ¬X86BranchCondition.notEqual.holds (writeStates state).2.2.2 := by
          rw [write_branch_iff, holds.rcx, remainingLength, restEmpty]
          simp
        have finalRip := write_final_rip_fallthrough state hrip fallthrough
        have boundary := spike2_selected_silent_nonIat final 5368713457 finalRip (by decide)
          (by rw [finalText3457Initial]; exact frame.text3457)
        have placement := spike2_write_selected_placement state hrip safe
          (by
            have selectedFinal : selectedNonInputPlatformCall final.rip final = true := by
              rw [finalRip]
              exact boundary.1
            simpa only [final, writeFinal] using selectedFinal)
          (by
            have silentFinal : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
                final.rip final = none := by
              rw [finalRip]
              exact boundary.2
            simpa only [final, writeFinal] using silentFinal)
        have pass : SelectedWritePass (Event := AnyEvent) selectedNonInputPlatformCall
            spike2Indexed 243 initial.rsp (UInt64.ofNat (2 ^ 64 - 1)) state :=
          ⟨placement, pre, safe, Or.inr fallthrough, effect⟩
        refine ⟨243, initial.rsp, UInt64.ofNat (2 ^ 64 - 1), pass, ?_⟩
        refine ⟨{
          events := holds.events
          within := by omega
          written := holds.written ++ [byte]
          remaining := rest
          content := finalContent
          writtenLength := by simp [holds.writtenLength]
          remainingLength := by
            have accounting := restAccounting
            rw [restEmpty] at accounting
            simp only [List.length_nil, Nat.zero_add] at accounting
            rw [restEmpty]
            simp only [List.length_nil, Nat.zero_add]
            omega
          rcx := finalRcx
          rspAccounting := finalRspAccounting
          rdi := finalRdi
          rdiNat := finalRdiNat
          fault := effect.fault
          stack := finalStack
          buffer := finalBuffer
          preservesR12 := effect.preservesR12.trans holds.preservesR12
          preservesR13 := effect.preservesR13.trans holds.preservesR13
          preservesR14 := effect.preservesR14.trans holds.preservesR14
          preservesR15 := effect.preservesR15.trans holds.preservesR15
          text3424 := finalText3424Initial
          text3444 := finalText3444Initial
          text3457 := finalText3457Initial
          activeRip := by intro impossible; rw [restEmpty] at restAccounting; simp at restAccounting; omega
          completedRip := fun _ => finalRip }⟩
      · have taken : X86BranchCondition.notEqual.holds (writeStates state).2.2.2 := by
          rw [write_branch_iff, holds.rcx, remainingLength]
          intro one
          have oneNat := congrArg UInt64.toNat one
          have restBound : rest.length + 1 < 2 ^ 64 := by omega
          change (rest.length + 1) % (2 ^ 64) = 1 at oneNat
          rw [Nat.mod_eq_of_lt restBound] at oneNat
          apply restEmpty
          simpa using (show rest.length = 0 by omega)
        have finalRip := write_final_rip_taken state hrip taken
        have boundary := spike2_selected_silent_nonIat final 5368713444 finalRip (by decide)
          (by rw [finalText3444Initial]; exact frame.text3444)
        have placement := spike2_write_selected_placement state hrip safe
          (by
            have selectedFinal : selectedNonInputPlatformCall final.rip final = true := by
              rw [finalRip]
              exact boundary.1
            simpa only [final, writeFinal] using selectedFinal)
          (by
            have silentFinal : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
                final.rip final = none := by
              rw [finalRip]
              exact boundary.2
            simpa only [final, writeFinal] using silentFinal)
        have pass : SelectedWritePass (Event := AnyEvent) selectedNonInputPlatformCall
            spike2Indexed 243 initial.rsp (UInt64.ofNat (2 ^ 64 - 1)) state :=
          ⟨placement, pre, safe, Or.inl taken, effect⟩
        refine ⟨243, initial.rsp, UInt64.ofNat (2 ^ 64 - 1), pass, ?_⟩
        refine ⟨{
          events := holds.events
          within := by omega
          written := holds.written ++ [byte]
          remaining := rest
          content := finalContent
          writtenLength := by simp [holds.writtenLength]
          remainingLength := by omega
          rcx := finalRcx
          rspAccounting := finalRspAccounting
          rdi := finalRdi
          rdiNat := finalRdiNat
          fault := effect.fault
          stack := finalStack
          buffer := finalBuffer
          preservesR12 := effect.preservesR12.trans holds.preservesR12
          preservesR13 := effect.preservesR13.trans holds.preservesR13
          preservesR14 := effect.preservesR14.trans holds.preservesR14
          preservesR15 := effect.preservesR15.trans holds.preservesR15
          text3424 := finalText3424Initial
          text3444 := finalText3444Initial
          text3457 := finalText3457Initial
          activeRip := fun _ => finalRip
          completedRip := by
            intro impossible
            exfalso
            apply restEmpty
            simpa using (show rest.length = 0 by omega) }⟩

end Spikes.Spike2Fibonacci.Windows
