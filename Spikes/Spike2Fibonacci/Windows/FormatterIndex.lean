/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.FormatterBranch
import Spikes.Spike2Fibonacci.Windows.FormatterLiteral

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.Windows Gasm.Targets.Linux Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions Gasm.Targets.X86_64.MacroAssembler

private theorem sequentialCmpIndex : SequentialInstruction (cmp_r64_imm8 .r13 10) where
  encoding := .compareImm8 .r13 10
  safeFallthrough := by intro _ _; rfl

/-- The branch state after comparing the formatter index against ten. -/
def spike2AfterIndexCompare (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (cmp_r64_imm8 .r13 10) state

/-- The local index-format branch following the `Fib(` literal. -/
def spike2AfterIndexHeader (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (jge_rel8 41) (spike2AfterIndexCompare state)

theorem spike2_index_header_one_digit_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713297)
    (oneDigit : ¬ X86BranchCondition.greaterEqual.holds (spike2AfterIndexCompare state))
    (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 2 state eventsRev
      (spike2AfterIndexHeader state) eventsRev [] := by
  have hcmpRip : (spike2AfterIndexCompare state).rip = 5368713301 := by
    unfold spike2AfterIndexCompare
    rw [show (X86_64Instruction.step (cmp_r64_imm8 .r13 10) state).rip = state.rip + 4 by rfl, hrip]
    rfl
  have hcmpSafe : (spike2AfterIndexCompare state).fault = none := by
    change state.fault = none
    exact hsafe
  have hjgeRip : (spike2AfterIndexHeader state).rip = 5368713303 := by
    unfold spike2AfterIndexHeader
    simp only [X86BranchCondition.holds] at oneDigit
    rw [step_jge_rel8_fallthrough_rip _ _ (decide_eq_false_iff_not.mpr oneDigit), hcmpRip]
    rfl
  have compare := spike2_selected_local_prefix (cmp_r64_imm8 .r13 10) sequentialCmpIndex
    state eventsRev (by rw [hrip]; rfl) 5368713301 hcmpRip (by decide) (by decide) hcmpSafe
  have branch := spike2_selected_conditional_fallthrough_prefix (.jge8 41)
    (spike2AfterIndexCompare state) oneDigit eventsRev (by rw [hcmpRip]; rfl)
    5368713303 (by simpa [spike2AfterIndexHeader] using hjgeRip) (by
      change selectedNonInputPlatformCall (spike2AfterIndexHeader state).rip
        (spike2AfterIndexHeader state) = true
      rw [hjgeRip]
      have hnotLinux : (5368713303 : UInt64) ≠ linuxSyscallEntry := by decide
      simp [selectedNonInputPlatformCall, hnotLinux, selectedNonInputWin32Call,
        Gasm.Targets.Windows.findIatIndex]) (by
      change @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
        (spike2AfterIndexHeader state).rip (spike2AfterIndexHeader state) = none
      rw [hjgeRip]
      change (if (5368713303 : UInt64) == linuxSyscallEntry then
        linuxSyscallIntercept _ _ else Gasm.Targets.Windows.win32Intercept _ _) = none
      simp [linuxSyscallEntry, Gasm.Targets.Windows.win32Intercept,
        Gasm.Targets.Windows.findIatIndex]) (by
      change state.fault = none
      exact hsafe)
  simpa [spike2AfterIndexHeader, spike2AfterIndexCompare] using
    ProductionPrefix.SelectedPrefix.append compare branch

theorem spike2_index_header_two_digit_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713297)
    (twoDigit : X86BranchCondition.greaterEqual.holds (spike2AfterIndexCompare state))
    (twoSelected : selectedNonInputPlatformCall (spike2AfterIndexHeader state).rip
      (spike2AfterIndexHeader state) = true)
    (twoSilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (spike2AfterIndexHeader state).rip (spike2AfterIndexHeader state) = none)
    (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 2 state eventsRev
      (spike2AfterIndexHeader state) eventsRev [] := by
  have hcmpRip : (spike2AfterIndexCompare state).rip = 5368713301 := by
    unfold spike2AfterIndexCompare
    rw [show (X86_64Instruction.step (cmp_r64_imm8 .r13 10) state).rip = state.rip + 4 by rfl, hrip]
    rfl
  have hcmpSafe : (spike2AfterIndexCompare state).fault = none := by
    change state.fault = none
    exact hsafe
  have hjgeRip : (spike2AfterIndexHeader state).rip = 5368713344 := by
    unfold spike2AfterIndexHeader
    simp only [X86BranchCondition.holds] at twoDigit
    rw [step_jge_rel8_taken_rip _ _ (decide_eq_true_iff.mpr twoDigit), hcmpRip]
    decide
  have compare := spike2_selected_local_prefix (cmp_r64_imm8 .r13 10) sequentialCmpIndex
    state eventsRev (by rw [hrip]; rfl) 5368713301 hcmpRip (by decide) (by decide) hcmpSafe
  have branch := spike2_selected_conditional_prefix (.jge8 41)
    (spike2AfterIndexCompare state) twoDigit eventsRev (by rw [hcmpRip]; rfl)
    5368713344 (by simpa [spike2AfterIndexHeader] using hjgeRip) (by
      change selectedNonInputPlatformCall (spike2AfterIndexHeader state).rip
        (spike2AfterIndexHeader state) = true
      exact twoSelected) (by
      change @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
        (spike2AfterIndexHeader state).rip (spike2AfterIndexHeader state) = none
      exact twoSilent) (by
      change state.fault = none
      exact hsafe)
  simpa [spike2AfterIndexHeader, spike2AfterIndexCompare] using
    ProductionPrefix.SelectedPrefix.append compare branch

end Spikes.Spike2Fibonacci.Windows
