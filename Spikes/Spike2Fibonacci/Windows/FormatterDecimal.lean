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
import Gasm.Targets.X86_64.DecimalSegments
import Spikes.Spike2Fibonacci.Windows.FormatterBranch

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForFormatterDecimal :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.Windows Gasm.Targets.Linux
open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.DecimalSegments

set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

private theorem div_r10_fallthrough (state : X86_64MachineState)
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

/-- Concrete selected placement of one decimal extraction pass in the Spike 2 formatter.
The branch successor is intentionally supplied by the caller: both the loop back-edge and its
fallthrough are aligned text boundaries, so neither may be classified by the unaligned-local
shortcut. -/
theorem spike2_extraction_selected_placement (state : X86_64MachineState)
    (hrip : state.rip = 5368713424) (safe : ExtractionExecutionSafety 236 state)
    (branchSelected : selectedNonInputPlatformCall
      (X86_64Instruction.step (jne_rel8 236) (extractionStates state).2.2.2.2.2).rip
      (X86_64Instruction.step (jne_rel8 236) (extractionStates state).2.2.2.2.2) = true)
    (branchSilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (X86_64Instruction.step (jne_rel8 236) (extractionStates state).2.2.2.2.2).rip
      (X86_64Instruction.step (jne_rel8 236) (extractionStates state).2.2.2.2.2) = none) :
    ExtractionSelectedPlacement (Event := AnyEvent) selectedNonInputPlatformCall spike2Indexed 236 state := by
  have h1 : (extractionStates state).1.rip = 5368713426 := by
    unfold extractionStates
    rw [show (X86_64Instruction.step (xor_r32 .edx .edx) state).rip = state.rip + 2 by rfl, hrip]
    rfl
  have h2 : (extractionStates state).2.1.rip = 5368713429 := by
    have hdivSafe : (X86_64Instruction.step (div_r64 .r10)
        (X86_64Instruction.step (xor_r32 .edx .edx) state)).fault = none := by
      simpa [extractionStates] using safe.divSafe
    rw [show (extractionStates state).2.1.rip =
      (X86_64Instruction.step (div_r64 .r10)
        (X86_64Instruction.step (xor_r32 .edx .edx) state)).rip by rfl,
      div_r10_fallthrough _ hdivSafe,
      show (X86_64Instruction.step (xor_r32 .edx .edx) state).rip = state.rip + 2 by rfl,
      hrip]
    rfl
  have h3 : (extractionStates state).2.2.1.rip = 5368713433 := by
    have h2' : (X86_64Instruction.step (div_r64 .r10)
        (X86_64Instruction.step (xor_r32 .edx .edx) state)).rip = 5368713429 := by
      simpa [extractionStates] using h2
    unfold extractionStates
    rw [show (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
      (X86_64Instruction.step (div_r64 .r10)
        (X86_64Instruction.step (xor_r32 .edx .edx) state))).rip =
      (X86_64Instruction.step (div_r64 .r10)
        (X86_64Instruction.step (xor_r32 .edx .edx) state)).rip + 4 by rfl]
    rw [h2']
    decide
  have h4 : (extractionStates state).2.2.2.1.rip = 5368713434 := by
    have h3' : (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
        (X86_64Instruction.step (div_r64 .r10)
          (X86_64Instruction.step (xor_r32 .edx .edx) state))).rip = 5368713433 := by
      simpa [extractionStates] using h3
    unfold extractionStates
    rw [show (X86_64Instruction.step (push_r64 .rdx)
      (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
        (X86_64Instruction.step (div_r64 .r10)
          (X86_64Instruction.step (xor_r32 .edx .edx) state)))).rip =
      (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
        (X86_64Instruction.step (div_r64 .r10)
          (X86_64Instruction.step (xor_r32 .edx .edx) state))).rip + 1 by rfl]
    rw [h3']
    decide
  have h5 : (extractionStates state).2.2.2.2.1.rip = 5368713438 := by
    have h4' : (X86_64Instruction.step (push_r64 .rdx)
        (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
          (X86_64Instruction.step (div_r64 .r10)
            (X86_64Instruction.step (xor_r32 .edx .edx) state)))).rip = 5368713434 := by
      simpa [extractionStates] using h4
    unfold extractionStates
    rw [show (X86_64Instruction.step (add_r64_imm8 .rcx 1)
      (X86_64Instruction.step (push_r64 .rdx)
        (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
          (X86_64Instruction.step (div_r64 .r10)
            (X86_64Instruction.step (xor_r32 .edx .edx) state))))).rip =
      (X86_64Instruction.step (push_r64 .rdx)
        (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
          (X86_64Instruction.step (div_r64 .r10)
            (X86_64Instruction.step (xor_r32 .edx .edx) state)))).rip + 4 by rfl]
    rw [h4']
    decide
  have h6 : (extractionStates state).2.2.2.2.2.rip = 5368713442 := by
    have h5' : (X86_64Instruction.step (add_r64_imm8 .rcx 1)
        (X86_64Instruction.step (push_r64 .rdx)
          (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
            (X86_64Instruction.step (div_r64 .r10)
              (X86_64Instruction.step (xor_r32 .edx .edx) state))))).rip = 5368713438 := by
      simpa [extractionStates] using h5
    unfold extractionStates
    rw [show (X86_64Instruction.step (cmp_r64_imm8 .rax 0)
      (X86_64Instruction.step (add_r64_imm8 .rcx 1)
        (X86_64Instruction.step (push_r64 .rdx)
          (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
            (X86_64Instruction.step (div_r64 .r10)
              (X86_64Instruction.step (xor_r32 .edx .edx) state)))))).rip =
      (X86_64Instruction.step (add_r64_imm8 .rcx 1)
        (X86_64Instruction.step (push_r64 .rdx)
          (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
            (X86_64Instruction.step (div_r64 .r10)
              (X86_64Instruction.step (xor_r32 .edx .edx) state))))).rip + 4 by rfl]
    rw [h5']
    decide
  have s1 := spike2_selected_silent_unaligned (extractionStates state).1 5368713426 h1
    (by decide) (by decide)
  have s2 := spike2_selected_silent_unaligned (extractionStates state).2.1 5368713429 h2
    (by decide) (by decide)
  have s3 := spike2_selected_silent_unaligned (extractionStates state).2.2.1 5368713433 h3
    (by decide) (by decide)
  have s4 := spike2_selected_silent_unaligned (extractionStates state).2.2.2.1 5368713434 h4
    (by decide) (by decide)
  have s5 := spike2_selected_silent_unaligned (extractionStates state).2.2.2.2.1 5368713438 h5
    (by decide) (by decide)
  have s6 := spike2_selected_silent_unaligned (extractionStates state).2.2.2.2.2 5368713442 h6
    (by decide) (by decide)
  have ss1 : selectedNonInputPlatformCall (extractionStates state).1.rip
      (extractionStates state).1 = true ∧
      @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _ (extractionStates state).1.rip
        (extractionStates state).1 = none := by simpa only [h1] using s1
  have ss2 : selectedNonInputPlatformCall (extractionStates state).2.1.rip
      (extractionStates state).2.1 = true ∧
      @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _ (extractionStates state).2.1.rip
        (extractionStates state).2.1 = none := by simpa only [h2] using s2
  have ss3 : selectedNonInputPlatformCall (extractionStates state).2.2.1.rip
      (extractionStates state).2.2.1 = true ∧
      @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _ (extractionStates state).2.2.1.rip
        (extractionStates state).2.2.1 = none := by simpa only [h3] using s3
  have ss4 : selectedNonInputPlatformCall (extractionStates state).2.2.2.1.rip
      (extractionStates state).2.2.2.1 = true ∧
      @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _ (extractionStates state).2.2.2.1.rip
        (extractionStates state).2.2.2.1 = none := by simpa only [h4] using s4
  have ss5 : selectedNonInputPlatformCall (extractionStates state).2.2.2.2.1.rip
      (extractionStates state).2.2.2.2.1 = true ∧
      @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _ (extractionStates state).2.2.2.2.1.rip
        (extractionStates state).2.2.2.2.1 = none := by simpa only [h5] using s5
  have ss6 : selectedNonInputPlatformCall (extractionStates state).2.2.2.2.2.rip
      (extractionStates state).2.2.2.2.2 = true ∧
      @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _ (extractionStates state).2.2.2.2.2.rip
        (extractionStates state).2.2.2.2.2 = none := by simpa only [h6] using s6
  refine {
    lookupXor := ?_, lookupDiv := ?_, lookupAscii := ?_, lookupPush := ?_,
    lookupCount := ?_, lookupCmp := ?_, lookupBranch := ?_,
    silentXor := ss1.2, silentDiv := ss2.2, silentAscii := ss3.2, silentPush := ss4.2,
    silentCount := ss5.2, silentCmp := ss6.2, silentBranch := branchSilent,
    backTarget := ?_, selectedXor := ss1.1, selectedDiv := ss2.1, selectedAscii := ss3.1,
    selectedPush := ss4.1, selectedCount := ss5.1, selectedCmp := ss6.1,
    selectedBranch := branchSelected }
  · rw [hrip]; rfl
  · rw [h1]; rfl
  · rw [h2]; rfl
  · rw [h3]; rfl
  · rw [h4]; rfl
  · rw [h5]; rfl
  · rw [h6]; rfl
  · rw [h6, hrip]
    decide

/-- One exact selected decimal extraction pass, including its explicit taken/fallthrough edge. -/
theorem spike2_extraction_selected_prefix (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (stackLower : UInt64) (hrip : state.rip = 5368713424)
    (pre : ExtractionSafety stackLower state) (safe : ExtractionExecutionSafety 236 state)
    (branchSelected : selectedNonInputPlatformCall
      (X86_64Instruction.step (jne_rel8 236) (extractionStates state).2.2.2.2.2).rip
      (X86_64Instruction.step (jne_rel8 236) (extractionStates state).2.2.2.2.2) = true)
    (branchSilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (X86_64Instruction.step (jne_rel8 236) (extractionStates state).2.2.2.2.2).rip
      (X86_64Instruction.step (jne_rel8 236) (extractionStates state).2.2.2.2.2) = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 7 state eventsRev
      (extractionFinal 236 state) eventsRev [] := by
  have placement := spike2_extraction_selected_placement state hrip safe branchSelected branchSilent
  by_cases taken : X86BranchCondition.notEqual.holds (extractionStates state).2.2.2.2.2
  · exact extractionSelectedPrefixTaken placement pre safe taken
  · exact extractionSelectedPrefixFallthrough placement pre safe taken

/-- Concrete selected placement of one decimal reverse-write pass in the Spike 2 formatter.
As for extraction, the branch's actual successor is supplied explicitly because the loop target is
an aligned text boundary. -/
theorem spike2_write_selected_placement (state : X86_64MachineState)
    (hrip : state.rip = 5368713444) (safe : WriteExecutionSafety 243 state)
    (branchSelected : selectedNonInputPlatformCall
      (X86_64Instruction.step (jne_rel8 243) (writeStates state).2.2.2).rip
      (X86_64Instruction.step (jne_rel8 243) (writeStates state).2.2.2) = true)
    (branchSilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (X86_64Instruction.step (jne_rel8 243) (writeStates state).2.2.2).rip
      (X86_64Instruction.step (jne_rel8 243) (writeStates state).2.2.2) = none) :
    WriteSelectedPlacement (Event := AnyEvent) selectedNonInputPlatformCall spike2Indexed 243 state := by
  have h1 : (writeStates state).1.rip = 5368713445 := by
    unfold writeStates
    rw [show (X86_64Instruction.step (pop_r64 .rdx) state).rip = state.rip + 1 by rfl, hrip]
    rfl
  have h2 : (writeStates state).2.1.rip = 5368713447 := by
    have h1' : (X86_64Instruction.step (pop_r64 .rdx) state).rip = 5368713445 := by
      simpa [writeStates] using h1
    unfold writeStates
    rw [show (X86_64Instruction.step (mov_mem8 .rdi .rdx)
      (X86_64Instruction.step (pop_r64 .rdx) state)).rip =
      (X86_64Instruction.step (pop_r64 .rdx) state).rip + 2 by rfl, h1']
    decide
  have h3 : (writeStates state).2.2.1.rip = 5368713451 := by
    have h2' : (X86_64Instruction.step (mov_mem8 .rdi .rdx)
        (X86_64Instruction.step (pop_r64 .rdx) state)).rip = 5368713447 := by
      simpa [writeStates] using h2
    unfold writeStates
    rw [show (X86_64Instruction.step (add_r64_imm8 .rdi 1)
      (X86_64Instruction.step (mov_mem8 .rdi .rdx)
        (X86_64Instruction.step (pop_r64 .rdx) state))).rip =
      (X86_64Instruction.step (mov_mem8 .rdi .rdx)
        (X86_64Instruction.step (pop_r64 .rdx) state)).rip + 4 by rfl, h2']
    decide
  have h4 : (writeStates state).2.2.2.rip = 5368713455 := by
    have h3' : (X86_64Instruction.step (add_r64_imm8 .rdi 1)
        (X86_64Instruction.step (mov_mem8 .rdi .rdx)
          (X86_64Instruction.step (pop_r64 .rdx) state))).rip = 5368713451 := by
      simpa [writeStates] using h3
    unfold writeStates
    rw [show (X86_64Instruction.step (sub_r64_imm8 .rcx 1)
      (X86_64Instruction.step (add_r64_imm8 .rdi 1)
        (X86_64Instruction.step (mov_mem8 .rdi .rdx)
          (X86_64Instruction.step (pop_r64 .rdx) state)))).rip =
      (X86_64Instruction.step (add_r64_imm8 .rdi 1)
        (X86_64Instruction.step (mov_mem8 .rdi .rdx)
          (X86_64Instruction.step (pop_r64 .rdx) state))).rip + 4 by rfl, h3']
    decide
  have s1 := spike2_selected_silent_unaligned (writeStates state).1 5368713445 h1
    (by decide) (by decide)
  have s2 := spike2_selected_silent_unaligned (writeStates state).2.1 5368713447 h2
    (by decide) (by decide)
  have s3 := spike2_selected_silent_unaligned (writeStates state).2.2.1 5368713451 h3
    (by decide) (by decide)
  have s4 := spike2_selected_silent_unaligned (writeStates state).2.2.2 5368713455 h4
    (by decide) (by decide)
  have ss1 : selectedNonInputPlatformCall (writeStates state).1.rip (writeStates state).1 = true ∧
      @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _ (writeStates state).1.rip
        (writeStates state).1 = none := by simpa only [h1] using s1
  have ss2 : selectedNonInputPlatformCall (writeStates state).2.1.rip (writeStates state).2.1 = true ∧
      @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _ (writeStates state).2.1.rip
        (writeStates state).2.1 = none := by simpa only [h2] using s2
  have ss3 : selectedNonInputPlatformCall (writeStates state).2.2.1.rip (writeStates state).2.2.1 = true ∧
      @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _ (writeStates state).2.2.1.rip
        (writeStates state).2.2.1 = none := by simpa only [h3] using s3
  have ss4 : selectedNonInputPlatformCall (writeStates state).2.2.2.rip (writeStates state).2.2.2 = true ∧
      @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _ (writeStates state).2.2.2.rip
        (writeStates state).2.2.2 = none := by simpa only [h4] using s4
  refine {
    lookupPop := ?_, lookupStore := ?_, lookupCursor := ?_, lookupCount := ?_, lookupBranch := ?_,
    silentPop := ss1.2, silentStore := ss2.2, silentCursor := ss3.2, silentCount := ss4.2,
    silentBranch := branchSilent, backTarget := ?_, selectedPop := ss1.1, selectedStore := ss2.1,
    selectedCursor := ss3.1, selectedCount := ss4.1, selectedBranch := branchSelected }
  · rw [hrip]; rfl
  · rw [h1]; rfl
  · rw [h2]; rfl
  · rw [h3]; rfl
  · rw [h4]; rfl
  · rw [h4, hrip]
    decide

/-- One exact selected decimal reverse-write pass, including its explicit branch edge. -/
theorem spike2_write_selected_prefix (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (stackUpper outputLimit : UInt64) (hrip : state.rip = 5368713444)
    (pre : WriteSafety stackUpper outputLimit state) (safe : WriteExecutionSafety 243 state)
    (branchSelected : selectedNonInputPlatformCall
      (X86_64Instruction.step (jne_rel8 243) (writeStates state).2.2.2).rip
      (X86_64Instruction.step (jne_rel8 243) (writeStates state).2.2.2) = true)
    (branchSilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (X86_64Instruction.step (jne_rel8 243) (writeStates state).2.2.2).rip
      (X86_64Instruction.step (jne_rel8 243) (writeStates state).2.2.2) = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 5 state eventsRev
      (writeFinal 243 state) eventsRev [] := by
  have placement := spike2_write_selected_placement state hrip safe branchSelected branchSilent
  by_cases taken : X86BranchCondition.notEqual.holds (writeStates state).2.2.2
  · exact writeSelectedPrefixTaken placement pre safe taken
  · exact writeSelectedPrefixFallthrough placement pre safe taken

end Spikes.Spike2Fibonacci.Windows
