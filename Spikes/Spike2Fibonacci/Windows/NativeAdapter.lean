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
import Gasm.Targets.X86_64.MacroAssembler.PlatformBridge
import Gasm.Targets.Dispatcher
import Spikes.Spike2Fibonacci.Windows.Program

/-!
# Eventful production adapter for Windows Spike 2

This is the Windows sibling of the Linux production adapter.  In particular, the import call is
not modelled as a silent local instruction: the certificate fetches the concrete linked `CALL`,
then takes the production Win32 interceptor transition which supplies the standard-output handle.
The remaining setup instructions are exact fetch/step facts from the linked image.
-/

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Windows
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Spikes.Spike2Fibonacci

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

/-- The exact indexed lowering consumed by the Windows production outcome runner. -/
def spike2Indexed : List (UInt64 × X86_64Instr) :=
  indexInstructions spike2Executable.load.rip spike2Instructions

private theorem sequentialSubRsp (imm : UInt32) : SequentialInstruction (sub_rsp32 imm) where
  encoding := .subRsp32 imm
  safeFallthrough := by intro state _; rfl

private theorem sequentialMovImm (dst : Reg64) (imm : UInt64) :
    SequentialInstruction (mov_r64_imm64 dst imm) where
  encoding := .loadImm dst imm
  safeFallthrough := by intro state _; rfl

private theorem sequentialMov (dst src : Reg64) : SequentialInstruction (mov_r64 dst src) where
  encoding := .mov dst src
  safeFallthrough := by intro state _; rfl

/-- State after the linked `GetStdHandle` call has been processed by the real Win32 hook. -/
def spike2AfterGetStdHandle : X86_64MachineState :=
  (getStdHandleHook (Event := AnyEvent) (X86_64Instruction.step (call_rip 0x1fee)
    (X86_64Instruction.step (mov_r32 .ecx 0xFFFFFFF5)
      (X86_64Instruction.step (sub_rsp32 136) spike2Executable.load)))).1

/-- The Windows driver's first loop header state, including the concrete imported-call transition. -/
def spike2AfterPrologue : X86_64MachineState :=
  X86_64Instruction.step (mov_r64_imm64 .r15 1)
    (X86_64Instruction.step (mov_r64_imm64 .r14 1)
      (X86_64Instruction.step (mov_r64_imm64 .r13 1)
        (X86_64Instruction.step (mov_r64 .r12 .rax) spike2AfterGetStdHandle)))

/-- Concrete linked address of the first `cmp r13, 91` driver-header instruction.  This is
exported as a scalar boundary fact so consumers do not unfold the prologue state. -/
def spike2WindowsMainLoopRip : UInt64 := spike2AfterPrologue.rip

theorem spike2WindowsMainLoopRip_eq : spike2WindowsMainLoopRip = 5368713267 := by rfl

/-- Exact fetch at the opaque driver-header boundary. -/
theorem spike2MainLoop_fetch :
    instructionAtRipIndexed spike2Indexed spike2WindowsMainLoopRip = some (cmp_r64_imm8 .r13 91) := by
  rfl

/-- Opaque fetch facts for the fixed WriteFile/recurrence tail.  Keeping these in the local
linked-image producer prevents row consumers from reducing the full instruction index. -/
theorem spike2WriteFile_fetch :
    instructionAtRipIndexed spike2Indexed 5368713517 = some (call_rip 0x1edd) := by rfl

theorem spike2Recurrence_mov_fetch :
    instructionAtRipIndexed spike2Indexed 5368713523 = some (mov_r64 .r8 .r14) := by rfl

theorem spike2Recurrence_add_fetch :
    instructionAtRipIndexed spike2Indexed 5368713526 = some (add_r64 .r8 .r15) := by rfl

theorem spike2Recurrence_mov14_fetch :
    instructionAtRipIndexed spike2Indexed 5368713529 = some (mov_r64 .r14 .r15) := by rfl

theorem spike2Recurrence_mov15_fetch :
    instructionAtRipIndexed spike2Indexed 5368713532 = some (mov_r64 .r15 .r8) := by rfl

theorem spike2Recurrence_inc_fetch :
    instructionAtRipIndexed spike2Indexed 5368713535 = some (add_r64_imm8 .r13 1) := by rfl

theorem spike2Recurrence_backedge_fetch :
    instructionAtRipIndexed spike2Indexed 5368713539 = some (jmp_rel32 4294967019) := by rfl

/-- The seven linked setup transitions form a selected production prefix.  The third transition
is the actual IAT `GetStdHandle` call, so it cannot be replaced by a trace-only account of the
driver's initial register state. -/
theorem spike2_prologue_selected_prefix :
    ProductionPrefix.SelectedPrefix (Event := AnyEvent) selectedNonInputPlatformCall spike2Indexed 7 spike2Executable.load
      ([] : List AnyEvent) spike2AfterPrologue [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary (sequentialSubRsp 136) ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary (mov_r32_sequential .ecx 0xFFFFFFF5) ?_ ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · rfl
    · refine ProductionPrefix.SelectedPrefix.hostIntercept
        (Event := AnyEvent) (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed)
        (fuel := 4) (state := _) (hooked := spike2AfterGetStdHandle)
        (final := spike2AfterPrologue) (eventsRev := []) (finalEventsRev := []) (emitted := [])
        (instruction := call_rip 0x1fee) (event := none) (.callRip 0x1fee) ?_ ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · rfl
      · refine ProductionPrefix.SelectedPrefix.ordinary (sequentialMov .r12 .rax) ?_ ?_ ?_ ?_ ?_
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

/-- The selected setup certificate rewrites the unmodified production outcome runner, not a
trace surrogate.  This is the entry point used by the driver proof: every continuation sees the
same state that the real linked `CALL`/IAT transition produced. -/
theorem spike2_prologue_runs (continuationFuel : Nat) :
    runProgramOutcomeLoop spike2Indexed (7 + continuationFuel) spike2Executable.load
      ([] : List AnyEvent) =
      runProgramOutcomeLoop spike2Indexed continuationFuel spike2AfterPrologue [] := by
  exact spike2_prologue_selected_prefix.toProductionPrefix.run continuationFuel

end Spikes.Spike2Fibonacci.Windows
