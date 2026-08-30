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
import Gasm.Targets.Linux.OutcomeBridge
import Spikes.Spike2Fibonacci.NativeLoop
import Spikes.Spike2Fibonacci.Linux.Program

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

private theorem sequentialSubRsp (imm : UInt32) : SequentialInstruction (sub_rsp32 imm) where
  encoding := .subRsp32 imm
  safeFallthrough := by intro state _; rfl

private theorem sequentialMovImm (dst : Reg64) (imm : UInt64) :
    SequentialInstruction (mov_r64_imm64 dst imm) where
  encoding := .loadImm dst imm
  safeFallthrough := by intro state _; rfl

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
    ProductionPrefix.SelectedPrefix selectedNonInputLinuxCall spike2Indexed 4 spike2Executable.load
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
