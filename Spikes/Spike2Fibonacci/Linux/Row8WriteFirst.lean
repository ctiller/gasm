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
import Spikes.Spike2Fibonacci.Linux.Row8BoundaryData

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Spikes.Spike2Fibonacci
open Spikes.Spike2Fibonacci.Linux.Row8BoundaryData

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

theorem spike2_row8_write_first_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 5
      spike2Row8AfterExtraction ([] : List AnyEvent) spike2Row8AfterWriteFirst [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .pop .rdx
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
  · exact spike2Row8WriteFirstLookupPop
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .movMem8 .rdi .rdx
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
    · exact spike2Row8WriteFirstLookupStore
    · decide
    · decide
    · rfl
    · refine ProductionPrefix.SelectedPrefix.ordinary ({
        encoding := .addImm8 .rdi 1
        safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
      · exact spike2Row8WriteFirstLookupCursor
      · decide
      · decide
      · rfl
      · refine ProductionPrefix.SelectedPrefix.ordinary ({
          encoding := .subImm8 .rcx 1
          safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
        · exact spike2Row8WriteFirstLookupDecrement
        · decide
        · decide
        · rfl
        · refine ProductionPrefix.SelectedPrefix.conditionalTaken (.jne8 243)
            (by
              simp only [X86BranchCondition.holds]
              decide)
            ?_ ?_ ?_ ?_ ?_
          · exact spike2Row8WriteFirstLookupBranch
          · decide
          · decide
          · rfl
          · exact .nil _ _

end Spikes.Spike2Fibonacci.Linux
