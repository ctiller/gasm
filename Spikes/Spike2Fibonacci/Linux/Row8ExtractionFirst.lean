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

private theorem spike2Row8SequentialCmp (dst : Reg64) (value : UInt8) :
    SequentialInstruction (cmp_r64_imm8 dst value) where
  encoding := .compareImm8 dst value
  safeFallthrough := by intro _ _; rfl

private def spike2Row8ExtractionFirstMid : X86_64MachineState :=
  X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
    (X86_64Instruction.step (div_r64 .r10)
      (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row8AfterValueSetup))

private theorem spike2Row8ExtractionFirstHead :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 3
      spike2Row8AfterValueSetup ([] : List AnyEvent) spike2Row8ExtractionFirstMid [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .xor32 .edx .edx
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
  · exact spike2Row8ExtractionFirstLookupXor
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary spike2Row8SequentialDivR10 ?_ ?_ ?_ ?_ ?_
    · exact spike2Row8ExtractionFirstLookupDiv
    · decide
    · decide
    · decide
    · refine ProductionPrefix.SelectedPrefix.ordinary ({
        encoding := .addImm8 .rdx 0x30
        safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
      · exact spike2Row8ExtractionFirstLookupAscii
      · decide
      · decide
      · rfl
      · exact .nil _ _

private theorem spike2Row8ExtractionFirstTail :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 4
      spike2Row8ExtractionFirstMid ([] : List AnyEvent) spike2Row8AfterExtractionFirst [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .push .rdx
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
  · exact spike2Row8ExtractionFirstLookupPush
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .addImm8 .rcx 1
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
    · exact spike2Row8ExtractionFirstLookupCount
    · decide
    · decide
    · rfl
    · refine ProductionPrefix.SelectedPrefix.ordinary (spike2Row8SequentialCmp .rax 0)
        ?_ ?_ ?_ ?_ ?_
      · exact spike2Row8ExtractionFirstLookupCmp
      · decide
      · decide
      · rfl
      · refine ProductionPrefix.SelectedPrefix.conditionalTaken (.jne8 236)
          (by
            simp only [X86BranchCondition.holds]
            decide)
          ?_ ?_ ?_ ?_ ?_
        · exact spike2Row8ExtractionFirstLookupBranch
        · decide
        · decide
        · rfl
        · exact .nil _ _

theorem spike2_row8_extraction_first_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 7
      spike2Row8AfterValueSetup ([] : List AnyEvent) spike2Row8AfterExtractionFirst [] [] := by
  simpa using ProductionPrefix.SelectedPrefix.append
    spike2Row8ExtractionFirstHead spike2Row8ExtractionFirstTail

end Spikes.Spike2Fibonacci.Linux
