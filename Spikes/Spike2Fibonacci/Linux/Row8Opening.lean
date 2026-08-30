import Spikes.Spike2Fibonacci.Linux.Row7BoundaryFacts
import Spikes.Spike2Fibonacci.Linux.Row8BoundaryData

/-!
# Row 8 opening and index-formatting certificates

The predecessor is consumed only through Row 7's typed boundary facts.  The literal Row 8
instructions below are local to this producer and join the existing formatter at its linked
entry point.
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
open Spikes.Spike2Fibonacci.Linux.Row8BoundaryData

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/-- Six literal stores/comparison steps take Row 8's one-digit index path. -/
theorem spike2_row8_index_header_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
      (spike2AfterMainHeader spike2Row7AfterRecurrence) ([] : List AnyEvent)
      spike2Row8AfterIndexHeader [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .movRspByte 0x40 0x46
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
  · exact spike2Row8IndexHeaderLookupF
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .movRspByte 0x41 0x69
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
    · exact spike2Row8IndexHeaderLookupI
    · decide
    · decide
    · rfl
    · refine ProductionPrefix.SelectedPrefix.ordinary ({
        encoding := .movRspByte 0x42 0x62
        safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
      · exact spike2Row8IndexHeaderLookupB
      · decide
      · decide
      · rfl
      · refine ProductionPrefix.SelectedPrefix.ordinary ({
          encoding := .movRspByte 0x43 0x28
          safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
        · exact spike2Row8IndexHeaderLookupOpen
        · decide
        · decide
        · rfl
        · refine ProductionPrefix.SelectedPrefix.ordinary (spike2Row8SequentialCmp .r13 10)
            ?_ ?_ ?_ ?_ ?_
          · exact spike2Row8IndexHeaderLookupCmp
          · decide
          · decide
          · rfl
          · refine ProductionPrefix.SelectedPrefix.conditionalFallthrough (.jge8 41) (by
              simp only [X86BranchCondition.holds]
              decide) ?_ ?_ ?_ ?_ ?_
            · exact spike2Row8IndexHeaderLookupBranch
            · decide
            · decide
            · rfl
            · exact .nil _ _

/-- The one-digit index formatter reaches the actual linked value-format entry. -/
theorem spike2_row8_index_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 10
      spike2Row8AfterIndexHeader ([] : List AnyEvent) spike2Row8AfterIndex [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary (ControlFlowFree.mov .rax .r13).sequential
    ?_ ?_ ?_ ?_ ?_
  · exact spike2Row8IndexLookupMove
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .addImm8 .rax 0x30
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
    · exact spike2Row8IndexLookupAscii
    · decide
    · decide
    · rfl
    · refine ProductionPrefix.SelectedPrefix.ordinary ({
        encoding := .leaRsp .rdi 0x44
        safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
      · exact spike2Row8IndexLookupCursor
      · decide
      · decide
      · rfl
      · refine ProductionPrefix.SelectedPrefix.ordinary ({
          encoding := .movMem8 .rdi .rax
          safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
        · exact spike2Row8IndexLookupStore
        · decide
        · decide
        · rfl
        · refine ProductionPrefix.SelectedPrefix.ordinary ({
            encoding := .movRspByte 0x45 0x29
            safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
          · exact spike2Row8IndexLookupClose
          · decide
          · decide
          · rfl
          · refine ProductionPrefix.SelectedPrefix.ordinary ({
              encoding := .movRspByte 0x46 0x20
              safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
            · exact spike2Row8IndexLookupSpace
            · decide
            · decide
            · rfl
            · refine ProductionPrefix.SelectedPrefix.ordinary ({
                encoding := .movRspByte 0x47 0x3d
                safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
              · exact spike2Row8IndexLookupEquals
              · decide
              · decide
              · rfl
              · refine ProductionPrefix.SelectedPrefix.ordinary ({
                  encoding := .movRspByte 0x48 0x20
                  safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
                · exact spike2Row8IndexLookupValueSpace
                · decide
                · decide
                · rfl
                · refine ProductionPrefix.SelectedPrefix.ordinary ({
                    encoding := .leaRsp .rdi 0x49
                    safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
                  · exact spike2Row8IndexLookupValueCursor
                  · decide
                  · decide
                  · rfl
                  · refine ProductionPrefix.SelectedPrefix.directBranch (Event := AnyEvent)
                      (.rel8 65) ?_ ?_ ?_ ?_ ?_
                    · exact spike2Row8IndexLookupJoin
                    · decide
                    · decide
                    · rfl
                    · exact .nil _ _

/-- The three literal setup instructions seed the production decimal formatter. -/
theorem spike2_row8_value_setup_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 3
      spike2Row8AfterIndex ([] : List AnyEvent) spike2Row8AfterValueSetup [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary (ControlFlowFree.mov .rax .r14).sequential
    ?_ ?_ ?_ ?_ ?_
  · exact spike2Row8ValueSetupLookupMove
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary (ControlFlowFree.loadImm .r10 10).sequential
      ?_ ?_ ?_ ?_ ?_
    · exact spike2Row8ValueSetupLookupBase
    · decide
    · decide
    · rfl
    · refine ProductionPrefix.SelectedPrefix.ordinary ({
        encoding := .xor32 .ecx .ecx
        safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
      · exact spike2Row8ValueSetupLookupCount
      · decide
      · decide
      · rfl
      · exact .nil _ _

/-- Header, one-digit index path, and formatter setup compose through opaque Row 7 facts. -/
theorem spike2_row8_opening_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 18
      spike2Row7AfterRecurrence ([] : List AnyEvent) spike2Row8AfterIndex [] [] := by
  have predecessor := Spikes.Spike2Fibonacci.Linux.Row7BoundaryFacts.spike2Row7HeaderFacts
  have header := spike2_main_header_selected_prefix 7 spike2Row7AfterRecurrence ([] : List AnyEvent)
    (by omega) predecessor.1 predecessor.2.1 predecessor.2.2.2.2.2
  have indexed := ProductionPrefix.SelectedPrefix.append header spike2_row8_index_header_selected_prefix
  simpa using ProductionPrefix.SelectedPrefix.append indexed spike2_row8_index_selected_prefix

end Spikes.Spike2Fibonacci.Linux
