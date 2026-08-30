import Spikes.Spike2Fibonacci.Linux.Row8Opening
import Spikes.Spike2Fibonacci.Linux.Row8Formatting
import Spikes.Spike2Fibonacci.Linux.Row8Tail
import Spikes.Spike2Fibonacci.Linux.Row8BoundaryFacts

/-!
# Complete Row 8 certificate

The composition joins independently checked Row 8 slices.  It never unfolds a predecessor
certificate or identifies full machine states definitionally across a row boundary.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Spikes.Spike2Fibonacci
open Spikes.Spike2Fibonacci.Linux.Row8BoundaryData

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Row 8's exact 64-transition production certificate joins the main header, one-digit index,
two-digit decimal formatter, CR/LF suffix, selected `SYS_write`, and recurrence/back edge. -/
theorem spike2_row8_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 64
      spike2Row7AfterRecurrence ([] : List AnyEvent) spike2Row8AfterRecurrence
      spike2Row8WriteEventsRev
      (emittedBy (sysWriteHook (Event := AnyEvent)
        (X86_64Instruction.step syscall_op spike2Row8BeforeWriteSyscall)).2) := by
  have opening := spike2_row8_opening_selected_prefix
  have valueSetup := ProductionPrefix.SelectedPrefix.append opening
    spike2_row8_value_setup_selected_prefix
  have formatter := ProductionPrefix.SelectedPrefix.append valueSetup
    spike2_row8_decimal_formatter_selected_prefix
  have terminator := ProductionPrefix.SelectedPrefix.append formatter
    spike2_row8_line_terminator_selected_prefix
  have writeSetup := ProductionPrefix.SelectedPrefix.append terminator
    spike2_row8_write_setup_selected_prefix
  have writeSyscall := ProductionPrefix.SelectedPrefix.append writeSetup
    spike2_row8_write_syscall_selected_prefix
  have recurrence := ProductionPrefix.SelectedPrefix.append writeSyscall
    spike2_row8_recurrence_selected_prefix
  simpa [spike2Row8WriteEventsRev] using recurrence

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The data-only Row 8 boundary is re-exported as the narrow connector for subsequent rows and
termination: RIP, live Fibonacci registers, RSP, and fault status only. -/
theorem spike2_row8_after_recurrence_boundary :
    spike2Row8AfterRecurrence.rip = spike2MainLoopRip ∧
    spike2Row8AfterRecurrence.gprs .r13 = 9 ∧
    spike2Row8AfterRecurrence.gprs .r14 = 34 ∧
    spike2Row8AfterRecurrence.gprs .r15 = 55 ∧
    spike2Row8AfterRecurrence.rsp = spike2Row7AfterRecurrence.rsp ∧
    spike2Row8AfterRecurrence.fault = none :=
  Spikes.Spike2Fibonacci.Linux.Row8BoundaryFacts.spike2Row8HeaderFacts

end Spikes.Spike2Fibonacci.Linux
