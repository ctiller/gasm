import Spikes.Spike2Fibonacci.Linux.Row8ExtractionFirst
import Spikes.Spike2Fibonacci.Linux.Row8ExtractionSecond
import Spikes.Spike2Fibonacci.Linux.Row8WriteFirst
import Spikes.Spike2Fibonacci.Linux.Row8WriteSecond

/-!
# Row 8 decimal formatter composition

The four instruction certificates remain separate cache boundaries.  This module composes only
their typed endpoints; it never unfolds either a predecessor row certificate or a concrete state.
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
/-- The actual two-digit extraction and write loops for Row 8 compose without reducing the
closed physical boundary through an earlier row certificate. -/
theorem spike2_row8_decimal_formatter_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 24
      spike2Row8AfterValueSetup ([] : List AnyEvent) spike2Row8AfterWrite [] [] := by
  have extractionFirst := spike2_row8_extraction_first_selected_prefix
  have extractionSecond := spike2_row8_extraction_second_selected_prefix
  have writeFirst := spike2_row8_write_first_selected_prefix
  have writeSecond := spike2_row8_write_second_selected_prefix
  have extraction := ProductionPrefix.SelectedPrefix.append extractionFirst extractionSecond
  have write := ProductionPrefix.SelectedPrefix.append writeFirst writeSecond
  simpa using ProductionPrefix.SelectedPrefix.append extraction write

end Spikes.Spike2Fibonacci.Linux
