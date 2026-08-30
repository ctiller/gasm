import Spikes.Spike2Fibonacci.Linux.Row1BoundaryData

/-!
# Row 1 data-only header boundary

This module imports checkpoint data only, never a `SelectedPrefix` certificate.  Its exact
physical header fields are the complete predecessor interface consumed by a later row stage.
-/

namespace Spikes.Spike2Fibonacci.Linux.Row1BoundaryFacts

open Gasm.Targets.X86_64
open Spikes.Spike2Fibonacci.Linux.Row1BoundaryData

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Exact post-recurrence facts for closed Row 1. -/
theorem spike2Row1HeaderFacts :
    spike2Row1AfterRecurrence.rip = spike2MainLoopRip ∧
    spike2Row1AfterRecurrence.gprs .r13 = 2 ∧
    spike2Row1AfterRecurrence.gprs .r14 = 1 ∧
    spike2Row1AfterRecurrence.gprs .r15 = 2 ∧
    spike2Row1AfterRecurrence.rsp = spike2AfterPrologue.rsp ∧
    spike2Row1AfterRecurrence.fault = none := by
  decide

end Spikes.Spike2Fibonacci.Linux.Row1BoundaryFacts
