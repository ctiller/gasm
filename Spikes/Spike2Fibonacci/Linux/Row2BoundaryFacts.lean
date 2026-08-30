import Spikes.Spike2Fibonacci.Linux.Row2BoundaryData

/-!
# Row 2 data-only header boundary

This module imports checkpoint data only, never a `SelectedPrefix` certificate.  Its exact
physical header fields are the complete predecessor interface consumed by a later row stage.
-/

namespace Spikes.Spike2Fibonacci.Linux.Row2BoundaryFacts

open Gasm.Targets.X86_64
open Spikes.Spike2Fibonacci.Linux.Row2BoundaryData

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Exact post-recurrence facts for closed Row 2. -/
theorem spike2Row2HeaderFacts :
    spike2Row2AfterRecurrence.rip = spike2MainLoopRip ∧
    spike2Row2AfterRecurrence.gprs .r13 = 3 ∧
    spike2Row2AfterRecurrence.gprs .r14 = 2 ∧
    spike2Row2AfterRecurrence.gprs .r15 = 3 ∧
    spike2Row2AfterRecurrence.rsp = Spikes.Spike2Fibonacci.Linux.Row1BoundaryData.spike2Row1AfterRecurrence.rsp ∧
    spike2Row2AfterRecurrence.fault = none := by
  decide

end Spikes.Spike2Fibonacci.Linux.Row2BoundaryFacts
