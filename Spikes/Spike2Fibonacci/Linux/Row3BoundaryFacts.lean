import Spikes.Spike2Fibonacci.Linux.Row3BoundaryData

/-!
# Row 3 data-only header boundary

This module imports checkpoint data only, never a `SelectedPrefix` certificate.  Its exact
physical header fields are the complete predecessor interface consumed by a later row stage.
-/

namespace Spikes.Spike2Fibonacci.Linux.Row3BoundaryFacts

open Gasm.Targets.X86_64
open Spikes.Spike2Fibonacci.Linux.Row3BoundaryData

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Exact post-recurrence facts for closed Row 3. -/
theorem spike2Row3HeaderFacts :
    spike2Row3AfterRecurrence.rip = spike2MainLoopRip ∧
    spike2Row3AfterRecurrence.gprs .r13 = 4 ∧
    spike2Row3AfterRecurrence.gprs .r14 = 3 ∧
    spike2Row3AfterRecurrence.gprs .r15 = 5 ∧
    spike2Row3AfterRecurrence.rsp = Spikes.Spike2Fibonacci.Linux.Row2BoundaryData.spike2Row2AfterRecurrence.rsp ∧
    spike2Row3AfterRecurrence.fault = none := by
  decide

end Spikes.Spike2Fibonacci.Linux.Row3BoundaryFacts
