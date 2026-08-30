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
import Spikes.Spike2Fibonacci.Linux.Row7BoundaryData

/-!
# Row 7 data-only header boundary

This module imports checkpoint data only, never a `SelectedPrefix` certificate.  Its exact
physical header fields are the complete predecessor interface consumed by a later row stage.
-/

namespace Spikes.Spike2Fibonacci.Linux.Row7BoundaryFacts

open Gasm.Targets.X86_64
open Spikes.Spike2Fibonacci.Linux.Row7BoundaryData

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Exact post-recurrence facts for closed Row 7. -/
theorem spike2Row7HeaderFacts :
    spike2Row7AfterRecurrence.rip = spike2MainLoopRip ∧
    spike2Row7AfterRecurrence.gprs .r13 = 8 ∧
    spike2Row7AfterRecurrence.gprs .r14 = 21 ∧
    spike2Row7AfterRecurrence.gprs .r15 = 34 ∧
    spike2Row7AfterRecurrence.rsp = Spikes.Spike2Fibonacci.Linux.Row6BoundaryData.spike2Row6AfterRecurrence.rsp ∧
    spike2Row7AfterRecurrence.fault = none := by
  decide

end Spikes.Spike2Fibonacci.Linux.Row7BoundaryFacts
