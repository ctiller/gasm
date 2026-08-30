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

/-!
# Row 8 data-only header boundary

This module imports checkpoint data only, never a `SelectedPrefix` certificate.  Its exact
physical header fields are the complete predecessor interface consumed by a later row stage.
-/

namespace Spikes.Spike2Fibonacci.Linux.Row8BoundaryFacts

open Gasm.Targets.X86_64
open Spikes.Spike2Fibonacci.Linux.Row8BoundaryData

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Exact post-recurrence facts for closed Row 8. -/
theorem spike2Row8HeaderFacts :
    spike2Row8AfterRecurrence.rip = spike2MainLoopRip ∧
    spike2Row8AfterRecurrence.gprs .r13 = 9 ∧
    spike2Row8AfterRecurrence.gprs .r14 = 34 ∧
    spike2Row8AfterRecurrence.gprs .r15 = 55 ∧
    spike2Row8AfterRecurrence.rsp = Spikes.Spike2Fibonacci.Linux.Row7BoundaryData.spike2Row7AfterRecurrence.rsp ∧
    spike2Row8AfterRecurrence.fault = none := by
  decide

end Spikes.Spike2Fibonacci.Linux.Row8BoundaryFacts
