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

import Spikes.Spike2Fibonacci.Linux.Rows1To4
import Spikes.Spike2Fibonacci.Linux.Rows5To6

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/-- The production prologue and first six rows, joined only through their exact Row 4 boundary.
The right-hand cached producer is rebased beneath the left producer's already-established event
accumulator before `SelectedPrefix.append` consumes the shared machine boundary. -/
theorem spike2_prologue_to_row6_selected_prefix :
    ∃ eventsRev emitted,
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 316
        spike2Executable.load ([] : List AnyEvent) spike2Row6AfterRecurrence eventsRev emitted := by
  rcases spike2_prologue_to_row4_selected_prefix with ⟨events4, emitted4, rows14⟩
  rcases spike2_rows5_to6_selected_prefix with ⟨events6, emitted6, rows56⟩
  have rows56' := rows56.rebaseEvents events4
  have rows16 := ProductionPrefix.SelectedPrefix.append rows14 rows56'
  exact ⟨_, _, by simpa using rows16⟩

end Spikes.Spike2Fibonacci.Linux
