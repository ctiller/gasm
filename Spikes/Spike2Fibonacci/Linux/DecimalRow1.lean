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

import Spikes.Spike2Fibonacci.Linux.DecimalRuntime
import Spikes.Spike2Fibonacci.Linux.Row1

/-!
# Row-one validation of the linked decimal bridge

This is deliberately an anchor, not an alternate formatter proof: it instantiates the new
actual-index layout/runtime bridge at the existing first reachable decimal entry.  It confirms
the bridge's stateful ordinary-code condition against real Linux text memory.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.DecimalSegments

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

private theorem spike2_row1_extraction_ordinary :
    Spike2ExtractionOrdinary 236 spike2Row1AfterValueSetup := by
  constructor <;> constructor <;> decide

private theorem spike2_row1_write_ordinary :
    Spike2WriteOrdinary 243 spike2Row1AfterExtraction := by
  constructor <;> constructor <;> decide

/-- The existing row-one extraction state satisfies the generic final-link bridge. -/
theorem spike2_row1_extraction_selected_prefix_via_layout :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 7
      spike2Row1AfterValueSetup ([] : List AnyEvent) spike2Row1AfterExtraction [] [] := by
  have pass := spike2ExtractionLinkedLayout_selectedPass (stackLower := 0)
    spike2Row1AfterValueSetup rfl
    (by
      refine ⟨rfl, ?_, by decide, rfl⟩
      change 8 ≤ 140737488289656
      omega) (by constructor <;> decide)
    spike2_row1_extraction_ordinary (Or.inr (by
      simp only [X86BranchCondition.holds]
      decide))
  exact pass.selectedPrefix

/-- The existing row-one reverse write state satisfies the generic final-link bridge. -/
theorem spike2_row1_write_selected_prefix_via_layout :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 5
      spike2Row1AfterExtraction ([] : List AnyEvent) spike2Row1AfterWrite [] [] := by
  have pass := spike2WriteLinkedLayout_selectedPass
    (stackUpper := 18446744073709551615) (outputLimit := 18446744073709551615)
    spike2Row1AfterExtraction rfl
    (by
      refine ⟨?_, ?_, by decide, rfl⟩
      · change 140737488289648 + 8 ≤ 18446744073709551615
        omega
      · change 140737488289729 < 18446744073709551615
        omega) (by constructor <;> decide)
    spike2_row1_write_ordinary (Or.inr (by
      simp only [X86BranchCondition.holds]
      decide))
  exact pass.selectedPrefix

end Spikes.Spike2Fibonacci.Linux
