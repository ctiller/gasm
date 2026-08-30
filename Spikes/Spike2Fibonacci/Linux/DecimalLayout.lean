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

import Gasm.Targets.X86_64.DecimalMacroSelectedPrefix
import Spikes.Spike2Fibonacci.Linux.NativeAdapter

/-!
# Linux Spike 2 decimal-loop final-link witness

This is the one program-owned placement boundary for the two decimal loops.  The symbolic
decimal schedule deliberately has no concrete RIPs; this module ties its nominal coordinates to
the exact final `spike2Indexed` stream, including byte slices and the two relative JNE targets.
It proves no arithmetic, memory-safety, selector, or interceptor fact, and so cannot be used to
fabricate a decimal execution prefix without the corresponding runtime evidence.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.CFGLinker
open Gasm.Targets.X86_64.DecimalMacro

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/-- The exact linked text consumed by the Spike 2 native runner.  Its index is definitionally
the production `spike2Indexed`; it is not a duplicate instruction list. -/
def spike2DecimalText : LinkedText where
  base := spike2Executable.load.rip
  instructions := spike2Instructions

@[simp] theorem spike2DecimalText_indexed : spike2DecimalText.indexed = spike2Indexed := rfl

/-- The seven extraction coordinates in the final Linux text.  `exit` is the first pop/write
instruction and is a boundary rather than an extraction instruction. -/
def spike2ExtractionAddress : ExtractionPoint → UInt64
  | .clearHigh => 4198594
  | .divide => 4198596
  | .ascii => 4198599
  | .push => 4198603
  | .increment => 4198604
  | .compare => 4198608
  | .branch => 4198612
  | .exit => 4198614

/-- The five reverse-write coordinates in the final Linux text.  `exit` is the first CR store
setup instruction and is a boundary rather than a write instruction. -/
def spike2WriteAddress : WritePoint → UInt64
  | .pop => 4198614
  | .store => 4198615
  | .advance => 4198617
  | .decrement => 4198621
  | .branch => 4198625
  | .exit => 4198627

/-- Exact final-link realization of the decimal extraction loop in `spike2Indexed`. -/
def spike2ExtractionLinkedLayout :
    ExtractionLinkedLayout spike2DecimalText spike2Indexed 236 where
  address := spike2ExtractionAddress
  addressInjective := by
    intro left right equal
    cases left <;> cases right <;> simp [spike2ExtractionAddress] at equal ⊢
  index_eq := rfl
  textNoWrap := by decide
  lookup := by
    intro point selected atPoint
    cases point <;> simp [extractionInstruction] at atPoint
    all_goals subst selected <;> rfl
  bytes := by
    intro point selected atPoint
    cases point <;> simp [extractionInstruction] at atPoint
    all_goals subst selected <;> decide
  noWrap := by
    intro point selected atPoint
    cases point <;> simp [extractionInstruction] at atPoint
    all_goals subst selected <;> decide
  covered := by
    intro point selected atPoint
    cases point <;> simp [extractionInstruction] at atPoint
    all_goals subst selected <;> decide
  clearHighNext := by decide
  divideNext := by decide
  asciiNext := by decide
  pushNext := by decide
  incrementNext := by decide
  compareNext := by decide
  takenTarget := by decide
  falseFallthrough := by decide

/-- Exact final-link realization of the decimal reverse-write loop in `spike2Indexed`. -/
def spike2WriteLinkedLayout :
    WriteLinkedLayout spike2DecimalText spike2Indexed 243 where
  address := spike2WriteAddress
  addressInjective := by
    intro left right equal
    cases left <;> cases right <;> simp [spike2WriteAddress] at equal ⊢
  index_eq := rfl
  textNoWrap := by decide
  lookup := by
    intro point selected atPoint
    cases point <;> simp [writeInstruction] at atPoint
    all_goals subst selected <;> rfl
  bytes := by
    intro point selected atPoint
    cases point <;> simp [writeInstruction] at atPoint
    all_goals subst selected <;> decide
  noWrap := by
    intro point selected atPoint
    cases point <;> simp [writeInstruction] at atPoint
    all_goals subst selected <;> decide
  covered := by
    intro point selected atPoint
    cases point <;> simp [writeInstruction] at atPoint
    all_goals subst selected <;> decide
  popNext := by decide
  storeNext := by decide
  advanceNext := by decide
  decrementNext := by decide
  takenTarget := by decide
  falseFallthrough := by decide

end Spikes.Spike2Fibonacci.Linux
