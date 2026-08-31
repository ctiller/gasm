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

import Lean
import Gasm.Core.Types
import Gasm.Core.Verification
import Gasm.Effects.Inject
import Gasm.Effects.Trace
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.Windows.Win32API
import Spikes.Spike2Fibonacci.Spec
import Spikes.Spike2Fibonacci.Windows.Program
import Spikes.Spike2Fibonacci.Windows.RowTermination

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForCanonicalTrace :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.Windows

set_option maxRecDepth 10000 in
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Whole-program canonical effect trace equivalence for Spike 2.

    The native side is obtained from the compositional prefix/loop/exit proof; only the small pure
    reference trace reduces here.  No whole-machine evaluator is replayed by the kernel. -/
theorem spike2_canonical_effect_trace_equivalence :
    (runAsmTrace (Event := AnyEvent) spike2Instructions spike2Executable.load ==
     runModelTrace (fibonacciSpec : TraceM AnyEvent Unit)) = true := by
  apply beq_iff_eq.mpr
  rcases spike2_selected_outcome_constructive with ⟨final, outcome⟩
  have outcomeEvents := congrArg NativeRunOutcome.events outcome
  have projection := runProgramOutcomeLoop_events (Event := AnyEvent) spike2Indexed 50000
    spike2Executable.load ([] : List AnyEvent)
  have emptyPrefix :
      ([] : List AnyEvent).reverse ++
          runProgramTraceLoop spike2Indexed 50000 spike2Executable.load =
        runProgramTraceLoop spike2Indexed 50000 spike2Executable.load := by
    rfl
  have projectionClean := projection.trans emptyPrefix
  have terminatedEvents :
      (NativeRunOutcome.terminated (.processExit 0) final
        ((spike2ExpectedEventsRev 90).reverse ++
          [Inject.inject (ProcessEvent.exit 0)])).events =
        (spike2ExpectedEventsRev 90).reverse ++
          [Inject.inject (ProcessEvent.exit 0)] := by
    rfl
  have outcomeClean := outcomeEvents.trans terminatedEvents
  have nativeTrace :
      runAsmTrace (Event := AnyEvent) spike2Instructions spike2Executable.load =
        (spike2ExpectedEventsRev 90).reverse ++
          [Inject.inject (ProcessEvent.exit 0)] := by
    calc
      runAsmTrace (Event := AnyEvent) spike2Instructions spike2Executable.load =
          runProgramTraceLoop spike2Indexed 50000 spike2Executable.load := rfl
      _ = _ := projectionClean.symm.trans outcomeClean
  rw [nativeTrace, runModelTrace_fibonacciSpec,
    spike2ExpectedEventsRev_eq_reverse]
  simp

end Spikes.Spike2Fibonacci.Windows
