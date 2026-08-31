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
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.Linux.Syscall
import Gasm.Targets.Linux.Linker
import Spikes.Spike3SortLines.Spec
import Spikes.Spike3SortLines.Linux.LinkCertificate
import Spikes.Spike3SortLines.Linux.Program

namespace Spikes.Spike3SortLines.Linux

open Gasm.Core
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.Linux
open Spikes.Spike3SortLines

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Observable assembly trace on empty stdin for Linux. -/
def asmTraceEmpty : List AnyEvent :=
  runAsmTrace (Event := AnyEvent) spike3Instructions spike3Executable.load

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Observable monadic model trace on empty stdin. -/
def modelTraceEmpty : List AnyEvent :=
  runModelTrace (sortLinesSpec : TraceM AnyEvent Unit) []

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Observable assembly trace on canonical 3-line input for Linux. -/
def asmTraceCanonical : List AnyEvent :=
  runAsmTrace (Event := AnyEvent) spike3Instructions (spike3Executable.loadWithStdin defaultSampleInput)

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Observable monadic model trace on canonical 3-line input. -/
def modelTraceCanonical : List AnyEvent :=
  runModelTrace (sortLinesSpec : TraceM AnyEvent Unit) defaultInputLines

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof of semantic trace equivalence between high-level sorting spec and lowered machine execution on canonical input. -/
theorem spike3_canonical_effect_trace_equivalence_inst :
    (asmTraceCanonical == modelTraceCanonical) = true := by
  native_decide

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof of semantic trace equivalence on empty input. -/
theorem spike3_empty_effect_trace_equivalence_inst :
    (runAsmTrace (Event := AnyEvent) spike3Instructions spike3Executable.load == modelTraceEmpty) = true := by
  decide +kernel

/- The two theorems above are closed regression vectors only. This module deliberately does not
   claim a universal `VerifiedProgram`: arbitrary finite stdin remains Spike 3 proof debt. -/

end Spikes.Spike3SortLines.Linux
