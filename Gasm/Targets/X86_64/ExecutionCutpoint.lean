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

import Gasm.Targets.X86_64.EventfulSegment

namespace Gasm.Targets.X86_64.ProductionPrefix.SelectedPrefix

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- A proof-backed semantic cache boundary.  Program adapters may define an opaque value of
this type so downstream proofs can consume an exact production prefix without unfolding the
concrete machine-state or event expressions used to construct it. -/
structure Cutpoint {Event : Type} [ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr)) (fuel : Nat)
    (initial : X86_64MachineState) (initialEventsRev : List Event) where
  final : X86_64MachineState
  finalEventsRev : List Event
  emitted : List Event
  certificate : SelectedPrefix selected indexed fuel initial initialEventsRev
    final finalEventsRev emitted

end Gasm.Targets.X86_64.ProductionPrefix.SelectedPrefix
