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

import Gasm.Targets.X86_64.ExecutionCutpoint

/-!
Proof-producing local-block contracts over exact selected production prefixes.  This module does
not select contracts, infer block identity, construct artifact placement, prove termination, or
create CFG/artifact/export/`VerifiedProgram` authority.  It packages evidence already checked by
`ProductionPrefix.SelectedPrefix` so generated and handwritten bodies can discharge the same local
hole and can be composed without replaying the production runner.
-/

namespace Gasm.Targets.X86_64

open Gasm.Targets.X86_64.ProductionPrefix

/- REF: docs/MACRO_ASSEMBLER.md#proof-directed-local-blocks -/
/-- Explicit bidirectional contract for one local block.  `entry` is the meet of the caller's
    forward-available fact and backward-required precondition.  `Result` and the ghost transition
    are caller-logical phase classifications only; actual production outcomes remain in the
    selected runner semantics and require separate terminal evidence when claimed. -/
structure LocalBlockContract (Event Ghost Result : Type) where
  entry : X86_64MachineState → List Event → Ghost → Prop
  exit : X86_64MachineState → List Event → Ghost →
    X86_64MachineState → List Event → Ghost → List Event → Result → Prop

/- REF: docs/MACRO_ASSEMBLER.md#proof-directed-local-blocks -/
/-- One concrete proof-backed local run.  `selected` and `indexed` are exact type indices, so a
    replacement under a different selected artifact instruction index must construct new evidence.
    Symbolic body identity and placement remain separate CFG/linker concerns. -/
structure LocalBlockRun {Event Ghost Result : Type}
    [ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr))
    (contract : LocalBlockContract Event Ghost Result)
    (fuel : Nat) (initial : X86_64MachineState) (initialEventsRev : List Event)
    (initialGhost : Ghost) : Type where
  cutpoint : SelectedPrefix.Cutpoint selected indexed fuel initial initialEventsRev
  finalGhost : Ghost
  result : Result
  entry : contract.entry initial initialEventsRev initialGhost
  exit : contract.exit initial initialEventsRev initialGhost
    cutpoint.final cutpoint.finalEventsRev finalGhost cutpoint.emitted result

namespace LocalBlockRun

variable {Event Ghost Result : Type} [ExternalCallInterceptor X86_64 Event]
  {selected : Gasm.Core.Address → X86_64MachineState → Bool}
  {indexed : List (UInt64 × X86_64Instr)}
  {contract : LocalBlockContract Event Ghost Result}
  {fuel : Nat} {initial : X86_64MachineState} {initialEventsRev : List Event}
  {initialGhost : Ghost}

def final (run : LocalBlockRun selected indexed contract fuel initial initialEventsRev initialGhost) :
    X86_64MachineState := run.cutpoint.final

def finalEventsRev
    (run : LocalBlockRun selected indexed contract fuel initial initialEventsRev initialGhost) :
    List Event := run.cutpoint.finalEventsRev

def emitted
    (run : LocalBlockRun selected indexed contract fuel initial initialEventsRev initialGhost) :
    List Event := run.cutpoint.emitted

theorem certificate
    (run : LocalBlockRun selected indexed contract fuel initial initialEventsRev initialGhost) :
    SelectedPrefix selected indexed fuel initial initialEventsRev
      run.final run.finalEventsRev run.emitted := run.cutpoint.certificate

/- REF: docs/MACRO_ASSEMBLER.md#proof-directed-local-blocks -/
/-- A local run rewrites the real production runner to the unchanged caller continuation.  It does
    not claim that the continuation terminates or succeeds. -/
theorem run_continuation {Event Ghost Result : Type}
    [ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)}
    {contract : LocalBlockContract Event Ghost Result}
    {fuel : Nat} {initial : X86_64MachineState} {initialEventsRev : List Event}
    {initialGhost : Ghost}
    (run : LocalBlockRun selected indexed contract fuel initial initialEventsRev initialGhost)
    (continuationFuel : Nat) :
    runProgramOutcomeLoop indexed (fuel + continuationFuel) initial initialEventsRev =
      runProgramOutcomeLoop indexed continuationFuel run.final run.finalEventsRev := by
  exact run.certificate.toProductionPrefix.run continuationFuel

/- REF: docs/MACRO_ASSEMBLER.md#proof-directed-local-blocks -/
/-- Exact event history law inherited from the selected production prefix. -/
theorem events_reverse_append {Event Ghost Result : Type}
    [ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)}
    {contract : LocalBlockContract Event Ghost Result}
    {fuel : Nat} {initial : X86_64MachineState} {initialEventsRev : List Event}
    {initialGhost : Ghost}
    (run : LocalBlockRun selected indexed contract fuel initial initialEventsRev initialGhost) :
    run.finalEventsRev.reverse = initialEventsRev.reverse ++ run.emitted :=
  run.certificate.toProductionPrefix.events_reverse_append

end LocalBlockRun

/- REF: docs/MACRO_ASSEMBLER.md#proof-directed-local-blocks -/
/-- A reusable implementation of one explicit local contract.  The fuel is fixed by the selected
    body; the returned witness retains the exact initial state rather than existentially choosing a
    more convenient entry. -/
structure LocalBlockDischarge {Event Ghost Result : Type}
    [ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr))
    (contract : LocalBlockContract Event Ghost Result) : Type where
  fuel : Nat
  discharge : ∀ initial initialEventsRev initialGhost,
    contract.entry initial initialEventsRev initialGhost →
    Nonempty (LocalBlockRun selected indexed contract fuel
      initial initialEventsRev initialGhost)

namespace LocalBlockDischarge

/- REF: docs/MACRO_ASSEMBLER.md#proof-directed-local-blocks -/
/-- Strengthen an entry requirement and weaken/project an exit requirement without changing the
    selected artifact index or nominal body identity.  This is property-relative transport, not a
    code replacement or placement theorem. -/
def refine {Event Ghost Result : Type}
    [ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)}
    {source target : LocalBlockContract Event Ghost Result}
    (implementation : LocalBlockDischarge selected indexed source)
    (entry : ∀ state eventsRev ghost,
      target.entry state eventsRev ghost → source.entry state eventsRev ghost)
    (exit : ∀ initial initialEventsRev initialGhost final finalEventsRev finalGhost emitted result,
      source.exit initial initialEventsRev initialGhost
          final finalEventsRev finalGhost emitted result →
        target.exit initial initialEventsRev initialGhost
          final finalEventsRev finalGhost emitted result) :
    LocalBlockDischarge selected indexed target where
  fuel := implementation.fuel
  discharge initial initialEventsRev initialGhost accepted := by
    let sourceAccepted := entry initial initialEventsRev initialGhost accepted
    let ⟨sourceRun⟩ := implementation.discharge initial initialEventsRev initialGhost sourceAccepted
    exact ⟨{
      cutpoint := sourceRun.cutpoint
      finalGhost := sourceRun.finalGhost
      result := sourceRun.result
      entry := accepted
      exit := exit _ _ _ _ _ _ _ _ sourceRun.exit
    }⟩

end LocalBlockDischarge

/- REF: docs/MACRO_ASSEMBLER.md#proof-directed-local-blocks -/
/-- Two concrete runs composed at the exact middle machine/event/ghost state.  Retaining both
    witnesses prevents an existentially reselected middle state from satisfying a different second
    precondition. -/
structure SequentialLocalBlockRuns {Event Ghost FirstResult SecondResult : Type}
    [ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr))
    (firstContract : LocalBlockContract Event Ghost FirstResult)
    (secondContract : LocalBlockContract Event Ghost SecondResult)
    (firstFuel secondFuel : Nat) (initial : X86_64MachineState)
    (initialEventsRev : List Event) (initialGhost : Ghost) : Type where
  first : LocalBlockRun selected indexed firstContract firstFuel
    initial initialEventsRev initialGhost
  second : LocalBlockRun selected indexed secondContract secondFuel
    first.final first.finalEventsRev first.finalGhost

namespace SequentialLocalBlockRuns

/- REF: docs/MACRO_ASSEMBLER.md#proof-directed-local-blocks -/
/-- Exact selected-prefix composition through the retained middle state. -/
theorem combinedPrefix {Event Ghost FirstResult SecondResult : Type}
    [ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)}
    {firstContract : LocalBlockContract Event Ghost FirstResult}
    {secondContract : LocalBlockContract Event Ghost SecondResult}
    {firstFuel secondFuel : Nat} {initial : X86_64MachineState}
    {initialEventsRev : List Event} {initialGhost : Ghost}
    (runs : SequentialLocalBlockRuns selected indexed
      firstContract secondContract firstFuel secondFuel initial initialEventsRev initialGhost) :
    SelectedPrefix selected indexed (firstFuel + secondFuel) initial initialEventsRev
      runs.second.final runs.second.finalEventsRev
      (runs.first.emitted ++ runs.second.emitted) :=
  runs.first.certificate.append runs.second.certificate

/- REF: docs/MACRO_ASSEMBLER.md#proof-directed-local-blocks -/
/-- Exact continuation theorem for the composed pair. -/
theorem run_continuation {Event Ghost FirstResult SecondResult : Type}
    [ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)}
    {firstContract : LocalBlockContract Event Ghost FirstResult}
    {secondContract : LocalBlockContract Event Ghost SecondResult}
    {firstFuel secondFuel continuationFuel : Nat} {initial : X86_64MachineState}
    {initialEventsRev : List Event} {initialGhost : Ghost}
    (runs : SequentialLocalBlockRuns selected indexed
      firstContract secondContract firstFuel secondFuel initial initialEventsRev initialGhost) :
    runProgramOutcomeLoop indexed (firstFuel + secondFuel + continuationFuel)
        initial initialEventsRev =
      runProgramOutcomeLoop indexed continuationFuel
        runs.second.final runs.second.finalEventsRev := by
  exact runs.combinedPrefix.toProductionPrefix.run continuationFuel

end SequentialLocalBlockRuns

/- REF: docs/MACRO_ASSEMBLER.md#proof-directed-local-blocks -/
/-- Apply the second discharge to the first run's exact final machine/event/ghost state.  The caller
    supplies the explicit forward/backward meet establishing the second entry. -/
theorem LocalBlockRun.then {Event Ghost FirstResult SecondResult : Type}
    [ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)}
    {firstContract : LocalBlockContract Event Ghost FirstResult}
    {secondContract : LocalBlockContract Event Ghost SecondResult}
    {firstFuel : Nat} {initial : X86_64MachineState}
    {initialEventsRev : List Event} {initialGhost : Ghost}
    (first : LocalBlockRun selected indexed firstContract firstFuel
      initial initialEventsRev initialGhost)
    (second : LocalBlockDischarge selected indexed secondContract)
    (middle : secondContract.entry first.final first.finalEventsRev first.finalGhost) :
    Nonempty (SequentialLocalBlockRuns selected indexed
      firstContract secondContract firstFuel second.fuel initial initialEventsRev initialGhost) := by
  let ⟨secondRun⟩ := second.discharge first.final first.finalEventsRev first.finalGhost middle
  exact ⟨⟨first, secondRun⟩⟩

end Gasm.Targets.X86_64
