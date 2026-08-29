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

import Gasm.Core.AbiContext
import Spikes.Spike4HttpServer.StreamingRequestLine

namespace Spikes.Spike4HttpServer

open Gasm.Core

/-!
The request-line parser is a component boundary, not trusted host magic.  This file gives its
streaming implementation a nominal ABI key, a result-dependent contract, an implementation and
artifact identity, and an assume/guarantee realization.  Target lowerings may statically inline or
dynamically link the component, but a whole-program capability connection must consume this
realization rather than merely claim the import name.
-/

structure ParserWorld where
  requestOpen : Bool
  retainedBytes : Nat
  deriving DecidableEq, Repr

inductive StreamingParserKey

structure StreamingParserArgs where
  budget : Nat
  bytes : List UInt8

inductive StreamingParserOutcome where
  | needMore
  | completed
  | resourceExhausted
  deriving DecidableEq, BEq, Repr

def parserOutcome : StreamingRequestLineResult → StreamingParserOutcome
  | .needMore _ => .needMore
  | .complete _ => .completed
  | .resourceExhausted _ => .resourceExhausted

def parserNeedsMore : StreamingParserOutcome → Bool
  | .needMore => true
  | .completed | .resourceExhausted => false

instance : BoundaryContextSpec ParserWorld StreamingParserKey where
  Args := StreamingParserArgs
  Binding := Unit
  Result := StreamingRequestLineResult
  Outcome := StreamingParserOutcome
  ObligationFragment := Nat
  requiredObligations := fun _ _ => 1
  emittedObligations := fun _ _ _ outcome =>
    match outcome with
    | .needMore => 1
    | .completed | .resourceExhausted => 0
  requires := fun _ _ world => world.requestOpen = true
  transitions := fun args _ result outcome before after =>
    result = streamRequestLineChunk args.budget default args.bytes ∧
    outcome = parserOutcome result ∧
    after.retainedBytes = 0 ∧
    after.requestOpen = parserNeedsMore outcome ∧
    before.requestOpen = true

inductive StreamingParserImplementation
  | parser

inductive StreamingParserArtifact
  | parser

inductive StreamingParserExport
  | parseChunk

inductive StreamingParserTarget

instance : TargetBoundarySemantics StreamingParserTarget where
  Implementation := StreamingParserImplementation
  Artifact := StreamingParserArtifact
  Signature := Unit
  EntryKind := Unit
  ExitKind := StreamingParserOutcome
  PhysicalState := StreamingParserArgs
  Execution := StreamingRequestLineResult
  artifactImplements := fun artifact implementation =>
    artifact = .parser ∧ implementation = .parser
  runs := fun implementation _ _ before execution exitKind after =>
    implementation = .parser ∧
    after = before ∧
    execution = streamRequestLineChunk before.budget default before.bytes ∧
    exitKind = parserOutcome execution
  admissible := fun implementation _ _ before execution exitKind after =>
    implementation = .parser ∧
    after = before ∧
    execution = streamRequestLineChunk before.budget default before.bytes ∧
    exitKind = parserOutcome execution

def parserRealization :
    ContextBoundaryRealization ParserWorld StreamingParserKey StreamingParserTarget where
  signature := ()
  entryKind := ()
  implementation := .parser
  artifact := .parser
  artifactConnection := ⟨rfl, rfl⟩
  relatesEntry := fun physical args _ world =>
    physical = args ∧ world.requestOpen = true ∧ world.retainedBytes = 0
  logicalResult := fun _ execution _ => execution
  logicalOutcome := fun _ _ exitKind _ => exitKind
  relatesWorld := fun _ world => world.retainedBytes = 0 ∨ world.requestOpen = true
  entryRelatesWorld := by
    intro physical args binding world related
    exact Or.inr related.2.1
  physicalAdmissibility := by
    intro before execution exitKind after runs
    exact runs
  refinesContract := by
    intro physicalBefore args binding logicalBefore execution exitKind physicalAfter
      related required runs
    rcases related with ⟨hPhysical, hOpen, hRetained⟩
    rcases runs with ⟨_, hAfter, hExecution, hOutcome⟩
    have hExecution' : execution = streamRequestLineChunk args.budget default args.bytes := by
      rw [hPhysical] at hExecution
      exact hExecution
    have hOutcome' : exitKind = parserOutcome execution := hOutcome
    let after : ParserWorld :=
      { requestOpen := parserNeedsMore exitKind, retainedBytes := 0 }
    refine ⟨after, ?_, ?_⟩
    · simp [after]
    · constructor
      · exact hExecution'
      constructor
      · exact hOutcome'
      · simp [after, hOpen]

def verifiedStreamingParserComponent :
    VerifiedComponent ParserWorld StreamingParserKey StreamingParserTarget where
  Export := StreamingParserExport
  artifact := .parser
  exports := [.parseChunk]
  exportsNonempty := by simp
  realization := fun _ => parserRealization
  realizationUsesArtifact := by intro exported; cases exported; rfl

/-- Non-vacuous implementation connection consumed by a platform capability.  It names the exact
    component artifact and the exact realization whose `artifactConnection`, `physicalAdmissibility`
    and `refinesContract` fields carry the proof. -/
structure StreamingParserComponentConnection where
  component : VerifiedComponent ParserWorld StreamingParserKey StreamingParserTarget
  exactComponent : component = verifiedStreamingParserComponent

def streamingParserComponentConnection : StreamingParserComponentConnection :=
  ⟨verifiedStreamingParserComponent, rfl⟩

end Spikes.Spike4HttpServer
