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
import Spikes.Spike4HttpServer.Runtime
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
  | parseChunk

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
  Args := fun _ => StreamingParserArgs
  Binding := fun _ => Unit
  Result := fun _ => StreamingRequestLineResult
  Outcome := fun _ => StreamingParserOutcome
  ObligationFragment := fun _ => Nat
  requiredObligations := fun _ _ _ => 1
  emittedObligations := fun _ _ _ _ outcome =>
    match outcome with
    | .needMore => 1
    | .completed | .resourceExhausted => 0
  requires := fun _ _ _ world => world.requestOpen = true
  transitions := fun _ args _ result outcome before after =>
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
  PublicEntry := StreamingParserExport
  LookupKey := StreamingParserExport
  artifactImplements := fun artifact implementation =>
    artifact = .parser ∧ implementation = .parser
  publicEntries := fun _ => [.parseChunk]
  callableEntries := fun _ => [.parseChunk]
  lookupKey := id
  resolvesEntry := fun artifact entry implementation _ _ =>
    artifact = .parser ∧ entry = .parseChunk ∧ implementation = .parser
  jointlyAdmissible := fun artifact entries =>
    artifact = .parser ∧ entries = [(.parseChunk, .parser, (), ())]
  runs := fun artifact implementation _ _ before execution exitKind after =>
    artifact = .parser ∧
    implementation = .parser ∧
    after = before ∧
    execution = streamRequestLineChunk before.budget default before.bytes ∧
    exitKind = parserOutcome execution
  admissible := fun artifact implementation _ _ before execution exitKind after =>
    artifact = .parser ∧
    implementation = .parser ∧
    after = before ∧
    execution = streamRequestLineChunk before.budget default before.bytes ∧
    exitKind = parserOutcome execution

def parserRealization :
    ContextBoundaryRealization ParserWorld StreamingParserKey StreamingParserTarget
      .parseChunk where
  signature := ()
  entryKind := ()
  implementation := .parser
  artifact := .parser
  artifactConnection := ⟨rfl, rfl⟩
  relatesEntry := fun physical args _ world =>
    physical = args ∧ world.requestOpen = true ∧ world.retainedBytes = 0
  relatesWorld := fun _ world => world.retainedBytes = 0 ∨ world.requestOpen = true
  relatesExit := fun _ execution exitKind _ result outcome world =>
    result = execution ∧ outcome = exitKind ∧
      world = { requestOpen := parserNeedsMore exitKind, retainedBytes := 0 }
  entryRelatesWorld := by
    intro physical args binding world related
    exact Or.inr related.2.1
  exitRelatesWorld := by
    intro physicalBefore execution exitKind physicalAfter result outcome world related
    rcases related with ⟨_, _, rfl⟩
    exact Or.inl rfl
  physicalAdmissibility := by
    intro before execution exitKind after runs
    exact runs
  refinesContract := by
    intro physicalBefore args binding logicalBefore execution exitKind physicalAfter
      related required runs
    rcases related with ⟨hPhysical, hOpen, hRetained⟩
    rcases runs with ⟨_, _, hAfter, hExecution, hOutcome⟩
    have hExecution' : execution = streamRequestLineChunk args.budget default args.bytes := by
      rw [hPhysical] at hExecution
      exact hExecution
    have hOutcome' : exitKind = parserOutcome execution := hOutcome
    let after : ParserWorld :=
      { requestOpen := parserNeedsMore exitKind, retainedBytes := 0 }
    refine ⟨execution, exitKind, after, ?_, ?_⟩
    · exact ⟨rfl, rfl, rfl⟩
    · constructor
      · exact hExecution'
      constructor
      · exact hOutcome'
      · simp [after, hOpen]

def verifiedStreamingParserComponent :
    VerifiedComponent ParserWorld StreamingParserKey StreamingParserTarget
      (inferInstance : BoundaryContextSpec ParserWorld StreamingParserKey)
      (inferInstance : TargetBoundarySemantics StreamingParserTarget) where
  exportSet := {
    artifact := .parser
    publicManifest := [.parseChunk]
    entries := [{
      key := .parseChunk
      physicalEntry := .parseChunk
      realization := parserRealization
      resolves := ⟨rfl, rfl, rfl⟩
    }]
    uniqueLookup := by simp
    exactPublicTable := rfl
    exactCallableTable := rfl
    sameArtifact := by simp [parserRealization]
    jointlyAdmissible := ⟨rfl, rfl⟩
  }
  callableNonempty := by simp

/-- Non-vacuous implementation connection consumed by a platform capability.  It names the exact
    component artifact and the exact realization whose `artifactConnection`, `physicalAdmissibility`
    and `refinesContract` fields carry the proof. -/
structure StreamingParserComponentConnection where
  component : VerifiedComponent ParserWorld StreamingParserKey StreamingParserTarget
    (inferInstance : BoundaryContextSpec ParserWorld StreamingParserKey)
    (inferInstance : TargetBoundarySemantics StreamingParserTarget)
  exactComponent : component = verifiedStreamingParserComponent

def requestParserArgs (request : ByteArray) : StreamingParserArgs :=
  { budget := requestLineBudget, bytes := Gasm.Effects.toByteList request }

def requestParserExecution (request : ByteArray) : StreamingRequestLineResult :=
  streamRequestLineChunk requestLineBudget default (Gasm.Effects.toByteList request)

/-- One request-driver invocation is an established execution of the exact published parser
    realization.  The proof consumes `parserRealization.refinesContract`; it is not a second
    restatement of the parser implementation. -/
theorem request_driver_consumes_parser_realization (request : ByteArray) :
    ∃ result outcome logicalAfter,
      parserRealization.relatesExit
        (requestParserArgs request)
        (requestParserExecution request)
        (parserOutcome (requestParserExecution request))
        (requestParserArgs request)
        result outcome logicalAfter ∧
      (inferInstance : BoundaryContextSpec ParserWorld StreamingParserKey).transitions
        .parseChunk (requestParserArgs request) () result outcome
        { requestOpen := true, retainedBytes := 0 } logicalAfter := by
  apply parserRealization.refinesContract
  · exact ⟨rfl, rfl, rfl⟩
  · rfl
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Reusable library-owned connection from the arbitrary-finite request driver to the exact
    verified parser component. Target adapters consume this once; ordinary programs do not replay
    parser or ABI proofs. -/
structure StreamingParserDriverConnection extends StreamingParserComponentConnection where
  routeConnected : ∀ request : ByteArray,
    (driveRequest request).1 = routeParserResult (requestParserExecution request)
  boundaryConnected : ∀ request : ByteArray,
    ∃ result outcome logicalAfter,
      parserRealization.relatesExit
        (requestParserArgs request)
        (requestParserExecution request)
        (parserOutcome (requestParserExecution request))
        (requestParserArgs request)
        result outcome logicalAfter ∧
      (inferInstance : BoundaryContextSpec ParserWorld StreamingParserKey).transitions
        .parseChunk (requestParserArgs request) () result outcome
        { requestOpen := true, retainedBytes := 0 } logicalAfter

def streamingParserDriverConnection : StreamingParserDriverConnection where
  component := verifiedStreamingParserComponent
  exactComponent := rfl
  routeConnected := driveRequest_route_refines_parser
  boundaryConnected := request_driver_consumes_parser_realization

def streamingParserComponentConnection : StreamingParserComponentConnection :=
  streamingParserDriverConnection.toStreamingParserComponentConnection

end Spikes.Spike4HttpServer
