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

import Gasm.MemoryModel.ProgramOrderPath

/-!
Private controls for exact program-order path endpoint projection.

These controls exercise the public consequence without creating a target fixture or claiming target
origin, fidelity, admission, heterogeneous causality, or execution authority.
-/

namespace Gasm.MemoryModel.CpuGraph.ProgramOrderPathControls

open RelationPath
open Graph

universe u v w x y

variable {EventId : Type u} {Location : Type v} {Value : Type w} {AtomicObject : Type x}
variable {Agent : Type y}
variable {g : Graph EventId Location Value AtomicObject}

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem two_edges_have_ordered_points (p : ProgramOrderProjection g Agent)
    {first middle last : EventId} (firstStep : g.po first middle)
    (secondStep : g.po middle last) :
    ∃ agent firstSeq lastSeq,
      p.programPoint first = some (agent, firstSeq) ∧
      p.programPoint last = some (agent, lastSeq) ∧
      firstSeq < lastSeq := by
  apply p.po_path_points
  exact .cons (label := ()) firstStep (.single (label := ()) secondStep)

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem path_from_no_point_rejected (p : ProgramOrderProjection g Agent)
    {source target : EventId} {labels : List Unit}
    (sourceNone : p.programPoint source = none)
    (path : LabeledPath (poEdge g) source target labels) : False := by
  obtain ⟨agent, sourceSeq, _, sourcePoint, _, _⟩ := p.po_path_points path
  simp [sourceNone] at sourcePoint

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem path_to_no_point_rejected (p : ProgramOrderProjection g Agent)
    {source target : EventId} {labels : List Unit}
    (targetNone : p.programPoint target = none)
    (path : LabeledPath (poEdge g) source target labels) : False := by
  obtain ⟨agent, _, targetSeq, _, targetPoint, _⟩ := p.po_path_points path
  simp [targetNone] at targetPoint

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem distinct_agent_endpoints_rejected (p : ProgramOrderProjection g Agent)
    {source target : EventId} {sourceAgent targetAgent : Agent}
    {sourceSeq targetSeq : Nat} (agentsDiffer : sourceAgent ≠ targetAgent)
    (sourcePoint : p.programPoint source = some (sourceAgent, sourceSeq))
    (targetPoint : p.programPoint target = some (targetAgent, targetSeq))
    {labels : List Unit} (path : LabeledPath (poEdge g) source target labels) : False := by
  obtain ⟨agent, pathSourceSeq, pathTargetSeq, pathSource, pathTarget, _⟩ :=
    p.po_path_points path
  have sourcePair : (sourceAgent, sourceSeq) = (agent, pathSourceSeq) :=
    Option.some.inj (sourcePoint.symm.trans pathSource)
  have targetPair : (targetAgent, targetSeq) = (agent, pathTargetSeq) :=
    Option.some.inj (targetPoint.symm.trans pathTarget)
  exact agentsDiffer ((congrArg Prod.fst sourcePair).trans (congrArg Prod.fst targetPair).symm)

end Gasm.MemoryModel.CpuGraph.ProgramOrderPathControls
