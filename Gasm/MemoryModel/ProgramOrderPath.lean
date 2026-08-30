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

import Gasm.MemoryModel.ProgramOrder
import Gasm.MemoryModel.CpuGraphOrderPath

/-!
Program-point consequences of exact structural CPU program-order paths.

This module uses only `ProgramOrderProjection`: fragment, reads-from, and coherence well-formedness
are unrelated to the endpoint fact and impose no premise. The retained `LabeledPath` remains the
source witness; the theorem below exposes only its program-point consequence and grants no target
fidelity, observable-path fidelity, execution admission, heterogeneous causality, or authority.
-/

namespace Gasm.MemoryModel.CpuGraph

open RelationPath

namespace Graph.ProgramOrderProjection

universe u v w x y

variable {EventId : Type u} {Location : Type v} {Value : Type w} {AtomicObject : Type x}
variable {Agent : Type y}
variable {g : Graph EventId Location Value AtomicObject}

private theorem po_trans_projection_only (p : ProgramOrderProjection g Agent)
    {first middle last : EventId}
    (firstStep : g.po first middle) (secondStep : g.po middle last) : g.po first last := by
  obtain ⟨agent₁, firstSeq, middleSeq₁, firstPoint, middlePoint₁, firstLt⟩ :=
    p.po_iff.mp firstStep
  obtain ⟨agent₂, middleSeq₂, lastSeq, middlePoint₂, lastPoint, secondLt⟩ :=
    p.po_iff.mp secondStep
  have middlePair : (agent₁, middleSeq₁) = (agent₂, middleSeq₂) :=
    Option.some.inj (middlePoint₁.symm.trans middlePoint₂)
  have agentsEqual : agent₁ = agent₂ := congrArg Prod.fst middlePair
  have sequencesEqual : middleSeq₁ = middleSeq₂ := congrArg Prod.snd middlePair
  subst agent₂
  subst middleSeq₂
  exact p.po_iff.mpr
    ⟨agent₁, firstSeq, lastSeq, firstPoint, lastPoint, Nat.lt_trans firstLt secondLt⟩

private theorem po_of_path (p : ProgramOrderProjection g Agent) {source target : EventId}
    {labels : List Unit} (path : LabeledPath (Graph.poEdge g) source target labels) :
    g.po source target := by
  induction path with
  | single step => exact step
  | cons step _ ih => exact po_trans_projection_only p step ih

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- An exact structural CPU program-order path has strictly ordered endpoints on one CPU agent. -/
theorem po_path_points (p : ProgramOrderProjection g Agent) {source target : EventId}
    {labels : List Unit} (path : LabeledPath (Graph.poEdge g) source target labels) :
    ∃ agent sourceSeq targetSeq,
      p.programPoint source = some (agent, sourceSeq) ∧
      p.programPoint target = some (agent, targetSeq) ∧
      sourceSeq < targetSeq :=
  p.po_iff.mp (po_of_path p path)

end Graph.ProgramOrderProjection

end Gasm.MemoryModel.CpuGraph
