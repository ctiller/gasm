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

/-!
Private positive fixture for the CPU structural certificates.

The fixture contains one structural initial write and one ordinary read of the same byte/value,
plus the smallest honest CPU program-point assignment. Constructing the real
`StructuralCpuProjection` prevents rejection-only controls from becoming vacuous if a future edit
makes the certificates inconsistent. This proves structural inhabitation only: it grants no target
fidelity, execution authority, or M2-X/M2-A admission.
-/

namespace Gasm.MemoryModel.CpuGraph.StructuralBaselineFixture

open Graph

private inductive FixtureEvent where
  | initial
  | read
deriving DecidableEq

private inductive FixtureLocation where
  | byte
deriving DecidableEq

private inductive FixtureAgent where
  | cpu

private def fixtureGraph : Graph FixtureEvent FixtureLocation Nat Unit where
  events := [.initial, .read]
  locations := [.byte]
  readAt e loc := e = .read ∧ loc = .byte
  writeAt e loc := e = .initial ∧ loc = .byte
  initialAt e loc := e = .initial ∧ loc = .byte
  isAtomicRead _ := False
  isAtomicRmw _ := False
  isFailedWrite _ := False
  atomicObject _ := none
  atomicCompatible _ _ := False
  readValue e loc := if e = .read ∧ loc = .byte then some 7 else none
  writeValue e loc := if e = .initial ∧ loc = .byte then some 7 else none
  po _ _ := False
  rf w r loc := w = .initial ∧ r = .read ∧ loc = .byte
  co _ _ _ := False

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem fixtureWellFormed : fixtureGraph.WellFormed where
  events_nodup := by simp [fixtureGraph]
  locations_nodup := by simp [fixtureGraph]
  read_fragment_mem := by
    intro r loc h
    rcases h with ⟨rfl, rfl⟩
    simp [fixtureGraph]
  write_fragment_mem := by
    intro w loc h
    rcases h with ⟨rfl, rfl⟩
    simp [fixtureGraph]
  initial_fragment_mem := by
    intro init loc h
    rcases h with ⟨rfl, rfl⟩
    simp [fixtureGraph]
  atomic_read_mem := by simp [fixtureGraph]
  atomic_read_nonempty := by simp [fixtureGraph]
  atomic_rmw_is_atomic_read := by simp [fixtureGraph]
  failed_write_mem := by simp [fixtureGraph]
  atomic_object_mem := by simp [fixtureGraph]
  initial_is_write := by simp [fixtureGraph]
  read_has_value := by
    intro r loc h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨7, by simp [fixtureGraph]⟩
  write_has_value := by
    intro w loc h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨7, by simp [fixtureGraph]⟩
  read_value_has_fragment := by
    intro r loc value h
    cases r <;> cases loc <;> simp_all [fixtureGraph]
  write_value_has_fragment := by
    intro w loc value h
    cases w <;> cases loc <;> simp_all [fixtureGraph]
  failed_write_has_no_fragment := by simp [fixtureGraph]
  po_endpoints := by simp [fixtureGraph]
  po_irrefl := by simp [fixtureGraph]
  po_trans := by simp [fixtureGraph]
  rf_endpoints := by
    intro w r loc h
    rcases h with ⟨rfl, rfl, rfl⟩
    simp [fixtureGraph]
  rf_classes := by simp [fixtureGraph]
  rf_value_agreement := by
    intro w r loc h
    rcases h with ⟨rfl, rfl, rfl⟩
    simp [fixtureGraph]
  rf_irrefl := by
    intro e loc h
    rcases h with ⟨h₁, h₂, _⟩
    cases h₁
    contradiction
  rf_total := by
    intro r loc h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨.initial, by simp [fixtureGraph]⟩
  rf_functional := by
    intro w₁ w₂ r loc h₁ h₂
    exact h₁.1.trans h₂.1.symm
  co_endpoints := by simp [fixtureGraph]
  co_classes := by simp [fixtureGraph]
  co_irrefl := by simp [fixtureGraph]
  co_trans := by simp [fixtureGraph]
  co_total := by
    intro a b loc ha hb hne
    have hab : a = b := ha.1.trans hb.1.symm
    exact (hne hab).elim
  initial_exists := by
    intro loc hloc
    cases loc
    exact ⟨.initial, by simp [fixtureGraph]⟩
  initial_unique := by
    intro a b loc ha hb
    exact ha.1.trans hb.1.symm
  initial_first := by
    intro init w loc hi hw hne
    have : init = w := hi.1.trans hw.1.symm
    exact (hne this).elim
  atomic_co_uniform := by simp [fixtureGraph]
  atomic_read_single_source := by simp [fixtureGraph]
  successful_rmw_same_footprint := by simp [fixtureGraph]
  successful_rmw_adjacent := by simp [fixtureGraph]

private def fixtureProgramPoint : FixtureEvent → Option (FixtureAgent × Nat)
  | .initial => none
  | .read => some (.cpu, 0)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private def fixtureProgramOrder : fixtureGraph.ProgramOrderProjection FixtureAgent where
  programPoint := fixtureProgramPoint
  point_mem := by
    intro e agent sequence h
    cases e <;> simp [fixtureProgramPoint, fixtureGraph] at h ⊢
  sequence_unique := by
    intro a b agent sequence ha hb
    cases a <;> cases b <;> simp [fixtureProgramPoint] at ha hb ⊢
  initial_no_point := by
    intro init loc h
    rcases h with ⟨rfl, rfl⟩
    simp [fixtureProgramPoint]
  po_iff := by
    intro a b
    cases a <;> cases b <;> simp [fixtureGraph, fixtureProgramPoint]

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Elaboration of this private witness is the positive non-vacuity control. -/
private def structuralCertificatesAreInhabited :
    StructuralCpuProjection fixtureGraph FixtureAgent where
  fragments := fixtureWellFormed
  programOrder := fixtureProgramOrder

end Gasm.MemoryModel.CpuGraph.StructuralBaselineFixture
