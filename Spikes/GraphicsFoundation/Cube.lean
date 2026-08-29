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

import Spikes.GraphicsFoundation.Presentation

namespace Spikes.GraphicsFoundation.Cube

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Exact logical vertex data. The native adapter realizes these integers as floating-point values. -/
structure Vertex where
  x : Int
  y : Int
  z : Int
  r : Nat
  g : Nat
  b : Nat
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
def vertices : List Vertex := [
  ⟨-1, -1, -1, 0, 0, 0⟩, ⟨1, -1, -1, 1, 0, 0⟩,
  ⟨1, 1, -1, 1, 1, 0⟩, ⟨-1, 1, -1, 0, 1, 0⟩,
  ⟨-1, -1, 1, 0, 0, 1⟩, ⟨1, -1, 1, 1, 0, 1⟩,
  ⟨1, 1, 1, 1, 1, 1⟩, ⟨-1, 1, 1, 0, 1, 1⟩]

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- Twelve counter-clockwise triangles, two for each cube face. -/
def indices : List Nat := [
  0, 2, 1, 0, 3, 2,
  4, 5, 6, 4, 6, 7,
  0, 1, 5, 0, 5, 4,
  2, 3, 7, 2, 7, 6,
  0, 4, 7, 0, 7, 3,
  1, 2, 6, 1, 6, 5]

private def triangles : List Nat → List (Nat × Nat × Nat)
  | a :: b :: c :: rest => (a, b, c) :: triangles rest
  | _ => []

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
def geometryValid : Bool :=
  vertices.length == 8 && indices.length == 36 &&
  indices.all (fun i => i < vertices.length) &&
  (triangles indices).all (fun t => t.1 != t.2.1 && t.2.1 != t.2.2 && t.1 != t.2.2)

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
theorem geometry_valid : geometryValid = true := by rfl

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- The selected inter-stage color contract. Position is a built-in and is intentionally absent. -/
def colorSlot : Presentation.InterfaceSlot := { location := 0, components := 3 }

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
structure ShaderContract where
  vertexInputs : List Presentation.InterfaceSlot
  vertexOutputs : List Presentation.InterfaceSlot
  fragmentInputs : List Presentation.InterfaceSlot
  fragmentOutputs : List Presentation.InterfaceSlot
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
def shaderContract : ShaderContract := {
  vertexInputs := [{ location := 0, components := 3 }, { location := 1, components := 3 }]
  vertexOutputs := [colorSlot]
  fragmentInputs := [colorSlot]
  fragmentOutputs := [{ location := 0, components := 4 }] }

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
def shaderContractValid (c : ShaderContract) : Bool :=
  c.fragmentInputs.all (fun input => c.vertexOutputs.contains input) &&
  c.vertexInputs.all (fun slot => slot.components > 0 && slot.components ≤ 4) &&
  c.fragmentOutputs == [{ location := 0, components := 4 }]

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
theorem shader_contract_valid : shaderContractValid shaderContract = true := by rfl

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
/-- A rotation tick is deliberately parametric: no floating-point equivalence is claimed. -/
structure FrameParameters where
  rotationTick : Nat
  viewport : Presentation.Extent
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#5-cube-and-presentation-prototype -/
def frameParametersValid (p : FrameParameters) : Bool :=
  p.viewport.width > 0 && p.viewport.height > 0

end Spikes.GraphicsFoundation.Cube
