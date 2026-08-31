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

import Gasm.MemoryModel.AddressRange
import Gasm.Targets.X86_64.Memory

/-!
Exact projection from the canonical x86 memory descriptor to the target-neutral byte range.
This is descriptor geometry only: it proves no provenance, permissions, mapping, target
attributes, or execution admission.
-/

namespace Gasm.Targets.X86_64

open Gasm.MemoryModel

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- The exact contiguous byte range denoted by one descriptor in its pre-step state. -/
def MemAccessSpec.addressRange (spec : MemAccessSpec) (state : X86_64MachineState) :
    AddressRange :=
  ⟨spec.ref.effectiveAddress state, spec.width.bytes⟩

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- Descriptor and neutral-range byte enumerations are definitionally aligned. -/
@[simp] theorem MemAccessSpec.addresses_eq_addressRange_addresses
    (spec : MemAccessSpec) (state : X86_64MachineState) :
    spec.addresses state = (spec.addressRange state).addresses := by
  rfl

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
/-- Every supported x86 memory width is nonempty. Non-wrapping remains a dynamic/profile proof. -/
theorem MemAccessSpec.addressRange_nonempty (spec : MemAccessSpec)
    (state : X86_64MachineState) : 0 < (spec.addressRange state).length := by
  change 0 < spec.width.bytes
  cases spec.width <;> decide

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
/-- For x86 descriptors, range validity reduces exactly to the dynamic no-wrap fact. -/
theorem MemAccessSpec.addressRange_wellFormed_iff (spec : MemAccessSpec)
    (state : X86_64MachineState) :
    (spec.addressRange state).WellFormed ↔
      (spec.ref.effectiveAddress state).toNat + spec.width.bytes ≤ 2 ^ 64 := by
  constructor
  · intro wellFormed
    exact wellFormed.noWrap
  · intro noWrap
    exact ⟨spec.addressRange_nonempty state, noWrap⟩

end Gasm.Targets.X86_64
