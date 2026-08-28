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
import Gasm.Targets.X86_64.MemoryFrame.Common
import Gasm.Targets.X86_64.Instructions.Ret

namespace Gasm.Targets.X86_64.MemoryFrame

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- RET never writes memory (its declared store footprint is empty). -/
theorem RetOp.writesWithin (i : RetOp) : WritesWithin i := by
  intro s a _
  show X86_64Mem.read .w8 a (X86_64Instruction.step i s).memory = X86_64Mem.read .w8 a s.memory
  simp only [X86_64Instruction.step, X86_64MachineState.setGpr64]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- RET's declared load footprint (`[rsp, rsp+8)`, the return address `pop64` reads to compute
    the new `rip`) is exactly what `step` reads: two pre-states agreeing outside memory and
    agreeing on that footprint step to states agreeing outside memory. RET declares no store, so
    the `StoreAgreeOn` conjunct is vacuous (its empty store footprint has no members). -/
theorem RetOp.readsWithin (i : RetOp) : ReadsWithin i := by
  intro s1 s2 hout hagree
  obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
  simp [X86_64Instruction.memAccesses, loadFootprint, footprintFor,
    MemAccessSpec.addresses, MemRef.effectiveAddress, agreeOn] at hagree
  have hread : X86_64Mem.read .w64 (s1.gprs Reg64.rsp) s1.memory =
      X86_64Mem.read .w64 (s1.gprs Reg64.rsp) s2.memory :=
    X86_64Mem.read_congr' .w64 _ s1.memory s2.memory hagree
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.rsp,
        X86_64MachineState.setGpr64, X86_64MachineState.read64] <;>
      simp_all
  · intro a ha
    simp [X86_64Instruction.memAccesses, storeFootprint, footprintFor] at ha

end Gasm.Targets.X86_64.MemoryFrame
