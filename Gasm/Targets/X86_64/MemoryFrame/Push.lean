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
import Gasm.Targets.X86_64.Instructions.Push

namespace Gasm.Targets.X86_64.MemoryFrame

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- PUSH's declared store footprint (`[rsp-8, rsp-8+8)`, evaluated at the pre-step `rsp`) is
    exactly what `step` (via `push64`) writes: everywhere else is untouched. -/
theorem PushR64.writesWithin (i : PushR64) : WritesWithin i := by
  intro s a ha
  simp [X86_64Instruction.memAccesses, storeFootprint, footprintFor,
    MemAccessSpec.addresses, MemRef.effectiveAddress] at ha
  have hbase : s.gprs Reg64.rsp + (-8 : UInt64) = s.gprs Reg64.rsp - 8 := by
    apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_add, UInt64.toNat_sub, UInt64.size]
    omega
  rw [hbase] at ha
  have h0 : s.gprs Reg64.rsp - 8 ≠ a := by simpa using ha 0 (by decide)
  have h1 : s.gprs Reg64.rsp - 8 + 1 ≠ a := by simpa using ha 1 (by decide)
  have h2 : s.gprs Reg64.rsp - 8 + 2 ≠ a := by simpa using ha 2 (by decide)
  have h3 : s.gprs Reg64.rsp - 8 + 3 ≠ a := by simpa using ha 3 (by decide)
  have h4 : s.gprs Reg64.rsp - 8 + 4 ≠ a := by simpa using ha 4 (by decide)
  have h5 : s.gprs Reg64.rsp - 8 + 5 ≠ a := by simpa using ha 5 (by decide)
  have h6 : s.gprs Reg64.rsp - 8 + 6 ≠ a := by simpa using ha 6 (by decide)
  have h7 : s.gprs Reg64.rsp - 8 + 7 ≠ a := by simpa using ha 7 (by decide)
  show X86_64Mem.read .w8 a (X86_64Instruction.step i s).memory = X86_64Mem.read .w8 a s.memory
  simp only [X86_64Instruction.step, X86_64Mem.read, X86_64Mem.readByte,
    X86_64MachineState.rsp, X86_64MachineState.setGpr64, X86_64Mem.write, beq_self_eq_true,
    if_true]
  simp [Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6,
    Ne.symm h7]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- PUSH never reads memory (its declared load footprint is empty), so two pre-states agreeing
    outside memory step to states agreeing outside memory regardless of memory contents. The
    `StoreAgreeOn` conjunct is not vacuous here (PUSH declares a store): it holds because the
    pushed address and value are both register-derived, so `agreeOutsideMemory` fixes them, and
    `readByte_write_inside` then says the written bytes do not depend on the pre-image. -/
theorem PushR64.readsWithin (i : PushR64) : ReadsWithin i := by
  intro s1 s2 hout _
  obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.rsp,
        X86_64MachineState.setGpr64] <;>
      simp_all
  · intro a ha
    simp [X86_64Instruction.memAccesses, storeFootprint, footprintFor,
      MemAccessSpec.addresses, MemRef.effectiveAddress] at ha
    obtain ⟨k, hk, hak⟩ := ha
    subst hak
    have hbase : s1.gprs Reg64.rsp + (-8 : UInt64) = s1.gprs Reg64.rsp - 8 := by
      apply UInt64.toNat_inj.mp
      simp [UInt64.toNat_add, UInt64.toNat_sub, UInt64.size]
      omega
    rw [hbase]
    simp only [X86_64Instruction.step, X86_64MachineState.rsp, X86_64MachineState.setGpr64,
      X86_64MachineState.write64, X86_64Mem.read, hgprs]
    exact congrArg UInt8.toUInt64 (X86_64Mem.readByte_write_inside .w64 _ _ _ _ k hk)

end Gasm.Targets.X86_64.MemoryFrame
