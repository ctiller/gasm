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
import Gasm.Targets.X86_64.Instructions.Mov

namespace Gasm.Targets.X86_64.MemoryFrame

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovMem8Reg8.writesWithin (i : MovMem8Reg8) : WritesWithin i := by
  intro s a ha
  simp [X86_64Instruction.memAccesses, storeFootprint, footprintFor,
    MemAccessSpec.addresses, MemRef.effectiveAddress] at ha
  have h0 : s.gprs i.dstPtr ≠ a := by simpa using ha 0 (by decide)
  show X86_64Mem.read .w8 a (X86_64Instruction.step i s).memory = X86_64Mem.read .w8 a s.memory
  simp only [X86_64Instruction.step, X86_64Mem.read, X86_64Mem.readByte, X86_64Mem.write,
    X86_64Mem.writeByte]
  simp [Ne.symm h0]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovMem8Reg8.readsWithin (i : MovMem8Reg8) : ReadsWithin i := by
  intro s1 s2 hout _
  obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [X86_64Instruction.step] <;>
    simp_all

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovzxR64Mem8.writesWithin (i : MovzxR64Mem8) : WritesWithin i := by
  intro s a _
  show X86_64Mem.read .w8 a (X86_64Instruction.step i s).memory = X86_64Mem.read .w8 a s.memory
  simp only [X86_64Instruction.step, X86_64MachineState.setGpr64]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovzxR64Mem8.readsWithin (i : MovzxR64Mem8) : ReadsWithin i := by
  intro s1 s2 hout hagree
  obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
  simp [X86_64Instruction.memAccesses, loadFootprint, footprintFor,
    MemAccessSpec.addresses, MemRef.effectiveAddress, agreeOn] at hagree
  have h0 := hagree 0 (by decide)
  have hbase : s1.gprs i.basePtr + signExtend8To64 i.disp = s2.gprs i.basePtr + signExtend8To64 i.disp := by
    rw [hgprs]
  rw [hbase] at h0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64, X86_64MachineState.read8] <;>
    simp_all

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovRspDispByte.writesWithin (i : MovRspDispByte) : WritesWithin i := by
  intro s a ha
  simp [X86_64Instruction.memAccesses, storeFootprint, footprintFor,
    MemAccessSpec.addresses, MemRef.effectiveAddress] at ha
  have h0 : s.gprs Reg64.rsp + signExtend8To64 i.disp ≠ a := by simpa using ha 0 (by decide)
  show X86_64Mem.read .w8 a (X86_64Instruction.step i s).memory = X86_64Mem.read .w8 a s.memory
  simp only [X86_64Instruction.step, X86_64Mem.read, X86_64Mem.readByte, X86_64Mem.write,
    X86_64Mem.writeByte, X86_64MachineState.rsp]
  simp [Ne.symm h0]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovRspDispByte.readsWithin (i : MovRspDispByte) : ReadsWithin i := by
  intro s1 s2 hout _
  obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [X86_64Instruction.step, X86_64MachineState.rsp] <;>
    simp_all

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovRspDispImm32.writesWithin (i : MovRspDispImm32) : WritesWithin i := by
  intro s a ha
  simp [X86_64Instruction.memAccesses, storeFootprint, footprintFor,
    MemAccessSpec.addresses, MemRef.effectiveAddress] at ha
  have h0 : s.gprs Reg64.rsp + signExtend8To64 i.disp ≠ a := by simpa using ha 0 (by decide)
  have h1 : s.gprs Reg64.rsp + signExtend8To64 i.disp + 1 ≠ a := by simpa using ha 1 (by decide)
  have h2 : s.gprs Reg64.rsp + signExtend8To64 i.disp + 2 ≠ a := by simpa using ha 2 (by decide)
  have h3 : s.gprs Reg64.rsp + signExtend8To64 i.disp + 3 ≠ a := by simpa using ha 3 (by decide)
  show X86_64Mem.read .w8 a (X86_64Instruction.step i s).memory = X86_64Mem.read .w8 a s.memory
  simp only [X86_64Instruction.step, X86_64Mem.read, X86_64Mem.readByte,
    X86_64MachineState.rsp, X86_64MachineState.write32, X86_64Mem.write, beq_self_eq_true,
    if_true]
  simp [Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovRspDispImm32.readsWithin (i : MovRspDispImm32) : ReadsWithin i := by
  intro s1 s2 hout _
  obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [X86_64Instruction.step, X86_64MachineState.rsp] <;>
    simp_all

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovReg32RspDisp32.writesWithin (i : MovReg32RspDisp32) : WritesWithin i := by
  intro s a _
  show X86_64Mem.read .w8 a (X86_64Instruction.step i s).memory = X86_64Mem.read .w8 a s.memory
  simp only [X86_64Instruction.step, X86_64MachineState.setGpr32]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovReg32RspDisp32.readsWithin (i : MovReg32RspDisp32) : ReadsWithin i := by
  intro s1 s2 hout hagree
  obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
  simp [X86_64Instruction.memAccesses, loadFootprint, footprintFor,
    MemAccessSpec.addresses, MemRef.effectiveAddress, agreeOn] at hagree
  have hbase : s1.gprs Reg64.rsp + signExtend8To64 i.disp = s2.gprs Reg64.rsp + signExtend8To64 i.disp := by
    rw [hgprs]
  rw [hbase] at hagree
  have hread : X86_64Mem.read .w32 (s2.gprs Reg64.rsp + signExtend8To64 i.disp) s1.memory =
      X86_64Mem.read .w32 (s2.gprs Reg64.rsp + signExtend8To64 i.disp) s2.memory :=
    X86_64Mem.read_congr' .w32 _ s1.memory s2.memory hagree
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [X86_64Instruction.step, X86_64MachineState.rsp, X86_64MachineState.setGpr32,
      X86_64MachineState.read32] <;>
    simp_all

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- Uses the same `write64` call `MovRspDispImm64`'s `step` was migrated onto (its own comment
    explains the byte-for-byte equivalence with the pre-hook inline sign-extension ladder), so
    this proof is identical in shape to `MovMem64DispReg64`'s below rather than needing the old
    4-plus-uniform-extension-byte case split. -/
theorem MovRspDispImm64.writesWithin (i : MovRspDispImm64) : WritesWithin i := by
  intro s a ha
  simp [X86_64Instruction.memAccesses, storeFootprint, footprintFor,
    MemAccessSpec.addresses, MemRef.effectiveAddress] at ha
  have h0 : s.gprs Reg64.rsp + signExtend8To64 i.disp ≠ a := by simpa using ha 0 (by decide)
  have h1 : s.gprs Reg64.rsp + signExtend8To64 i.disp + 1 ≠ a := by simpa using ha 1 (by decide)
  have h2 : s.gprs Reg64.rsp + signExtend8To64 i.disp + 2 ≠ a := by simpa using ha 2 (by decide)
  have h3 : s.gprs Reg64.rsp + signExtend8To64 i.disp + 3 ≠ a := by simpa using ha 3 (by decide)
  have h4 : s.gprs Reg64.rsp + signExtend8To64 i.disp + 4 ≠ a := by simpa using ha 4 (by decide)
  have h5 : s.gprs Reg64.rsp + signExtend8To64 i.disp + 5 ≠ a := by simpa using ha 5 (by decide)
  have h6 : s.gprs Reg64.rsp + signExtend8To64 i.disp + 6 ≠ a := by simpa using ha 6 (by decide)
  have h7 : s.gprs Reg64.rsp + signExtend8To64 i.disp + 7 ≠ a := by simpa using ha 7 (by decide)
  show X86_64Mem.read .w8 a (X86_64Instruction.step i s).memory = X86_64Mem.read .w8 a s.memory
  simp only [X86_64Instruction.step, X86_64Mem.read, X86_64Mem.readByte,
    X86_64MachineState.rsp, X86_64MachineState.write64, X86_64Mem.write, beq_self_eq_true,
    if_true]
  simp [Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6,
    Ne.symm h7]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovRspDispImm64.readsWithin (i : MovRspDispImm64) : ReadsWithin i := by
  intro s1 s2 hout _
  obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [X86_64Instruction.step, X86_64MachineState.rsp] <;>
    simp_all

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovMem64DispReg64.writesWithin (i : MovMem64DispReg64) : WritesWithin i := by
  intro s a ha
  simp [X86_64Instruction.memAccesses, storeFootprint, footprintFor,
    MemAccessSpec.addresses, MemRef.effectiveAddress] at ha
  have h0 : s.gprs i.basePtr + signExtend8To64 i.disp ≠ a := by simpa using ha 0 (by decide)
  have h1 : s.gprs i.basePtr + signExtend8To64 i.disp + 1 ≠ a := by simpa using ha 1 (by decide)
  have h2 : s.gprs i.basePtr + signExtend8To64 i.disp + 2 ≠ a := by simpa using ha 2 (by decide)
  have h3 : s.gprs i.basePtr + signExtend8To64 i.disp + 3 ≠ a := by simpa using ha 3 (by decide)
  have h4 : s.gprs i.basePtr + signExtend8To64 i.disp + 4 ≠ a := by simpa using ha 4 (by decide)
  have h5 : s.gprs i.basePtr + signExtend8To64 i.disp + 5 ≠ a := by simpa using ha 5 (by decide)
  have h6 : s.gprs i.basePtr + signExtend8To64 i.disp + 6 ≠ a := by simpa using ha 6 (by decide)
  have h7 : s.gprs i.basePtr + signExtend8To64 i.disp + 7 ≠ a := by simpa using ha 7 (by decide)
  show X86_64Mem.read .w8 a (X86_64Instruction.step i s).memory = X86_64Mem.read .w8 a s.memory
  simp only [X86_64Instruction.step, X86_64Mem.read, X86_64Mem.readByte,
    X86_64MachineState.write64, X86_64Mem.write, beq_self_eq_true, if_true]
  simp [Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6,
    Ne.symm h7]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovMem64DispReg64.readsWithin (i : MovMem64DispReg64) : ReadsWithin i := by
  intro s1 s2 hout _
  obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [X86_64Instruction.step] <;>
    simp_all

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovMem64DispImm32.writesWithin (i : MovMem64DispImm32) : WritesWithin i := by
  intro s a ha
  simp [X86_64Instruction.memAccesses, storeFootprint, footprintFor,
    MemAccessSpec.addresses, MemRef.effectiveAddress] at ha
  have h0 : s.gprs i.basePtr + signExtend8To64 i.disp ≠ a := by simpa using ha 0 (by decide)
  have h1 : s.gprs i.basePtr + signExtend8To64 i.disp + 1 ≠ a := by simpa using ha 1 (by decide)
  have h2 : s.gprs i.basePtr + signExtend8To64 i.disp + 2 ≠ a := by simpa using ha 2 (by decide)
  have h3 : s.gprs i.basePtr + signExtend8To64 i.disp + 3 ≠ a := by simpa using ha 3 (by decide)
  have h4 : s.gprs i.basePtr + signExtend8To64 i.disp + 4 ≠ a := by simpa using ha 4 (by decide)
  have h5 : s.gprs i.basePtr + signExtend8To64 i.disp + 5 ≠ a := by simpa using ha 5 (by decide)
  have h6 : s.gprs i.basePtr + signExtend8To64 i.disp + 6 ≠ a := by simpa using ha 6 (by decide)
  have h7 : s.gprs i.basePtr + signExtend8To64 i.disp + 7 ≠ a := by simpa using ha 7 (by decide)
  show X86_64Mem.read .w8 a (X86_64Instruction.step i s).memory = X86_64Mem.read .w8 a s.memory
  simp only [X86_64Instruction.step, X86_64Mem.read, X86_64Mem.readByte,
    X86_64MachineState.write64, X86_64Mem.write, beq_self_eq_true, if_true]
  simp [Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6,
    Ne.symm h7]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovMem64DispImm32.readsWithin (i : MovMem64DispImm32) : ReadsWithin i := by
  intro s1 s2 hout _
  obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [X86_64Instruction.step] <;>
    simp_all

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovReg64Mem64Disp.writesWithin (i : MovReg64Mem64Disp) : WritesWithin i := by
  intro s a _
  show X86_64Mem.read .w8 a (X86_64Instruction.step i s).memory = X86_64Mem.read .w8 a s.memory
  simp only [X86_64Instruction.step, X86_64MachineState.setGpr64]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovReg64Mem64Disp.readsWithin (i : MovReg64Mem64Disp) : ReadsWithin i := by
  intro s1 s2 hout hagree
  obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
  simp [X86_64Instruction.memAccesses, loadFootprint, footprintFor,
    MemAccessSpec.addresses, MemRef.effectiveAddress, agreeOn] at hagree
  have hbase : s1.gprs i.basePtr + signExtend8To64 i.disp = s2.gprs i.basePtr + signExtend8To64 i.disp := by
    rw [hgprs]
  rw [hbase] at hagree
  have hread : X86_64Mem.read .w64 (s2.gprs i.basePtr + signExtend8To64 i.disp) s1.memory =
      X86_64Mem.read .w64 (s2.gprs i.basePtr + signExtend8To64 i.disp) s2.memory :=
    X86_64Mem.read_congr' .w64 _ s1.memory s2.memory hagree
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64, X86_64MachineState.read64] <;>
    simp_all

-- MovR32Imm32/MovR64Imm64/MovR64R64 are register-only (`memAccesses _ := []`): unlike the 9
-- memory forms above, these instantiate the shared batch lemma
-- (`registerOnly_writesWithin`/`registerOnly_readsWithin`, MemoryFrame/Common.lean) instead of
-- re-deriving a bespoke connection proof, since their `step` never reads or writes `.memory` --
-- see MemoryFrame/Add.lean's header comment for the batch-lemma-instantiation rationale (identical
-- here). They live in this file (rather than a separate shard) because they're MOV variants, and
-- Instructions/Mov.lean already mixes them with the 9 memory forms.

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovR32Imm32.writesWithin (i : MovR32Imm32) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr32] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovR32Imm32.readsWithin (i : MovR32Imm32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr32, hrip, hgprs, hflags, hstdin,
        hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovR64Imm64.writesWithin (i : MovR64Imm64) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovR64Imm64.readsWithin (i : MovR64Imm64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64, hrip, hgprs, hflags, hstdin,
        hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovR64R64.writesWithin (i : MovR64R64) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MovR64R64.readsWithin (i : MovR64R64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64, hrip, hgprs, hflags, hstdin,
        hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

end Gasm.Targets.X86_64.MemoryFrame
