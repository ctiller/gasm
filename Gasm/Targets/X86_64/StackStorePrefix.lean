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
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.MemoryFrame.Mov

/-!
# Production stack-allocation/store prefix facts

This module isolates the authority-independent operational prefix selected by the M1 checked
authoring demonstration: the real production instructions `sub rsp, 40` and
`mov byte [rsp + 32], value`.  It connects their exact post-allocation address, descriptor
footprint, and memory image without inventing logical ownership or treating total machine memory
as mapped and writable.

These facts grant no stack allocation, physical accessibility, binding/view validity, obligation
ownership, dynamic-event origin, platform admission, or `VerifiedProgram` authority.  The future
Windows M2-B profile and canonical obligation world must supply those premises when this prefix is
composed into the required production demonstration.
-/

namespace Gasm.Targets.X86_64.StackStorePrefix

open Gasm.Core
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MemoryFrame

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The Windows call-frame-sized allocation selected by the checked-store demonstration. -/
def frameSize : UInt8 := 40

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The selected byte lies at the first byte beyond the 32-byte Windows parameter area. -/
def byteOffset : UInt8 := 32

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- State after executing the actual production `sub rsp, 40` instruction. -/
def afterAllocate (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (SubRspImm8.mk frameSize) state

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- State after the actual production allocation and selected byte store. -/
def afterStore (value : UInt8) (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (MovRspDispByte.mk byteOffset value) (afterAllocate state)

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The typed allocation step above is definitionally the step selected by the production
existential instruction constructor. -/
theorem afterAllocate_eq_production (state : X86_64MachineState) :
    afterAllocate state = X86_64Instruction.step (sub_rsp frameSize) state := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The typed two-step prefix is definitionally the same prefix selected by the production
existential instruction constructors. -/
theorem afterStore_eq_production (value : UInt8) (state : X86_64MachineState) :
    afterStore value state =
      X86_64Instruction.step (mov_rsp_byte byteOffset value)
        (X86_64Instruction.step (sub_rsp frameSize) state) := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The selected positive displacement has the same 64-bit value after sign extension. -/
@[simp] theorem signExtend_byteOffset : signExtend8To64 byteOffset = 32 := by
  decide

private theorem signExtend_32 : signExtend8To64 32 = 32 := by
  decide

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The production allocation changes RSP by exactly 40 bytes. -/
@[simp] theorem afterAllocate_rsp (state : X86_64MachineState) :
    (afterAllocate state).rsp = state.rsp - 40 := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The production allocation does not itself touch memory. -/
@[simp] theorem afterAllocate_memory (state : X86_64MachineState) :
    (afterAllocate state).memory = state.memory := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The production allocation advances RIP by its exact four-byte encoding. -/
@[simp] theorem afterAllocate_rip (state : X86_64MachineState) :
    (afterAllocate state).rip = state.rip + 4 := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The selected store preserves the post-allocation stack pointer. -/
@[simp] theorem afterStore_rsp (value : UInt8) (state : X86_64MachineState) :
    (afterStore value state).rsp = state.rsp - 40 := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The prefix reaches the exact fallthrough address after its four- and five-byte encodings. -/
@[simp] theorem afterStore_rip (value : UInt8) (state : X86_64MachineState) :
    (afterStore value state).rip = state.rip + 4 + 5 := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Neither selected instruction manufactures a machine fault. -/
@[simp] theorem afterStore_fault (value : UInt8) (state : X86_64MachineState) :
    (afterStore value state).fault = state.fault := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The selected store's declared footprint is the exact post-allocation stack byte. -/
@[simp] theorem selected_storeFootprint (value : UInt8) (state : X86_64MachineState) :
    storeFootprint
        (X86_64Instruction.memAccesses (MovRspDispByte.mk byteOffset value))
        (afterAllocate state) =
      [state.rsp - 40 + 32] := by
  rw [MovRspDispByte.storeFootprint_eq, afterAllocate_rsp]
  simp [byteOffset, signExtend_32]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The two-instruction production prefix has exactly one memory effect: the selected byte write
at the post-allocation descriptor address. -/
@[simp] theorem afterStore_memory (value : UInt8) (state : X86_64MachineState) :
    (afterStore value state).memory =
      X86_64Mem.write .w8 (state.rsp - 40 + 32) value.toUInt64 state.memory := by
  unfold afterStore
  rw [MovRspDispByte.step_memory_eq, afterAllocate_rsp, afterAllocate_memory]
  simp [byteOffset, signExtend_32]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Reading the selected byte after the production prefix returns the authored immediate. -/
@[simp] theorem afterStore_value (value : UInt8) (state : X86_64MachineState) :
    X86_64Mem.read .w8 (state.rsp - 40 + 32) (afterStore value state).memory =
      value.toUInt64 := by
  rw [afterStore_memory]
  simp [X86_64Mem.read, X86_64Mem.write]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- Under the explicit no-underflow premise required from the future Windows entry grant, the
selected one-byte range is contained in the 40-byte frame `[entryRsp - 40, entryRsp)`. -/
theorem selected_byte_within_frame (state : X86_64MachineState)
    (entryEnough : 40 ≤ state.rsp.toNat) :
    (afterAllocate state).rsp.toNat ≤ (state.rsp - 40 + 32).toNat ∧
      (state.rsp - 40 + 32).toNat + 1 ≤ state.rsp.toNat := by
  have h40 : (40 : UInt64) ≤ state.rsp := by
    apply UInt64.le_iff_toNat_le.mpr
    change 40 ≤ state.rsp.toNat
    exact entryEnough
  rw [afterAllocate_rsp, UInt64.toNat_sub_of_le state.rsp 40 h40,
    UInt64.toNat_add, UInt64.toNat_sub_of_le state.rsp 40 h40]
  change state.rsp.toNat - 40 ≤ (state.rsp.toNat - 40 + 32) % 2 ^ 64 ∧
    (state.rsp.toNat - 40 + 32) % 2 ^ 64 + 1 ≤ state.rsp.toNat
  have sumLt : state.rsp.toNat - 40 + 32 < 2 ^ 64 := by
    have rspLt := state.rsp.toNat_lt
    omega
  rw [Nat.mod_eq_of_lt sumLt]
  omega

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- The mathematical exclusive end of any selected one-byte range stays within the 64-bit address
space; the separate containment theorem rules out stack-allocation underflow. -/
theorem selected_byte_noWrap (state : X86_64MachineState) :
    (state.rsp - 40 + 32).toNat + 1 ≤ 2 ^ 64 := by
  exact Nat.succ_le_of_lt (state.rsp - 40 + 32).toNat_lt

end Gasm.Targets.X86_64.StackStorePrefix
