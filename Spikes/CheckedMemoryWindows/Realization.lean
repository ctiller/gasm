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

import Spikes.CheckedMemoryWindows.Authority

/-!
Windows-x64 physical realization and the provisional checked authoring wrapper for the selected
byte store. Logical ownership is supplied independently by `Authority.TypedStoreView`; this module
does not derive mappedness or writability from total `X86_64Memory`.

`EntryStackCommittedWritable` is the spike-local M2-B process-entry rule. It applies only to the
exact linked artifact/load state and its explicit 40-byte allocation, reflecting the selected
Windows loader/ABI stack premise. It is intentionally not a generic proposition over arbitrary
numeric RSP values or arbitrary executables.
-/

namespace Spikes.CheckedMemoryWindows.Realization

open Gasm.MemoryModel.Envelope
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.StackStorePrefix
open Gasm.Targets.X86_64.StackStorePrefixLink
open Spikes.CheckedMemoryWindows.Authority

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/- REF: windows-thread-stack-size -/
/- REF: windows-x64-stack-usage -/
/-- The selected loader rule's exact committed+writable stack region. This relation does not inspect
    or infer permission from the target's total byte-memory implementation. -/
def EntryStackCommittedWritable (state : X86_64MachineState) (region : Footprint) : Prop :=
  state = entryState ∧ region = frameFootprint entryState

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/- REF: windows-x64-calling-convention -/
/-- Exact, artifact-indexed M2-B stack grant used by this provisional profile. -/
structure WindowsEntryStackGrant (state : X86_64MachineState) : Prop where
  private mk ::
  exactLoadedArtifact : state = executable.load
  entryRsp : state.rsp = 0x7FFFFFFF0008
  committedWritable : EntryStackCommittedWritable state (frameFootprint state)
  liveAtCapture : (execution state).event .capture = some ⟨some .main,
    .captureBinding (afterAllocate state).rip (storeAddress state)⟩
  liveAtStore : (execution state).event .store = some ⟨some .main,
    .executeStore (afterAllocate state).rip (storeAddress state) storedValue⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
theorem entryStackGrant : WindowsEntryStackGrant entryState where
  exactLoadedArtifact := rfl
  entryRsp := rfl
  committedWritable := ⟨rfl, rfl⟩
  liveAtCapture := rfl
  liveAtStore := rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def continuation : List X86_64Instr :=
  [xor_r32 .ecx .ecx, call_rip 8199]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem instructions_prefix :
    instructions = StackStorePrefixLink.instructions storedValue ++ continuation := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The use occurrence is the actual second fetched instruction, and its step is exactly the
    state transition described by the selected envelope payload. -/
structure StoreOrigin (state : X86_64MachineState) : Prop where
  private mk ::
  exactArtifactState : state = entryState
  fetched : instructionAtRipIndexed (indexInstructions state.rip instructions)
    (afterAllocate state).rip = some (mov_rsp_byte byteOffset storedValue)
  stepped : X86_64Instruction.step (mov_rsp_byte byteOffset storedValue)
    (afterAllocate state) = afterStore storedValue state
  eventResolved : (execution state).event .store = some ⟨some .main,
    .executeStore (afterAllocate state).rip (storeAddress state) storedValue⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem storeOrigin : StoreOrigin entryState where
  exactArtifactState := rfl
  fetched := by
    rw [instructions_prefix]
    apply lookup_store_after_allocate_with_continuation
    decide
  stepped := rfl
  eventResolved := rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Independent target realization for the selected logical byte view. -/
structure X86StoreRealization (state : X86_64MachineState) : Prop where
  private mk ::
  grant : WindowsEntryStackGrant state
  origin : StoreOrigin state
  descriptorFootprint :
    storeFootprint
        (X86_64Instruction.memAccesses (mov_rsp_byte byteOffset storedValue))
        (afterAllocate state) = [storeAddress state]
  logicalByte : byteFootprint state = ⟨storeAddress state, 1⟩
  withinFrame :
    (afterAllocate state).rsp.toNat ≤ (storeAddress state).toNat ∧
      (storeAddress state).toNat + 1 ≤ state.rsp.toNat
  noWrap : (storeAddress state).toNat + 1 ≤ 2 ^ 64
  alignmentOne : (storeAddress state).toNat % 1 = 0

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem storeRealization : X86StoreRealization entryState where
  grant := entryStackGrant
  origin := storeOrigin
  descriptorFootprint := by
    change storeFootprint
        (X86_64Instruction.memAccesses (MovRspDispByte.mk byteOffset storedValue))
        (afterAllocate entryState) = [storeAddress entryState]
    rw [selected_storeFootprint]
    rfl
  logicalByte := rfl
  withinFrame := by
    change (afterAllocate entryState).rsp.toNat ≤
        (entryState.rsp - 40 + 32).toNat ∧
      (entryState.rsp - 40 + 32).toNat + 1 ≤ entryState.rsp.toNat
    exact selected_byte_within_frame entryState (by decide)
  noWrap := by
    change (entryState.rsp - 40 + 32).toNat + 1 ≤ 2 ^ 64
    exact selected_byte_noWrap entryState
  alignmentOne := by omega

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Proof-bearing authoring result. Its constructor is private: callers use `author`, which requires
    the exact logical view and independent physical realization. -/
structure CheckedStore (state : X86_64MachineState) where
  private mk ::
  view : TypedStoreView state
  realization : X86StoreRealization state
  ordinary : X86_64Instr
  ordinary_eq : ordinary = mov_rsp_byte byteOffset storedValue

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def author (state : X86_64MachineState) (view : TypedStoreView state)
    (realization : X86StoreRealization state) : CheckedStore state :=
  .mk view realization (mov_rsp_byte byteOffset storedValue) rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Proof erasure returns the ordinary registered instruction consumed by encoding and decoding. -/
def CheckedStore.erase {state : X86_64MachineState} (checked : CheckedStore state) :
    X86_64Instr := checked.ordinary

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
@[simp] theorem CheckedStore.erase_eq {state : X86_64MachineState}
    (checked : CheckedStore state) :
    checked.erase = mov_rsp_byte byteOffset storedValue :=
  checked.ordinary_eq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def checkedStore : CheckedStore entryState :=
  author entryState typedStoreView storeRealization

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The emitted artifact's selected second instruction is the erasure of the proof-bearing
    authoring result, not a detached ordinary surrogate. -/
theorem instructions_authored :
    instructions =
      [sub_rsp frameSize, checkedStore.erase,
        xor_r32 .ecx .ecx, call_rip 8199] := by
  rw [CheckedStore.erase_eq]
  exact instructions_shape

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem checkedStore_encoding :
    X86_64Instruction.encode checkedStore.erase =
      X86_64Instruction.encode (mov_rsp_byte byteOffset storedValue) := by
  rw [CheckedStore.erase_eq]

end Spikes.CheckedMemoryWindows.Realization
