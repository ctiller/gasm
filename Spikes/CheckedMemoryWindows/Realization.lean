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

import Gasm.Core.Verification
import Gasm.Effects.Trace
import Gasm.Targets.X86_64.MemoryRange
import Spikes.CheckedMemoryWindows.Authority

/-!
Load-bearing production, binding-liveness, and physical-mapping refinement for the selected
Windows x86 byte store.

The generic `BindingHistory` certificate is structural only. This module composes it with the
actual two-step production-runner prefix, a closed target classification saying that the selected
`SUB` and `MOV` steps preserve the invocation's stack binding, and the target-owned Windows loader
grant for the exact descriptor range. Only that composition may construct `TypedStoreView` and
`CheckedStore`; numeric RSP equality or total machine memory grants no authority.
-/

namespace Spikes.CheckedMemoryWindows.Realization

open Gasm.Core.Verification
open Gasm.Effects
open Gasm.MemoryModel
open Gasm.MemoryModel.AddressRange
open Gasm.MemoryModel.BindingHistory
open Gasm.Targets.Windows
open Gasm.Targets.Windows.ProcessEntryMemory
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Gasm.Targets.X86_64.StackStorePrefix
open Gasm.Targets.X86_64.StackStorePrefixExecution
open Gasm.Targets.X86_64.StackStorePrefixLink
open Spikes.CheckedMemoryWindows.Authority

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
abbrev Event := AnyEvent

local instance : ExternalCallInterceptor X86_64 Event :=
  standardWindowsRuntime Event

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def continuation : List X86_64Instr :=
  [xor_r32 .ecx .ecx, call_rip 8199]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem instructions_prefix :
    instructions = StackStorePrefixLink.instructions storedValue ++ continuation := by
  rfl

private theorem allocateSilent :
    win32Intercept (Event := Event) (afterAllocate entryState).rip
      (afterAllocate entryState) = none := by
  decide

private theorem storeSilent :
    win32Intercept (Event := Event) (afterStore storedValue entryState).rip
      (afterStore storedValue entryState) = none := by
  decide

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The exact production runner prefix for the emitted artifact, not a detached surrogate. -/
theorem productionStorePrefix :
    ProductionPrefix (Event := Event)
      (indexInstructions entryState.rip instructions) 2 entryState []
      (afterStore storedValue entryState) [] [] := by
  rw [instructions_prefix]
  exact productionPrefixWithContinuation (Event := Event) entryState [] storedValue continuation
    (by decide) rfl allocateSilent storeSilent

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Closed target classification of the only two instructions before the selected use. These
    constructors mean that the instruction changes machine registers/bytes but performs no
    loader, unmap, free, binding-generation, or view-invalidation transition. -/
inductive PreservesEntryStackBinding : X86_64Instr → Prop where
  | allocate : PreservesEntryStackBinding (sub_rsp frameSize)
  | store : PreservesEntryStackBinding (mov_rsp_byte byteOffset storedValue)

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The classification is exhaustive for the actual fetched prefix. -/
theorem productionPrefix_preserves_binding (instruction : X86_64Instr)
    (member : instruction ∈ instructions.take 2) :
    PreservesEntryStackBinding instruction := by
  rw [instructions_shape] at member
  simp only [List.take, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .allocate
  · exact .store

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Fidelity of the structural use occurrence to the actual production prefix and descriptor.
    Its private constructor prevents a caller from declaring an arbitrary history use to be an
    executed x86 access. -/
structure ProductionStoreUse (selected : InvocationId)
    (state : X86_64MachineState) : Prop where
  private mk ::
  exactInvocation : selected = invocation
  exactState : state = entryState
  productionPrefix : ProductionPrefix (Event := Event)
    (indexInstructions state.rip instructions) 2 state []
    (afterStore storedValue state) [] []
  fetched : instructionAtRipIndexed (indexInstructions state.rip instructions)
    (afterAllocate state).rip = some (mov_rsp_byte byteOffset storedValue)
  stepped : X86_64Instruction.step (mov_rsp_byte byteOffset storedValue)
    (afterAllocate state) = afterStore storedValue state
  eventResolved : (execution state).event .store = some ⟨some .main,
    .executeStore selected (afterAllocate state).rip (storeAddress state) storedValue⟩
  descriptorExact :
    X86_64Instruction.memAccesses (mov_rsp_byte byteOffset storedValue) =
      [⟨.store, .w8, ⟨some .rsp, none, signExtend8To64 byteOffset⟩⟩]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem productionStoreUse : ProductionStoreUse invocation entryState where
  exactInvocation := rfl
  exactState := rfl
  productionPrefix := productionStorePrefix
  fetched := by
    rw [instructions_prefix]
    apply lookup_store_after_allocate_with_continuation
    decide
  stepped := rfl
  eventResolved := rfl
  descriptorExact := rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Target refinement from structural history to a live/latest binding at the executed store.
    `prefixTransitionsComplete` closes the relevant production interval: every actually fetched
    instruction before and including the use is classified above, while `historyHasNoTransition`
    states that the structural projection contains no invented rebind or invalidation. -/
structure LiveLatestStoreRefinement (selected : InvocationId)
    (state : X86_64MachineState) : Prop where
  private mk ::
  structural : StructuralStoreAuthority selected state
  production : ProductionStoreUse selected state
  prefixTransitionsComplete : ∀ instruction, instruction ∈ instructions.take 2 →
    PreservesEntryStackBinding instruction
  historyHasNoTransition : (history state).transitions = []
  rootLatestAtCapture : (history state).FrontierResolves
    (.root (entryRoot selected)) .stack (some (entryBinding selected))
  capturedBinding : (history state).Captures
    (storeCapture selected) (entryBinding selected)
  usedBinding : (history state).Uses (storeUse selected) (entryBinding selected)
  bindingRecordExact : (history state).bindingRecord (entryBinding selected) =
    some (entryBindingRecord state)
  exclusiveWrite : (entryBindingRecord state).rights = .exclusiveWrite
  logicalByteWithinBinding : (entryBindingRecord state).logicalFootprint.Contains (byteRange state)

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem liveLatestStoreRefinement : LiveLatestStoreRefinement invocation entryState where
  structural := structuralStoreAuthority
  production := productionStoreUse
  prefixTransitionsComplete := productionPrefix_preserves_binding
  historyHasNoTransition := rfl
  rootLatestAtCapture :=
    ⟨entryRootRecord, history_rootRecord_entry entryState, rfl, rfl⟩
  capturedBinding := structuralStoreAuthority.captureResolves
  usedBinding := structuralStoreAuthority.useResolves
  bindingRecordExact := history_bindingRecord_entry entryState
  exclusiveWrite := rfl
  logicalByteWithinBinding := by
    change (frameRange entryState).Contains (byteRange entryState)
    change (entryState.rsp - 40).toNat ≤ (entryState.rsp - 40 + 32).toNat ∧
      (entryState.rsp - 40 + 32).toNat + 1 ≤
        (entryState.rsp - 40).toNat + 40
    decide

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
theorem selectedByteWellFormed : (byteRange entryState).WellFormed := by
  constructor
  · decide
  · exact selected_byte_noWrap entryState

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
theorem selectedByteWithinCommitted :
    processEntryLoad.stack.committedRange.Contains (byteRange entryState) := by
  rw [processEntryLoad.stackExact]
  change 0x7FFFFFFEF000 ≤ (entryState.rsp - 40 + 32).toNat ∧
    (entryState.rsp - 40 + 32).toNat + 1 ≤ 0x7FFFFFFEF000 + 0x2000
  decide

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
theorem selectedMappedWritable : MappedWritable processEntryLoad (byteRange entryState) :=
  mappedWritable processEntryLoad (byteRange entryState)
    selectedByteWellFormed selectedByteWithinCommitted

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The one canonical descriptor consumed by the selected production store. -/
def selectedDescriptor : MemAccessSpec :=
  ⟨.store, .w8, ⟨some .rsp, none, signExtend8To64 byteOffset⟩⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Independent physical realization of the same invocation, state, production descriptor, and
    one-byte range used by the logical refinement. -/
structure X86StoreRealization (selected : InvocationId)
    (state : X86_64MachineState) : Prop where
  private mk ::
  exactInvocation : selected = processEntryLoad.invocation
  exactLoadedState : state = processEntryLoad.machine
  mapped : MappedWritable processEntryLoad (byteRange state)
  descriptorExact : X86_64Instruction.memAccesses
    (mov_rsp_byte byteOffset storedValue) = [selectedDescriptor]
  descriptorRange : selectedDescriptor.addressRange (afterAllocate state) = byteRange state
  descriptorStore : selectedDescriptor.kind = .store
  backingTranslation : ∀ address, (byteRange state).ContainsAddress address →
    processEntryLoad.stack.translate address = address

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem storeRealization : X86StoreRealization invocation entryState where
  exactInvocation := rfl
  exactLoadedState := rfl
  mapped := selectedMappedWritable
  descriptorExact := rfl
  descriptorRange := by rfl
  descriptorStore := by rfl
  backingTranslation := selectedMappedWritable.backingTranslation

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The logical view is constructible only from the structural certificate plus its production
    live/latest refinement. -/
structure TypedStoreView (selected : InvocationId) (state : X86_64MachineState) : Prop where
  private mk ::
  refinement : LiveLatestStoreRefinement selected state

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem typedStoreView : TypedStoreView invocation entryState :=
  ⟨liveLatestStoreRefinement⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Proof-bearing instruction authoring. Both logical and physical legs share the exact
    invocation and state indices, and the private constructor prevents bypass authoring. -/
structure CheckedStore (selected : InvocationId) (state : X86_64MachineState) where
  private mk ::
  view : TypedStoreView selected state
  realization : X86StoreRealization selected state
  ordinary : X86_64Instr
  ordinary_eq : ordinary = mov_rsp_byte byteOffset storedValue

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def author (selected : InvocationId) (state : X86_64MachineState)
    (view : TypedStoreView selected state)
    (realization : X86StoreRealization selected state) : CheckedStore selected state :=
  .mk view realization (mov_rsp_byte byteOffset storedValue) rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def CheckedStore.erase {selected : InvocationId} {state : X86_64MachineState}
    (checked : CheckedStore selected state) : X86_64Instr :=
  checked.ordinary

@[simp] theorem CheckedStore.erase_eq {selected : InvocationId} {state : X86_64MachineState}
    (checked : CheckedStore selected state) :
    checked.erase = mov_rsp_byte byteOffset storedValue :=
  checked.ordinary_eq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def checkedStore : CheckedStore invocation entryState :=
  author invocation entryState typedStoreView storeRealization

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem instructions_authored :
    instructions = [sub_rsp frameSize, checkedStore.erase,
      xor_r32 .ecx .ecx, call_rip 8199] := by
  rw [CheckedStore.erase_eq]
  exact instructions_shape

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem checkedStore_encoding :
    X86_64Instruction.encode checkedStore.erase =
      X86_64Instruction.encode (mov_rsp_byte byteOffset storedValue) := by
  rw [CheckedStore.erase_eq]

end Spikes.CheckedMemoryWindows.Realization
