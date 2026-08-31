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
import Gasm.Targets.X86_64.MemoryFrame.Mov
import Gasm.Targets.X86_64.MemoryRange
import Gasm.Targets.X86_64.Roundtrip
import Spikes.CheckedMemoryWindows.Authority

/-!
Load-bearing production, binding-liveness, and physical-mapping refinement for the selected
Windows x86 byte store.

The generic `BindingHistory` certificate is structural only. This module composes it with the
actual two-step production runner and the target-owned `ProcessExecution` projection. Ordinary
CPU steps preserve the host page table by definition, while the closed target event vocabulary
projects every rebind/invalidation/retirement separately. Only that operational composition may
construct `TypedStoreView` and `CheckedStore`; numeric RSP equality or total machine memory grants
no authority.
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

variable [selectedHost : HostSelection]

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
  targetStoreProjected : productionBindingExecution.events.getLast? =
    some (.cpuStep selected (afterAllocate state).rip (afterStore storedValue state).rip
      [⟨.store, .w8, ⟨some .rsp, none, signExtend8To64 byteOffset⟩⟩])
  descriptorExact :
    X86_64Instruction.memAccesses (mov_rsp_byte byteOffset storedValue) =
      [⟨.store, .w8, ⟨some .rsp, none, signExtend8To64 byteOffset⟩⟩]
  codecRoundtrip : Gasm.Targets.X86_64.Roundtrip.DecodesTo
    (mov_rsp_byte byteOffset storedValue)
  frameWrites : Gasm.Targets.X86_64.MemoryFrame.WritesWithin
    (MovRspDispByte.mk byteOffset storedValue)
  frameReads : Gasm.Targets.X86_64.MemoryFrame.ReadsWithin
    (MovRspDispByte.mk byteOffset storedValue)

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
  targetStoreProjected := rfl
  descriptorExact := rfl
  codecRoundtrip :=
    Gasm.Targets.X86_64.Roundtrip.roundtrip_mov_rsp_disp_byte byteOffset storedValue
  frameWrites := Gasm.Targets.X86_64.MemoryFrame.MovRspDispByte.writesWithin _
  frameReads := Gasm.Targets.X86_64.MemoryFrame.MovRspDispByte.readsWithin _

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Target refinement from structural history to a live/latest binding at the executed store.
    `targetProjectionComplete` closes the relevant production interval through the target-owned
    event projection; `historyHasNoTransition` is derived from that actual SUB/MOV trace. -/
structure LiveLatestStoreRefinement (selected : InvocationId)
    (state : X86_64MachineState) : Prop where
  private mk ::
  structural : StructuralStoreAuthority selected state
  production : ProductionStoreUse selected state
  targetProjectionComplete : (history state).transitions = projectedTransitionIds
  targetMachineExact : productionBindingExecution.machine = afterStore storedValue state
  targetHostExact : productionBindingExecution.host = processEntryLoad.afterHost
  targetBindingLive : productionBindingExecution.binding = some processEntryLoad.addressDomain
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
  targetProjectionComplete := rfl
  targetMachineExact := rfl
  targetHostExact := rfl
  targetBindingLive := rfl
  historyHasNoTransition := by simp [history]
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
    stackCommittedRange.Contains (byteRange entryState) := by
  change 0x7FFFFFFEF000 ≤ (entryState.rsp - 40 + 32).toNat ∧
    (entryState.rsp - 40 + 32).toNat + 1 ≤ 0x7FFFFFFEF000 + 0x2000
  decide

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
theorem selectedFrameWithinCommitted :
    stackCommittedRange.Contains (frameRange entryState) := by
  change 0x7FFFFFFEF000 ≤ (entryState.rsp - 40).toNat ∧
    (entryState.rsp - 40).toNat + 40 ≤ 0x7FFFFFFEF000 + 0x2000
  decide

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
theorem selectedMappedWritable :
    MappedWritable processEntryLoad processEntryLoad.afterHost (byteRange entryState) :=
  mappedWritable selectedHost.beforeHost executable (byteRange entryState)
    selectedByteWellFormed selectedByteWithinCommitted

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The one canonical descriptor consumed by the selected production store. -/
def selectedDescriptor : MemAccessSpec :=
  ⟨.store, .w8, ⟨some .rsp, none, signExtend8To64 byteOffset⟩⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Operationally generated association between the selected logical binding and the exact
    Windows address-domain mapping used by the production store. This is an indexed relation, not
    a caller-filled record of desired equalities: its only constructor consumes the already-proved
    live target execution and active mapping at the same use host, and its result indices are fixed
    by those operational witnesses. -/
inductive StoreBindingAssociation :
    WindowsHostState → BindingInstance → BindingGeneration → AddressDomainGeneration →
      PageMapping → AddressRange → AddressRange → Prop where
  | processEntry
      (live : LiveLatestStoreRefinement invocation entryState)
      (mapped : MappedWritable processEntryLoad processEntryLoad.afterHost
        (byteRange entryState)) :
      StoreBindingAssociation processEntryLoad.afterHost
        (entryBinding invocation) (entryGeneration invocation)
        processEntryLoad.addressDomain (committedEntry processEntryLoad)
        (byteRange entryState) (frameRange entryState)

namespace StoreBindingAssociation

theorem hostExact
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    current = processEntryLoad.afterHost := by
  cases association
  rfl

theorem bindingExact
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    binding = entryBinding invocation := by
  cases association
  rfl

theorem generationExact
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    generation = entryGeneration invocation := by
  cases association
  rfl

theorem generationDomainAgreement
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    generation.invocation = domain.invocation ∧
      domain.generation = generation.invocation.generation := by
  cases association
  exact ⟨rfl, rfl⟩

theorem domainExact
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    domain = processEntryLoad.addressDomain := by
  cases association
  rfl

theorem mappingExact
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    mapping = committedEntry processEntryLoad := by
  cases association
  rfl

theorem logicalExact
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    logical = byteRange entryState := by
  cases association
  rfl

theorem backingExact
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    backing = frameRange entryState := by
  cases association
  rfl

theorem mapped
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    MappedWritable processEntryLoad current logical := by
  cases association with
  | processEntry _ mapped => exact mapped

theorem bindingRecordExact
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    (history entryState).bindingRecord binding = some (entryBindingRecord entryState) := by
  cases association with
  | processEntry live _ => exact live.bindingRecordExact

theorem bindingLiveAtUse
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    productionBindingExecution.binding = some domain := by
  cases association with
  | processEntry live _ => exact live.targetBindingLive

theorem targetHostAtUse
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    productionBindingExecution.host = current := by
  cases association with
  | processEntry live _ => exact live.targetHostExact

theorem productionUse
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    ProductionStoreUse invocation entryState := by
  cases association with
  | processEntry live _ => exact live.production

theorem logicalWithinBinding
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    (entryBindingRecord entryState).logicalFootprint.Contains logical := by
  cases association with
  | processEntry live _ => exact live.logicalByteWithinBinding

theorem backingIdentity
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    (entryBindingRecord entryState).backingFootprint = backing := by
  cases association
  rfl

theorem backingWithinMapping
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    mapping.range.Contains backing := by
  cases association
  exact selectedFrameWithinCommitted

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- Target translation for the selected logical byte: the associated address domain translates
    its exact logical start to the exact physical store descriptor address. -/
theorem selectedAddressTranslated
    (association : StoreBindingAssociation current binding generation domain mapping logical backing) :
    domain.translate logical.start =
      (selectedDescriptor.addressRange (afterAllocate entryState)).start := by
  cases association
  rfl

end StoreBindingAssociation

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Physical realization of the same invocation, state, production descriptor, and one-byte
    range used by the logical refinement. `association` is the operational bridge: the physical
    mapping is no longer merely conjoined later with an unrelated logical view. -/
structure X86StoreRealization (selected : InvocationId)
    (state : X86_64MachineState) (currentHost : WindowsHostState) : Prop where
  private mk ::
  exactInvocation : selected = processEntryLoad.invocation
  exactLoadedState : state = processEntryLoad.machine
  association : StoreBindingAssociation currentHost
    (entryBinding selected) (entryGeneration selected) processEntryLoad.addressDomain
    (committedEntry processEntryLoad) (byteRange state) (frameRange state)
  descriptorExact : X86_64Instruction.memAccesses
    (mov_rsp_byte byteOffset storedValue) = [selectedDescriptor]
  descriptorRange : selectedDescriptor.addressRange (afterAllocate state) = byteRange state
  descriptorStore : selectedDescriptor.kind = .store
  naturallyAligned :
    (selectedDescriptor.addressRange (afterAllocate state)).start.toNat %
      selectedDescriptor.width.bytes = 0

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem storeRealization :
    X86StoreRealization invocation entryState processEntryLoad.afterHost where
  exactInvocation := rfl
  exactLoadedState := rfl
  association := .processEntry liveLatestStoreRefinement selectedMappedWritable
  descriptorExact := rfl
  descriptorRange := by rfl
  descriptorStore := by rfl
  naturallyAligned := by
    change _ % 1 = 0
    exact Nat.mod_one _

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
structure CheckedStore (selected : InvocationId) (state : X86_64MachineState)
    (currentHost : WindowsHostState) where
  private mk ::
  view : TypedStoreView selected state
  realization : X86StoreRealization selected state currentHost
  ordinary : X86_64Instr
  ordinary_eq : ordinary = mov_rsp_byte byteOffset storedValue

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def author (selected : InvocationId) (state : X86_64MachineState)
    (currentHost : WindowsHostState)
    (view : TypedStoreView selected state)
    (realization : X86StoreRealization selected state currentHost) :
    CheckedStore selected state currentHost :=
  .mk view realization (mov_rsp_byte byteOffset storedValue) rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def CheckedStore.erase {selected : InvocationId} {state : X86_64MachineState}
    {currentHost : WindowsHostState}
    (checked : CheckedStore selected state currentHost) : X86_64Instr :=
  checked.ordinary

@[simp] theorem CheckedStore.erase_eq {selected : InvocationId} {state : X86_64MachineState}
    {currentHost : WindowsHostState} (checked : CheckedStore selected state currentHost) :
    checked.erase = mov_rsp_byte byteOffset storedValue :=
  checked.ordinary_eq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def checkedStore : CheckedStore invocation entryState processEntryLoad.afterHost :=
  author invocation entryState processEntryLoad.afterHost typedStoreView storeRealization

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
