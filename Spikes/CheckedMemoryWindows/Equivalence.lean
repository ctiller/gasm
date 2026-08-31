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
import Spikes.CheckedMemoryWindows.Realization

/-!
Whole-program authority for the checked-memory demonstration. The production Windows runner
executes the instruction erased from `CheckedStore`, reaches the real `ExitProcess` provider, and
the same proof constructs the sole `VerifiedProgram.compose` value. The CALL's implicit stack
write and IAT read remain ordinary, explicitly unselected effects in this first profile.
-/

namespace Spikes.CheckedMemoryWindows

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.MemoryModel.ObligationWorld
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Gasm.Targets.X86_64.StackStorePrefix
open Gasm.Targets.X86_64.StackStorePrefixExecution
open Gasm.Targets.Windows
open Spikes.CheckedMemoryWindows.Authority
open Spikes.CheckedMemoryWindows.Realization

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
abbrev Event := AnyEvent

local instance : ExternalCallInterceptor X86_64 Event :=
  standardWindowsRuntime Event

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def indexed : List (UInt64 × X86_64Instr) :=
  indexInstructions entryState.rip instructions

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private theorem allocateSilent :
    win32Intercept (Event := Event) (afterAllocate entryState).rip
      (afterAllocate entryState) = none := by
  decide

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private theorem storeSilent :
    win32Intercept (Event := Event) (afterStore storedValue entryState).rip
      (afterStore storedValue entryState) = none := by
  decide

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private def afterXor : X86_64MachineState :=
  X86_64Instruction.step (xor_r32 .ecx .ecx) (afterStore storedValue entryState)

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private theorem afterXor_fault : afterXor.fault = none := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private theorem afterXor_rcx : afterXor.gprs .rcx = 0 := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private theorem afterXor_rip :
    afterXor.rip = (afterStore storedValue entryState).rip + 2 := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private theorem lookupXor :
    instructionAtRipIndexed
      (indexInstructions entryState.rip
        (StackStorePrefixLink.instructions storedValue ++ Realization.continuation))
      (afterStore storedValue entryState).rip = some (xor_r32 .ecx .ecx) := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private theorem afterXorSilent :
    win32Intercept (Event := Event) afterXor.rip afterXor = none := by
  decide

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private theorem xorTransition :
    nativeOutcomeTransition (Event := Event) (xor_r32 .ecx .ecx)
      (afterStore storedValue entryState) [] = (afterXor, []) := by
  unfold nativeOutcomeTransition
  change (match win32Intercept (Event := Event) afterXor.rip afterXor with
    | some (hooked, event) => (hooked, event.elim [] fun emitted => [emitted])
    | none => (afterXor, [])) = (afterXor, [])
  rw [afterXorSilent]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private def callExitProcess : X86_64Instr := call_rip 8199

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private theorem lookupCall :
    instructionAtRipIndexed
      (indexInstructions entryState.rip
        (StackStorePrefixLink.instructions storedValue ++ Realization.continuation))
      afterXor.rip = some callExitProcess := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private def afterCall : X86_64MachineState :=
  X86_64Instruction.step callExitProcess afterXor

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private theorem afterCall_rcx : afterCall.gprs .rcx = 0 := by
  exact afterXor_rcx

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private theorem afterCall_exitCode : (afterCall.gprs .rcx).toUInt32 = 0 := by
  rw [afterCall_rcx]
  decide

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private theorem callDispatch :
    win32Intercept (Event := Event) afterCall.rip afterCall =
      some (exitProcessHook afterCall) := by
  unfold win32Intercept
  rw [show findIatIndex afterCall afterCall.rip = some 3 by decide]
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private def exitedState : X86_64MachineState :=
  (exitProcessHook (Event := Event) afterCall).1

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
private theorem callTransition :
    nativeOutcomeTransition (Event := Event) callExitProcess afterXor [] =
      (exitedState, [Inject.inject (ProcessEvent.exit 0)]) := by
  unfold nativeOutcomeTransition
  change (match win32Intercept (Event := Event) afterCall.rip afterCall with
    | some (hooked, event) => (hooked, event.elim [] fun emitted => [emitted])
    | none => (afterCall, [])) = _
  rw [callDispatch]
  simp [exitedState, exitProcessHook]
  rw [afterCall_exitCode]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The exact production runner consumes the checked prefix and real terminal continuation. -/
theorem canonicalObservable :
    (runProgramOutcomeLoop (Event := Event) indexed 4 entryState []).observable =
      .processExited 0 [Inject.inject (ProcessEvent.exit 0)] := by
  change (runProgramOutcomeLoop (Event := Event)
    (indexInstructions entryState.rip
      (StackStorePrefixLink.instructions storedValue ++ Realization.continuation))
    4 entryState []).observable = _
  rw [runProgramOutcomeLoop_prefixWithContinuation entryState [] storedValue
    Realization.continuation (by decide) rfl allocateSilent storeSilent 2]
  rw [runProgramOutcomeLoop]
  simp only [lookupXor]
  rw [xorTransition]
  simp only [afterXor_fault]
  rw [runProgramOutcomeLoop]
  simp only [lookupCall]
  rw [callTransition]
  simp [exitedState, exitProcessHook, NativeRunOutcome.observable]
  exact afterCall_exitCode

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def proofBudget : NativeProofBudget where
  evaluatorFuel := 4

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def artifact : WindowsX86_64Artifact where
  executable := executable
  instructions := instructions

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Universe-erased evidence that the selected ordinary instruction was produced by the sealed
    checked authoring path. -/
def AuthoringEstablished (state : X86_64MachineState) : Prop :=
  ∃ checked : CheckedStore state,
    checked.erase = mov_rsp_byte byteOffset storedValue

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Erased ghost context carried by the real program capability row. Its indices force all three
    witnesses to describe one exact core entry state. The constructor is private so the selected
    entry certificate is the only source of this spike-local capability context. -/
structure CheckedMemoryContext where
  private mk ::
  state : X86_64MachineState
  logical : TypedStoreView state
  physical : X86StoreRealization state
  authored : AuthoringEstablished state

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def checkedEntryContext : CheckedMemoryContext where
  state := entryState
  logical := typedStoreView
  physical := storeRealization
  authored := ⟨checkedStore, CheckedStore.erase_eq checkedStore⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The platform load may add arbitrary external-input queues; the checked logical and physical
    state is the exact loader core from which that external-input frame is formed. -/
def CheckedMemoryEstablished (selectedArtifact : WindowsX86_64Artifact)
    (environment : Environment) (loaded : X86_64MachineState)
    (context : CheckedMemoryContext) : Prop :=
  selectedArtifact = artifact ∧
    loaded = entryState.withExternalInputs environment.stdin environment.incomingRequests ∧
    context.state = entryState ∧
    selectedArtifact.instructions =
      [sub_rsp frameSize, mov_rsp_byte byteOffset storedValue,
        xor_r32 .ecx .ecx, call_rip 8199]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def checkedMemoryCapability : Capability (WindowsX86_64 Event) where
  Context := CheckedMemoryContext
  providers := []
  establishes := CheckedMemoryEstablished

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Host providers and checked memory authority occupy one composed entry row. The runtime is still
    the production Win32 dispatcher; the memory component contributes no fabricated provider. -/
def capabilities : CapabilityComposition (WindowsX86_64 Event) where
  root := Capability.compose
    (windowsHostCapability Event standardWindowsProviders) checkedMemoryCapability
  realize := fun _ _ =>
    ({ interceptor := standardWindowsRuntime Event, proofBudget } : NativeX86_64Runtime Event)
  realizeSupports := by
    intro context selectedArtifact provider membership linked
    simp only [Capability.compose, windowsHostCapability, checkedMemoryCapability,
      List.append_nil] at membership
    exact standardWindowsRuntimeSupports Event proofBudget selectedArtifact provider
      membership linked

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def artifactCertificate : ProgramArtifactCertificate (WindowsX86_64 Event) where
  artifact := artifact
  exports := VerifiedExportSet.empty _ _ _ _ _ () rfl rfl rfl
  exportsArtifact := rfl
  artifactConnection := artifact_connected

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem providerCertificate : ProgramProviderCertificate (WindowsX86_64 Event)
    capabilities artifact where
  importsCovered := by
    intro imported membership
    change imported ∈ [GetStdHandleDef, ReadFileDef, WriteFileDef, ExitProcessDef,
      VirtualAllocDef, VirtualFreeDef] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact ⟨windowsProvider GetStdHandleDef 0 0, by simp [capabilities, Capability.compose,
          standardWindowsProviders, windowsHostCapability], rfl⟩
      | exact ⟨windowsProvider ReadFileDef 1 1, by simp [capabilities, Capability.compose,
          standardWindowsProviders, windowsHostCapability], rfl⟩
      | exact ⟨windowsProvider WriteFileDef 2 2, by simp [capabilities, Capability.compose,
          standardWindowsProviders, windowsHostCapability], rfl⟩
      | exact ⟨windowsProvider ExitProcessDef 3 3, by simp [capabilities, Capability.compose,
          standardWindowsProviders, windowsHostCapability], rfl⟩
      | exact ⟨windowsProvider VirtualAllocDef 4 4, by simp [capabilities, Capability.compose,
          standardWindowsProviders, windowsHostCapability], rfl⟩
      | exact ⟨windowsProvider VirtualFreeDef 5 5, by simp [capabilities, Capability.compose,
          standardWindowsProviders, windowsHostCapability], rfl⟩
  providersLinked := by
    intro provider membership
    simp only [capabilities, Capability.compose, standardWindowsProviders,
      windowsHostCapability, checkedMemoryCapability, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      change (_ = _) ∧ _
      constructor
      · decide
      · rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Establishment explicitly constructs the checked logical and physical evidence for the loaded
    entry state before satisfying the current platform's unit host context. -/
def entryCertificate : ProgramEntryCertificate (WindowsX86_64 Event)
    capabilities artifact where
  entryContext := fun _ => ((), checkedEntryContext)
  entryEstablished := by
    intro environment
    constructor
    · trivial
    · exact ⟨rfl, rfl, rfl, instructions_shape⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem selectedTermination :
    selectedExecutionTerminates (Event := Event) false selectedNonInputWin32Call indexed
      proofBudget.evaluatorFuel executable.load = true := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def terminationCertificate :
    SelectedTerminationCertificate (Event := Event) false selectedNonInputWin32Call
      executable.load.rip instructions executable.load where
  fuel := proofBudget.evaluatorFuel
  verifies := selectedTermination

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem outcomeExternalInputFrame (environment : Environment) :
    runProgramOutcomeWithLoops (Event := Event) executable.load.rip instructions
        proofBudget.evaluatorFuel
        (executable.load.withExternalInputs environment.stdin environment.incomingRequests) =
      (runProgramOutcomeWithLoops (Event := Event) executable.load.rip instructions
        proofBudget.evaluatorFuel executable.load).withExternalInputs
          environment.stdin environment.incomingRequests := by
  exact terminationCertificate.externalInputFrame
    (fun instruction _ => instruction_preserves_external_input_frame instruction)
    (by
      intro address state stdin requests selected
      exact win32CallIntercept_preserves_selected_external_input_frame
        address state stdin requests selected)
    environment.stdin environment.incomingRequests

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def afterInvalidationWorld : World ObligationId ObligationKind :=
  ⟨[accessEntry entryState], by simp [accessEntry]⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def completedWorld : World ObligationId ObligationKind := World.empty

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem invalidateRemoval :
    Removal (entryWorld entryState) afterInvalidationWorld invalidateEntry := by
  exact ⟨by
    change [accessEntry entryState, invalidateEntry].Perm
      [invalidateEntry, accessEntry entryState]
    exact .swap _ _ []⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem accessRemoval :
    Removal afterInvalidationWorld completedWorld (accessEntry entryState) := by
  exact ⟨by simp [afterInvalidationWorld, completedWorld, World.empty]⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Profile-owned lifecycle authority is tied to this exact terminal execution. It justifies the
    two structural removals; the generic obligation module itself grants no discharge authority.
    Its private constructor prevents callers from repackaging structural deltas as lifecycle
    authority. -/
structure LifecycleCompletion : Prop where
  private mk ::
  terminal :
    (runProgramOutcomeLoop (Event := Event) indexed 4 entryState []).observable =
      .processExited 0 [Inject.inject (ProcessEvent.exit 0)]
  invalidatesView : Removal (entryWorld entryState) afterInvalidationWorld invalidateEntry
  returnsExclusive : Removal afterInvalidationWorld completedWorld (accessEntry entryState)

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem lifecycleCompletion : LifecycleCompletion where
  terminal := canonicalObservable
  invalidatesView := invalidateRemoval
  returnsExclusive := accessRemoval

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem admissibilityCertificate : ProgramAdmissibilityCertificate (WindowsX86_64 Event)
    capabilities artifact entryCertificate where
  platformAdmissible := by
    intro environment
    have logical := typedStoreView
    have physical := storeRealization
    have lifecycle := lifecycleCompletion
    change (runProgramOutcomeWithLoops (Event := Event) executable.load.rip instructions
      proofBudget.evaluatorFuel (executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).isAdmissible false
    rw [outcomeExternalInputFrame]
    simp only [NativeRunOutcome.withExternalInputs_isAdmissible]
    exact terminationCertificate.isAdmissible

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def behaviorCertificate : ProgramBehaviorCertificate (WindowsX86_64 Event)
    capabilities artifact entryCertificate where
  spec := fun _ => .processExited 0 [Inject.inject (ProcessEvent.exit 0)]
  traceEquivalence := by
    intro environment
    change (runProgramOutcomeWithLoops (Event := Event) executable.load.rip instructions
      proofBudget.evaluatorFuel (executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).observable = _
    rw [outcomeExternalInputFrame]
    simp only [NativeRunOutcome.withExternalInputs_observable]
    exact canonicalObservable

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Sole whole-program proof and emission authority for the checked-memory demonstration. -/
def verifiedProgram : VerifiedProgram (WindowsX86_64 Event)
    capabilities :=
  VerifiedProgram.compose "Checked x86 byte store to Windows process exit"
    artifactCertificate providerCertificate entryCertificate admissibilityCertificate
    behaviorCertificate

end Spikes.CheckedMemoryWindows
