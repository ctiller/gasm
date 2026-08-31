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
import Gasm.Targets.X86_64.MacroAssembler.PlatformBridge
import Spikes.CompilerBulk.WindowsX64.Program

namespace Spikes.CompilerBulk.WindowsX64

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry
open Gasm.Targets
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Gasm.Targets.Windows

abbrev Event := AnyEvent

local instance : ExternalCallInterceptor X86_64 Event :=
  standardWindowsRuntime Event

def indexed : List (UInt64 × X86_64Instr) :=
  indexInstructions executable.load.rip instructions

theorem instructions_decomposition :
    instructions = [] ++ compiled.instructions ++ instructions.drop compiled.instructions.length := by
  rfl

theorem indexedLayout : IndexedLayoutCertificate indexed :=
  IndexedLayoutCertificate.ofNoDupAddresses _ (by decide)

theorem bodySubsequence :
    ContiguousInstructionSubsequence indexed executable.load.rip compiled.instructions :=
  ContiguousInstructionSubsequence.ofDecomposition executable.load.rip executable.load.rip
    instructions [] compiled.instructions (instructions.drop compiled.instructions.length)
    instructions_decomposition rfl

/- REF: docs/MACRO_ASSEMBLER.md#verified-microsoft-x64-compiler-bulk-spike -/
theorem bodyPlacement : ContextualStraightLinePlacement indexed executable.load.rip
    compiled.instructions executable.load :=
  ContextualStraightLinePlacement.ofSubsequence indexed executable.load.rip
    compiled.instructions executable.load compiled.controlFlowFree rfl indexedLayout bodySubsequence

private def SuccessorsUnaligned (base : UInt64) : List X86_64Instr → Bool
  | [] => true
  | instruction :: rest =>
      let next := base + (X86_64Instruction.encode instruction).size.toUInt64
      (next % 8 != 0) && SuccessorsUnaligned next rest

private theorem SuccessorsUnaligned.resolve {base : UInt64} {code : List X86_64Instr}
    (unaligned : SuccessorsUnaligned base code = true)
    (before : List X86_64Instr) (instruction : X86_64Instr) (suffix : List X86_64Instr)
    (split : code = before ++ instruction :: suffix) :
    ((base + instructionSpan before +
      (X86_64Instruction.encode instruction).size.toUInt64) % 8 != 0) = true := by
  induction before generalizing base code with
  | nil =>
      simp only [List.nil_append] at split
      subst code
      have parts :
          ((base + (X86_64Instruction.encode instruction).size.toUInt64) % 8 != 0) = true ∧
            SuccessorsUnaligned
              (base + (X86_64Instruction.encode instruction).size.toUInt64) suffix = true := by
        simpa [SuccessorsUnaligned] using unaligned
      simpa [instructionSpan] using parts.1
  | cons first before ih =>
      cases code with
      | nil => simp at split
      | cons head rest =>
          simp only [List.cons_append, List.cons.injEq] at split
          rcases split with ⟨equal, split⟩
          subst head
          have parts :
              ((base + (X86_64Instruction.encode first).size.toUInt64) % 8 != 0) = true ∧
                SuccessorsUnaligned
                  (base + (X86_64Instruction.encode first).size.toUInt64) rest = true := by
            simpa [SuccessorsUnaligned] using unaligned
          have resolved := ih (base := base +
            (X86_64Instruction.encode first).size.toUInt64) parts.2 split
          simpa [instructionSpan, UInt64.add_assoc] using resolved

private theorem bodySuccessorsUnaligned :
    SuccessorsUnaligned executable.load.rip compiled.instructions = true := by
  rfl

private theorem win32Intercept_none_of_unaligned {state : X86_64MachineState}
    {address : UInt64} (unaligned : (address % 8 != 0) = true) :
    win32Intercept (Event := Event) address state = none := by
  unfold win32Intercept findIatIndex
  rw [show (state.read64 address != address || address % 8 != 0) = true by
    rw [unaligned, Bool.or_true]]
  rfl

/- REF: docs/MACRO_ASSEMBLER.md#verified-microsoft-x64-compiler-bulk-spike -/
theorem bodyRuntimeSilent : RuntimeSilentOn (Event := Event) compiled.instructions executable.load := by
  intro before instruction suffix split
  let beforeState := runLocalSteps before executable.load
  let after := X86_64Instruction.step instruction beforeState
  have beforeOrdinary : ∀ selected ∈ before, ControlFlowFree selected := by
    intro selected member
    apply compiled.controlFlowFree selected
    rw [split]
    exact List.mem_append_left _ member
  have instructionOrdinary : ControlFlowFree instruction := by
    apply compiled.controlFlowFree instruction
    rw [split]
    simp
  have beforeRip : beforeState.rip = executable.load.rip + instructionSpan before := by
    exact runLocalSteps_rip_eq before beforeOrdinary executable.load
  have afterRip : after.rip = beforeState.rip +
      (X86_64Instruction.encode instruction).size.toUInt64 := by
    exact instructionOrdinary.step_rip_eq beforeState
  apply win32Intercept_none_of_unaligned
  rw [afterRip, beforeRip]
  simpa [UInt64.add_assoc] using
    SuccessorsUnaligned.resolve bodySuccessorsUnaligned before instruction suffix split

def bodyState : X86_64MachineState :=
  runLocalSteps compiled.instructions executable.load

theorem bodyState_result : bodyState.gprs .rax = 42 := by
  rw [show bodyState.gprs .rax = bulkExitWord.fn (argsOfState executable.load) from
    compiled.localResult executable.load]
  rfl

theorem bodyState_rip :
    bodyState.rip = executable.load.rip + instructionSpan compiled.instructions := by
  exact compiled.ripAdvance executable.load

private theorem compiled_instructionSpan : instructionSpan compiled.instructions = 34 := by
  rfl

theorem bodyState_fault : bodyState.fault = none := by
  exact (compiled.preservesFault executable.load).trans rfl

private def reserveCallFrame : X86_64Instr := sub_rsp 40

private def afterReserveCallFrame : X86_64MachineState :=
  X86_64Instruction.step reserveCallFrame bodyState

private theorem lookupReserveCallFrame :
    instructionAtRipIndexed indexed bodyState.rip = some reserveCallFrame := by
  rw [bodyState_rip]
  rw [compiled_instructionSpan]
  rfl

private theorem afterReserveCallFrame_fault : afterReserveCallFrame.fault = none := by
  change ({ (bodyState.setGpr64 .rsp (bodyState.gprs .rsp - 40)).setFlagsSub64
    (bodyState.gprs .rsp) 40 with rip := bodyState.rip + 4 }).fault = none
  exact bodyState_fault

private theorem afterReserveCallFrame_rax : afterReserveCallFrame.gprs .rax = 42 := by
  change ((bodyState.setGpr64 .rsp (bodyState.gprs .rsp - 40)).setFlagsSub64
    (bodyState.gprs .rsp) 40).gprs .rax = 42
  simp [X86_64MachineState.setFlagsSub64, X86_64MachineState.setFlagsCmp64,
    X86_64MachineState.setGpr64, bodyState_result]

private theorem afterReserveCallFrame_rip :
    afterReserveCallFrame.rip = bodyState.rip + 4 := by
  rfl

private theorem afterReserveCallFrame_silent :
    win32Intercept (Event := Event) afterReserveCallFrame.rip afterReserveCallFrame = none := by
  apply win32Intercept_none_of_unaligned
  rw [afterReserveCallFrame_rip, bodyState_rip]
  rfl

private theorem reserveCallFrameTransition :
    nativeOutcomeTransition (Event := Event) reserveCallFrame bodyState [] =
      (afterReserveCallFrame, []) := by
  unfold nativeOutcomeTransition
  change (match win32Intercept (Event := Event) afterReserveCallFrame.rip afterReserveCallFrame with
    | some (hooked, event) => (hooked, event.elim [] fun emitted => [emitted])
    | none => (afterReserveCallFrame, [])) = (afterReserveCallFrame, [])
  rw [afterReserveCallFrame_silent]

private def moveExitCode : X86_64Instr := mov_r64 .rcx .rax

private def afterMoveExitCode : X86_64MachineState :=
  X86_64Instruction.step moveExitCode afterReserveCallFrame

private theorem lookupMoveExitCode :
    instructionAtRipIndexed indexed afterReserveCallFrame.rip = some moveExitCode := by
  rw [afterReserveCallFrame_rip, bodyState_rip]
  rw [compiled_instructionSpan]
  rfl

private theorem afterMoveExitCode_fault : afterMoveExitCode.fault = none := by
  change ({ afterReserveCallFrame.setGpr64 .rcx (afterReserveCallFrame.gprs .rax) with
    rip := afterReserveCallFrame.rip + 3 }).fault = none
  exact afterReserveCallFrame_fault

private theorem afterMoveExitCode_rcx : afterMoveExitCode.gprs .rcx = 42 := by
  change (afterReserveCallFrame.setGpr64 .rcx
    (afterReserveCallFrame.gprs .rax)).gprs .rcx = 42
  simp [X86_64MachineState.setGpr64, afterReserveCallFrame_rax]

private theorem afterMoveExitCode_rip :
    afterMoveExitCode.rip = afterReserveCallFrame.rip + 3 := by
  rfl

private theorem afterMoveExitCode_silent :
    win32Intercept (Event := Event) afterMoveExitCode.rip afterMoveExitCode = none := by
  apply win32Intercept_none_of_unaligned
  rw [afterMoveExitCode_rip, afterReserveCallFrame_rip, bodyState_rip]
  rfl

private def callExitProcess : X86_64Instr := call_rip 8169

private theorem lookupCallExitProcess :
    instructionAtRipIndexed indexed afterMoveExitCode.rip = some callExitProcess := by
  rw [afterMoveExitCode_rip, afterReserveCallFrame_rip, bodyState_rip]
  rw [compiled_instructionSpan]
  rfl

private theorem moveExitCodeTransition :
    nativeOutcomeTransition (Event := Event) moveExitCode afterReserveCallFrame [] =
      (afterMoveExitCode, []) := by
  unfold nativeOutcomeTransition
  change (match win32Intercept (Event := Event) afterMoveExitCode.rip afterMoveExitCode with
    | some (hooked, event) => (hooked, event.elim [] fun emitted => [emitted])
    | none => (afterMoveExitCode, [])) = (afterMoveExitCode, [])
  rw [afterMoveExitCode_silent]

private def afterCallExitProcess : X86_64MachineState :=
  X86_64Instruction.step callExitProcess afterMoveExitCode

private theorem afterCallExitProcess_rcx : afterCallExitProcess.gprs .rcx = 42 := by
  change afterMoveExitCode.gprs .rcx = 42
  exact afterMoveExitCode_rcx

private theorem callExitProcessDispatch :
    win32Intercept (Event := Event) afterCallExitProcess.rip afterCallExitProcess =
      some (exitProcessHook afterCallExitProcess) := by
  unfold win32Intercept
  rw [show findIatIndex afterCallExitProcess afterCallExitProcess.rip = some 3 by decide]
  rfl

private def exitedState : X86_64MachineState :=
  (exitProcessHook (Event := Event) afterCallExitProcess).1

private theorem callExitProcessTransition :
    nativeOutcomeTransition (Event := Event) callExitProcess afterMoveExitCode [] =
      (exitedState, [Inject.inject (ProcessEvent.exit 42)]) := by
  unfold nativeOutcomeTransition
  change (match win32Intercept (Event := Event) afterCallExitProcess.rip afterCallExitProcess with
    | some (hooked, event) => (hooked, event.elim [] fun emitted => [emitted])
    | none => (afterCallExitProcess, [])) = _
  rw [callExitProcessDispatch]
  simp [exitedState, exitProcessHook, afterCallExitProcess_rcx]

/- REF: docs/MACRO_ASSEMBLER.md#verified-microsoft-x64-compiler-bulk-spike -/
/-- The generated body is consumed by the contextual production-runner bridge. The remaining three
    handwritten instructions reserve the required Microsoft-x64 call frame, move the proved result
    into the Win32 argument register, and reach the linked `ExitProcess` provider, whose actual hook
    produces the terminal process outcome. -/
theorem canonicalObservable :
    (runProgramOutcomeLoop (Event := Event) indexed
      (compiled.instructions.length + 3) executable.load []).observable =
      .processExited 42 [Inject.inject (ProcessEvent.exit 42)] := by
  rw [runProgramOutcomeLoop_prefix (Event := Event) compiled.instructions
    compiled.controlFlowFree indexed executable.load.rip executable.load bodyPlacement
    bodyRuntimeSilent rfl 3 []]
  change (runProgramOutcomeLoop (Event := Event) indexed 3 bodyState []).observable = _
  rw [runProgramOutcomeLoop]
  simp only [lookupReserveCallFrame]
  rw [reserveCallFrameTransition]
  simp only [afterReserveCallFrame_fault]
  rw [runProgramOutcomeLoop]
  simp only [lookupMoveExitCode]
  rw [moveExitCodeTransition]
  simp only [afterMoveExitCode_fault]
  rw [runProgramOutcomeLoop]
  simp only [lookupCallExitProcess]
  rw [callExitProcessTransition]
  simp [exitedState, exitProcessHook, afterCallExitProcess_rcx,
    NativeRunOutcome.observable]

def proofBudget : NativeProofBudget where
  evaluatorFuel := compiled.instructions.length + 3

def artifact : WindowsX86_64Artifact where
  executable := executable
  instructions := instructions

def artifactCertificate : ProgramArtifactCertificate (WindowsX86_64 Event) where
  artifact := artifact
  exports := VerifiedExportSet.empty _ _ _ _ _ () rfl rfl rfl
  exportsArtifact := rfl
  artifactConnection := rfl

def providerCertificate : ProgramProviderCertificate (WindowsX86_64 Event)
    (standardWindowsHostCapabilities Event proofBudget) artifact where
  importsCovered := by
    intro imported membership
    change imported ∈ [GetStdHandleDef, ReadFileDef, WriteFileDef, ExitProcessDef,
      VirtualAllocDef, VirtualFreeDef] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact ⟨windowsProvider GetStdHandleDef 0 0, by simp [standardWindowsHostCapabilities,
          standardWindowsProviders, windowsHostCapability], rfl⟩
      | exact ⟨windowsProvider ReadFileDef 1 1, by simp [standardWindowsHostCapabilities,
          standardWindowsProviders, windowsHostCapability], rfl⟩
      | exact ⟨windowsProvider WriteFileDef 2 2, by simp [standardWindowsHostCapabilities,
          standardWindowsProviders, windowsHostCapability], rfl⟩
      | exact ⟨windowsProvider ExitProcessDef 3 3, by simp [standardWindowsHostCapabilities,
          standardWindowsProviders, windowsHostCapability], rfl⟩
      | exact ⟨windowsProvider VirtualAllocDef 4 4, by simp [standardWindowsHostCapabilities,
          standardWindowsProviders, windowsHostCapability], rfl⟩
      | exact ⟨windowsProvider VirtualFreeDef 5 5, by simp [standardWindowsHostCapabilities,
          standardWindowsProviders, windowsHostCapability], rfl⟩
  providersLinked := by
    intro provider membership
    simp only [standardWindowsHostCapabilities, standardWindowsProviders, windowsHostCapability,
      List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      change (_ = _) ∧ _
      constructor
      · decide
      · rfl

def entryCertificate : ProgramEntryCertificate (WindowsX86_64 Event)
    (standardWindowsHostCapabilities Event proofBudget) artifact where
  entryContext := fun _ => ()
  entryEstablished := by intro; trivial

theorem selectedTermination :
    selectedExecutionTerminates (Event := Event) false selectedNonInputWin32Call indexed
      proofBudget.evaluatorFuel executable.load = true := by
  rfl

def terminationCertificate :
    SelectedTerminationCertificate (Event := Event) false selectedNonInputWin32Call
      executable.load.rip instructions executable.load where
  fuel := proofBudget.evaluatorFuel
  verifies := selectedTermination

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

def admissibilityCertificate : ProgramAdmissibilityCertificate (WindowsX86_64 Event)
    (standardWindowsHostCapabilities Event proofBudget) artifact entryCertificate where
  platformAdmissible := by
    intro environment
    change (runProgramOutcomeWithLoops (Event := Event) executable.load.rip instructions
      proofBudget.evaluatorFuel (executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).isAdmissible false
    rw [outcomeExternalInputFrame]
    simp only [NativeRunOutcome.withExternalInputs_isAdmissible]
    exact terminationCertificate.isAdmissible

def behaviorCertificate : ProgramBehaviorCertificate (WindowsX86_64 Event)
    (standardWindowsHostCapabilities Event proofBudget) artifact entryCertificate where
  spec := fun _ => .processExited 42 [Inject.inject (ProcessEvent.exit 42)]
  traceEquivalence := by
    intro environment
    change (runProgramOutcomeWithLoops (Event := Event) executable.load.rip instructions
      proofBudget.evaluatorFuel (executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).observable = _
    rw [outcomeExternalInputFrame]
    simp only [NativeRunOutcome.withExternalInputs_observable]
    change (runProgramOutcomeLoop (Event := Event) indexed
      (compiled.instructions.length + 3) executable.load []).observable = _
    exact canonicalObservable

/- REF: docs/MACRO_ASSEMBLER.md#verified-microsoft-x64-compiler-bulk-spike -/
/-- Sole whole-program authority for this compiler-bulk demonstration. -/
def verifiedProgram : VerifiedProgram (WindowsX86_64 Event)
    (standardWindowsHostCapabilities Event proofBudget) :=
  VerifiedProgram.compose "Compiler bulk: Lean to Windows x64 process exit"
    artifactCertificate providerCertificate entryCertificate admissibilityCertificate
    behaviorCertificate

end Spikes.CompilerBulk.WindowsX64
