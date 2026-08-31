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
import Gasm.Targets.AArch64.MacroAssembler.PlatformBridge
import Gasm.Targets.Dispatcher
import Spikes.CompilerBulk.AArch64Linux.Program

namespace Spikes.CompilerBulk.AArch64Linux

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Compiler.Word.StructuredStraightLineAArch64
open Gasm.Targets
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Instructions
open Gasm.Targets.AArch64.Linux
open Gasm.Targets.AArch64.MacroAssembler

attribute [local simp] instAArch64InstructionAnyAArch64Instruction
  instAArch64InstructionMovz instAArch64InstructionSvc

abbrev Event := AnyEvent

def indexed : List (UInt64 × Instructions.AnyAArch64Instruction) :=
  indexInstructions executable.load.pc instructions

private theorem index_lt_7_cases (index : Nat) (bound : index < 7) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
    index = 5 ∨ index = 6 := by
  omega

/- REF: docs/MACRO_ASSEMBLER.md#verified-compiler-bulk-spike -/
def bodyPlacement :
    ContextualStraightLinePlacement indexed optimized.code executable.load where
  lookup := by
    intro index inBounds
    change index < 7 at inBounds
    have bound : index < 7 := inBounds
    rcases index_lt_7_cases index bound with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/- REF: docs/MACRO_ASSEMBLER.md#verified-compiler-bulk-spike -/
def bodyRuntimeSilent : RuntimeSilentOn (Event := Event) optimized.code executable.load := by
  intro index inBounds
  change index < 7 at inBounds
  have bound : index < 7 := inBounds
  rcases index_lt_7_cases index bound with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def bodyState : AArch64MachineState := runLocalSteps optimized.code executable.load

theorem bodyState_result : bodyState.gprs x0 = 42 := by
  rw [show bodyState.gprs x0 = bulkExitWord.fn (argsOfState executable.load) from
    optimized.localResult executable.load]
  rfl

theorem bodyState_pc : bodyState.pc = executable.load.pc + 28 := by
  rw [show bodyState.pc = executable.load.pc + localCodeSize optimized.code from
    optimized.pcAdvance executable.load]
  rfl

/- REF: docs/MACRO_ASSEMBLER.md#verified-compiler-bulk-spike -/
/-- The compiler source theorem is transported through the seven-instruction hand replacement;
    only the two handwritten Linux tail steps are then discharged in the selected runtime. -/
theorem canonicalEvents :
    (runAArch64OutcomeLoop (Event := Event) indexed 50000 executable.load []).events =
      [Inject.inject (ProcessEvent.exit 42)] := by
  rw [show 50000 = optimized.code.length + 49993 by rfl]
  rw [runAArch64OutcomeLoop_prefix (Event := Event) optimized.code indexed executable.load
    bodyPlacement bodyRuntimeSilent rfl rfl 49993 []]
  change (runAArch64OutcomeLoop (Event := Event) indexed 49993 bodyState []).events = _
  have bodyFault : bodyState.fault = none := by
    exact (optimized.preservesFault executable.load).trans rfl
  have bodyRunning : bodyState.terminated = false := by
    exact (optimized.preservesTerminated executable.load).trans rfl
  have bodyFaultSome : bodyState.fault.isSome = false := by rw [bodyFault]; rfl
  let movExit : Instructions.AnyAArch64Instruction :=
    Instructions.AnyAArch64Instruction.mk (movz64 .x8 93)
  let afterMov := AArch64Instruction.step movExit bodyState
  have lookupMov : instructionAtPcIndexed indexed bodyState.pc = some movExit := by
    rw [bodyState_pc]
    rfl
  have afterMovPc : afterMov.pc = bodyState.pc + 4 := by
    simp [afterMov, movExit, AArch64Instruction.step, movz64,
      AArch64MachineState.setReg64, AArch64MachineState.setGpr64,
      AArch64MachineState.advancePc, regIndex]
  have afterMovFault : afterMov.fault = none := by
    simp [afterMov, movExit, AArch64Instruction.step, movz64, bodyFault,
      AArch64MachineState.setReg64, AArch64MachineState.setGpr64,
      AArch64MachineState.advancePc, regIndex]
  have afterMovRunning : afterMov.terminated = false := by
    simp [afterMov, movExit, AArch64Instruction.step, movz64, bodyRunning,
      AArch64MachineState.setReg64, AArch64MachineState.setGpr64,
      AArch64MachineState.advancePc, regIndex]
  have afterMovFaultSome : afterMov.fault.isSome = false := by rw [afterMovFault]; rfl
  have afterMovX0 : afterMov.gprs x0 = 42 := by
    have x0Ne8 : x0 ≠ (8 : Fin 31) := by
      intro equal
      have values := congrArg Fin.val equal
      change 0 = 8 at values
      omega
    simp [afterMov, movExit, AArch64Instruction.step, movz64,
      AArch64MachineState.setReg64, AArch64MachineState.setGpr64,
      AArch64MachineState.advancePc, regIndex, x0Ne8, bodyState_result]
  have afterMovX8 : afterMov.getReg64 .x8 = 93 := by
    simp [afterMov, movExit, AArch64Instruction.step, movz64,
      AArch64MachineState.setReg64, AArch64MachineState.setGpr64,
      AArch64MachineState.advancePc, AArch64MachineState.getReg64,
      AArch64MachineState.getGpr64, regIndex]
  have silentMov :
      (inferInstance : ExternalCallInterceptor AArch64 Event).interceptCall
        afterMov.pc afterMov = none := by
    change linuxSyscallIntercept afterMov.pc afterMov = none
    have addressNe : executable.load.pc + 28 + 4 ≠ linuxSyscallEntry := by decide
    simp [afterMovPc, bodyState_pc, linuxSyscallIntercept, addressNe]
  let service : Instructions.AnyAArch64Instruction :=
    Instructions.AnyAArch64Instruction.mk (svcInstr 0)
  let afterSvc := AArch64Instruction.step service afterMov
  have lookupSvc : instructionAtPcIndexed indexed afterMov.pc = some service := by
    rw [afterMovPc, bodyState_pc]
    rfl
  have afterSvcFaultSome : afterSvc.fault.isSome = false := by
    simp [afterSvc, service, AArch64Instruction.step, svcInstr, afterMovFault]
  have afterSvcRunning : afterSvc.terminated = false := by
    simp [afterSvc, service, AArch64Instruction.step, svcInstr, afterMovRunning]
  have afterSvcX0 : afterSvc.gprs x0 = 42 := by
    simp [afterSvc, service, AArch64Instruction.step, svcInstr, afterMovX0]
  have afterSvcX8 : afterSvc.getReg64 .x8 = 93 := by
    change afterMov.getReg64 .x8 = 93
    exact afterMovX8
  have afterSvcPc : afterSvc.pc = linuxSyscallEntry := by
    simp [afterSvc, service, AArch64Instruction.step, svcInstr]
  have afterSvcFin0 : afterSvc.gprs (⟨0, by omega⟩ : Fin 31) = 42 := by
    have zeroEq : (⟨0, by omega⟩ : Fin 31) = x0 := by apply Fin.ext; rfl
    rw [zeroEq]
    exact afterSvcX0
  have dispatch :
      (inferInstance : ExternalCallInterceptor AArch64 Event).interceptCall
        afterSvc.pc afterSvc = some (sysExitHook afterSvc) := by
    change linuxSyscallIntercept afterSvc.pc afterSvc = some (sysExitHook afterSvc)
    rw [afterSvcPc]
    simp [linuxSyscallIntercept, afterSvcX8, SYS_read, SYS_write, SYS_openat,
      SYS_close, SYS_mmap, SYS_munmap, SYS_socket, SYS_accept, SYS_bind,
      SYS_listen, SYS_exit]
  rw [runAArch64OutcomeLoop]
  simp only [bodyFaultSome, bodyRunning, Bool.false_eq_true, ↓reduceIte,
    lookupMov]
  rw [show AArch64Instruction.step movExit bodyState = afterMov from rfl]
  simp only [afterMovFaultSome, afterMovRunning, Bool.false_eq_true, ↓reduceIte,
    silentMov]
  rw [runAArch64OutcomeLoop]
  simp only [afterMovFaultSome, afterMovRunning, Bool.false_eq_true, ↓reduceIte,
    lookupSvc]
  rw [show AArch64Instruction.step service afterMov = afterSvc from rfl]
  simp [afterSvcFaultSome, afterSvcRunning, dispatch, sysExitHook]
  change [Inject.inject (ProcessEvent.exit
    (afterSvc.gprs (⟨0, by omega⟩ : Fin 31)).toUInt32)] =
      [Inject.inject (ProcessEvent.exit 42)]
  rw [afterSvcFin0]
  rfl

def artifact : LinuxAArch64Artifact where
  executable := executable
  instructions := instructions

def artifactCertificate : ProgramArtifactCertificate (LinuxAArch64 Event) where
  artifact := artifact
  exports := VerifiedExportSet.empty _ _ _ _ _ () rfl rfl rfl
  exportsArtifact := rfl
  artifactConnection := rfl

def providerCertificate : ProgramProviderCertificate (LinuxAArch64 Event)
    (aarch64LinuxHostCapabilities Event) artifact where
  importsCovered := by
    intro imported membership
    change imported ∈ ([] : List Unit) at membership
    contradiction
  providersLinked := by intro provider; exact nomatch provider

def entryCertificate : ProgramEntryCertificate (LinuxAArch64 Event)
    (aarch64LinuxHostCapabilities Event) artifact where
  entryContext := fun _ => ()
  entryEstablished := by intro; trivial

theorem selectedTermination :
    selectedExecutionTerminates (Event := Event) selectedNonInputAArch64LinuxCall
      indexed 50000 executable.load = true := by
  rfl

def terminationCertificate :
    SelectedTerminationCertificate (Event := Event) selectedNonInputAArch64LinuxCall
      executable.load.pc instructions executable.load where
  fuel := 50000
  verifies := selectedTermination

theorem outcomeExternalInputFrame (environment : Environment) :
    runAArch64Outcome (Event := Event) executable.load.pc instructions 50000
        (executable.load.withExternalInputs environment.stdin environment.incomingRequests) =
      (runAArch64Outcome (Event := Event) executable.load.pc instructions 50000
        executable.load).withExternalInputs environment.stdin environment.incomingRequests := by
  exact terminationCertificate.externalInputFrame
    aarch64LinuxCallInterceptor_preserves_selected_external_input_frame
    environment.stdin environment.incomingRequests

def admissibilityCertificate : ProgramAdmissibilityCertificate (LinuxAArch64 Event)
    (aarch64LinuxHostCapabilities Event) artifact entryCertificate where
  platformAdmissible := by
    intro environment
    change (runAArch64Outcome (Event := Event) executable.load.pc instructions 50000
      (executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).isAdmissible
    rw [outcomeExternalInputFrame]
    simp only [AArch64RunOutcome.withExternalInputs_isAdmissible]
    exact terminationCertificate.isAdmissible (selected := selectedNonInputAArch64LinuxCall)

def behaviorCertificate : ProgramBehaviorCertificate (LinuxAArch64 Event)
    (aarch64LinuxHostCapabilities Event) artifact entryCertificate where
  spec := fun _ => [Inject.inject (ProcessEvent.exit 42)]
  traceEquivalence := by
    intro environment
    change runAArch64Trace (Event := Event) instructions
      (executable.load.withExternalInputs environment.stdin environment.incomingRequests) = _
    have outcome := congrArg AArch64RunOutcome.events (outcomeExternalInputFrame environment)
    simp only [AArch64RunOutcome.withExternalInputs_events] at outcome
    rw [show runAArch64Trace (Event := Event) instructions
      (executable.load.withExternalInputs environment.stdin environment.incomingRequests) =
        runAArch64Trace (Event := Event) instructions executable.load by
          simpa [runAArch64Trace, runAArch64Outcome_events] using outcome]
    change (runAArch64OutcomeLoop (Event := Event) indexed 50000 executable.load []).events = _
    exact canonicalEvents

/- REF: docs/MACRO_ASSEMBLER.md#verified-compiler-bulk-spike -/
/-- The sole whole-program authority for the compiler-bulk demonstration. -/
def verifiedProgram :
    VerifiedProgram (LinuxAArch64 Event) (aarch64LinuxHostCapabilities Event) :=
  VerifiedProgram.compose "Compiler bulk: Lean to AArch64 Linux exit"
    artifactCertificate providerCertificate entryCertificate admissibilityCertificate
    behaviorCertificate

end Spikes.CompilerBulk.AArch64Linux
