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
import Gasm.Targets.X86_64.ClosedExecution
import Gasm.Targets.Windows.Linker

/-!
# Windows native program certificates

This module owns the repeated Windows boundary work between an exact closed x86 execution and the
platform-neutral program certificates.  Standard import coverage/linkage and external-input
framing are proved here instead of being enumerated by every spike.
-/

namespace Gasm.Targets.Windows

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.X86_64

local instance {Event : Type}
    [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event] :
    ExternalCallInterceptor X86_64 Event := standardWindowsRuntime Event

/-- The import manifest installed by the standard Windows linker/runtime profile. -/
def standardWindowsImports : List Win32Function :=
  [GetStdHandleDef, ReadFileDef, WriteFileDef, ExitProcessDef,
    VirtualAllocDef, VirtualFreeDef]

private theorem standardIatOffset (rva : UInt32) (index : Nat) (small : index ≤ 5) :
    (((0x140000000 : UInt64) + rva.toUInt64 + (index * 8).toUInt64 -
      ((0x140000000 : UInt64) + rva.toUInt64)) / 8).toNat = index := by
  have hrva : rva.toNat < 4294967296 := UInt32.toNat_lt rva
  simp [UInt64.toNat_sub, UInt64.toNat_add, Nat.toUInt64]
  generalize hbase : 5368709120 + rva.toNat = base
  have baseSmall : base < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt baseSmall]
  have cancel : 18446744073709551616 - base + (base + index * 8) =
      18446744073709551616 + index * 8 := by omega
  rw [cancel, Nat.add_mod]
  omega

/-- Linker-owned evidence that the standard manifest describes this exact final artifact and that
each standard provider resolves through its physical import slot. -/
structure StandardProviderLinkCertificate {Event : Type}
    (artifact : WindowsX86_64Artifact) where
  private mk ::
  importsExact : artifact.executable.imports = standardWindowsImports
  providersLinked : ∀ provider, provider ∈ standardWindowsProviders →
    Platform.providerLinked (P := WindowsX86_64 Event) artifact provider

namespace StandardProviderLinkCertificate

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- The standard linker discharges its recurring provider-slot proof once for every program it
produces with the standard manifest. -/
theorem ofLinkedProgram {Event : Type} (symbolicProgram : List Assembler.SymbolicInstr)
    (dataItems : List (String × ByteArray) := []) :
    let linked := Linker.linkWindowsProgram symbolicProgram dataItems
    StandardProviderLinkCertificate (Event := Event)
      { executable := linked.executable, instructions := linked.instructions } := by
  dsimp
  refine {
    importsExact := rfl
    providersLinked := ?_
  }
  intro provider membership
  simp only [standardWindowsProviders, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    change (_ = _) ∧ _
    constructor
    · rfl
    · first
      | simpa [Linker.linkWindowsProgram, WindowsExecutable.iatFunctionSlots,
          WindowsExecutable.iatFunctionSlots.loop, groupImportsByDll, groupImportsByDll.loop,
          windowsProvider] using standardIatOffset
            (computeSectionLayout
              (Linker.linkWindowsProgram symbolicProgram dataItems).executable.textBytes.size
              (Linker.linkWindowsProgram symbolicProgram dataItems).executable.rdataBytes.size
              512).idataRva 0 (by omega)
      | simpa [Linker.linkWindowsProgram, WindowsExecutable.iatFunctionSlots,
          WindowsExecutable.iatFunctionSlots.loop, groupImportsByDll, groupImportsByDll.loop,
          windowsProvider] using standardIatOffset
            (computeSectionLayout
              (Linker.linkWindowsProgram symbolicProgram dataItems).executable.textBytes.size
              (Linker.linkWindowsProgram symbolicProgram dataItems).executable.rdataBytes.size
              512).idataRva 1 (by omega)
      | simpa [Linker.linkWindowsProgram, WindowsExecutable.iatFunctionSlots,
          WindowsExecutable.iatFunctionSlots.loop, groupImportsByDll, groupImportsByDll.loop,
          windowsProvider] using standardIatOffset
            (computeSectionLayout
              (Linker.linkWindowsProgram symbolicProgram dataItems).executable.textBytes.size
              (Linker.linkWindowsProgram symbolicProgram dataItems).executable.rdataBytes.size
              512).idataRva 2 (by omega)
      | simpa [Linker.linkWindowsProgram, WindowsExecutable.iatFunctionSlots,
          WindowsExecutable.iatFunctionSlots.loop, groupImportsByDll, groupImportsByDll.loop,
          windowsProvider] using standardIatOffset
            (computeSectionLayout
              (Linker.linkWindowsProgram symbolicProgram dataItems).executable.textBytes.size
              (Linker.linkWindowsProgram symbolicProgram dataItems).executable.rdataBytes.size
              512).idataRva 3 (by omega)
      | simpa [Linker.linkWindowsProgram, WindowsExecutable.iatFunctionSlots,
          WindowsExecutable.iatFunctionSlots.loop, groupImportsByDll, groupImportsByDll.loop,
          windowsProvider] using standardIatOffset
            (computeSectionLayout
              (Linker.linkWindowsProgram symbolicProgram dataItems).executable.textBytes.size
              (Linker.linkWindowsProgram symbolicProgram dataItems).executable.rdataBytes.size
              512).idataRva 4 (by omega)
      | simpa [Linker.linkWindowsProgram, WindowsExecutable.iatFunctionSlots,
          WindowsExecutable.iatFunctionSlots.loop, groupImportsByDll, groupImportsByDll.loop,
          windowsProvider] using standardIatOffset
            (computeSectionLayout
              (Linker.linkWindowsProgram symbolicProgram dataItems).executable.textBytes.size
              (Linker.linkWindowsProgram symbolicProgram dataItems).executable.rdataBytes.size
              512).idataRva 5 (by omega)

end StandardProviderLinkCertificate

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
/-- Standard provider coverage and physical linkage derived from the artifact import table and the
capability row's certified provider manifest. -/
theorem standardProviderCertificate {Event : Type}
    {capabilities : CapabilityComposition (WindowsX86_64 Event)}
    (artifact : WindowsX86_64Artifact)
    (link : StandardProviderLinkCertificate (Event := Event) artifact)
    (providersExact : capabilities.root.providers = standardWindowsProviders) :
    ProgramProviderCertificate (WindowsX86_64 Event) capabilities artifact where
  importsCovered := by
    intro imported membership
    change imported ∈ artifact.executable.imports at membership
    rw [link.importsExact] at membership
    simp only [standardWindowsImports, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact ⟨windowsProvider GetStdHandleDef 0 0, by rw [providersExact]; simp [standardWindowsProviders], rfl⟩
      | exact ⟨windowsProvider ReadFileDef 1 1, by rw [providersExact]; simp [standardWindowsProviders], rfl⟩
      | exact ⟨windowsProvider WriteFileDef 2 2, by rw [providersExact]; simp [standardWindowsProviders], rfl⟩
      | exact ⟨windowsProvider ExitProcessDef 3 3, by rw [providersExact]; simp [standardWindowsProviders], rfl⟩
      | exact ⟨windowsProvider VirtualAllocDef 4 4, by rw [providersExact]; simp [standardWindowsProviders], rfl⟩
      | exact ⟨windowsProvider VirtualFreeDef 5 5, by rw [providersExact]; simp [standardWindowsProviders], rfl⟩
  providersLinked := by
    intro provider membership
    apply link.providersLinked provider
    rwa [← providersExact]

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- One exact non-input Windows artifact/load/runtime/entry object closed by a selected x86
execution.  The minimal realization facts ensure platform certificates consume the same proof
budget and interceptor as the closed execution.  This adapter deliberately excludes input,
allocation/resource, and network calls even though the standard provider manifest lists them. -/
structure NonInputStandardNativeProgram {Event : Type}
    [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event]
    (capabilities : CapabilityComposition (WindowsX86_64 Event))
    (artifact : WindowsX86_64Artifact)
    (entry : ProgramEntryCertificate (WindowsX86_64 Event) capabilities artifact) where
  execution : @ClosedExecution Event (standardWindowsRuntime Event) selectedNonInputWin32Call
    (indexInstructions artifact.executable.load.rip artifact.instructions)
    artifact.executable.load []
  interceptorExact : ∀ environment,
    (capabilities.realize artifact (entry.entryContext environment)).interceptor =
      standardWindowsRuntime Event
  fuelExact : ∀ environment,
    (capabilities.realize artifact
      (entry.entryContext environment)).proofBudget.evaluatorFuel = execution.fuel

namespace NonInputStandardNativeProgram

variable {Event : Type}
  [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event]
  {capabilities : CapabilityComposition (WindowsX86_64 Event)}
  {artifact : WindowsX86_64Artifact}
  {entry : ProgramEntryCertificate (WindowsX86_64 Event) capabilities artifact}

/-- Standard selected-call termination authority for this exact loaded artifact. -/
def terminationCertificate (program : NonInputStandardNativeProgram capabilities artifact entry) :
    @SelectedTerminationCertificate Event (standardWindowsRuntime Event) false selectedNonInputWin32Call
      artifact.executable.load.rip artifact.instructions artifact.executable.load :=
  program.execution.terminationCertificate false artifact.executable.load.rip
    artifact.instructions rfl

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Universal stdin/request framing for executions certified by `selectedNonInputWin32Call`. -/
theorem externalInputFrame (program : NonInputStandardNativeProgram capabilities artifact entry)
    (environment : Environment) :
    @runProgramOutcomeWithLoops Event (standardWindowsRuntime Event)
        artifact.executable.load.rip artifact.instructions program.execution.fuel
        (artifact.executable.load.withExternalInputs environment.stdin environment.incomingRequests) =
      (@runProgramOutcomeWithLoops Event (standardWindowsRuntime Event)
        artifact.executable.load.rip artifact.instructions program.execution.fuel
        artifact.executable.load).withExternalInputs
          environment.stdin environment.incomingRequests := by
  exact program.terminationCertificate.externalInputFrame
    (fun instruction _ => instruction_preserves_external_input_frame instruction)
    (by
      intro address state stdin requests selected
      exact win32CallIntercept_preserves_selected_external_input_frame
        address state stdin requests selected)
    environment.stdin environment.incomingRequests

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- Platform admissibility derived from the exact closed outcome for every environment. -/
theorem admissibilityCertificate (program : NonInputStandardNativeProgram capabilities artifact entry) :
    ProgramAdmissibilityCertificate (WindowsX86_64 Event) capabilities artifact entry where
  platformAdmissible := by
    intro environment
    have runtimeExact : capabilities.realize artifact (entry.entryContext environment) =
        ({ interceptor := standardWindowsRuntime Event,
           proofBudget := ⟨program.execution.fuel⟩ } : NativeX86_64Runtime Event) := by
      cases runtime : capabilities.realize artifact (entry.entryContext environment) with
      | mk interceptor proofBudget =>
        cases proofBudget with
        | mk evaluatorFuel =>
          have interceptorEq := program.interceptorExact environment
          have fuelEq := program.fuelExact environment
          rw [runtime] at interceptorEq fuelEq
          simp only at interceptorEq fuelEq
          subst interceptor
          subst evaluatorFuel
          rfl
    rw [runtimeExact]
    change (@runProgramOutcomeWithLoops Event (standardWindowsRuntime Event)
      artifact.executable.load.rip artifact.instructions program.execution.fuel
      (artifact.executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).isAdmissible false
    rw [program.externalInputFrame environment]
    simp only [NativeRunOutcome.withExternalInputs_isAdmissible]
    change (runProgramOutcomeLoop
      (indexInstructions artifact.executable.load.rip artifact.instructions)
      program.execution.fuel artifact.executable.load []).isAdmissible false
    rw [program.execution.run]
    exact program.execution.admissible false

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- Transport the exact closed execution to an independently authored specification.  The caller's
refinement premise owns semantic meaning; this adapter supplies only execution/framing plumbing. -/
def behaviorCertificate (program : NonInputStandardNativeProgram capabilities artifact entry)
    (spec : Environment → NativeObservable Event)
    (refines : ∀ environment, program.execution.outcome.observable = spec environment) :
    ProgramBehaviorCertificate (WindowsX86_64 Event) capabilities artifact entry where
  spec := spec
  traceEquivalence := by
    intro environment
    have runtimeExact : capabilities.realize artifact (entry.entryContext environment) =
        ({ interceptor := standardWindowsRuntime Event,
           proofBudget := ⟨program.execution.fuel⟩ } : NativeX86_64Runtime Event) := by
      cases runtime : capabilities.realize artifact (entry.entryContext environment) with
      | mk interceptor proofBudget =>
        cases proofBudget with
        | mk evaluatorFuel =>
          have interceptorEq := program.interceptorExact environment
          have fuelEq := program.fuelExact environment
          rw [runtime] at interceptorEq fuelEq
          simp only at interceptorEq fuelEq
          subst interceptor
          subst evaluatorFuel
          rfl
    rw [runtimeExact]
    change (@runProgramOutcomeWithLoops Event (standardWindowsRuntime Event)
      artifact.executable.load.rip artifact.instructions program.execution.fuel
      (artifact.executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).observable = _
    rw [program.externalInputFrame environment]
    simp only [NativeRunOutcome.withExternalInputs_observable]
    change (runProgramOutcomeLoop
      (indexInstructions artifact.executable.load.rip artifact.instructions)
      program.execution.fuel artifact.executable.load []).observable = _
    rw [program.execution.run]
    exact refines environment

end NonInputStandardNativeProgram

end Gasm.Targets.Windows
