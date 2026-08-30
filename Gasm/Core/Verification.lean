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
import Gasm.Core.Platform
import Gasm.Effects.Trace
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.Dispatcher
import Gasm.Targets.Linux.Linker
import Gasm.Targets.AArch64.Semantics
import Gasm.Targets.AArch64.Linux.Linker

namespace Gasm.Core.Verification

universe u

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.Windows
open Gasm.Targets.Linux
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Linux

export Gasm.Core.Platform
  (Environment Platform Capability CapabilityComposition VerifiedProgram
   ProgramArtifactCertificate ProgramProviderCertificate ProgramEntryCertificate
   ProgramAdmissibilityCertificate ProgramBehaviorCertificate
   emitVerifiedProgram FuzzingEmitter rawEmitForFuzzing)

/-! Native platform profiles. The artifact pairs the emitted image with the
instruction sequence whose operational semantics is proved. -/

structure WindowsX86_64Artifact where
  executable : WindowsExecutable
  instructions : List X86_64Instr

/-- One PE import-table provider. `importIndex` identifies the typed entry in
    the compact artifact manifest; `iatIndex` identifies its physical thunk
    after per-DLL terminator slots are inserted. Keeping both prevents a
    multi-DLL image from confusing logical import order with physical layout. -/
structure WindowsX86_64Provider where
  protocol : ProviderProtocolKey
  imported : Win32Function
  importIndex : Nat
  iatIndex : Nat

/-- A nominal Linux library requirement.  It remains present even when target
    lowering resolves the provider statically. -/
structure LinuxLibraryRequirement where
  library : String
  symbol : String
  protocolVersion : Nat
deriving DecidableEq, BEq

/-- One statically resolved Linux provider call target. -/
structure LinuxX86_64Provider where
  protocol : ProviderProtocolKey
  requirement : LinuxLibraryRequirement
  instructionIndex : Nat
  callTarget : Address

structure LinuxX86_64Artifact where
  executable : LinuxExecutable
  instructions : List X86_64Instr
  imports : List LinuxLibraryRequirement := []

structure LinuxAArch64Artifact where
  executable : AArch64LinuxExecutable
  instructions : List AnyAArch64Instruction

inductive WindowsX86_64 (Event : Type)
inductive LinuxX86_64 (Event : Type)
inductive LinuxAArch64 (Event : Type)

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- A caller-selected finite execution resource.  It is intentionally a value in the native
    runtime context rather than a target constant: selecting a capability composition also
    selects the budget under which its explicit `.fuelExhausted` result is observed. -/
structure NativeExecutionPolicy where
  instructionFuel : Nat

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- The realized native runtime consists of the target's host-call implementation and the
    selected finite execution policy.  Keeping them together prevents a verified program from
    proving behavior for one interceptor while `Platform.run` silently chooses another budget. -/
structure NativeX86_64Runtime (Event : Type) where
  interceptor : Gasm.Targets.X86_64.ExternalCallInterceptor X86_64 Event
  executionPolicy : NativeExecutionPolicy

def linuxProviderCallTarget (artifact : LinuxX86_64Artifact)
    (index : Nat) : Option Address :=
  let indexed := indexInstructions artifact.executable.load.rip artifact.instructions
  match indexed[index]? with
  | some (instructionRip, instruction) =>
      let before : X86_64MachineState :=
        { artifact.executable.load with rip := instructionRip }
      some (Gasm.Targets.X86_64.Instructions.X86_64Instruction.step
        instruction before).rip
  | none => none

def emptyBoundarySpec : BoundaryContextSpec Unit Unit where
  Args := fun _ => Unit
  Binding := fun _ => Unit
  Result := fun _ => Unit
  Outcome := fun _ => Unit
  ObligationFragment := fun _ => Unit
  requiredObligations := fun _ _ _ => ()
  emittedObligations := fun _ _ _ _ _ => ()
  requires := fun _ _ _ _ => True
  transitions := fun _ _ _ _ _ before after => before = after

def emptyBoundarySemantics (Target State : Type) :
    TargetBoundarySemantics Target where
  Implementation := Unit
  Artifact := Unit
  Signature := Unit
  EntryKind := Unit
  ExitKind := Unit
  PhysicalState := State
  Execution := Unit
  PublicEntry := Empty
  LookupKey := Empty
  artifactImplements := (· = ·)
  publicEntries := fun _ => []
  callableEntries := fun _ => []
  lookupKey := fun entry => nomatch entry
  resolvesEntry := fun _ entry => nomatch entry
  jointlyAdmissible := fun _ entries => entries = []
  runs := fun _ _ _ _ _ _ _ _ => False
  admissible := fun _ _ _ _ _ _ _ _ => False

instance {Event : Type} : Platform (WindowsX86_64 Event) where
  Artifact := WindowsX86_64Artifact
  State := X86_64MachineState
  Observation := NativeObservable Event
  RuntimeContext := NativeX86_64Runtime Event
  Import := Win32Function
  Provider := WindowsX86_64Provider
  BoundaryWorld := Unit
  BoundaryKey := Unit
  BoundaryTarget := WindowsX86_64 Event
  boundarySpec := emptyBoundarySpec
  boundarySemantics := emptyBoundarySemantics _ X86_64MachineState
  imports := fun artifact => artifact.executable.imports
  providerProvides := fun provider imported => provider.imported = imported
  providerLinked := fun artifact provider =>
    artifact.executable.imports[provider.importIndex]? = some provider.imported ∧
      let executable := artifact.executable
      let layout := computeSectionLayout executable.textBytes.size executable.rdataBytes.size 512
      let iatBase := executable.imageBase + layout.idataRva.toUInt64
      match (executable.iatFunctionSlots layout.idataRva)[provider.importIndex]? with
      | some address => ((address - iatBase) / 8).toNat = provider.iatIndex
      | none => False
  runtimeSupports := fun runtime artifact provider =>
    let executable := artifact.executable
    let layout := computeSectionLayout executable.textBytes.size executable.rdataBytes.size 512
    match (executable.iatFunctionSlots layout.idataRva)[provider.importIndex]? with
    | some address => ∀ state,
        Gasm.Targets.Windows.findIatIndex state address = some provider.iatIndex →
        (runtime.interceptor.interceptCall address state).isSome
    | none => False
  boundaryArtifact := fun _ => ()
  artifactConnected := fun artifact =>
    artifact.executable.textBytes =
      Gasm.Targets.X86_64.Assembler.serializeInstructions artifact.instructions
  load := fun artifact environment =>
    let state := artifact.executable.loadWithStdin environment.stdin
    { state with incomingRequests := environment.incomingRequests }
  run := fun runtime artifact state =>
    letI := runtime.interceptor
    (runProgramOutcomeWithLoops (Event := Event) state.rip artifact.instructions
      runtime.executionPolicy.instructionFuel state).observable
  admissible := fun runtime artifact state =>
    letI := runtime.interceptor
    (runProgramOutcomeWithLoops (Event := Event) state.rip artifact.instructions
      runtime.executionPolicy.instructionFuel state).isAdmissible false
  emit := fun artifact => .ok artifact.executable.emit

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- Linux x86-64 termination/admissibility, named at the target boundary so dependent
    whole-program certificates do not normalize a concrete 50k-step interpreter merely to expose
    the proposition.  The iff below records that this wrapper is exactly the platform condition. -/
def linuxX86_64Admissible {Event : Type}
    (runtime : NativeX86_64Runtime Event)
    (artifact : LinuxX86_64Artifact) (state : X86_64MachineState) : Prop :=
  letI := runtime.interceptor
  (runProgramOutcomeWithLoops (Event := Event) state.rip artifact.instructions
    runtime.executionPolicy.instructionFuel state).isAdmissible true

theorem linuxX86_64Admissible_iff {Event : Type}
    (runtime : NativeX86_64Runtime Event)
    (artifact : LinuxX86_64Artifact) (state : X86_64MachineState) :
    linuxX86_64Admissible runtime artifact state ↔
      (letI := runtime.interceptor
       (runProgramOutcomeWithLoops (Event := Event) state.rip artifact.instructions
         runtime.executionPolicy.instructionFuel state).isAdmissible true) := Iff.rfl

theorem linuxX86_64Admissible_of_outcome {Event : Type}
    (runtime : NativeX86_64Runtime Event)
    (artifact : LinuxX86_64Artifact) (state : X86_64MachineState)
    (outcome :
      (letI := runtime.interceptor
       (runProgramOutcomeWithLoops (Event := Event) state.rip artifact.instructions
         runtime.executionPolicy.instructionFuel state).isAdmissible true)) :
    linuxX86_64Admissible runtime artifact state := outcome

/-- Admissibility from a proved execution result.  Keeping the execution equality separate prevents
    elaboration of a concrete certificate from evaluating the interpreter while preserving the
    exact target predicate. -/
theorem linuxX86_64Admissible_of_execution {Event : Type}
    (runtime : NativeX86_64Runtime Event)
    (artifact : LinuxX86_64Artifact) (state : X86_64MachineState)
    (execution : NativeRunOutcome Event)
    (executes :
      (letI := runtime.interceptor
       runProgramOutcomeWithLoops (Event := Event) state.rip artifact.instructions
         runtime.executionPolicy.instructionFuel state) = execution)
    (admissible : execution.isAdmissible true) :
    linuxX86_64Admissible runtime artifact state := by
  apply linuxX86_64Admissible_of_outcome
  rw [executes]
  exact admissible

theorem linuxX86_64Admissible_of_returned {Event : Type}
    (runtime : NativeX86_64Runtime Event)
    (artifact : LinuxX86_64Artifact) (state finalState : X86_64MachineState)
    (events : List Event)
    (executes :
      (letI := runtime.interceptor
       runProgramOutcomeWithLoops (Event := Event) state.rip artifact.instructions
         runtime.executionPolicy.instructionFuel state) = .returned finalState events) :
    linuxX86_64Admissible runtime artifact state := by
  apply linuxX86_64Admissible_of_execution runtime artifact state (.returned finalState events)
  · exact executes
  · trivial

theorem linuxX86_64Admissible_to_outcome {Event : Type}
    (runtime : NativeX86_64Runtime Event)
    (artifact : LinuxX86_64Artifact) (state : X86_64MachineState)
    (admissible : linuxX86_64Admissible runtime artifact state) :
    (letI := runtime.interceptor
     (runProgramOutcomeWithLoops (Event := Event) state.rip artifact.instructions
       runtime.executionPolicy.instructionFuel state).isAdmissible true) := admissible

instance {Event : Type} : Platform (LinuxX86_64 Event) where
  Artifact := LinuxX86_64Artifact
  State := X86_64MachineState
  Observation := NativeObservable Event
  RuntimeContext := NativeX86_64Runtime Event
  Import := LinuxLibraryRequirement
  Provider := LinuxX86_64Provider
  BoundaryWorld := Unit
  BoundaryKey := Unit
  BoundaryTarget := LinuxX86_64 Event
  boundarySpec := emptyBoundarySpec
  boundarySemantics := emptyBoundarySemantics _ X86_64MachineState
  imports := fun artifact => artifact.imports
  providerProvides := fun provider imported => provider.requirement = imported
  providerLinked := fun artifact provider =>
    provider.requirement ∈ artifact.imports ∧
      linuxProviderCallTarget artifact provider.instructionIndex = some provider.callTarget
  runtimeSupports := fun runtime _ provider =>
    ∀ state, (runtime.interceptor.interceptCall provider.callTarget state).isSome
  boundaryArtifact := fun _ => ()
  artifactConnected := fun artifact =>
    artifact.executable.textBytes =
      Gasm.Targets.X86_64.Assembler.serializeInstructions artifact.instructions
  load := fun artifact environment =>
    let state := artifact.executable.loadWithStdin environment.stdin
    { state with incomingRequests := environment.incomingRequests }
  run := fun runtime artifact state =>
    letI := runtime.interceptor
    (runProgramOutcomeWithLoops (Event := Event) state.rip artifact.instructions
      runtime.executionPolicy.instructionFuel state).observable
  admissible := linuxX86_64Admissible
  emit := fun artifact => .ok artifact.executable.emit

instance {Event : Type} : Platform (LinuxAArch64 Event) where
  Artifact := LinuxAArch64Artifact
  State := AArch64MachineState
  Observation := List Event
  RuntimeContext := Gasm.Targets.AArch64.ExternalCallInterceptor AArch64 Event
  Import := Unit
  Provider := Empty
  BoundaryWorld := Unit
  BoundaryKey := Unit
  BoundaryTarget := LinuxAArch64 Event
  boundarySpec := emptyBoundarySpec
  boundarySemantics := emptyBoundarySemantics _ AArch64MachineState
  imports := fun _ => []
  providerProvides := fun provider => nomatch provider
  providerLinked := fun _ provider => nomatch provider
  runtimeSupports := fun _ _ provider => nomatch provider
  boundaryArtifact := fun _ => ()
  artifactConnected := fun artifact =>
    artifact.executable.textBytes =
      Gasm.Targets.AArch64.Linux.serializeInstructions artifact.instructions
  load := fun artifact environment =>
    let state := artifact.executable.loadWithStdin environment.stdin
    { state with incomingRequests := environment.incomingRequests }
  run := fun runtime artifact state =>
    letI := runtime
    runAArch64Trace artifact.instructions state
  admissible := fun runtime artifact state =>
    letI := runtime
    (Gasm.Targets.AArch64.runAArch64Outcome (Event := Event)
      state.pc artifact.instructions 50000 state).isAdmissible
  emit := fun artifact => .ok artifact.executable.emit

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
def windowsProvider (imported : Win32Function) (importIndex iatIndex : Nat) :
    WindowsX86_64Provider where
  protocol :=
    { protocolNamespace := imported.moduleName
      operation := imported.symbolName
      version := 0 }
  imported := imported
  importIndex := importIndex
  iatIndex := iatIndex

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
/-- Exact provider table for artifacts linked with `linkWindowsProgram`'s default KERNEL32 import
    vector.  `importIndex` and physical `iatIndex` coincide because this is one DLL. -/
def standardWindowsProviders : List WindowsX86_64Provider :=
  [windowsProvider GetStdHandleDef 0 0,
   windowsProvider ReadFileDef 1 1,
   windowsProvider WriteFileDef 2 2,
   windowsProvider ExitProcessDef 3 3,
   windowsProvider VirtualAllocDef 4 4,
   windowsProvider VirtualFreeDef 5 5]

@[instance_reducible] def standardWindowsRuntime (Event : Type)
    [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event] :
    Gasm.Targets.X86_64.ExternalCallInterceptor X86_64 Event where
  interceptCall := Gasm.Targets.Windows.win32Intercept

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
/-- The production Win32 dispatcher supports every provider in the exact standard table whenever
    that provider is linked into the final artifact.  This target-owned fact is proved once here,
    not replayed by each `VerifiedProgram`. -/
theorem standardWindowsRuntimeSupports (Event : Type) (executionPolicy : NativeExecutionPolicy)
    [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event] :
    ∀ artifact provider, provider ∈ standardWindowsProviders →
      Platform.providerLinked (P := WindowsX86_64 Event) artifact provider →
      Platform.runtimeSupports (P := WindowsX86_64 Event)
        ({ interceptor := standardWindowsRuntime Event, executionPolicy } : NativeX86_64Runtime Event)
        artifact provider := by
  intro artifact provider hprovider hlinked
  rcases hlinked with ⟨_, hlinkedSlot⟩
  let layout := computeSectionLayout artifact.executable.textBytes.size
    artifact.executable.rdataBytes.size 512
  let slots := artifact.executable.iatFunctionSlots layout.idataRva
  change (match slots[provider.importIndex]? with
    | some address => ∀ state, Gasm.Targets.Windows.findIatIndex state address =
        some provider.iatIndex →
        ((standardWindowsRuntime Event).interceptCall
          address state).isSome
    | none => False)
  change (match slots[provider.importIndex]? with
    | some address => _
    | none => False) at hlinkedSlot
  generalize hslot : slots[provider.importIndex]? = resolved at hlinkedSlot ⊢
  cases resolved with
  | none => exact hlinkedSlot.elim
  | some address =>
      intro state hfind
      simp only [standardWindowsProviders, List.mem_cons, List.not_mem_nil, or_false] at hprovider
      rcases hprovider with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        change (Gasm.Targets.Windows.win32Intercept (Event := Event) address state).isSome
        simp [Gasm.Targets.Windows.win32Intercept, windowsProvider, hfind]

/-- Windows host services form an explicit typed capability row. Provider
    selection is artifact-specific; an empty or catch-all helper cannot cover a
    PE import table soundly. -/
def windowsHostCapability (Event : Type) (providers : List WindowsX86_64Provider)
    [Gasm.Targets.X86_64.ExternalCallInterceptor X86_64 Event] :
    Capability (WindowsX86_64 Event) where
  Context := Unit
  providers := providers
  establishes := fun _ _ _ _ => True

def windowsHostCapabilities (Event : Type) (providers : List WindowsX86_64Provider)
    (executionPolicy : NativeExecutionPolicy)
    [runtime : Gasm.Targets.X86_64.ExternalCallInterceptor X86_64 Event]
    (supports : ∀ artifact provider, provider ∈ providers →
      Platform.providerLinked (P := WindowsX86_64 Event) artifact provider →
      Platform.runtimeSupports (P := WindowsX86_64 Event)
        ({ interceptor := runtime, executionPolicy } : NativeX86_64Runtime Event) artifact provider) :
    CapabilityComposition (WindowsX86_64 Event) where
  root := windowsHostCapability Event providers
  realize := fun _ _ => by
    exact ({ interceptor := runtime, executionPolicy } : NativeX86_64Runtime Event)
  realizeSupports := by
    intro context artifact provider membership linked
    exact supports artifact provider membership linked

def standardWindowsHostCapabilities (Event : Type) (executionPolicy : NativeExecutionPolicy)
    [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event] :
    CapabilityComposition (WindowsX86_64 Event) :=
  { root := windowsHostCapability Event standardWindowsProviders
    realize := fun _ _ =>
      ({ interceptor := standardWindowsRuntime Event, executionPolicy } : NativeX86_64Runtime Event)
    realizeSupports := by
      intro context artifact provider membership linked
      exact standardWindowsRuntimeSupports Event executionPolicy artifact provider membership linked }

def linuxHostCapabilities (Event : Type) (executionPolicy : NativeExecutionPolicy)
    [runtime : Gasm.Targets.X86_64.ExternalCallInterceptor X86_64 Event] :
    CapabilityComposition (LinuxX86_64 Event) where
  root := Capability.empty _
  realize := fun _ _ => by
    exact ({ interceptor := runtime, executionPolicy } : NativeX86_64Runtime Event)
  realizeSupports := by simp [Capability.empty]

def aarch64LinuxHostCapabilities (Event : Type)
    [runtime : Gasm.Targets.AArch64.ExternalCallInterceptor AArch64 Event] :
    CapabilityComposition (LinuxAArch64 Event) where
  root := Capability.empty _
  realize := fun _ _ => by
    change Gasm.Targets.AArch64.ExternalCallInterceptor AArch64 Event
    exact runtime
  realizeSupports := by simp [Capability.empty]

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- A verified library routine remains target-independent. -/
structure VerifiedRoutine (SpecState : Type) (MachineState : Type) (Event : Type) [BEq Event] where
  name : String
  program : List SymbolicInstr
  couplingInv : SpecState → MachineState → Bool
  specStep : SpecState → Option (SpecState × List Event)
  machStep : MachineState → Option (MachineState × List Event)
  traceEquivalence :
    ∀ (s_spec : SpecState) (s_mach : MachineState),
      couplingInv s_spec s_mach = true →
      match specStep s_spec, machStep s_mach with
      | some (s_spec', specTrace), some (s_mach', machTrace) =>
          (specTrace == machTrace && couplingInv s_spec' s_mach' == true) = true
      | none, none => True
      | _, _ => False

end Gasm.Core.Verification
