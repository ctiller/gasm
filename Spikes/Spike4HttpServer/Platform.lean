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
import Gasm.Targets.Dispatcher
import Gasm.Targets.WASI.ABI
import Spikes.Spike4HttpServer.ParserCapability
import Spikes.Spike4HttpServer.Runtime
import Spikes.Spike4HttpServer.Windows.Program
import Spikes.Spike4HttpServer.Linux.Program
import Spikes.Spike4HttpServer.Wasm.Program

namespace Spikes.Spike4HttpServer

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.Windows
open Gasm.Targets.Linux
open Gasm.Targets.Wasm
open Gasm.Targets.WASI

def routeCode : RuntimeRoute → UInt64
  | .root => 0
  | .status => 1
  | .notFound => 2
  | .badRequest => 3
  | .resourceExhausted => 4

def parserInput (requests : List ByteArray) : RuntimeRoute × ByteArray × List ByteArray :=
  match requests with
  | [] => (.badRequest, ByteArray.empty, [])
  | request :: rest => ((driveRequest request).1, observedRequest request, rest)

def requestRuntimeEvent (phase : UInt64) (hasRequest : Bool)
    (parsed : RuntimeRoute × ByteArray × List ByteArray) :
    Option AnyEvent :=
  if phase = 0 then some (AnyEvent.of (NetEvent.listen 8080))
  else if !hasRequest then none
  else if phase = 1 then some (AnyEvent.of (NetEvent.accept "127.0.0.1"))
  else if phase = 2 then some (AnyEvent.of (NetEvent.recv (bytesToPayload parsed.2.1)))
  else if phase = 3 then some (AnyEvent.of (NetEvent.send (responseForRoute parsed.1)))
  else if phase = 4 then some (AnyEvent.of (NetEvent.close 101))
  else none

/-- Physical post-state for one Windows request-lifecycle boundary. -/
def windowsAfterPhase (phase : UInt64) (s : X86_64MachineState) : X86_64MachineState :=
  let parsed := parserInput s.incomingRequests
  let popped := popReturnAddress s
  let requests := if phase = 4 then parsed.2.2 else s.incomingRequests
  { (popped.setGpr64 .rax (routeCode parsed.1)) with incomingRequests := requests }

/-- Candidate Windows x64 ABI adapter for the staged request runtime. The intended ABI is
`(socket, scratch, scratchCapacity, retainedBudget) -> RuntimeRoute`. This executable hook models
the calling convention and lifecycle events, but no theorem here yet relates its machine-state
transition to `parserRealization`'s abstract boundary semantics. -/
def windowsParserHook (s : X86_64MachineState) : X86_64MachineState × Option AnyEvent :=
  let phase := s.gprs .r9
  let parsed := parserInput s.incomingRequests
  (windowsAfterPhase phase s,
    requestRuntimeEvent phase (!s.incomingRequests.isEmpty) parsed)

/-- Candidate composed Windows runtime binding. Provider support below proves dispatch at the
linked import slot; it does not by itself prove refinement to the parser component contract. -/
def spike4WindowsRuntime : ExternalCallInterceptor X86_64 AnyEvent where
  interceptCall addr state :=
    if findIatIndex state addr = some 0 then some (windowsParserHook state)
    else win32Intercept addr state

/-- Physical post-state for one Linux request-lifecycle boundary. -/
def linuxAfterPhase (phase : UInt64) (s : X86_64MachineState) : X86_64MachineState :=
  let parsed := parserInput s.incomingRequests
  let requests := if phase = 4 then parsed.2.2 else s.incomingRequests
  { (s.setGpr64 .rax (routeCode parsed.1)) with
    rip := s.gprs .rcx, incomingRequests := requests }

/-- Candidate Linux x86-64 ABI adapter. `gasmHttpLinuxSyscall` is deliberately not represented as
a Linux kernel syscall; it is a required import of the OS + Gasm-runtime profile. The adapter is
executable, but its refinement to `parserRealization` remains a separate proof obligation. -/
def linuxParserHook (s : X86_64MachineState) : X86_64MachineState × Option AnyEvent :=
  let phase := s.gprs .r10
  let parsed := parserInput s.incomingRequests
  (linuxAfterPhase phase s,
    requestRuntimeEvent phase (!s.incomingRequests.isEmpty) parsed)

/-- Candidate composed Linux runtime binding, with linked-call support but no claimed semantic
bridge from the machine transition to the abstract parser boundary. -/
def spike4LinuxRuntime : ExternalCallInterceptor X86_64 AnyEvent where
  interceptCall addr state :=
    if addr = linuxSyscallEntry ∧ state.gprs .rax = gasmHttpLinuxSyscall then
      some (linuxParserHook state)
    else linuxSyscallIntercept addr state

def appendRuntimeEvent (events : List AnyEvent) : Option AnyEvent → List AnyEvent
  | some emitted => events ++ [emitted]
  | none => events

/-- One explicit WASI boundary post-state. Whole-program proofs compose these five boundary
edges and do not unfold the streaming parser at each call site. -/
def wasiAfterPhase (phase : UInt32) (state : WasmMachineState) : WasmMachineState :=
  let parsed := parserInput state.incomingRequests
  let event := requestRuntimeEvent phase.toUInt64 (!state.incomingRequests.isEmpty) parsed
  let requests := if phase = 4 then state.incomingRequests.drop 1 else state.incomingRequests
  { state with incomingRequests := requests, events := appendRuntimeEvent state.events event }

def wasiPhaseResult (state : WasmMachineState) : UInt32 :=
  (routeCode (parserInput state.incomingRequests).1).toUInt32

@[simp] theorem wasiAfterPhase_trapped (phase : UInt32) (state : WasmMachineState) :
    (wasiAfterPhase phase state).trapped = state.trapped := rfl

@[simp] theorem wasiAfterPhase_exitCode (phase : UInt32) (state : WasmMachineState) :
    (wasiAfterPhase phase state).exitCode = state.exitCode := rfl

/-- Candidate Wasm canonical-import adapter for the staged request runtime. Its stack/event
behavior is executable; equivalence to `parserRealization` is not established in this file. -/
def spike4WasiRuntime : WasiHostRuntime := fun imports idx state =>
  if imports[idx]? = some gasmHttpParserSymbol then
    let (phase, s1) := popI32 state
    let (_scratchCapacity, s2) := popI32 s1
    let (_scratch, s3) := popI32 s2
    let (_socket, s4) := popI32 s3
    (pushVal (.i32 (wasiPhaseResult s4)) (wasiAfterPhase phase s4), .next)
  else
    wasiHostCall imports idx state

@[simp] theorem popI32_preserves_trapped (state : WasmMachineState) :
    (popI32 state).2.trapped = state.trapped := by
  rcases state with ⟨stack, locals, memory, memMax, stdin, stdinPos, requests,
    trapped, exitCode, events, fuelExhausted⟩
  cases stack with
  | nil => rfl
  | cons value rest => cases value <;> rfl

@[simp] theorem pushVal_preserves_trapped (value : WasmVal) (state : WasmMachineState) :
    (pushVal value state).trapped = state.trapped := rfl

def windowsParserImport : Win32Function :=
  { moduleName := gasmHttpRuntimeDll, symbolName := gasmHttpParserSymbol }

def winImport (moduleName symbolName : String) : Win32Function :=
  { moduleName, symbolName }

def linuxParserImport : LinuxLibraryRequirement :=
  { library := "gasm.runtime", symbol := gasmHttpParserSymbol, protocolVersion := 1 }

def parserProtocol : ProviderProtocolKey :=
  { protocolNamespace := gasmHttpWasmModule, operation := gasmHttpParserSymbol, version := 1 }

def spike4WindowsProviders : List WindowsX86_64Provider :=
  [{ protocol := parserProtocol, imported := windowsParserImport, importIndex := 0, iatIndex := 0 }]

def parserPhaseProtocol (phase : Nat) : ProviderProtocolKey :=
  { protocolNamespace := gasmHttpWasmModule,
    operation := s!"{gasmHttpParserSymbol}/phase/{phase}", version := 1 }

def linuxParserProvider (phase instructionIndex : Nat) : LinuxX86_64Provider :=
  { protocol := parserPhaseProtocol phase, requirement := linuxParserImport,
    instructionIndex, callTarget := linuxSyscallEntry }

def spike4LinuxProviders : List LinuxX86_64Provider :=
  [linuxParserProvider 0 2, linuxParserProvider 1 5, linuxParserProvider 2 8,
   linuxParserProvider 3 11, linuxParserProvider 4 14]

def spike4WasiProviders : List WasiProvider :=
  [{ protocol := .library parserProtocol, imports := Wasm.spike4WasmImports, importIndex := 0 }]

/-- Staging linkage records. They pin the selected component identity, required import, and final
instruction sequence for each artifact. These facts prevent accidental artifact drift, but they
do **not** constitute a machine/Wasm-to-`parserRealization` semantic refinement proof; that bridge
remains an explicit whole-program behavior obligation. -/
structure WindowsParserConnection (artifact : WindowsX86_64Artifact) where
  component : StreamingParserComponentConnection
  exactComponent : component = streamingParserComponentConnection
  imported : windowsParserImport ∈ artifact.executable.imports
  finalInstructions : artifact.instructions = Windows.spike4Instructions

structure LinuxParserConnection (artifact : LinuxX86_64Artifact) where
  component : StreamingParserComponentConnection
  exactComponent : component = streamingParserComponentConnection
  imported : linuxParserImport ∈ artifact.imports
  finalInstructions : artifact.instructions = Linux.spike4Instructions

structure WasiParserConnection (artifact : WasiArtifact) where
  component : StreamingParserComponentConnection
  exactComponent : component = streamingParserComponentConnection
  imported : gasmHttpParserSymbol ∈ artifact.imports
  finalInstructions : artifact.instructions = Wasm.spike4WasmInstructions

def windowsParserCapability : Capability (WindowsX86_64 AnyEvent) where
  Context := Unit
  providers := spike4WindowsProviders
  establishes := fun artifact _ _ _ => Nonempty (WindowsParserConnection artifact)

def linuxParserCapability : Capability (LinuxX86_64 AnyEvent) where
  Context := Unit
  providers := spike4LinuxProviders
  establishes := fun artifact _ _ _ => Nonempty (LinuxParserConnection artifact)

def wasiParserCapability : Capability WasiPlatform where
  Context := Unit
  providers := spike4WasiProviders
  establishes := fun artifact _ _ _ => Nonempty (WasiParserConnection artifact)

def spike4WindowsCapabilities : CapabilityComposition (WindowsX86_64 AnyEvent) where
  root := windowsParserCapability
  realize := fun _ _ => spike4WindowsRuntime
  realizeSupports := by
    intro context artifact provider membership linked
    let executable := artifact.executable
    let layout := computeSectionLayout executable.textBytes.size executable.rdataBytes.size 512
    let slots := executable.iatFunctionSlots layout.idataRva
    change (match slots[provider.importIndex]? with
      | some address => ∀ state, findIatIndex state address = some provider.iatIndex →
          (@ExternalCallInterceptor.interceptCall X86_64 AnyEvent
            spike4WindowsRuntime address state).isSome
      | none => False)
    change artifact.executable.imports[provider.importIndex]? = some provider.imported ∧
      (match slots[provider.importIndex]? with
      | some address => ((address - (executable.imageBase + layout.idataRva.toUInt64)) / 8).toNat =
          provider.iatIndex
      | none => False) at linked
    rcases linked with ⟨_, slotLinked⟩
    generalize slotEq : slots[provider.importIndex]? = slot at slotLinked ⊢
    cases slot with
    | none => exact False.elim slotLinked
    | some address =>
      intro state found
      simp [windowsParserCapability, spike4WindowsProviders] at membership
      rcases membership with rfl
      change (@ExternalCallInterceptor.interceptCall X86_64 AnyEvent
        spike4WindowsRuntime address state).isSome = true
      simp only [windowsProvider] at found
      change (if findIatIndex state address = some 0 then
        some (windowsParserHook state) else win32Intercept address state).isSome = true
      rw [found]
      rfl

def spike4LinuxCapabilities : CapabilityComposition (LinuxX86_64 AnyEvent) where
  root := linuxParserCapability
  realize := fun _ _ => spike4LinuxRuntime
  realizeSupports := by
    intro context artifact provider membership linked state
    simp [linuxParserCapability, spike4LinuxProviders] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl <;>
      change (@ExternalCallInterceptor.interceptCall X86_64 AnyEvent
        spike4LinuxRuntime linuxSyscallEntry state).isSome = true <;>
      change (if linuxSyscallEntry = linuxSyscallEntry ∧
        state.gprs .rax = gasmHttpLinuxSyscall then some (linuxParserHook state)
        else linuxSyscallIntercept linuxSyscallEntry state).isSome = true <;>
      by_cases parserCall : state.gprs .rax = gasmHttpLinuxSyscall <;>
      simp [parserCall, Gasm.Targets.Linux.linuxSyscallIntercept]
    all_goals split <;> rfl

def spike4WasiCapabilities : CapabilityComposition WasiPlatform where
  root := wasiParserCapability
  realize := fun _ _ => spike4WasiRuntime
  realizeSupports := by
    intro context artifact provider membership linked
    simp [wasiParserCapability, spike4WasiProviders] at membership
    rcases membership with rfl
    intro state
    simp [spike4WasiRuntime, Wasm.spike4WasmImports]

def spike4WindowsArtifact : WindowsX86_64Artifact :=
  { executable := Windows.spike4Executable, instructions := Windows.spike4Instructions }

def spike4LinuxArtifact : LinuxX86_64Artifact :=
  { executable := Linux.spike4Executable
    instructions := Linux.spike4Instructions
    imports := [linuxParserImport] }

def spike4WasiArtifact : WasiArtifact :=
  { module := Wasm.spike4WasmModule
    typeSignatures := Wasm.spike4TypeSignatures
    instructions := Wasm.spike4WasmInstructions
    dataSegments := Wasm.spike4DataSegments
    imports := Wasm.spike4WasmImports
    resources := { fuel := 512, memoryPages := 1 } }

end Spikes.Spike4HttpServer
