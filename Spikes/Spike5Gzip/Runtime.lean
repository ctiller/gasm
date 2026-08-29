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
import Gasm.Effects.Console
import Gasm.Effects.Process
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.Windows.Linker
import Gasm.Targets.WASI.ABI
import Stdlib.Zlib.Streaming
import Spikes.Spike5Gzip.Spec

namespace Spikes.Spike5Gzip

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.Windows
open Gasm.Targets.Windows.Linker
open Gasm.Targets.Linux
open Gasm.Targets.Wasm
open Gasm.Targets.WASI
open Stdlib.Zlib

/-!
Spike 5 lowers both directions of the streaming Zlib ABI to four calls:
`start`, `push`, `finish`, and a process-level completion call.  The reference
lowering is deliberately buffered, but whole-buffer compression and
decompression remain folds over the streaming primitives in
`Stdlib.Zlib.Streaming`.

Every invocation receives a finite caller-owned allocation scope.  Success,
malformed input, allocation exhaustion, interpreter fuel exhaustion, and WASI
memory refusal remain distinct observations.
-/

inductive CodecDirection where
  | compress
  | decompress
deriving DecidableEq, Repr, Inhabited

def spike5AllocationCapacity : Nat := 1024 * 1024

def spike5AllocationScope : AllocationScope :=
  { capacity := spike5AllocationCapacity }

def bytesAsString (bytes : ByteArray) : String :=
  match String.fromUTF8? bytes with
  | some text => text
  | none => String.ofList (bytes.toList.map (fun byte => Char.ofNat byte.toNat))

def successfulStreamTrace (output : ByteArray) : List AnyEvent :=
  [Inject.inject (ConsoleEvent.out (bytesAsString output)),
   Inject.inject (ProcessEvent.exit 0)]

def malformedStreamTrace : List AnyEvent :=
  [Inject.inject (ProcessEvent.exit 1)]

def exhaustedStreamTrace : List AnyEvent :=
  [Inject.inject (ProcessEvent.exit 2)]

def streamingInvocationResult (direction : CodecDirection)
    (scope : AllocationScope) (input : ByteArray) :=
  match direction with
  | .compress => Sum.inl (compressAll bufferedStreamingZlibCapability scope input)
  | .decompress => Sum.inr (decompressAll bufferedStreamingZlibCapability scope input)

def streamingInvocationTrace (direction : CodecDirection)
    (scope : AllocationScope) (input : ByteArray) : List AnyEvent :=
  match direction with
  | .compress =>
    match compressAll bufferedStreamingZlibCapability scope input with
    | .success output _ => successfulStreamTrace output
    | .rejected error _ => nomatch error
    | .resourceExhausted _ => exhaustedStreamTrace
  | .decompress =>
    match decompressAll bufferedStreamingZlibCapability scope input with
    | .success output _ => successfulStreamTrace output
    | .rejected _ _ => malformedStreamTrace
    | .resourceExhausted _ => exhaustedStreamTrace

theorem streaming_compression_success_is_gzip (scope : AllocationScope)
    (input output : ByteArray) (finalScope : AllocationScope)
    (h : compressAll bufferedStreamingZlibCapability scope input =
      .success output finalScope) :
    gzipDecompress output = .ok input :=
  compressAll_sound bufferedStreamingZlibCapability scope input output finalScope h

theorem streaming_decompression_success_is_gunzip (scope : AllocationScope)
    (input output : ByteArray) (finalScope : AllocationScope)
    (h : decompressAll bufferedStreamingZlibCapability scope input =
      .success output finalScope) :
    gzipDecompress input = .ok output :=
  decompressAll_sound bufferedStreamingZlibCapability scope input output finalScope h

def streamImportNames : CodecDirection → List String
  | .compress =>
    ["gasm_zlib_compress_start", "gasm_zlib_compress_push",
      "gasm_zlib_compress_finish", "gasm_process_exit"]
  | .decompress =>
    ["gasm_zlib_decompress_start", "gasm_zlib_decompress_push",
      "gasm_zlib_decompress_finish", "gasm_process_exit"]

def streamWindowsImports (direction : CodecDirection) : List Win32Function :=
  (streamImportNames direction).map fun name =>
    { moduleName := "gasm_zlib.dll", symbolName := name }

def nativeProviderProtocol (direction : CodecDirection) (index : Nat) :
    ProviderProtocolKey :=
  { protocolNamespace := "stdlib.zlib.streaming"
    operation := (streamImportNames direction).getD index "invalid"
    version := 1 }

def windowsStreamSymbolicProgram (direction : CodecDirection) : List SymbolicInstr :=
  (streamImportNames direction).map call_import

def windowsStreamLinked (direction : CodecDirection) : LinkedWindowsProgram :=
  linkWindowsProgramMultiDll (windowsStreamSymbolicProgram direction) []
    [("gasm_zlib.dll", streamImportNames direction)]

def windowsStreamArtifact (direction : CodecDirection) : WindowsX86_64Artifact :=
  { executable := (windowsStreamLinked direction).executable
    instructions := (windowsStreamLinked direction).instructions }

def windowsStreamProviders (direction : CodecDirection) :
    List WindowsX86_64Provider :=
  (streamWindowsImports direction).zipIdx.map fun (imported, index) =>
    { protocol := nativeProviderProtocol direction index
      imported, importIndex := index, iatIndex := index }

def windowsArtifactCallTarget (artifact : WindowsX86_64Artifact) (index : Nat) : Address :=
  let executable := artifact.executable
  let layout := computeSectionLayout executable.textBytes.size executable.rdataBytes.size 512
  (executable.iatFunctionSlots layout.idataRva)[index]?.getD 0

def windowsProviderCallTarget (artifact : WindowsX86_64Artifact)
    (provider : WindowsX86_64Provider) : Option Address :=
  let executable := artifact.executable
  let layout := computeSectionLayout executable.textBytes.size executable.rdataBytes.size 512
  (executable.iatFunctionSlots layout.idataRva)[provider.importIndex]?

def linuxCallDisplacements : List Int32 := [0x10000, 0x20000, 0x30000, 0x40000]

def linuxStreamInstructions : List X86_64Instr :=
  linuxCallDisplacements.map fun displacement => call_rel32 displacement

def linuxStreamLinked : LinkedLinuxProgram :=
  linkLinuxProgramStatic (linuxStreamInstructions.map SymbolicInstr.concrete)

def linuxStreamRequirements (direction : CodecDirection) :
    List LinuxLibraryRequirement :=
  (streamImportNames direction).map fun symbol =>
    { library := "gasm-zlib-streaming"
      symbol
      protocolVersion := 1 }

def linuxStreamArtifact (direction : CodecDirection) : LinuxX86_64Artifact :=
  { executable := linuxStreamLinked.executable
    instructions := linuxStreamLinked.instructions
    imports := linuxStreamRequirements direction }

def linuxStaticCallTarget (index : Nat) : Address :=
  let entryRip := linuxStreamLinked.executable.load.rip
  let instructionRip := entryRip + (index * 5).toUInt64
  instructionRip + 5 + signExtend32To64 (linuxCallDisplacements.getD index 0)

theorem linux_find_call_zero :
    (List.range 4).find? (fun index =>
      linuxStaticCallTarget index == linuxStaticCallTarget 0) = some 0 := by
  native_decide

theorem linux_find_call_one :
    (List.range 4).find? (fun index =>
      linuxStaticCallTarget index == linuxStaticCallTarget 1) = some 1 := by
  native_decide

theorem linux_find_call_two :
    (List.range 4).find? (fun index =>
      linuxStaticCallTarget index == linuxStaticCallTarget 2) = some 2 := by
  native_decide

theorem linux_find_call_three :
    (List.range 4).find? (fun index =>
      linuxStaticCallTarget index == linuxStaticCallTarget 3) = some 3 := by
  native_decide

def linuxStreamProviders (direction : CodecDirection) :
    List LinuxX86_64Provider :=
  (linuxStreamRequirements direction).zipIdx.map fun (requirement, index) =>
    { requirement
      protocol := nativeProviderProtocol direction index
      instructionIndex := index
      callTarget := linuxStaticCallTarget index }

structure StreamingInvocationContext where
  direction : CodecDirection
  input : ByteArray
  scope : AllocationScope
  entryRip : Address

def returnFromNativeCall (state : X86_64MachineState) : X86_64MachineState :=
  let (returnRip, popped) := state.pop64
  { popped with rip := returnRip }

def withPhase (state : X86_64MachineState) (phase : UInt64) : X86_64MachineState :=
  (returnFromNativeCall state).setGpr64 .r15 phase

def streamResultEvent (context : StreamingInvocationContext) :
    Option AnyEvent × Bool :=
  match context.direction with
  | .compress =>
    match compressAll bufferedStreamingZlibCapability context.scope context.input with
    | .success output _ => (some (Inject.inject (ConsoleEvent.out (bytesAsString output))), true)
    | .rejected error _ => nomatch error
    | .resourceExhausted _ => (some (Inject.inject (ProcessEvent.exit 2)), false)
  | .decompress =>
    match decompressAll bufferedStreamingZlibCapability context.scope context.input with
    | .success output _ => (some (Inject.inject (ConsoleEvent.out (bytesAsString output))), true)
    | .rejected _ _ => (some (Inject.inject (ProcessEvent.exit 1)), false)
    | .resourceExhausted _ => (some (Inject.inject (ProcessEvent.exit 2)), false)

def linuxCallTarget (context : StreamingInvocationContext) (index : Nat) : Address :=
  let instructionRip := context.entryRip + (index * 5).toUInt64
  let displacement := linuxCallDisplacements.getD index 0
  instructionRip + 5 + signExtend32To64 displacement

def nativeCallIndex (context : StreamingInvocationContext)
    (address : Address) (state : X86_64MachineState) : Option Nat :=
  match Gasm.Targets.Windows.findIatIndex state address with
  | some index => if index < 4 then some index else none
  | none => (List.range 4).find? fun index =>
      linuxStaticCallTarget index == address

def streamingNativeCall
    (resolveCall : Address → X86_64MachineState → Option Nat)
    (context : StreamingInvocationContext) (address : Address)
    (state : X86_64MachineState) : Option (X86_64MachineState × Option AnyEvent) :=
    match resolveCall address state with
    | some 0 => some (withPhase state 1, none)
    | some 1 =>
      if state.gprs .r15 == 1 then some (withPhase state 2, none)
      else some (state, some (Inject.inject (ProcessEvent.exit 3)))
    | some 2 =>
      if state.gprs .r15 == 2 then
        let (event, continueExecution) := streamResultEvent context
        if continueExecution then
          some (withPhase state 3, event)
        else
          some (state, event)
      else
        some (state, some (Inject.inject (ProcessEvent.exit 3)))
    | some 3 =>
      if state.gprs .r15 == 3 then
        some (state, some (Inject.inject (ProcessEvent.exit 0)))
      else
        some (state, some (Inject.inject (ProcessEvent.exit 3)))
    | _ => none

def streamingNativeInterceptorWith
    (resolveCall : Address → X86_64MachineState → Option Nat)
    (context : StreamingInvocationContext) :
    ExternalCallInterceptor X86_64 AnyEvent where
  interceptCall := streamingNativeCall resolveCall context

@[simp] theorem streamingNativeInterceptorWith_call
    (resolveCall : Address → X86_64MachineState → Option Nat)
    (context : StreamingInvocationContext) (address : Address)
    (state : X86_64MachineState) :
    @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (streamingNativeInterceptorWith resolveCall context) address state =
      streamingNativeCall resolveCall context address state := by
  rfl

def windowsStreamingInterceptor (_artifact : WindowsX86_64Artifact)
    (context : StreamingInvocationContext) :
    ExternalCallInterceptor X86_64 AnyEvent :=
  streamingNativeInterceptorWith (fun address state =>
    match Gasm.Targets.Windows.findIatIndex state address with
    | some index => if index < 4 then some index else none
    | none => none) context

@[simp] theorem windowsStreamingInterceptor_call
    (artifact : WindowsX86_64Artifact) (context : StreamingInvocationContext)
    (address : Address) (state : X86_64MachineState) :
    @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (windowsStreamingInterceptor artifact context) address state =
      @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
        (streamingNativeInterceptorWith (fun callAddress callState =>
          match Gasm.Targets.Windows.findIatIndex callState callAddress with
          | some index => if index < 4 then some index else none
          | none => none) context) address state := by
  rfl

def linuxStreamingInterceptor (context : StreamingInvocationContext) :
    ExternalCallInterceptor X86_64 AnyEvent :=
  streamingNativeInterceptorWith (fun address _ =>
    (List.range 4).find? fun index => linuxStaticCallTarget index == address) context

def windowsStreamingCapability (direction : CodecDirection) :
    Capability (WindowsX86_64 AnyEvent) where
  Context := StreamingInvocationContext
  providers := windowsStreamProviders direction
  establishes := fun artifact environment state context =>
    artifact = windowsStreamArtifact direction ∧
      context = StreamingInvocationContext.mk direction environment.stdin
        spike5AllocationScope state.rip

def windowsStreamingCapabilities (direction : CodecDirection) :
    CapabilityComposition (WindowsX86_64 AnyEvent) where
  root := windowsStreamingCapability direction
  realize := windowsStreamingInterceptor
  realizeSupports := by
    intro context artifact provider hprovider hlinked
    change StreamingInvocationContext at context
    change (match windowsProviderCallTarget artifact provider with
      | some address => ∀ state, _
      | none => False)
    rcases hlinked with ⟨himport, hphysical⟩
    cases direction <;>
      simp [windowsStreamingCapability, windowsStreamProviders, streamWindowsImports,
        streamImportNames, nativeProviderProtocol] at hprovider
    all_goals
      rcases hprovider with rfl | rfl | rfl | rfl
    all_goals
      simp only [windowsProviderCallTarget]
      split
      · intro state hindex
        unfold windowsStreamingInterceptor streamingNativeInterceptorWith streamingNativeCall
        by_cases hphaseOne : state.gprs .r15 = 1 <;>
          by_cases hphaseTwo : state.gprs .r15 = 2 <;>
          by_cases hphaseThree : state.gprs .r15 = 3 <;>
          by_cases hcontinue : (streamResultEvent context).snd <;>
          simp [hindex, hphaseOne, hphaseTwo, hphaseThree, hcontinue]
      · simp_all [windowsProviderCallTarget]

def linuxStreamingCapability (direction : CodecDirection) :
    Capability (LinuxX86_64 AnyEvent) where
  Context := StreamingInvocationContext
  providers := linuxStreamProviders direction
  establishes := fun artifact environment state context =>
    artifact = linuxStreamArtifact direction ∧
      context = StreamingInvocationContext.mk direction environment.stdin
        spike5AllocationScope state.rip

def linuxStreamingCapabilities (direction : CodecDirection) :
    CapabilityComposition (LinuxX86_64 AnyEvent) where
  root := linuxStreamingCapability direction
  realize := fun _ => linuxStreamingInterceptor
  realizeSupports := by
    intro context artifact provider hprovider hlinked
    change StreamingInvocationContext at context
    cases direction <;>
      simp [linuxStreamingCapability, linuxStreamProviders, linuxStreamRequirements,
        streamImportNames, nativeProviderProtocol] at hprovider
    all_goals
      rcases hprovider with rfl | rfl | rfl | rfl <;> intro state <;>
        unfold linuxStreamingInterceptor streamingNativeInterceptorWith streamingNativeCall <;>
        simp [linux_find_call_zero, linux_find_call_one, linux_find_call_two,
          linux_find_call_three] <;> try split <;> simp
    all_goals
      by_cases hphase : state.gprs .r15 = 2
      · simp [hphase]
        cases hcontinue : (streamResultEvent context).snd <;> simp [hcontinue]
      · simp [hphase]

structure WasiStreamingContext where
  direction : CodecDirection
  input : ByteArray
  scope : AllocationScope

def wasiStreamingHost (context : WasiStreamingContext) : WasiHostRuntime :=
  fun _ index state =>
    match index with
    | 0 => (state, .next)
    | 1 => (state, .next)
    | 2 =>
        match context.direction with
        | .compress =>
          match compressAll bufferedStreamingZlibCapability context.scope context.input with
          | .success output _ =>
            ({ state with events := state.events ++
              [Inject.inject (ConsoleEvent.out (bytesAsString output))] }, .next)
          | .rejected error _ => nomatch error
          | .resourceExhausted _ =>
            ({ state with exitCode := some 2, events := state.events ++
              [Inject.inject (ProcessEvent.exit 2)] }, .ret)
        | .decompress =>
          match decompressAll bufferedStreamingZlibCapability context.scope context.input with
          | .success output _ =>
            ({ state with events := state.events ++
              [Inject.inject (ConsoleEvent.out (bytesAsString output))] }, .next)
          | .rejected _ _ =>
            ({ state with exitCode := some 1, events := state.events ++
              [Inject.inject (ProcessEvent.exit 1)] }, .ret)
          | .resourceExhausted _ =>
            ({ state with exitCode := some 2, events := state.events ++
              [Inject.inject (ProcessEvent.exit 2)] }, .ret)
    | 3 =>
      ({ state with exitCode := some 0, events := state.events ++
        [Inject.inject (ProcessEvent.exit 0)] }, .ret)
    | _ => ({ state with trapped := true }, .ret)

def wasiStreamInstructions : List WasmInstr :=
  [.call 0, .call 1, .call 2, .call 3]

def wasiStreamStartFunction : WasmFunction :=
  { name := "_start"
    params := []
    results := []
    locals := []
    body := wasiStreamInstructions
    exportName := some "_start" }

def wasiStreamModule (direction : CodecDirection) : WasmModule :=
  let imports : List Gasm.Targets.Wasm.Import :=
    (streamImportNames direction).zipIdx.map fun (name, index) =>
      { module := "gasm:zlib/streaming"
        name := name
        desc := .func index }
  { imports := imports
    functions := [wasiStreamStartFunction]
    memoryPages := some 1
    dataSegments := []
    exports := [] }

def emptyFunctionType : FuncType := { params := [], results := [] }

def wasiStreamTypeSignatures : List FuncType :=
  [emptyFunctionType, emptyFunctionType, emptyFunctionType,
    emptyFunctionType, emptyFunctionType]

def wasiStreamArtifact (direction : CodecDirection) : WasiArtifact :=
  { module := wasiStreamModule direction
    typeSignatures := wasiStreamTypeSignatures
    instructions := wasiStreamInstructions
    dataSegments := []
    imports := streamImportNames direction
    resources := { fuel := 16, memoryPages := 1 } }

theorem empty_wasi_memory_size : WasmMem.size (initWasmMemory []) = 65536 := by
  native_decide

theorem empty_wasi_initial_pages :
    (WasmMem.size (initWasmMemory []) + 65535) / 65536 = 1 := by
  native_decide

theorem one_wasi_page_available : Nat.min 1 65536 = 1 := by decide

theorem one_wasi_page_not_exhausted : ¬ (1 : Nat) > 1 := by decide

def wasiStreamingCapability (direction : CodecDirection) :
    Capability WasiPlatform where
  Context := WasiStreamingContext
  providers := (streamImportNames direction).zipIdx.map fun (_, index) =>
    { protocol := .library (nativeProviderProtocol direction index)
      imports := streamImportNames direction
      importIndex := index }
  establishes := fun artifact environment _ context =>
    artifact = wasiStreamArtifact direction ∧
      context = WasiStreamingContext.mk direction environment.stdin spike5AllocationScope

def wasiStreamingCapabilities (direction : CodecDirection) :
    CapabilityComposition WasiPlatform where
  root := wasiStreamingCapability direction
  realize := fun _ => wasiStreamingHost
  realizeSupports := by
    intro context artifact provider hprovider hlinked
    change WasiStreamingContext at context
    cases direction <;>
      simp [wasiStreamingCapability, streamImportNames, nativeProviderProtocol] at hprovider
    all_goals
      rcases hprovider with rfl | rfl | rfl | rfl <;>
        intro state <;> simp [wasiStreamingHost]
    all_goals
      cases context.direction with
      | compress =>
        cases hresult : compressAll bufferedStreamingZlibCapability
          context.scope context.input with
        | rejected error scope => exact Empty.elim error
        | resourceExhausted scope => simp [wasiStreamingHost, hresult]
        | success output scope => simp [wasiStreamingHost, hresult]
      | decompress =>
        cases hresult : decompressAll bufferedStreamingZlibCapability
          context.scope context.input <;> simp [wasiStreamingHost, hresult]

def wasiStreamingSpec (direction : CodecDirection) (environment : Environment) :
    WasiObservable AnyEvent :=
  match direction with
  | .compress =>
    match compressAll bufferedStreamingZlibCapability spike5AllocationScope environment.stdin with
    | .success output _ => .exited 0 (successfulStreamTrace output)
    | .rejected error _ => nomatch error
    | .resourceExhausted _ => .exited 2 exhaustedStreamTrace
  | .decompress =>
    match decompressAll bufferedStreamingZlibCapability spike5AllocationScope environment.stdin with
    | .success output _ => .exited 0 (successfulStreamTrace output)
    | .rejected _ _ => .exited 1 malformedStreamTrace
    | .resourceExhausted _ => .exited 2 exhaustedStreamTrace

def wasiStreamingEntryContext (direction : CodecDirection) (environment : Environment) :
    WasiStreamingContext :=
  .mk direction environment.stdin spike5AllocationScope

theorem wasi_streaming_trace_equivalence (direction : CodecDirection)
    (environment : Environment) :
    Platform.run (P := WasiPlatform)
      (wasiStreamingHost (wasiStreamingEntryContext direction environment))
      (wasiStreamArtifact direction) environment =
        wasiStreamingSpec direction environment := by
  cases direction with
  | compress =>
    cases hresult : compressAll bufferedStreamingZlibCapability
      spike5AllocationScope environment.stdin with
    | rejected error scope => exact Empty.elim error
    | resourceExhausted scope =>
      change (runWasiOutcomeWithHost
        (wasiStreamingHost (wasiStreamingEntryContext .compress environment))
        wasiStreamInstructions [] environment.stdin (streamImportNames .compress)
        environment.incomingRequests { fuel := 16, memoryPages := 1 }).observable = _
      unfold runWasiOutcomeWithHost
      simp only [empty_wasi_initial_pages, one_wasi_page_available,
        one_wasi_page_not_exhausted, ↓reduceIte]
      simp only [evalInstrs, evalInstrMatch, evalLeafInstr, wasiStreamInstructions,
        wasiStreamingHost, wasiStreamingEntryContext, hresult, WasiRunOutcome.ofResult,
        WasiRunOutcome.observable, wasiStreamingSpec, exhaustedStreamTrace]
      simp only [Bool.or_false, Option.isSome_none, Bool.false_eq_true,
        if_false, List.nil_append]
    | success output scope =>
      change (runWasiOutcomeWithHost
        (wasiStreamingHost (wasiStreamingEntryContext .compress environment))
        wasiStreamInstructions [] environment.stdin (streamImportNames .compress)
        environment.incomingRequests { fuel := 16, memoryPages := 1 }).observable = _
      unfold runWasiOutcomeWithHost
      simp only [empty_wasi_initial_pages, one_wasi_page_available,
        one_wasi_page_not_exhausted, ↓reduceIte]
      simp only [evalInstrs, evalInstrMatch, evalLeafInstr, wasiStreamInstructions,
        wasiStreamingHost, wasiStreamingEntryContext, hresult, WasiRunOutcome.ofResult,
        WasiRunOutcome.observable, wasiStreamingSpec, successfulStreamTrace]
      simp only [Bool.or_false, Option.isSome_none, Bool.false_eq_true,
        if_false, List.nil_append, List.singleton_append]

  | decompress =>
    cases hresult : decompressAll bufferedStreamingZlibCapability
      spike5AllocationScope environment.stdin with
    | rejected message scope =>
      change (runWasiOutcomeWithHost
        (wasiStreamingHost (wasiStreamingEntryContext .decompress environment))
        wasiStreamInstructions [] environment.stdin (streamImportNames .decompress)
        environment.incomingRequests { fuel := 16, memoryPages := 1 }).observable = _
      unfold runWasiOutcomeWithHost
      simp only [empty_wasi_initial_pages, one_wasi_page_available,
        one_wasi_page_not_exhausted, ↓reduceIte]
      simp only [evalInstrs, evalInstrMatch, evalLeafInstr, wasiStreamInstructions,
        wasiStreamingHost, wasiStreamingEntryContext, hresult, WasiRunOutcome.ofResult,
        WasiRunOutcome.observable, wasiStreamingSpec, malformedStreamTrace]
      simp only [Bool.or_false, Option.isSome_none, Bool.false_eq_true,
        if_false, List.nil_append]
    | resourceExhausted scope =>
      change (runWasiOutcomeWithHost
        (wasiStreamingHost (wasiStreamingEntryContext .decompress environment))
        wasiStreamInstructions [] environment.stdin (streamImportNames .decompress)
        environment.incomingRequests { fuel := 16, memoryPages := 1 }).observable = _
      unfold runWasiOutcomeWithHost
      simp only [empty_wasi_initial_pages, one_wasi_page_available,
        one_wasi_page_not_exhausted, ↓reduceIte]
      simp only [evalInstrs, evalInstrMatch, evalLeafInstr, wasiStreamInstructions,
        wasiStreamingHost, wasiStreamingEntryContext, hresult, WasiRunOutcome.ofResult,
        WasiRunOutcome.observable, wasiStreamingSpec, exhaustedStreamTrace]
      simp only [Bool.or_false, Option.isSome_none, Bool.false_eq_true,
        if_false, List.nil_append]
    | success output scope =>
      change (runWasiOutcomeWithHost
        (wasiStreamingHost (wasiStreamingEntryContext .decompress environment))
        wasiStreamInstructions [] environment.stdin (streamImportNames .decompress)
        environment.incomingRequests { fuel := 16, memoryPages := 1 }).observable = _
      unfold runWasiOutcomeWithHost
      simp only [empty_wasi_initial_pages, one_wasi_page_available,
        one_wasi_page_not_exhausted, ↓reduceIte]
      simp only [evalInstrs, evalInstrMatch, evalLeafInstr, wasiStreamInstructions,
        wasiStreamingHost, wasiStreamingEntryContext, hresult, WasiRunOutcome.ofResult,
        WasiRunOutcome.observable, wasiStreamingSpec, successfulStreamTrace]
      simp only [Bool.or_false, Option.isSome_none, Bool.false_eq_true,
        if_false, List.nil_append, List.singleton_append]

def wasiStreamExports (direction : CodecDirection) :=
  VerifiedExportSet.withoutCallableEntries Unit Unit WasiPlatform wasiBoundarySpec
    wasiBoundarySemantics (wasiStreamArtifact direction)
    (by
      change ((wasiPublicEntries (wasiStreamArtifact direction)).map
        (fun entry => entry.name)).Nodup
      cases direction <;> native_decide)
    (by
      change wasiCallableEntries (wasiStreamArtifact direction) = []
      cases direction <;> native_decide)
    (by rfl)

theorem wasi_stream_artifact_connected (direction : CodecDirection) :
    Platform.artifactConnected (P := WasiPlatform) (wasiStreamArtifact direction) := by
  cases direction <;>
    simp [Platform.artifactConnected, wasiStreamArtifact, wasiStreamModule,
      wasiStreamStartFunction, wasiStreamInstructions, streamImportNames]

def wasiStreamEmittedBytes (direction : CodecDirection) : ByteArray :=
  match emitWasmBinary (wasiStreamArtifact direction).module
      (wasiStreamArtifact direction).typeSignatures with
  | .ok bytes => bytes
  | .error _ => ByteArray.empty

theorem wasi_stream_emit_eq (direction : CodecDirection) :
    emitWasmBinary (wasiStreamArtifact direction).module
      (wasiStreamArtifact direction).typeSignatures =
        .ok (wasiStreamEmittedBytes direction) := by
  cases direction <;> rfl

theorem wasi_stream_artifact_emits (direction : CodecDirection) :
    ∃ bytes, emitWasmBinary (wasiStreamArtifact direction).module
      (wasiStreamArtifact direction).typeSignatures = .ok bytes := by
  exact ⟨wasiStreamEmittedBytes direction, wasi_stream_emit_eq direction⟩

def wasiStreamingVerifiedProgram (direction : CodecDirection) :
    VerifiedProgram WasiPlatform (wasiStreamingCapabilities direction) where
  name := match direction with
    | .compress => "spike5_gzip_wasi"
    | .decompress => "spike5_gunzip_wasi"
  artifact := wasiStreamArtifact direction
  exports := wasiStreamExports direction
  exportsArtifact := rfl
  artifactConnection := wasi_stream_artifact_connected direction
  spec := wasiStreamingSpec direction
  importsCovered := by
    intro imported himport
    change imported ∈ streamImportNames direction at himport
    cases direction <;> simp [streamImportNames] at himport
    all_goals
      rcases himport with rfl | rfl | rfl | rfl <;>
        simp [wasiStreamingCapabilities, wasiStreamingCapability, streamImportNames,
          nativeProviderProtocol, Platform.providerProvides]
  providersLinked := by
    intro provider hprovider
    change provider ∈ (wasiStreamingCapability direction).providers at hprovider
    change provider.imports = (wasiStreamArtifact direction).imports
    cases direction <;>
      simp [wasiStreamingCapability, streamImportNames,
        nativeProviderProtocol] at hprovider
    all_goals
      rcases hprovider with rfl | rfl | rfl | rfl <;> rfl
  entryContext := wasiStreamingEntryContext direction
  entryEstablished := by intro environment; exact ⟨rfl, rfl⟩
  platformAdmissible := by
    intro environment
    exact wasi_stream_artifact_emits direction
  traceEquivalence := wasi_streaming_trace_equivalence direction

end Spikes.Spike5Gzip
