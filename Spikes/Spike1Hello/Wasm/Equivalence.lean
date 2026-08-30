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
import Gasm.Core.Types
import Gasm.Core.Verification
import Gasm.Effects.Inject
import Gasm.Effects.Trace
import Gasm.Targets.Wasm.Types
import Gasm.Targets.Wasm.AST
import Gasm.Targets.WASI.ABI
import Spikes.Spike1Hello.Spec
import Spikes.Spike1Hello.Wasm.Program

namespace Spikes.Spike1Hello.Wasm

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.Wasm
open Gasm.Targets.WASI

set_option maxRecDepth 10000 in
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Structural clean-exit and trace certificate for the exact Spike 1 artifact budget.  Loader,
    host-call, and instruction-sequence facts are composed at their owning layers; no whole-page
    evaluation or native proof oracle is involved. -/
theorem spike1_wasm_canonical_effect_trace_equivalence :
    (runWasiOutcome spike1WasmInstructions spike1DataSegments ByteArray.empty
      ["fd_write", "proc_exit"] [] { fuel := 100, memoryPages := 65536 }).observable =
        .exited 0 (runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)) := by
  obtain ⟨writtenMemory, hwritten⟩ := spike1InitialMemory_nwritten
  have hwrite := wasiHostCall_fd_write_single
    (memory := spike1InitialMemory) (writtenMemory := writtenMemory)
    (memMax := some 65536) (text := "Hello, World!\n")
    (len := helloMessage.size.toUInt32)
    spike1InitialMemory_ciovec (by decide) (by exact spike1InitialMemory_payload) hwritten
  have hwrite' :
      wasiHostCall ["fd_write", "proc_exit"] 0
          { stack := [.i32 8, .i32 1, .i32 0, .i32 1],
            memory := initWasmMemory spike1DataSegments, memMax := some 65536 } =
        ({ stack := [.i32 0], memory := writtenMemory, memMax := some 65536,
            events := [Inject.inject (ConsoleEvent.out "Hello, World!\n")] }, .next) := by
    simpa [spike1InitialMemory] using hwrite
  have hmodel : runModelTrace (helloWorldSpec : TraceM AnyEvent Unit) =
      [Inject.inject (ConsoleEvent.out "Hello, World!\n"),
       Inject.inject (ProcessEvent.exit 0)] := by
    rfl
  unfold runWasiOutcome runWasiOutcomeWithHost
  dsimp only
  simp only [initWasmMemory_size]
  simp
  rw [show spike1WasmInstructions =
    [.i32_const 1, .i32_const 0, .i32_const 1, .i32_const 8,
     .call 0, .drop, .i32_const 0, .call 1] from rfl]
  rw [evalWasiWriteThenExit (initWasmMemory spike1DataSegments) writtenMemory
    (some 65536) "Hello, World!\n" hwrite']
  simp [hmodel, WasiRunOutcome.ofResult, WasiRunOutcome.observable]

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- The exact emitted module, operational program, import layout, and finite runtime resources. -/
def spike1WasiArtifact : WasiArtifact where
  module := spike1WasmModule
  typeSignatures := spike1TypeSignatures
  instructions := spike1WasmInstructions
  dataSegments := spike1DataSegments
  imports := ["fd_write", "proc_exit"]
  resources := { fuel := 100, memoryPages := 65536 }

def spike1WasiExports : VerifiedExportSet Unit Unit WasiPlatform
    wasiBoundarySpec wasiBoundarySemantics :=
  VerifiedExportSet.withoutCallableEntries Unit Unit WasiPlatform
    wasiBoundarySpec wasiBoundarySemantics spike1WasiArtifact
    (by
      change (["_start", "memory"] : List String).Nodup
      decide)
    (by
      change ([] : List Export) = []
      rfl)
    (by rfl)

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- One explicit clean-exit certificate for the canonical input-erased execution. -/
theorem spike1_wasi_reference_outcome :
    (runWasiOutcome spike1WasmInstructions spike1DataSegments ByteArray.empty
      ["fd_write", "proc_exit"] []
      { fuel := 100, memoryPages := 65536 }).observable =
        .exited 0 (runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)) := by
  exact spike1_wasm_canonical_effect_trace_equivalence

private def spike1WasiEmittedBytes : ByteArray :=
  match spike1WasmBinary with
  | .ok bytes => bytes
  | .error _ => ByteArray.empty

private theorem spike1_wasi_emits :
    emitWasmBinary spike1WasmModule spike1TypeSignatures =
      .ok spike1WasiEmittedBytes := by
  set_option maxRecDepth 100000 in
    rfl

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Artifact-owned serialization and public-manifest certificate. -/
def spike1WasiArtifactCertificate : ProgramArtifactCertificate WasiPlatform where
  artifact := spike1WasiArtifact
  exports := spike1WasiExports
  exportsArtifact := rfl
  artifactConnection := by
    constructor
    · rfl
    constructor <;> rfl

/-- Provider-owned import coverage and final-link certificate. -/
theorem spike1WasiProviderCertificate :
    ProgramProviderCertificate WasiPlatform wasiHostCapabilities spike1WasiArtifact where
  importsCovered := by
    intro imported himported
    change imported ∈ ["fd_write", "proc_exit"] at himported
    simp only [List.mem_cons, List.not_mem_nil, or_false] at himported
    rcases himported with rfl | rfl
    · let provider : WasiProvider :=
        { protocol := .preview1, imports := ["fd_write", "proc_exit"], importIndex := 0 }
      refine ⟨provider, ?_, ?_⟩
      · simp [provider, wasiHostCapabilities, wasiHostCapability]
      · rfl
    · let provider : WasiProvider :=
        { protocol := .preview1, imports := ["fd_write", "proc_exit"], importIndex := 1 }
      refine ⟨provider, ?_, ?_⟩
      · simp [provider, wasiHostCapabilities, wasiHostCapability]
      · rfl
  providersLinked := by
    intro provider hprovider
    simp only [wasiHostCapabilities, wasiHostCapability, List.mem_cons,
      List.not_mem_nil, or_false] at hprovider
    rcases hprovider with rfl | rfl <;> rfl

/-- Root-entry capability establishment. -/
def spike1WasiEntryCertificate :
    ProgramEntryCertificate WasiPlatform wasiHostCapabilities spike1WasiArtifact where
  entryContext := fun _ => { fuel := 100, memoryPages := 65536 }
  entryEstablished := by intro; trivial

/-- Artifact serialization is the platform admissibility fact for WASI emission. -/
theorem spike1WasiAdmissibilityCertificate :
    ProgramAdmissibilityCertificate WasiPlatform wasiHostCapabilities spike1WasiArtifact
      spike1WasiEntryCertificate where
  platformAdmissible := by
    intro
    refine ⟨spike1WasiEmittedBytes, ?_⟩
    exact spike1_wasi_emits

/-- Universal behavior, composed from one closed outcome and the platform frame theorem. -/
def spike1WasiBehaviorCertificate :
    ProgramBehaviorCertificate WasiPlatform wasiHostCapabilities spike1WasiArtifact
      spike1WasiEntryCertificate where
  spec := fun _ => .exited 0 (runModelTrace (helloWorldSpec : TraceM AnyEvent Unit))
  traceEquivalence := by
    intro environment
    change (runWasiOutcome spike1WasmInstructions spike1DataSegments environment.stdin
      ["fd_write", "proc_exit"] environment.incomingRequests
      { fuel := 100, memoryPages := 65536 }).observable = _
    rw [runWasiOutcome_output_only_observable_external_input_frame]
    exact spike1_wasi_reference_outcome

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Sole universal whole-program contract for Spike 1 (Hello World WASI). -/
def spike1VerifiedWasmProgram : VerifiedProgram WasiPlatform wasiHostCapabilities :=
  VerifiedProgram.compose "Spike 1: Hello World (WebAssembly / WASI Preview 1)"
    spike1WasiArtifactCertificate spike1WasiProviderCertificate spike1WasiEntryCertificate
    spike1WasiAdmissibilityCertificate spike1WasiBehaviorCertificate

end Spikes.Spike1Hello.Wasm
