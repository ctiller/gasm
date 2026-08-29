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
import Spikes.Spike3SortLines.Input
import Spikes.Spike3SortLines.Model
import Spikes.Spike3SortLines.Platform
import Spikes.Spike3SortLines.Spec
import Spikes.Spike3SortLines.Wasm.Program
import Spikes.Spike3SortLines.Wasm.Outcome

namespace Spikes.Spike3SortLines.Wasm

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.Wasm
open Gasm.Targets.WASI
open Spikes.Spike3SortLines

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Default sample test input string for standard verified execution. -/
def defaultSampleInput : ByteArray :=
  "cherry\r\napple\r\nbanana\r\n".toUTF8

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Finite capability selected at the Spike 3 WASI boundary.  It does not constrain stdin: an
    allocation or execution shortfall is represented in `WasiObservable`, rather than converted
    to a partial output trace. -/
def spike3WasiResources : WasiResourceBudget :=
  { fuel := defaultWasmFuel, memoryPages := 65536 }

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Explicit resource-aware result for the canonical executable trace. -/
def spike3WasmCanonicalOutcome : WasiRunOutcome :=
  runSpike3WasiOutcome defaultSampleInput spike3WasiResources

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Observable Wasm trace on canonical 3-line input. -/
def wasmTraceCanonical : List AnyEvent :=
  runWasiTrace spike3WasmInstructions spike3DataSegments defaultSampleInput ["fd_read", "fd_write", "proc_exit"]

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- High-level model specification trace on canonical 3-line input. -/
def specTraceCanonical : List AnyEvent := [
  Inject.inject (ConsoleEvent.out "apple"),
  Inject.inject (ConsoleEvent.out "\r\n"),
  Inject.inject (ConsoleEvent.out "banana"),
  Inject.inject (ConsoleEvent.out "\r\n"),
  Inject.inject (ConsoleEvent.out "cherry"),
  Inject.inject (ConsoleEvent.out "\r\n"),
  Inject.inject (ProcessEvent.exit 0)
]

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Canonical high-level outcome.  Other finite resource outcomes remain representable by
    `WasiObservable.memoryExhausted` and `.fuelExhausted` in the verified-program contract. -/
def specOutcomeCanonical : WasiObservable AnyEvent :=
  .exited 0 specTraceCanonical

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Formally verified theorem: WebAssembly operational trace on canonical stdin matches specification trace. -/
theorem spike3_wasm_canonical_effect_trace_equivalence :
    (spike3WasmCanonicalOutcome.observable == specOutcomeCanonical) = true := by
  native_decide

-- REF: wasm-exec-runtime#administrative-instructions -- Fuel-safety witness (see the identical
-- check and its rationale in Spikes/Spike1Hello/Wasm/Equivalence.lean): proves the actual Spike 3
-- program on its canonical sample input never exhausts `defaultWasmFuel` under
-- `runWasiTraceState`, rather than merely assuming it.
#guard !Gasm.Targets.Wasm.WasmRunResult.isError
  (runWasiTraceState spike3WasmInstructions spike3DataSegments defaultSampleInput ["fd_read", "fd_write", "proc_exit"])

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- The operational target is parameterized by the canonical environment, not a Bool or a finite
    collection of samples. `environmentInputLines` is its shared executable byte-stream model. -/
def spike3WasmTraceFor (environment : Environment) : WasiObservable AnyEvent :=
  (runWasiOutcome spike3WasmInstructions spike3DataSegments environment.stdin
    ["fd_read", "fd_write", "proc_exit"] environment.incomingRequests spike3WasiResources).observable

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- The exact byte-level input observation which the whole-program sort specification consumes. -/
def spike3WasmInputFor (environment : Environment) : List (List UInt8) :=
  environmentInputLines environment

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- The independent, byte-total specification attached to the canonical environment. -/
def spike3WasmSpec (environment : Environment) : WasiObservable AnyEvent :=
  .exited 0 (spike3ByteSortSpec environment)

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- The Spike 3 WASI profile preserves the environment verbatim at the platform boundary. This
    establishes the loading premise required before the target trace can be coupled to the
    byte-stream specification. -/
theorem spike3_wasi_platform_loads_environment
    (artifact : Spike3WasiArtifact) (environment : Environment) :
    Platform.load (P := Spike3WasiPreview1Platform) artifact environment = environment := rfl

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- The sole admitted shape for the remaining semantic work: a caller must supply the actual
    universal simulation theorem, over arbitrary bytes, before an emitted Spike 3 artifact can be
    classified as verified.  This is a constructor, not a compatibility escape hatch: its only
    proof input is precisely the `VerifiedProgram` trace obligation. -/
def spike3WasiArtifact : WasiArtifact where
  module := spike3WasmModule
  typeSignatures := spike3TypeSignatures
  instructions := spike3WasmInstructions
  dataSegments := spike3DataSegments
  imports := ["fd_read", "fd_write", "proc_exit"]
  resources := spike3WasiResources

def spike3WasiExports : VerifiedExportSet Unit Unit WasiPlatform
    wasiBoundarySpec wasiBoundarySemantics :=
  VerifiedExportSet.withoutCallableEntries Unit Unit WasiPlatform
    wasiBoundarySpec wasiBoundarySemantics spike3WasiArtifact
    (by
      change (["_start", "memory"] : List String).Nodup
      decide)
    (by
      change ([] : List Export) = []
      rfl)
    (by rfl)

def spike3VerifiedWasmProgram
    (traceEquivalence : ∀ environment : Environment,
      spike3WasmTraceFor environment = spike3WasmSpec environment) :
    VerifiedProgram Spike3WasiPreview1Platform spike3WasiCapabilities := {
  name := "Spike 3: Byte-stream line sorter (WebAssembly / WASI Preview 1)"
  artifact := spike3WasiArtifact
  exports := spike3WasiExports
  exportsArtifact := rfl
  artifactConnection := by
    change
      spike3WasmModule.functions.head?.map (fun fn => fn.body) = some spike3WasmInstructions ∧
      spike3WasmModule.dataSegments = spike3DataSegments ∧
      spike3WasmModule.imports.map (fun imported => imported.name) =
        ["fd_read", "fd_write", "proc_exit"]
    constructor
    · rfl
    constructor <;> rfl
  spec := spike3WasmSpec
  importsCovered := by
    intro imported himported
    change imported ∈ ["fd_read", "fd_write", "proc_exit"] at himported
    simp only [List.mem_cons, List.not_mem_nil, or_false] at himported
    rcases himported with rfl | rfl | rfl
    · refine ⟨spike3WasiProvider 0, ?_, ?_⟩
      · simp [spike3WasiCapabilities, spike3WasiReadWriteExitCapability]
      · change (["fd_read", "fd_write", "proc_exit"] : List String)[0]? = some "fd_read"
        rfl
    · refine ⟨spike3WasiProvider 1, ?_, ?_⟩
      · simp [spike3WasiCapabilities, spike3WasiReadWriteExitCapability]
      · change (["fd_read", "fd_write", "proc_exit"] : List String)[1]? = some "fd_write"
        rfl
    · refine ⟨spike3WasiProvider 2, ?_, ?_⟩
      · simp [spike3WasiCapabilities, spike3WasiReadWriteExitCapability]
      · change (["fd_read", "fd_write", "proc_exit"] : List String)[2]? = some "proc_exit"
        rfl
  providersLinked := by
    intro provider hprovider
    simp only [spike3WasiCapabilities, spike3WasiReadWriteExitCapability,
      List.mem_map] at hprovider
    rcases hprovider with ⟨index, hindex, rfl⟩
    rfl
  entryContext := fun _ => ()
  entryEstablished := by intros; trivial
  platformAdmissible := by
    intro
    exact ⟨spike3EncodedWasmBytes, spike3WasmEncoderOk⟩
  traceEquivalence := by
    intro environment
    exact traceEquivalence environment
}

end Spikes.Spike3SortLines.Wasm
