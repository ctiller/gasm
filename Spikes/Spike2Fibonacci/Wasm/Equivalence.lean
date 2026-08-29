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
import Gasm.Targets.Wasm.Semantics
import Gasm.Targets.WASI.ABI
import Spikes.Spike2Fibonacci.Spec
import Spikes.Spike2Fibonacci.Wasm.Program
import Spikes.Spike2Fibonacci.Wasm.LoopInvariant

namespace Spikes.Spike2Fibonacci.Wasm

open Gasm.Core
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.Wasm
open Gasm.Targets.WASI
open Spikes.Spike2Fibonacci

open Gasm.Core.Platform

/- REF: docs/ABI_CONTEXT.md#3-nominal-placement-free-contracts -/
/-- Nominal typed boundary published by the Spike 2 component artifact. -/
inductive Spike2WasiBoundaryKey where
  | fibIter
  deriving DecidableEq

@[instance_reducible] def spike2WasiBoundarySpec : BoundaryContextSpec Unit Spike2WasiBoundaryKey where
  Args := fun | .fibIter => UInt64
  Binding := fun | .fibIter => Unit
  Result := fun | .fibIter => UInt64
  Outcome := fun | .fibIter => ControlSignal
  ObligationFragment := fun | .fibIter => Unit
  requiredObligations := fun _ _ _ => ()
  emittedObligations := fun _ _ _ _ _ => ()
  requires := fun _ _ _ _ => True
  transitions := fun
    | .fibIter, n, _, result, outcome, _, _ =>
        result = (fibIter n.toNat).toUInt64 ∧ outcome = .next

@[instance_reducible] local instance spike2BoundarySpecInstance :
    BoundaryContextSpec Unit Spike2WasiBoundaryKey := spike2WasiBoundarySpec

inductive Spike2WasiBoundaryTarget

def spike2BoundaryFuel (state : WasmMachineState) : Nat :=
  match state.locals with
  | .i64 n :: _ => n.toNat + 26
  | _ => 26

@[instance_reducible] def spike2WasiBoundarySemantics : TargetBoundarySemantics Spike2WasiBoundaryTarget where
  Implementation := Nat
  Artifact := WasiArtifact
  Signature := FuncType
  EntryKind := Unit
  ExitKind := ControlSignal
  PhysicalState := WasmMachineState
  Execution := List WasmInstr
  PublicEntry := Export
  LookupKey := String
  artifactImplements := fun artifact implementation =>
    implementation < artifact.module.functions.length
  publicEntries := wasiPublicEntries
  callableEntries := wasiCallableEntries
  lookupKey := fun entry => entry.name
  resolvesEntry := fun artifact entry implementation signature _ =>
    ∃ fn,
      artifact.module.functions[implementation]? = some fn ∧
      entry.name = fn.exportName.getD "" ∧
      signature = { params := fn.params, results := fn.results }
  jointlyAdmissible := fun _ entries =>
    (entries.map fun entry => entry.2.1).Nodup
  runs := fun artifact implementation signature _ before execution exitKind after =>
    ∃ fn,
      artifact.module.functions[implementation]? = some fn ∧
      signature = { params := fn.params, results := fn.results } ∧
      execution = fn.body ∧
      exitKind = .next ∧
      after = runWasmFunction execution before.locals (spike2BoundaryFuel before)
  admissible := fun artifact implementation signature _ _ execution _ _ =>
    ∃ fn,
      artifact.module.functions[implementation]? = some fn ∧
      signature = { params := fn.params, results := fn.results } ∧
      execution = fn.body

@[instance_reducible] local instance spike2BoundarySemanticsInstance :
    TargetBoundarySemantics Spike2WasiBoundaryTarget :=
  spike2WasiBoundarySemantics

inductive Spike2WasiPlatform

instance : Platform Spike2WasiPlatform where
  Artifact := WasiArtifact
  State := Environment
  Observation := WasiObservable AnyEvent
  RuntimeContext := WasiHostRuntime
  Import := String
  Provider := WasiProvider
  BoundaryWorld := Unit
  BoundaryKey := Spike2WasiBoundaryKey
  BoundaryTarget := Spike2WasiBoundaryTarget
  boundarySpec := spike2WasiBoundarySpec
  boundarySemantics := spike2WasiBoundarySemantics
  imports := fun artifact => artifact.imports
  providerProvides := fun provider imported =>
    provider.imports[provider.importIndex]? = some imported
  providerLinked := fun artifact provider => provider.imports = artifact.imports
  runtimeSupports := fun runtime _ provider =>
    match provider.protocol with
    | .preview1 => ∀ state,
        runtime provider.imports provider.importIndex state =
          wasiHostCall provider.imports provider.importIndex state
    | .library _ => ∀ state,
        (runtime provider.imports provider.importIndex state).1.trapped = state.trapped
  boundaryArtifact := id
  artifactConnected := fun artifact =>
    artifact.module.functions.head?.map (fun fn => fn.body) = some artifact.instructions ∧
    artifact.module.dataSegments = artifact.dataSegments ∧
    artifact.module.imports.map (fun imported => imported.name) = artifact.imports
  load := fun _ environment => environment
  run := fun runtime artifact environment =>
    (runWasiOutcomeWithHost runtime artifact.instructions artifact.dataSegments environment.stdin
      artifact.imports environment.incomingRequests artifact.resources).observable
  admissible := fun _ artifact _ =>
    ∃ bytes, emitWasmBinary artifact.module artifact.typeSignatures = .ok bytes
  emit := fun artifact => emitWasmBinary artifact.module artifact.typeSignatures

def spike2WasiCapability : Capability Spike2WasiPlatform where
  Context := Unit
  providers :=
    [{ protocol := .preview1, imports := ["fd_write", "proc_exit"], importIndex := 0 },
     { protocol := .preview1, imports := ["fd_write", "proc_exit"], importIndex := 1 }]
  establishes := fun _ _ _ _ => True

def spike2WasiCapabilities : CapabilityComposition Spike2WasiPlatform where
  root := spike2WasiCapability
  realize := fun _ _ => wasiHostCall
  realizeSupports := by
    intro context artifact provider hprovider hlinked
    simp only [spike2WasiCapability, List.mem_cons, List.not_mem_nil, or_false] at hprovider
    rcases hprovider with rfl | rfl <;> intro state <;> rfl

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Simulates execution of the Wasm iterative Fibonacci routine for input n. -/
def runFibIterWasm (n : Nat) : Option UInt64 :=
  match (runWasmFunction fibIterWasmInstructions [.i64 n.toUInt64]).stack with
  | [.i64 v] => some v
  | _ => none

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- **PA15.** The WebAssembly iterative routine computes exact Fibonacci numbers, for every `n` the
    interpreter's default fuel budget (`defaultWasmFuel = 100000000`) can complete within. Discharged
    by `fibIterWasm_run` (`Spikes/Spike2Fibonacci/Wasm/LoopInvariant.lean`), whose content is
    `loop_correct`: an induction on the remaining iteration count against the loop invariant
    `FibLocals`, established by the routine's prologue and preserved by one pass through the
    `loop` body. A genuine structural argument -- not `native_decide` executing the interpreter on
    concrete inputs.

    This is a *different, more general* fact than the theorem it replaces: the previous
    `(List.range 91).all (...) = true` was a finite check over `n = 0..90`. The bound here is **not**
    the `UInt64`-overflow point the allowlist entry this replaces assumed was the relevant limit
    (`fib 93` is the last value that fits in 64 bits without wrapping) -- both sides of this equation
    wrap `UInt64` arithmetic identically (`Nat.toUInt64` distributes over `+`, discharged as
    `by simp [Nat.toUInt64]` inside `loop_correct`), so the equation holds *regardless* of `UInt64`
    overflow. The actual bound is the interpreter's own fuel budget: the routine consumes one unit
    per loop iteration plus a fixed prologue/epilogue cost, so `n + 26 ≤ defaultWasmFuel`.
    `fibIterWasm_run` is stated for arbitrary `fuel`, so a caller needing a larger `n` passes more;
    only this corollary fixes it at the default. -/
theorem fib_iter_wasm_soundness (n : Nat) (hn : n ≤ 99999974) :
    runFibIterWasm n = some (fibIter n).toUInt64 := by
  unfold runFibIterWasm
  rw [fibIterWasm_run n defaultWasmFuel (by omega)
    (show n + 26 ≤ 100000000 by omega), fibIter_eq_fibNat]

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Whole-program canonical effect trace equivalence for Spike 2 WebAssembly. -/
theorem spike2_wasm_canonical_effect_trace_equivalence :
    (runWasiTrace spike2WasmInstructions spike2DataSegments ==
     runModelTrace (fibonacciWasmSpec : TraceM AnyEvent Unit)) = true := by
  native_decide

-- REF: wasm-exec-runtime#administrative-instructions -- Fuel-safety witness (see the identical
-- check and its rationale in Spikes/Spike1Hello/Wasm/Equivalence.lean): proves the actual Spike 2
-- program -- which DOES contain a real `.loop` (the iterative Fibonacci routine) -- never
-- exhausts `defaultWasmFuel` under `runWasiTraceState`, rather than merely assuming it.
#guard !Gasm.Targets.Wasm.WasmRunResult.isError
  (Gasm.Targets.WASI.runWasiTraceState spike2WasmInstructions spike2DataSegments)

def spike2WasiArtifact : WasiArtifact where
  module := spike2WasmModule
  typeSignatures := spike2TypeSignatures
  instructions := spike2WasmInstructions
  dataSegments := spike2DataSegments
  imports := ["fd_write", "proc_exit"]
  resources := { fuel := defaultWasmFuel, memoryPages := 65536 }

def spike2FibExport : Export := { name := "fibIter", desc := .func 3 }

/- REF: docs/ABI_CONTEXT.md#11-non-total-components-and-exported-boundaries -/
/-- The callable `fibIter` export refines its typed mathematical Fibonacci contract for every
    `UInt64` argument.  Boundary fuel is selected from the argument, independently of the root
    executable's finite request budget. -/
def spike2FibRealization :
    ContextBoundaryRealization Unit Spike2WasiBoundaryKey Spike2WasiBoundaryTarget .fibIter where
  signature := { params := [.i64], results := [.i64] }
  entryKind := ()
  implementation := let implementation : Nat := 1; implementation
  artifact := spike2WasiArtifact
  artifactConnection := by
    change 1 < 2
    decide
  relatesEntry := fun physical args _ _ => physical.locals = [.i64 args]
  relatesWorld := fun _ _ => True
  relatesExit := fun _ _ exitKind physicalAfter result outcome _ =>
    physicalAfter.stack = [.i64 result] ∧ outcome = exitKind
  entryRelatesWorld := by intros; trivial
  exitRelatesWorld := by intros; trivial
  physicalAdmissibility := by
    intro before execution exitKind after hruns
    rcases hruns with ⟨fn, hfn, hsignature, hexecution, _, _⟩
    exact ⟨fn, hfn, hsignature, hexecution⟩
  refinesContract := by
    intro physicalBefore args binding logicalBefore execution exitKind physicalAfter
      hentry _ hruns
    rcases hruns with ⟨fn, hfn, hsignature, hexecution, hexit, hafter⟩
    have hfnExact : fn = fibIterFunction := by
      symm
      simpa [spike2WasiArtifact, spike2WasmModule, buildWasiModule] using hfn
    subst fn
    subst execution
    subst exitKind
    refine ⟨(fibIter args.toNat).toUInt64, .next, (), ?_, ?_⟩
    · constructor
      · rw [hafter]
        have hrun := fibIterWasm_run args.toNat (args.toNat + 26) args.toNat_lt (by omega)
        set_option maxHeartbeats 2000000 in
          simpa [spike2BoundaryFuel, hentry, fibIterFunction, fibIter_eq_fibNat,
            Nat.toUInt64] using hrun
      · rfl
    · constructor <;> rfl

def spike2PublishedFib : PublishedBoundary Unit Spike2WasiBoundaryKey
    Spike2WasiBoundaryTarget spike2WasiBoundarySpec spike2WasiBoundarySemantics where
  key := .fibIter
  physicalEntry := spike2FibExport
  realization := spike2FibRealization
  resolves := by
    refine ⟨fibIterFunction, ?_, rfl, rfl⟩
    simp [spike2FibRealization, spike2WasiArtifact, spike2WasmModule, buildWasiModule]

def spike2WasiExports : VerifiedExportSet Unit Spike2WasiBoundaryKey
    Spike2WasiBoundaryTarget spike2WasiBoundarySpec spike2WasiBoundarySemantics where
  artifact := spike2WasiArtifact
  publicManifest := wasiPublicEntries spike2WasiArtifact
  entries := [spike2PublishedFib]
  uniqueLookup := by
    change (["_start", "fibIter", "memory"] : List String).Nodup
    decide
  exactPublicTable := rfl
  exactCallableTable := by rfl
  sameArtifact := by
    intro entry hentry
    simp only [List.mem_singleton] at hentry
    subst entry
    simp [spike2PublishedFib, spike2FibRealization]
  jointlyAdmissible := by
    show ([1] : List Nat).Nodup
    simp

theorem spike2_wasi_reference_outcome :
    (runWasiOutcome spike2WasmInstructions spike2DataSegments ByteArray.empty
      ["fd_write", "proc_exit"] []
      { fuel := defaultWasmFuel, memoryPages := 65536 }).observable =
        .exited 0 (runModelTrace (fibonacciWasmSpec : TraceM AnyEvent Unit)) := by
  native_decide

private def spike2WasiEmittedBytes : ByteArray :=
  match spike2WasmBinary with
  | .ok bytes => bytes
  | .error _ => ByteArray.empty

private theorem spike2_wasi_emits :
    emitWasmBinary spike2WasmModule spike2TypeSignatures = .ok spike2WasiEmittedBytes := by
  set_option maxRecDepth 100000 in
    rfl

def spike2WasiArtifactCertificate : ProgramArtifactCertificate Spike2WasiPlatform where
  artifact := spike2WasiArtifact
  exports := spike2WasiExports
  exportsArtifact := rfl
  artifactConnection := by
    constructor
    · rfl
    constructor <;> rfl

theorem spike2WasiProviderCertificate :
    ProgramProviderCertificate Spike2WasiPlatform spike2WasiCapabilities spike2WasiArtifact where
  importsCovered := by
    intro imported himported
    change imported ∈ ["fd_write", "proc_exit"] at himported
    simp only [List.mem_cons, List.not_mem_nil, or_false] at himported
    rcases himported with rfl | rfl
    · let provider : WasiProvider :=
        { protocol := .preview1, imports := ["fd_write", "proc_exit"], importIndex := 0 }
      refine ⟨provider, ?_, rfl⟩
      simp [provider, spike2WasiCapabilities, spike2WasiCapability]
    · let provider : WasiProvider :=
        { protocol := .preview1, imports := ["fd_write", "proc_exit"], importIndex := 1 }
      refine ⟨provider, ?_, rfl⟩
      simp [provider, spike2WasiCapabilities, spike2WasiCapability]
  providersLinked := by
    intro provider hprovider
    simp only [spike2WasiCapabilities, spike2WasiCapability, List.mem_cons,
      List.not_mem_nil, or_false] at hprovider
    rcases hprovider with rfl | rfl <;> rfl

def spike2WasiEntryCertificate :
    ProgramEntryCertificate Spike2WasiPlatform spike2WasiCapabilities spike2WasiArtifact where
  entryContext := fun _ => ()
  entryEstablished := by intro; trivial

theorem spike2WasiAdmissibilityCertificate :
    ProgramAdmissibilityCertificate Spike2WasiPlatform spike2WasiCapabilities spike2WasiArtifact
      spike2WasiEntryCertificate where
  platformAdmissible := by
    intro
    exact ⟨spike2WasiEmittedBytes, spike2_wasi_emits⟩

def spike2WasiBehaviorCertificate :
    ProgramBehaviorCertificate Spike2WasiPlatform spike2WasiCapabilities spike2WasiArtifact
      spike2WasiEntryCertificate where
  spec := fun _ => .exited 0 (runModelTrace (fibonacciWasmSpec : TraceM AnyEvent Unit))
  traceEquivalence := by
    intro environment
    change (runWasiOutcome spike2WasmInstructions spike2DataSegments environment.stdin
      ["fd_write", "proc_exit"] environment.incomingRequests
      { fuel := defaultWasmFuel, memoryPages := 65536 }).observable = _
    rw [runWasiOutcome_output_only_observable_external_input_frame]
    exact spike2_wasi_reference_outcome

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Sole universal whole-program contract plus the exact typed callable `fibIter` boundary. -/
def spike2VerifiedWasmProgram : VerifiedProgram Spike2WasiPlatform spike2WasiCapabilities :=
  VerifiedProgram.compose "Spike 2: Fibonacci Sequence Driver (WebAssembly / WASI Preview 1)"
    spike2WasiArtifactCertificate spike2WasiProviderCertificate spike2WasiEntryCertificate
    spike2WasiAdmissibilityCertificate spike2WasiBehaviorCertificate

def renderSpike2VerifiedWasmText : String :=
  emitWasmText spike2VerifiedWasmProgram.artifact.module
    spike2VerifiedWasmProgram.artifact.typeSignatures

end Spikes.Spike2Fibonacci.Wasm
