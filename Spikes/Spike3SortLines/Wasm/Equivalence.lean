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
import Spikes.Spike3SortLines.Wasm.Fuel

namespace Spikes.Spike3SortLines.Wasm

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.Wasm
open Gasm.Targets.WASI
open Spikes.Spike3SortLines

/- The former canonical evaluator proof needed extreme elaborator limits.  The universal
   certificate below is structural; keeping those limits would turn an accidental reduction into
   a machine-wide memory hazard. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 500000

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Default sample test input string for standard verified execution. -/
def defaultSampleInput : ByteArray :=
  "cherry\r\napple\r\nbanana\r\n".toUTF8

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Candidate concrete evaluator-fuel grant for one finite input.  The quadratic component follows
    the selected in-place line sorter; it is deliberately a function of the environment, never a
    hidden bound on stdin.  `Spike3WasmBehavior.productionRunWithinFuel` is the load-bearing
    target proof that this exact provision covers the actual evaluator run after preparation
    seals. Memory remains finite and fallible: it is not made total by this fuel policy. -/
def spike3WasiFuelFor (environment : Environment) : Nat :=
  65536 + 4096 * (environment.stdin.size + 1) * (environment.stdin.size + 1)

def spike3WasiResourcesFor (environment : Environment) : WasiResourceBudget :=
  { fuel := spike3WasiFuelFor environment
    memoryPages := 65536 }

/-- The entry context contains exactly the published finite fuel bound, rather than a caller
    chosen unrelated number. -/
theorem spike3WasiResourcesFor_fuel (environment : Environment) :
    (spike3WasiResourcesFor environment).fuel = spike3WasiFuelFor environment := rfl

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

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- The operational target is parameterized by the canonical environment, not a Bool or a finite
    collection of samples. `environmentInputLines` is its shared executable byte-stream model. -/
def spike3WasmRunFor (environment : Environment) : WasiRunOutcome :=
  runWasiOutcome spike3WasmInstructions spike3DataSegments environment.stdin
    ["fd_read", "fd_write", "proc_exit"] environment.incomingRequests
    (spike3WasiResourcesFor environment)

def spike3WasmTraceFor (environment : Environment) : WasiObservable AnyEvent :=
  (spike3WasmRunFor environment).observable

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- The exact byte-level input observation which the whole-program sort specification consumes. -/
def spike3WasmInputFor (environment : Environment) : List (List UInt8) :=
  environmentInputLines environment

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- The accepted-output arm of the one preparation/output byte specification, retained as a named
    WASI observation for the target bridge.  A universal certificate must additionally classify
    real WASI resource outcomes as sealed preparation or exhaustion, and `fd_write` as accepted
    or refused; it cannot use this arm to erase either failure. -/
def spike3WasmSuccessSpec (environment : Environment) : WasiObservable AnyEvent :=
  .exited 0 (byteSortOutput (sortByteLines (environmentInputLines environment)))

/-- Complete target-observable classification for the current WASI runtime.  It is derived only
    from `WasiObservable`, so fuel exhaustion, memory exhaustion, and traps cannot be silently
    classified as successful source output.  The stock `fd_write` host model currently has no
    refusal constructor; a later host/profile that adds one must extend this type and connect it
    to `LogicalWorld.OutputCursor.WriteResult` before it can claim the shared output-refusal arm. -/
inductive Spike3WasmObservedOutcome where
  | completed (events : List AnyEvent)
  | preparationExhausted (events : List AnyEvent)
  | exited (code : UInt32) (events : List AnyEvent)
  | trapped (events : List AnyEvent)
  | fuelExhausted
  | memoryExhausted (requestedPages availablePages : Nat)

def Spike3WasmObservedOutcome.ofObservable : WasiObservable AnyEvent → Spike3WasmObservedOutcome
  | .completed events => .completed events
  | .exited code events =>
      if code == spike3ResourceFailureExitCode then .preparationExhausted events
      else .exited code events
  | .trapped events => .trapped events
  | .fuelExhausted => .fuelExhausted
  | .memoryExhausted requested available => .memoryExhausted requested available

/-- The finite WASI observation is computed from the actual platform outcome, not from free
    preparation/output classifiers. -/
def spike3WasmFiniteSpec (environment : Environment) : Spike3WasmObservedOutcome :=
  .ofObservable (spike3WasmTraceFor environment)

/-- The resource-failure exit code is a first-class observable classification.  It is not a
    success trace and does not fabricate a sealed source/table witness.  The target-level
    preparation proof must still establish that this exit is reached only from the checked
    allocation-failure path. -/
theorem spike3WasmFiniteSpec_preparationExhausted (environment : Environment) (events : List AnyEvent) :
    spike3WasmFiniteSpec environment = .preparationExhausted events ↔
      spike3WasmTraceFor environment = .exited spike3ResourceFailureExitCode events := by
  unfold spike3WasmFiniteSpec
  cases h : spike3WasmTraceFor environment with
  | completed events' => simp [Spike3WasmObservedOutcome.ofObservable]
  | exited code events' =>
      by_cases failure : code = spike3ResourceFailureExitCode
      · subst code
        simp [Spike3WasmObservedOutcome.ofObservable]
      · simp [Spike3WasmObservedOutcome.ofObservable, failure]
  | trapped events' => simp [Spike3WasmObservedOutcome.ofObservable]
  | fuelExhausted => simp [Spike3WasmObservedOutcome.ofObservable]
  | memoryExhausted requested available => simp [Spike3WasmObservedOutcome.ofObservable]

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- The Spike 3 WASI profile preserves the environment verbatim at the platform boundary. This
    establishes the loading premise required before the target trace can be coupled to the
    byte-stream specification. -/
theorem spike3_wasi_platform_loads_environment
    (artifact : Spike3WasiArtifact) (environment : Environment) :
    Platform.load (P := Spike3WasiPreview1Platform) artifact environment = environment := rfl

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- The sole non-definitional whole-artifact semantic obligation.  It ranges over every
    environment and only applies when the *actual* WASI execution has successfully exited.  A
    fuel exhaustion, memory exhaustion, trap, nonzero exit, or clean fall-through therefore
    cannot discharge this obligation or be silently rewritten as success. -/
structure Spike3WasmBehavior (environment : Environment) where
  /-- The capability's concrete environment-specific fuel grant is sufficient for this exact
      finite run.  This is a post-seal progress obligation, not an assumption that input is
      bounded or that the evaluator has unlimited fuel. -/
  productionRunWithinFuel : ∀ partialState,
    spike3WasmRunFor environment ≠ .fuelExhausted partialState
  successfulExitIsSorted : ∀ events,
    spike3WasmTraceFor environment = .exited 0 events →
      events = byteSortOutput (sortByteLines (environmentInputLines environment))

theorem WasiRunOutcome.observable_ne_fuelExhausted
    (outcome : WasiRunOutcome)
    (notFuel : ∀ partialState, outcome ≠ .fuelExhausted partialState) :
    outcome.observable ≠ .fuelExhausted := by
  cases outcome with
  | completed state signal => simp [WasiRunOutcome.observable]
  | exited state code => simp [WasiRunOutcome.observable]
  | trapped state => simp [WasiRunOutcome.observable]
  | fuelExhausted partialState => exact (notFuel partialState rfl).elim
  | memoryExhausted state requested available => simp [WasiRunOutcome.observable]

theorem Spike3WasmBehavior.noFuelExhausted
    (behavior : Spike3WasmBehavior environment) :
    spike3WasmTraceFor environment ≠ .fuelExhausted := by
  unfold spike3WasmTraceFor
  apply WasiRunOutcome.observable_ne_fuelExhausted
  exact behavior.productionRunWithinFuel

/-- Normalize one already-observed outcome without reducing the computation that produced it. -/
def normalizeWasmObservation
    (success observation : WasiObservable AnyEvent) : WasiObservable AnyEvent :=
  match observation with
  | .exited 0 _ => success
  | observation => observation

theorem normalizeWasmObservation_of_memoryExhausted
    (success observation : WasiObservable AnyEvent)
    (exhausted : observation = .memoryExhausted requested available) :
    normalizeWasmObservation success observation =
      .memoryExhausted requested available := by
  subst observation
  rfl

theorem normalizeWasmObservation_of_trapped
    (success observation : WasiObservable AnyEvent)
    (trapped : observation = .trapped events) :
    normalizeWasmObservation success observation = .trapped events := by
  subst observation
  rfl

theorem normalizeWasmObservation_of_completed
    (success observation : WasiObservable AnyEvent)
    (completed : observation = .completed events) :
    normalizeWasmObservation success observation = .completed events := by
  subst observation
  rfl

theorem normalizeWasmObservation_of_nonzeroExit
    (success observation : WasiObservable AnyEvent)
    (nonzero : code ≠ 0)
    (exited : observation = .exited code events) :
    normalizeWasmObservation success observation = .exited code events := by
  subst observation
  simp [normalizeWasmObservation, nonzero]

theorem observation_refines_normalizeWasmObservation
    (success observation : WasiObservable AnyEvent) :
    observation ≠ .fuelExhausted →
    (∀ events, observation = .exited 0 events → .exited 0 events = success) →
    observation = normalizeWasmObservation success observation := by
  cases observation with
  | completed events => intros; rfl
  | exited code events =>
      intro _ successCase
      by_cases zero : code = 0
      · subst code
        simpa [normalizeWasmObservation] using successCase events rfl
      · simp [normalizeWasmObservation, zero]
  | trapped events => intros; rfl
  | fuelExhausted =>
      intro noFuel
      exact False.elim (noFuel rfl)
  | memoryExhausted requested available => intros; rfl

/-- The verified post-seal contract normalizes exactly the successful-exit payload and excludes
    fuel exhaustion through the separately proved per-environment grant.  The raw finite
    observation is still available as `spike3WasmFiniteSpec`, preserving the platform's complete
    outcome vocabulary for diagnostics and preparation reasoning. -/
def spike3WasmSpecification (_behavior : Spike3WasmBehavior environment) : WasiObservable AnyEvent :=
  normalizeWasmObservation (spike3WasmSuccessSpec environment)
    (spike3WasmTraceFor environment)

/-- A rejected linear-memory capability remains an observable contract outcome. -/
theorem spike3WasmSpecification_memoryExhausted (behavior : Spike3WasmBehavior environment)
    (exhausted : spike3WasmTraceFor environment = .memoryExhausted requested available) :
    spike3WasmSpecification behavior = .memoryExhausted requested available := by
  unfold spike3WasmSpecification
  exact normalizeWasmObservation_of_memoryExhausted _ _ exhausted

/-- Traps and clean fall-through remain distinct from source-level success. -/
theorem spike3WasmSpecification_trapped (behavior : Spike3WasmBehavior environment)
    (trapped : spike3WasmTraceFor environment = .trapped events) :
    spike3WasmSpecification behavior = .trapped events := by
  unfold spike3WasmSpecification
  exact normalizeWasmObservation_of_trapped _ _ trapped

theorem spike3WasmSpecification_completed (behavior : Spike3WasmBehavior environment)
    (completed : spike3WasmTraceFor environment = .completed events) :
    spike3WasmSpecification behavior = .completed events := by
  unfold spike3WasmSpecification
  exact normalizeWasmObservation_of_completed _ _ completed

theorem spike3WasmSpecification_nonzeroExit (behavior : Spike3WasmBehavior environment)
    (nonzero : code ≠ 0)
    (exited : spike3WasmTraceFor environment = .exited code events) :
    spike3WasmSpecification behavior = .exited code events := by
  unfold spike3WasmSpecification
  exact normalizeWasmObservation_of_nonzeroExit _ _ nonzero exited

theorem Spike3WasmBehavior.refinesSpecification
    (behavior : Spike3WasmBehavior environment) :
    spike3WasmTraceFor environment = spike3WasmSpecification behavior := by
  unfold spike3WasmSpecification
  apply observation_refines_normalizeWasmObservation
  · exact behavior.noFuelExhausted
  intro events exited
  simpa [spike3WasmSuccessSpec] using congrArg (WasiObservable.exited 0)
    (behavior.successfulExitIsSorted events exited)

/-- A `VerifiedProgram` is constructible only from the full behavior proof above.  In particular,
    a caller cannot supply the old success-only `spike3WasmSuccessSpec` equality and erase a
    post-preparation fuel/trap outcome. -/
def spike3WasiArtifact : WasiArtifact where
  module := spike3WasmModule
  typeSignatures := spike3TypeSignatures
  instructions := spike3WasmInstructions
  dataSegments := spike3DataSegments
  imports := ["fd_read", "fd_write", "proc_exit"]
  -- This is a tool-facing default profile only. The entry capability supplies the actual finite
  -- fuel and linear-memory ceiling through `spike3WasiResourcesFor`.
  defaultResources := { fuel := 0, memoryPages := 65536 }

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

def spike3WasiArtifactCertificate : ProgramArtifactCertificate Spike3WasiPreview1Platform where
  artifact := spike3WasiArtifact
  exports := spike3WasiExports
  exportsArtifact := rfl
  artifactConnection := spike3WasmArtifactShape

def spike3WasiProviderCertificate :
    ProgramProviderCertificate Spike3WasiPreview1Platform spike3WasiCapabilities spike3WasiArtifact where
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

def spike3WasiEntryCertificate :
    ProgramEntryCertificate Spike3WasiPreview1Platform spike3WasiCapabilities spike3WasiArtifact where
  entryContext := spike3WasiResourcesFor
  entryEstablished := by intros; trivial

theorem spike3WasiAdmissibilityCertificate :
    ProgramAdmissibilityCertificate Spike3WasiPreview1Platform spike3WasiCapabilities spike3WasiArtifact
      spike3WasiEntryCertificate where
  platformAdmissible := by
    intro
    exact ⟨spike3EncodedWasmBytes, spike3WasmEncoderOk⟩

/-- This certificate is universal in the real `Environment`: the run sees its exact stdin and
    incoming requests.  It accepts the one target-specific successful-exit simulation lemma, but
    obtains all non-success outcome preservation by reduction of `spike3WasmSpecification`.
    In particular, no sample trace, evaluation shortcut, or fixed post-seal fuel bound is used. -/
def spike3WasiBehaviorCertificate
    (behavior : ∀ environment : Environment, Spike3WasmBehavior environment) :
    ProgramBehaviorCertificate Spike3WasiPreview1Platform spike3WasiCapabilities spike3WasiArtifact
      spike3WasiEntryCertificate where
  spec := fun environment => spike3WasmSpecification (behavior environment)
  traceEquivalence := by
    intro environment
    exact (behavior environment).refinesSpecification

/-- Sole universal whole-program authority for the Spike 3 WASI artifact.  The caller must supply
    a simulation proof for every actual successful exit; resource and operational outcomes remain
    in the verified observable contract rather than being discharged by that proof. -/
def spike3VerifiedWasmProgram
    (behavior : ∀ environment : Environment, Spike3WasmBehavior environment) :
    VerifiedProgram Spike3WasiPreview1Platform spike3WasiCapabilities :=
  VerifiedProgram.compose "Spike 3: Byte-stream line sorter (WebAssembly / WASI Preview 1)"
    spike3WasiArtifactCertificate spike3WasiProviderCertificate spike3WasiEntryCertificate
    spike3WasiAdmissibilityCertificate (spike3WasiBehaviorCertificate behavior)

end Spikes.Spike3SortLines.Wasm
