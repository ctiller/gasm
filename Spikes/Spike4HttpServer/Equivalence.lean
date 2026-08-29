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
import Spikes.Spike4HttpServer.Platform

namespace Spikes.Spike4HttpServer

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.Wasm
open Gasm.Targets.WASI

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

/-!
Spike 4 ABI integration boundary

The target entry points now call the staged Gasm HTTP runtime ABI. They must therefore execute with
the candidate runtime bindings selected by their capability compositions, not the stock host hooks
used by the former inline socket implementations.

Platform.lean currently proves component identity, import/provider linkage, final-instruction
selection, and executable dispatch to each candidate adapter. It does not yet prove that the
machine or Wasm adapter transition refines parserRealization. This file keeps that missing semantic
bridge explicit. The finite probes below are regression evidence only; they are not presented as a
universal proof or as authority to emit a verified artifact.
-/

/-- Windows execution under the runtime selected by the Spike 4 capability composition. -/
def windowsRuntimeTraceFor (environment : Environment) : List AnyEvent :=
  Platform.run
    (spike4WindowsCapabilities.realize spike4WindowsArtifact ())
    spike4WindowsArtifact (Platform.load spike4WindowsArtifact environment)

/-- Linux execution under the runtime selected by the Spike 4 capability composition. -/
def linuxRuntimeTraceFor (environment : Environment) : List AnyEvent :=
  Platform.run
    (spike4LinuxCapabilities.realize spike4LinuxArtifact ())
    spike4LinuxArtifact (Platform.load spike4LinuxArtifact environment)

/-- WASI execution retains completion and resource-failure classification. -/
def wasiRuntimeObservationFor (environment : Environment) : WasiObservable AnyEvent :=
  Platform.run
    (spike4WasiCapabilities.realize spike4WasiArtifact ())
    spike4WasiArtifact (Platform.load spike4WasiArtifact environment)

/-- The five externally visible lifecycle edges, expressed independently of target execution. -/
def requestRuntimeSchedule (requests : List ByteArray) : List AnyEvent :=
  let parsed := parserInput requests
  let hasRequest := !requests.isEmpty
  [0, 1, 2, 3, 4].foldl (fun events phase =>
    appendRuntimeEvent events (requestRuntimeEvent phase hasRequest parsed)) []

theorem requestRuntimeSchedule_eq (environment : Environment) :
    requestRuntimeSchedule environment.incomingRequests = serverEnvironmentSpec environment := by
  cases requestsEq : environment.incomingRequests with
  | nil => simp [requestRuntimeSchedule, serverEnvironmentSpec, runtimeTrace, requestsEq,
      requestRuntimeEvent, appendRuntimeEvent]
  | cons request rest =>
    simp [requestRuntimeSchedule, serverEnvironmentSpec, runtimeTrace, requestsEq,
      requestRuntimeEvent, requestTrace, parserInput, appendRuntimeEvent]

theorem evalInstrs_boundary_step (fuel : Nat) (instruction : WasmInstr)
    (rest : List WasmInstr) (state after : WasmMachineState)
    (host : Nat → WasmMachineState → WasmMachineState × ControlSignal)
    (notTrapped : state.trapped = false) (notExited : state.exitCode = none)
    (step : evalInstrMatch (fuel + 1) instruction state host = .ok (after, .next)) :
    evalInstrs (fuel + 2) (instruction :: rest) state host =
      evalInstrs (fuel + 1) rest after host := by
  rw [show fuel + 2 = (fuel + 1) + 1 from rfl]
  simp only [evalInstrs, notTrapped, notExited, Option.isSome_none, Bool.or_self,
    Bool.false_eq_true, if_false, step]

@[simp] theorem pushVal_exitCode (value : WasmVal) (state : WasmMachineState) :
    (pushVal value state).exitCode = state.exitCode := rfl

/-- One typed Wasm boundary block. The edge theorem below is reusable at every lifecycle call. -/
def wasiPhaseInstructions (phase : UInt32) : List WasmInstr :=
  [.i32_const 0, .i32_const 0x800, .i32_const requestReadChunk.toUInt32,
    .i32_const phase, .call 0, .drop]

set_option maxRecDepth 100000 in
theorem eval_wasi_phase_edge (fuel : Nat) (phase : UInt32) (rest : List WasmInstr)
    (state : WasmMachineState) (notTrapped : state.trapped = false)
    (notExited : state.exitCode = none) :
    evalInstrs (fuel + 7) (wasiPhaseInstructions phase ++ rest) state
      (spike4WasiRuntime Wasm.spike4WasmImports) =
    evalInstrs (fuel + 1) rest (wasiAfterPhase phase state)
      (spike4WasiRuntime Wasm.spike4WasmImports) := by
  unfold wasiPhaseInstructions
  simp only [List.cons_append, List.nil_append]
  let s1 := pushVal (.i32 0) state
  let s2 := pushVal (.i32 0x800) s1
  let s3 := pushVal (.i32 requestReadChunk.toUInt32) s2
  let s4 := pushVal (.i32 phase) s3
  have step1 : evalInstrMatch (fuel + 6) (.i32_const 0) state
      (spike4WasiRuntime Wasm.spike4WasmImports) = .ok (s1, .next) := by rfl
  have step2 : evalInstrMatch (fuel + 5) (.i32_const 0x800) s1
      (spike4WasiRuntime Wasm.spike4WasmImports) = .ok (s2, .next) := by rfl
  have step3 : evalInstrMatch (fuel + 4) (.i32_const requestReadChunk.toUInt32) s2
      (spike4WasiRuntime Wasm.spike4WasmImports) = .ok (s3, .next) := by rfl
  have step4 : evalInstrMatch (fuel + 3) (.i32_const phase) s3
      (spike4WasiRuntime Wasm.spike4WasmImports) = .ok (s4, .next) := by rfl
  rw [show fuel + 7 = (fuel + 5) + 2 by omega]
  rw [evalInstrs_boundary_step (fuel + 5) _ _ state s1 _ notTrapped notExited step1]
  rw [show fuel + 5 + 1 = (fuel + 4) + 2 by omega]
  rw [evalInstrs_boundary_step (fuel + 4) _ _ s1 s2 _ (by simp [s1, notTrapped])
    (by simp [s1, notExited]) step2]
  rw [show fuel + 4 + 1 = (fuel + 3) + 2 by omega]
  rw [evalInstrs_boundary_step (fuel + 3) _ _ s2 s3 _ (by simp [s2, s1, notTrapped])
    (by simp [s2, s1, notExited]) step3]
  rw [show fuel + 3 + 1 = (fuel + 2) + 2 by omega]
  rw [evalInstrs_boundary_step (fuel + 2) _ _ s3 s4 _ (by simp [s3, s2, s1, notTrapped])
    (by simp [s3, s2, s1, notExited]) step4]
  rw [show fuel + 2 + 1 = (fuel + 1) + 2 by omega]
  have callEdge :
      evalInstrMatch (fuel + 2) (.call 0)
        s4
        (spike4WasiRuntime Wasm.spike4WasmImports) =
      .ok (pushVal (.i32 (wasiPhaseResult state)) (wasiAfterPhase phase state), .next) := rfl
  let callAfter := pushVal (.i32 (wasiPhaseResult state)) (wasiAfterPhase phase state)
  rw [evalInstrs_boundary_step (fuel + 1) _ _ s4 _ _
    (by simp [s4, s3, s2, s1, notTrapped])
    (by simp [s4, s3, s2, s1, notExited]) callEdge]
  rw [show fuel + 1 + 1 = fuel + 2 by omega]
  have dropEdge : evalInstrMatch (fuel + 1) .drop callAfter
      (spike4WasiRuntime Wasm.spike4WasmImports) =
      .ok (wasiAfterPhase phase state, .next) := by rfl
  rw [evalInstrs_boundary_step fuel _ _ callAfter _ _
    (by simp [callAfter, notTrapped]) (by simp [callAfter, notExited]) dropEdge]

theorem spike4_wasi_runtime_trace_equivalence (environment : Environment) :
    wasiRuntimeObservationFor environment =
      .completed (serverEnvironmentSpec environment) := by
  have pages : ¬(WasmMem.size (initWasmMemory Wasm.spike4DataSegments) + 65535) / 65536 >
      ({ fuel := 512, memoryPages := 1 : WasiResourceBudget }.memoryPages.min 65536) := by
    native_decide
  unfold wasiRuntimeObservationFor
  change (runWasiOutcomeWithHost spike4WasiRuntime Wasm.spike4WasmInstructions
    Wasm.spike4DataSegments environment.stdin Wasm.spike4WasmImports
    environment.incomingRequests { fuel := 512, memoryPages := 1 }).observable = _
  rw [runWasiOutcomeWithHost, if_neg pages]
  change (WasiRunOutcome.ofResult (evalInstrs 512 Wasm.spike4WasmInstructions _ _)).observable = _
  rw [show Wasm.spike4WasmInstructions =
    wasiPhaseInstructions 0 ++ (wasiPhaseInstructions 1 ++ (wasiPhaseInstructions 2 ++
      (wasiPhaseInstructions 3 ++ wasiPhaseInstructions 4))) by rfl]
  rw [show wasiPhaseInstructions 4 = wasiPhaseInstructions 4 ++ [] by simp]
  rw [eval_wasi_phase_edge (fuel := 505) (notTrapped := by rfl) (notExited := by rfl),
    eval_wasi_phase_edge (fuel := 499) (notTrapped := by simp) (notExited := by simp),
    eval_wasi_phase_edge (fuel := 493) (notTrapped := by simp) (notExited := by simp),
    eval_wasi_phase_edge (fuel := 487) (notTrapped := by simp) (notExited := by simp),
    eval_wasi_phase_edge (fuel := 481) (notTrapped := by simp) (notExited := by simp)]
  rw [← requestRuntimeSchedule_eq environment]
  simp [evalInstrs, WasiRunOutcome.ofResult, WasiRunOutcome.observable,
    wasiAfterPhase, requestRuntimeSchedule]

/-- A closed one-request environment used only for finite regression probes. -/
def requestEnvironment (request : ByteArray) : Environment :=
  { incomingRequests := [request] }

/-- Closed-probe agreement with the independent logical runtime specification. -/
def spike4RuntimeAgreementOnAllTargets (request : ByteArray) : Bool :=
  let environment := requestEnvironment request
  let expected := serverEnvironmentSpec environment
  (windowsRuntimeTraceFor environment == expected) &&
  (linuxRuntimeTraceFor environment == expected) &&
  (wasiRuntimeObservationFor environment == .completed expected)

/-- Normal routing, malformed syntax, non-UTF-8 payload, and request-line exhaustion probes. -/
def spike4RuntimeRegressionRequests : List ByteArray :=
  [ req "GET / HTTP/1.1\r\nHost: localhost\r\n\r\n",
    req "GET /status HTTP/1.1\r\nHost: localhost\r\n\r\n",
    req "GET /unknown HTTP/1.1\r\nHost: localhost\r\n\r\n",
    req "FOO / HTTP/1.1\r\n\r\n",
    ByteArray.mk #[71, 69, 84, 32, 47, 32, 72, 84, 84, 80, 47, 49, 46, 49, 13, 10,
      88, 58, 32, 255, 13, 10, 13, 10],
    req (String.ofList (List.replicate 1025 'x')) ]

#guard spike4RuntimeRegressionRequests.all spike4RuntimeAgreementOnAllTargets

/-- Exact Windows behavior obligation left by the staged ABI adapter. -/
def Spike4WindowsRuntimeTraceEquivalence : Prop :=
  ∀ environment : Environment,
    windowsRuntimeTraceFor environment = serverEnvironmentSpec environment

/-- Exact Linux behavior obligation left by the staged ABI adapter. -/
def Spike4LinuxRuntimeTraceEquivalence : Prop :=
  ∀ environment : Environment,
    linuxRuntimeTraceFor environment = serverEnvironmentSpec environment

/-- Exact WASI behavior obligation left by the staged ABI adapter. -/
def Spike4WasiRuntimeTraceEquivalence : Prop :=
  ∀ environment : Environment,
    wasiRuntimeObservationFor environment = .completed (serverEnvironmentSpec environment)

/-- No verified whole-program constructor is exposed until all three semantic bridges exist. -/
structure Spike4RuntimeRefinementObligations : Prop where
  windows : Spike4WindowsRuntimeTraceEquivalence
  linux : Spike4LinuxRuntimeTraceEquivalence
  wasi : Spike4WasiRuntimeTraceEquivalence

/-- Recovery is already proved at the independent logical-runtime layer. Target adapters may cite
    it only after their refinement obligation above is discharged. -/
theorem spike4_runtime_resource_failure_does_not_poison_next (request next : ByteArray)
    (h : (driveRequest request).1 = .resourceExhausted) :
    (runtimeTrace [request, next]).drop (1 + (requestTrace request).length) = requestTrace next :=
  resource_failure_does_not_poison_next request next h

end Spikes.Spike4HttpServer
