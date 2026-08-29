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
