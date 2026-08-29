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
open Gasm.Targets.X86_64
open Gasm.Targets.Linux
open Gasm.Targets.Windows
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
  let initial := Platform.load (P := LinuxX86_64 AnyEvent) spike4LinuxArtifact environment
  letI := spike4LinuxRuntime
  (runProgramOutcomeWithLoops (Event := AnyEvent) 4198400 Linux.spike4Instructions
    50000 initial).events

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

/-- One silent native machine edge. This is the interpreter leaf used by typed block proofs. -/
theorem native_outcome_step_none {Event : Type}
    [runtime : ExternalCallInterceptor X86_64 Event]
    (indexed : List (UInt64 × X86_64Instr)) (fuel : Nat)
    (state stepped : X86_64MachineState) (eventsRev : List Event) (instruction : X86_64Instr)
    (lookup : instructionAtRipIndexed indexed state.rip = some instruction)
    (step : Instructions.X86_64Instruction.step instruction state = stepped)
    (intercept : runtime.interceptCall stepped.rip stepped = none)
    (notFaulted : stepped.fault = none) :
    @runProgramOutcomeLoop Event runtime indexed (fuel + 1) state eventsRev =
      @runProgramOutcomeLoop Event runtime indexed fuel stepped eventsRev := by
  simp [runProgramOutcomeLoop, nativeOutcomeTransition, lookup, step, intercept, notFaulted]

/-- One native call/jump boundary edge. Emission is accumulated without replaying predecessors. -/
theorem native_outcome_step_boundary {Event : Type}
    [runtime : ExternalCallInterceptor X86_64 Event]
    (indexed : List (UInt64 × X86_64Instr)) (fuel : Nat)
    (state stepped after : X86_64MachineState) (eventsRev : List Event)
    (instruction : X86_64Instr) (emitted : Option Event)
    (lookup : instructionAtRipIndexed indexed state.rip = some instruction)
    (step : Instructions.X86_64Instruction.step instruction state = stepped)
    (intercept : runtime.interceptCall stepped.rip stepped = some (after, emitted))
    (notFaulted : after.fault = none) :
    @runProgramOutcomeLoop Event runtime indexed (fuel + 1) state eventsRev =
      @runProgramOutcomeLoop Event runtime indexed fuel after
        (emitted.elim eventsRev fun event => event :: eventsRev) := by
  simp [runProgramOutcomeLoop, nativeOutcomeTransition, lookup, step, intercept, notFaulted]

def linuxPhaseEntry (phase : Nat) : UInt64 := 4198400 + phase.toUInt64 * 13

def linuxPhaseStepped (phase : Nat) (state : X86_64MachineState) : X86_64MachineState :=
  let s1 := { (state.setGpr32 .r10d phase.toUInt32) with rip := state.rip + 6 }
  let s2 := { (s1.setGpr32 .eax gasmHttpLinuxSyscall.toUInt32) with rip := s1.rip + 5 }
  { ((s2.setGpr64 .rcx (s2.rip + 2)).setGpr64 .r11 s2.flags) with
    rip := Instructions.linuxSyscallEntry }

def linuxPhaseComplete (phase : Nat) (state : X86_64MachineState) : X86_64MachineState :=
  linuxAfterPhase phase.toUInt64 (linuxPhaseStepped phase state)

def linuxPhaseEvent (phase : Nat) (state : X86_64MachineState) : Option AnyEvent :=
  requestRuntimeEvent phase.toUInt64 (!state.incomingRequests.isEmpty)
    (parserInput state.incomingRequests)

theorem linux_phase_lookup0 (phase : Nat) (phaseBound : phase < 5) :
    instructionAtRipIndexed (indexInstructions 4198400 Linux.spike4Instructions)
      (linuxPhaseEntry phase) = some (Instructions.mov_r32 .r10d phase.toUInt32) := by
  have cases : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 := by omega
  rcases cases with h | h | h | h | h <;> subst phase <;> rfl

theorem linux_phase_lookup1 (phase : Nat) (phaseBound : phase < 5) :
    instructionAtRipIndexed (indexInstructions 4198400 Linux.spike4Instructions)
      (linuxPhaseEntry phase + 6) =
      some (Instructions.mov_r32 .eax gasmHttpLinuxSyscall.toUInt32) := by
  have cases : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 := by omega
  rcases cases with h | h | h | h | h <;> subst phase <;> rfl

theorem linux_phase_lookup2 (phase : Nat) (phaseBound : phase < 5) :
    instructionAtRipIndexed (indexInstructions 4198400 Linux.spike4Instructions)
      (linuxPhaseEntry phase + 11) = some Instructions.syscall_op := by
  have cases : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 := by omega
  rcases cases with h | h | h | h | h <;> subst phase <;> rfl

/-- The Linux lifecycle block is a single assume/guarantee edge. Its predecessor supplies only
the entry RIP and no-fault invariant; its conclusion is the next boundary state and optional event. -/
theorem linux_phase_outcome_edge (phase : Nat) (phaseBound : phase < 5)
    (fuel : Nat) (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (entryRip : state.rip = linuxPhaseEntry phase) (notFaulted : state.fault = none) :
    @runProgramOutcomeLoop AnyEvent spike4LinuxRuntime
      (indexInstructions 4198400 Linux.spike4Instructions) (fuel + 3) state eventsRev =
    @runProgramOutcomeLoop AnyEvent spike4LinuxRuntime
      (indexInstructions 4198400 Linux.spike4Instructions) fuel
      (linuxPhaseComplete phase state)
      ((linuxPhaseEvent phase state).elim eventsRev fun event => event :: eventsRev) := by
  letI := spike4LinuxRuntime
  let indexed := indexInstructions 4198400 Linux.spike4Instructions
  let s1 := { (state.setGpr32 .r10d phase.toUInt32) with rip := state.rip + 6 }
  let s2 := { (s1.setGpr32 .eax gasmHttpLinuxSyscall.toUInt32) with rip := s1.rip + 5 }
  let s3 := { ((s2.setGpr64 .rcx (s2.rip + 2)).setGpr64 .r11 s2.flags) with
    rip := Instructions.linuxSyscallEntry }
  have step0 : Instructions.X86_64Instruction.step
      (Instructions.mov_r32 .r10d phase.toUInt32) state = s1 := rfl
  have step1 : Instructions.X86_64Instruction.step
      (Instructions.mov_r32 .eax gasmHttpLinuxSyscall.toUInt32) s1 = s2 := rfl
  have step2 : Instructions.X86_64Instruction.step Instructions.syscall_op s2 = s3 := rfl
  have s1rip : s1.rip = linuxPhaseEntry phase + 6 := by simp [s1, entryRip]
  have s2rip : s2.rip = linuxPhaseEntry phase + 11 := by
    simp only [s2, s1]
    rw [entryRip]
    bv_decide
  have notEntry1 : linuxPhaseEntry phase + 6 ≠ Instructions.linuxSyscallEntry := by
    have cases : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 := by omega
    rcases cases with h | h | h | h | h <;> subst phase <;> native_decide
  have notEntry2 : linuxPhaseEntry phase + 11 ≠ Instructions.linuxSyscallEntry := by
    have cases : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 := by omega
    rcases cases with h | h | h | h | h <;> subst phase <;> native_decide
  have intercept0 : (@ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      spike4LinuxRuntime s1.rip s1) = none := by
    change (if s1.rip = Instructions.linuxSyscallEntry ∧
      s1.gprs .rax = gasmHttpLinuxSyscall then some (linuxParserHook s1)
      else Gasm.Targets.Linux.linuxSyscallIntercept s1.rip s1) = none
    rw [s1rip]
    simp [notEntry1, Gasm.Targets.Linux.linuxSyscallIntercept]
  have intercept1 : (@ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      spike4LinuxRuntime s2.rip s2) = none := by
    change (if s2.rip = Instructions.linuxSyscallEntry ∧
      s2.gprs .rax = gasmHttpLinuxSyscall then some (linuxParserHook s2)
      else Gasm.Targets.Linux.linuxSyscallIntercept s2.rip s2) = none
    rw [s2rip]
    simp [notEntry2, Gasm.Targets.Linux.linuxSyscallIntercept]
  have fault1 : s1.fault = none := by
    change state.fault = none
    exact notFaulted
  have fault2 : s2.fault = none := by
    change state.fault = none
    exact notFaulted
  rw [show fuel + 3 = (fuel + 2) + 1 by omega,
    native_outcome_step_none indexed (fuel + 2) state s1 eventsRev _
      (by simpa [indexed, entryRip] using linux_phase_lookup0 phase phaseBound)
      step0 intercept0 fault1]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
    native_outcome_step_none indexed (fuel + 1) s1 s2 eventsRev _
      (by simpa [indexed, s1rip] using linux_phase_lookup1 phase phaseBound)
      step1 intercept1 fault2]
  have hrax : s3.gprs .rax = gasmHttpLinuxSyscall := by
    simp [s3, s2, s1, X86_64MachineState.setGpr32, X86_64MachineState.setGpr64,
      reg32To64, gasmHttpLinuxSyscall]
  have hphase : s3.gprs .r10 = phase.toUInt64 := by
    have cases : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 := by omega
    rcases cases with h | h | h | h | h <;> subst phase <;>
      simp [s3, s2, s1, X86_64MachineState.setGpr32, X86_64MachineState.setGpr64,
        reg32To64]
  have hrequests : s3.incomingRequests = state.incomingRequests := rfl
  have intercept2 : (@ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      spike4LinuxRuntime s3.rip s3) =
      some (linuxAfterPhase phase.toUInt64 s3, linuxPhaseEvent phase state) := by
    change (if s3.rip = Instructions.linuxSyscallEntry ∧
      s3.gprs .rax = gasmHttpLinuxSyscall then some (linuxParserHook s3)
      else Gasm.Targets.Linux.linuxSyscallIntercept s3.rip s3) = _
    rw [if_pos ⟨rfl, hrax⟩]
    simp [linuxParserHook, linuxPhaseEvent, hphase, hrequests]
  have fault3 : (linuxAfterPhase phase.toUInt64 s3).fault = none := by
    simp [linuxAfterPhase, s3, s2, s1, X86_64MachineState.setGpr32,
      X86_64MachineState.setGpr64, notFaulted]
  rw [native_outcome_step_boundary indexed fuel s2 s3
    (linuxAfterPhase phase.toUInt64 s3) eventsRev _ _
    (by simpa [indexed, s2rip] using linux_phase_lookup2 phase phaseBound)
    step2 intercept2 fault3]
  rfl

/-- Named-state form used by CFG composition. Equalities are supplied by the owning successor
block, avoiding reduction of a predecessor's concrete state transformer during composition. -/
theorem linux_phase_outcome_edge_named (phase : Nat) (phaseBound : phase < 5)
    (fuel : Nat) (state after : X86_64MachineState)
    (eventsRev nextEventsRev : List AnyEvent)
    (entryRip : state.rip = linuxPhaseEntry phase) (notFaulted : state.fault = none)
    (afterEq : after = linuxPhaseComplete phase state)
    (eventsEq : nextEventsRev =
      (linuxPhaseEvent phase state).elim eventsRev (fun event => event :: eventsRev)) :
    @runProgramOutcomeLoop AnyEvent spike4LinuxRuntime
      (indexInstructions 4198400 Linux.spike4Instructions) (fuel + 3) state eventsRev =
    @runProgramOutcomeLoop AnyEvent spike4LinuxRuntime
      (indexInstructions 4198400 Linux.spike4Instructions) fuel after nextEventsRev := by
  rw [afterEq, eventsEq]
  exact linux_phase_outcome_edge phase phaseBound fuel state eventsRev entryRip notFaulted

theorem linuxPhaseComplete_rip (phase : Nat) (phaseBound : phase < 5)
    (state : X86_64MachineState) (entryRip : state.rip = linuxPhaseEntry phase) :
    (linuxPhaseComplete phase state).rip = linuxPhaseEntry (phase + 1) := by
  have cases : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 := by omega
  rcases cases with h | h | h | h | h <;> subst phase <;>
    simp [linuxPhaseComplete, linuxPhaseStepped, linuxAfterPhase, linuxPhaseEntry, entryRip,
      X86_64MachineState.setGpr32, X86_64MachineState.setGpr64, reg32To64]

theorem linuxPhaseComplete_fault (phase : Nat) (state : X86_64MachineState)
    (notFaulted : state.fault = none) : (linuxPhaseComplete phase state).fault = none := by
  simp [linuxPhaseComplete, linuxPhaseStepped, linuxAfterPhase,
    X86_64MachineState.setGpr32, X86_64MachineState.setGpr64, notFaulted]

theorem linuxPhaseComplete_requests (phase : Nat) (state : X86_64MachineState)
    (phaseBound : phase < 4) :
    (linuxPhaseComplete phase state).incomingRequests = state.incomingRequests := by
  have cases : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 := by omega
  rcases cases with h | h | h | h <;> subst phase <;>
    simp [linuxPhaseComplete, linuxPhaseStepped, linuxAfterPhase,
      X86_64MachineState.setGpr32, X86_64MachineState.setGpr64]

def appendRuntimeEventRev (eventsRev : List AnyEvent) : Option AnyEvent → List AnyEvent
  | some emitted => emitted :: eventsRev
  | none => eventsRev

theorem appendRuntimeEventRev_eq (eventsRev : List AnyEvent) (event : Option AnyEvent) :
    appendRuntimeEventRev eventsRev event =
      event.elim eventsRev (fun emitted => emitted :: eventsRev) := by
  cases event <;> rfl

theorem reverse_five_optional_events (e0 e1 e2 e3 e4 : Option AnyEvent) :
    ([e0, e1, e2, e3, e4].foldl appendRuntimeEventRev []).reverse =
    [e0, e1, e2, e3, e4].foldl appendRuntimeEvent [] := by
  cases e0 <;> cases e1 <;> cases e2 <;> cases e3 <;> cases e4 <;> rfl

/-- Exact reusable Linux outcome certificate. Admissibility and behavior are projections, so the
whole-program constructor does not replay global runtime/link facts. -/
structure Spike4LinuxLifecycleCertificate (environment : Environment) where
  finalState : X86_64MachineState
  events : List AnyEvent
  outcome :
    let initial := Platform.load (P := LinuxX86_64 AnyEvent) spike4LinuxArtifact environment
    @runProgramOutcomeWithLoops AnyEvent spike4LinuxRuntime 4198400
      Linux.spike4Instructions 50000 initial = .returned finalState events
  eventsSpec : events = serverEnvironmentSpec environment

set_option maxHeartbeats 300000 in
def spike4_linux_lifecycle_certificate (environment : Environment) :
    Spike4LinuxLifecycleCertificate environment := by
  letI := spike4LinuxRuntime
  let initial := Platform.load (P := LinuxX86_64 AnyEvent) spike4LinuxArtifact environment
  let s1 := linuxPhaseComplete 0 initial
  let s2 := linuxPhaseComplete 1 s1
  let s3 := linuxPhaseComplete 2 s2
  let s4 := linuxPhaseComplete 3 s3
  let s5 := linuxPhaseComplete 4 s4
  have hs1 : s1 = linuxPhaseComplete 0 initial := rfl
  have hs2 : s2 = linuxPhaseComplete 1 s1 := rfl
  have hs3 : s3 = linuxPhaseComplete 2 s2 := rfl
  have hs4 : s4 = linuxPhaseComplete 3 s3 := rfl
  have hs5 : s5 = linuxPhaseComplete 4 s4 := rfl
  have initialRip : initial.rip = linuxPhaseEntry 0 := rfl
  have initialFault : initial.fault = none := rfl
  have s1Rip : s1.rip = linuxPhaseEntry 1 :=
    linuxPhaseComplete_rip 0 (by omega) initial initialRip
  have s2Rip : s2.rip = linuxPhaseEntry 2 :=
    linuxPhaseComplete_rip 1 (by omega) s1 s1Rip
  have s3Rip : s3.rip = linuxPhaseEntry 3 :=
    linuxPhaseComplete_rip 2 (by omega) s2 s2Rip
  have s4Rip : s4.rip = linuxPhaseEntry 4 :=
    linuxPhaseComplete_rip 3 (by omega) s3 s3Rip
  have s5Rip : s5.rip = linuxPhaseEntry 5 :=
    linuxPhaseComplete_rip 4 (by omega) s4 s4Rip
  have s1Fault : s1.fault = none := linuxPhaseComplete_fault 0 initial initialFault
  have s2Fault : s2.fault = none := linuxPhaseComplete_fault 1 s1 s1Fault
  have s3Fault : s3.fault = none := linuxPhaseComplete_fault 2 s2 s2Fault
  have s4Fault : s4.fault = none := linuxPhaseComplete_fault 3 s3 s3Fault
  have initialRequests : initial.incomingRequests = environment.incomingRequests := rfl
  have s1Requests : s1.incomingRequests = initial.incomingRequests :=
    linuxPhaseComplete_requests 0 initial (by omega)
  have s2Requests : s2.incomingRequests = initial.incomingRequests := by
    rw [linuxPhaseComplete_requests 1 s1 (by omega), s1Requests]
  have s3Requests : s3.incomingRequests = initial.incomingRequests := by
    rw [linuxPhaseComplete_requests 2 s2 (by omega), s2Requests]
  have s4Requests : s4.incomingRequests = initial.incomingRequests := by
    rw [linuxPhaseComplete_requests 3 s3 (by omega), s3Requests]
  have event1 : linuxPhaseEvent 1 s1 = linuxPhaseEvent 1 initial := by
    simp only [linuxPhaseEvent]
    rw [s1Requests]
  have event2 : linuxPhaseEvent 2 s2 = linuxPhaseEvent 2 initial := by
    simp only [linuxPhaseEvent]
    rw [s2Requests]
  have event3 : linuxPhaseEvent 3 s3 = linuxPhaseEvent 3 initial := by
    simp only [linuxPhaseEvent]
    rw [s3Requests]
  have event4 : linuxPhaseEvent 4 s4 = linuxPhaseEvent 4 initial := by
    simp only [linuxPhaseEvent]
    rw [s4Requests]
  let r1 := (linuxPhaseEvent 0 initial).elim [] (fun event => [event])
  let r2 := (linuxPhaseEvent 1 s1).elim r1 (fun event => event :: r1)
  let r3 := (linuxPhaseEvent 2 s2).elim r2 (fun event => event :: r2)
  let r4 := (linuxPhaseEvent 3 s3).elim r3 (fun event => event :: r3)
  let r5 := (linuxPhaseEvent 4 s4).elim r4 (fun event => event :: r4)
  have hr1 : r1 = (linuxPhaseEvent 0 initial).elim [] (fun event => [event]) := rfl
  have hr2 : r2 = (linuxPhaseEvent 1 s1).elim r1 (fun event => event :: r1) := rfl
  have hr3 : r3 = (linuxPhaseEvent 2 s2).elim r2 (fun event => event :: r2) := rfl
  have hr4 : r4 = (linuxPhaseEvent 3 s3).elim r3 (fun event => event :: r3) := rfl
  have hr5 : r5 = (linuxPhaseEvent 4 s4).elim r4 (fun event => event :: r4) := rfl
  have initialRip' : initial.rip = 4198400 := by
    simpa [linuxPhaseEntry] using initialRip
  have done : instructionAtRipIndexed (indexInstructions 4198400 Linux.spike4Instructions)
      s5.rip = none := by rw [s5Rip]; rfl
  have outcome : runProgramOutcomeWithLoops (Event := AnyEvent) 4198400
      Linux.spike4Instructions 50000 initial = .returned s5 r5.reverse := by
    unfold runProgramOutcomeWithLoops
    calc
      runProgramOutcomeLoop (indexInstructions 4198400 Linux.spike4Instructions)
          50000 initial [] =
        runProgramOutcomeLoop (indexInstructions 4198400 Linux.spike4Instructions)
          49997 s1 r1 := by
            have edge := linux_phase_outcome_edge_named 0 (by omega) 49997
              initial s1 [] r1 initialRip initialFault hs1 hr1
            rw [show 49997 + 3 = 50000 by omega] at edge
            exact edge
      _ = runProgramOutcomeLoop (indexInstructions 4198400 Linux.spike4Instructions)
          49994 s2 r2 := by
            have edge := linux_phase_outcome_edge_named 1 (by omega) 49994
              s1 s2 r1 r2 s1Rip s1Fault hs2 hr2
            rw [show 49994 + 3 = 49997 by omega] at edge
            exact edge
      _ = runProgramOutcomeLoop (indexInstructions 4198400 Linux.spike4Instructions)
          49991 s3 r3 := by
            have edge := linux_phase_outcome_edge_named 2 (by omega) 49991
              s2 s3 r2 r3 s2Rip s2Fault hs3 hr3
            rw [show 49991 + 3 = 49994 by omega] at edge
            exact edge
      _ = runProgramOutcomeLoop (indexInstructions 4198400 Linux.spike4Instructions)
          49988 s4 r4 := by
            have edge := linux_phase_outcome_edge_named 3 (by omega) 49988
              s3 s4 r3 r4 s3Rip s3Fault hs4 hr4
            rw [show 49988 + 3 = 49991 by omega] at edge
            exact edge
      _ = runProgramOutcomeLoop (indexInstructions 4198400 Linux.spike4Instructions)
          49985 s5 r5 := by
            have edge := linux_phase_outcome_edge_named 4 (by omega) 49985
              s4 s5 r4 r5 s4Rip s4Fault hs5 hr5
            rw [show 49985 + 3 = 49988 by omega] at edge
            exact edge
      _ = .returned s5 r5.reverse := by
        rw [show 49985 = 49984 + 1 by omega]
        rw [runProgramOutcomeLoop, done]
  refine ⟨s5, r5.reverse, outcome, ?_⟩
  have r5Fold : r5 = [linuxPhaseEvent 0 initial, linuxPhaseEvent 1 s1,
      linuxPhaseEvent 2 s2, linuxPhaseEvent 3 s3, linuxPhaseEvent 4 s4].foldl
      appendRuntimeEventRev [] := by
    rw [hr5, hr4, hr3, hr2, hr1]
    simp only [List.foldl_cons, List.foldl_nil, appendRuntimeEventRev_eq]
  rw [r5Fold, reverse_five_optional_events]
  rw [event1, event2, event3, event4]
  rw [← requestRuntimeSchedule_eq environment]
  simp only [requestRuntimeSchedule, linuxPhaseEvent, initialRequests]
  simp [Nat.toUInt64]

/-- Universal Linux behavior, projected from the exact lifecycle outcome. -/
theorem spike4_linux_runtime_trace_equivalence (environment : Environment) :
    linuxRuntimeTraceFor environment = serverEnvironmentSpec environment := by
  let certificate := spike4_linux_lifecycle_certificate environment
  unfold linuxRuntimeTraceFor
  dsimp only
  rw [certificate.outcome]
  exact certificate.eventsSpec

theorem spike4_linux_runtime_admissible (environment : Environment) :
    let initial := Platform.load (P := LinuxX86_64 AnyEvent) spike4LinuxArtifact environment
    (@runProgramOutcomeWithLoops AnyEvent spike4LinuxRuntime 4198400
      Linux.spike4Instructions 50000 initial).isAdmissible true := by
  let certificate := spike4_linux_lifecycle_certificate environment
  dsimp only
  rw [certificate.outcome]
  trivial

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
