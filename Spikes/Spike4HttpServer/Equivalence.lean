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
  let initial := Platform.load (P := WindowsX86_64 AnyEvent) spike4WindowsArtifact environment
  letI := spike4WindowsRuntime
  (runProgramOutcomeWithLoops (Event := AnyEvent) 5368713216 Windows.spike4Instructions
    50000 initial).events

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
  have initialRequests : initial.incomingRequests = environment.incomingRequests := rfl
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

def windowsTextBase : UInt64 := 5368713216
def windowsParserIat : UInt64 := 5368721408
def windowsRequestRsp : UInt64 := 140737488289768

def windowsPhaseEntry (phase : Nat) : UInt64 := windowsTextBase + 7 + phase.toUInt64 * 12

def windowsPhaseDisplacement : Nat → Int32
  | 0 => 8173 | 1 => 8161 | 2 => 8149 | 3 => 8137 | 4 => 8125
  | _ => 0

def windowsPrologueState (state : X86_64MachineState) : X86_64MachineState :=
  let rsp := state.gprs .rsp
  let withRsp := state.setGpr64 .rsp (rsp - 32)
  let withFlags := withRsp.setFlagsSub64 rsp 32
  { withFlags with rip := state.rip + 7 }

theorem windows_prologue_outcome_edge (fuel : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (entryRip : state.rip = windowsTextBase)
    (notFaulted : state.fault = none) :
    @runProgramOutcomeLoop AnyEvent spike4WindowsRuntime
      (indexInstructions windowsTextBase Windows.spike4Instructions) (fuel + 1) state eventsRev =
    @runProgramOutcomeLoop AnyEvent spike4WindowsRuntime
      (indexInstructions windowsTextBase Windows.spike4Instructions) fuel
      (windowsPrologueState state) eventsRev := by
  letI := spike4WindowsRuntime
  have lookup : instructionAtRipIndexed
      (indexInstructions windowsTextBase Windows.spike4Instructions) state.rip =
      some (Instructions.sub_rsp32 32) := by
    rw [entryRip]
    rfl
  have noIntercept : (@ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      spike4WindowsRuntime (windowsPrologueState state).rip (windowsPrologueState state)) = none := by
    change (if findIatIndex (windowsPrologueState state) (windowsPrologueState state).rip = some 0
      then some (windowsParserHook (windowsPrologueState state))
      else win32Intercept (windowsPrologueState state).rip (windowsPrologueState state)) = none
    have nextRip : (windowsPrologueState state).rip = windowsTextBase + 7 := by
      simp [windowsPrologueState, entryRip]
    rw [nextRip]
    simp [findIatIndex, win32Intercept, windowsTextBase]
  have noFault : (windowsPrologueState state).fault = none := by
    change state.fault = none
    exact notFaulted
  exact native_outcome_step_none _ fuel state (windowsPrologueState state) eventsRev _
    lookup rfl noIntercept noFault

theorem windowsPrologue_rip (state : X86_64MachineState)
    (entryRip : state.rip = windowsTextBase) :
    (windowsPrologueState state).rip = windowsPhaseEntry 0 := by
  simp [windowsPrologueState, windowsPhaseEntry, entryRip]

theorem windowsPrologue_rsp (state : X86_64MachineState)
    (rsp : state.rsp = 140737488289800) :
    (windowsPrologueState state).rsp = windowsRequestRsp := by
  change state.gprs .rsp = 140737488289800 at rsp
  simp [windowsPrologueState, X86_64MachineState.rsp, X86_64MachineState.setGpr64,
    X86_64MachineState.setFlagsSub64, X86_64MachineState.setFlagsCmp64,
    windowsRequestRsp, rsp]

theorem windows_push_preserves_parser_iat (state : X86_64MachineState)
    (rsp : state.rsp = windowsRequestRsp)
    (iat : state.read64 windowsParserIat = windowsParserIat) (value : UInt64) :
    (state.push64 value).read64 windowsParserIat = windowsParserIat := by
  change state.gprs .rsp = windowsRequestRsp at rsp
  change X86_64Mem.read .w64 windowsParserIat
      (X86_64Mem.write .w64 (state.gprs .rsp - 8) value state.memory) = windowsParserIat
  rw [rsp]
  change X86_64Mem.read .w64 windowsParserIat
      (X86_64Mem.write .w64 (windowsRequestRsp - 8) value state.memory) = windowsParserIat
  simp [X86_64Mem.read, X86_64Mem.write, X86_64Mem.readByte,
    windowsRequestRsp, windowsParserIat]
  exact iat

def windowsPhaseStepped (phase : Nat) (state : X86_64MachineState) : X86_64MachineState :=
  let moved := { (state.setGpr32 .r9d phase.toUInt32) with rip := state.rip + 6 }
  { (moved.push64 (moved.rip + 6)) with rip := windowsParserIat }

def windowsPhaseComplete (phase : Nat) (state : X86_64MachineState) : X86_64MachineState :=
  windowsAfterPhase phase.toUInt64 (windowsPhaseStepped phase state)

def windowsPhaseEvent (phase : Nat) (state : X86_64MachineState) : Option AnyEvent :=
  requestRuntimeEvent phase.toUInt64 (!state.incomingRequests.isEmpty)
    (parserInput state.incomingRequests)

theorem windows_phase_lookup0 (phase : Nat) (phaseBound : phase < 5) :
    instructionAtRipIndexed (indexInstructions windowsTextBase Windows.spike4Instructions)
      (windowsPhaseEntry phase) = some (Instructions.mov_r32 .r9d phase.toUInt32) := by
  have cases : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 := by omega
  rcases cases with h | h | h | h | h <;> subst phase <;> rfl

theorem windows_phase_lookup1 (phase : Nat) (phaseBound : phase < 5) :
    instructionAtRipIndexed (indexInstructions windowsTextBase Windows.spike4Instructions)
      (windowsPhaseEntry phase + 6) =
      some (Instructions.call_rip (windowsPhaseDisplacement phase)) := by
  have cases : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 := by omega
  rcases cases with h | h | h | h | h <;> subst phase <;> rfl

theorem windows_phase_outcome_edge (phase : Nat) (phaseBound : phase < 5)
    (fuel : Nat) (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (entryRip : state.rip = windowsPhaseEntry phase) (notFaulted : state.fault = none)
    (rsp : state.rsp = windowsRequestRsp)
    (iat : state.read64 windowsParserIat = windowsParserIat) :
    @runProgramOutcomeLoop AnyEvent spike4WindowsRuntime
      (indexInstructions windowsTextBase Windows.spike4Instructions) (fuel + 2) state eventsRev =
    @runProgramOutcomeLoop AnyEvent spike4WindowsRuntime
      (indexInstructions windowsTextBase Windows.spike4Instructions) fuel
      (windowsPhaseComplete phase state)
      ((windowsPhaseEvent phase state).elim eventsRev fun event => event :: eventsRev) := by
  letI := spike4WindowsRuntime
  let indexed := indexInstructions windowsTextBase Windows.spike4Instructions
  let moved := { (state.setGpr32 .r9d phase.toUInt32) with rip := state.rip + 6 }
  let called := { (moved.push64 (moved.rip + 6)) with rip := windowsParserIat }
  have moveStep : Instructions.X86_64Instruction.step
      (Instructions.mov_r32 .r9d phase.toUInt32) state = moved := rfl
  have movedRip : moved.rip = windowsPhaseEntry phase + 6 := by simp [moved, entryRip]
  have movedRsp : moved.rsp = windowsRequestRsp := by
    change state.rsp = windowsRequestRsp
    exact rsp
  have movedIat : moved.read64 windowsParserIat = windowsParserIat := by
    change state.read64 windowsParserIat = windowsParserIat
    exact iat
  have calledIat : called.read64 windowsParserIat = windowsParserIat := by
    change (moved.push64 (moved.rip + 6)).read64 windowsParserIat = windowsParserIat
    exact windows_push_preserves_parser_iat moved movedRsp movedIat _
  have callStep : Instructions.X86_64Instruction.step
      (Instructions.call_rip (windowsPhaseDisplacement phase)) moved = called := by
    have target : moved.rip + 6 +
        Instructions.signExtend32To64 (windowsPhaseDisplacement phase) = windowsParserIat := by
      rw [movedRip]
      have cases : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 := by omega
      rcases cases with h | h | h | h | h <;> subst phase <;> native_decide
    change { (moved.push64 (moved.rip + 6)) with
      rip := moved.read64 (moved.rip + 6 +
        Instructions.signExtend32To64 (windowsPhaseDisplacement phase)) } = called
    rw [target, movedIat]
  have noMoveIntercept : (@ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      spike4WindowsRuntime moved.rip moved) = none := by
    change (if findIatIndex moved moved.rip = some 0 then some (windowsParserHook moved)
      else win32Intercept moved.rip moved) = none
    rw [movedRip]
    have unaligned : (windowsPhaseEntry phase + 6) % 8 ≠ 0 := by
      have cases : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 := by omega
      rcases cases with h | h | h | h | h <;> subst phase <;> native_decide
    simp [findIatIndex, win32Intercept, unaligned]
  have movedFault : moved.fault = none := by
    change state.fault = none
    exact notFaulted
  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
    native_outcome_step_none indexed (fuel + 1) state moved eventsRev _
      (by simpa [indexed, entryRip] using windows_phase_lookup0 phase phaseBound)
      moveStep noMoveIntercept movedFault]
  have findProvider : findIatIndex called windowsParserIat = some 0 := by
    unfold findIatIndex
    rw [calledIat]
    native_decide
  have calledPhase : called.gprs .r9 = phase.toUInt64 := by
    have cases : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 := by omega
    rcases cases with h | h | h | h | h <;> subst phase <;>
      simp [called, moved, X86_64MachineState.push64, X86_64MachineState.setGpr32,
        X86_64MachineState.setGpr64, reg32To64]
  have calledRequests : called.incomingRequests = state.incomingRequests := rfl
  have callIntercept : (@ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      spike4WindowsRuntime called.rip called) =
      some (windowsAfterPhase phase.toUInt64 called, windowsPhaseEvent phase state) := by
    change (if findIatIndex called called.rip = some 0 then some (windowsParserHook called)
      else win32Intercept called.rip called) = _
    rw [if_pos (by simpa [called] using findProvider)]
    simp [windowsParserHook, windowsPhaseEvent, calledPhase, calledRequests]
  have completeFault : (windowsAfterPhase phase.toUInt64 called).fault = none := by
    change called.fault = none
    change state.fault = none
    exact notFaulted
  rw [native_outcome_step_boundary indexed fuel moved called
    (windowsAfterPhase phase.toUInt64 called) eventsRev _ _
    (by simpa [indexed, movedRip] using windows_phase_lookup1 phase phaseBound)
    callStep callIntercept completeFault]
  rfl

theorem windows_phase_outcome_edge_named (phase : Nat) (phaseBound : phase < 5)
    (fuel : Nat) (state after : X86_64MachineState)
    (eventsRev nextEventsRev : List AnyEvent)
    (entryRip : state.rip = windowsPhaseEntry phase) (notFaulted : state.fault = none)
    (rsp : state.rsp = windowsRequestRsp)
    (iat : state.read64 windowsParserIat = windowsParserIat)
    (afterEq : after = windowsPhaseComplete phase state)
    (eventsEq : nextEventsRev =
      (windowsPhaseEvent phase state).elim eventsRev (fun event => event :: eventsRev)) :
    @runProgramOutcomeLoop AnyEvent spike4WindowsRuntime
      (indexInstructions windowsTextBase Windows.spike4Instructions) (fuel + 2) state eventsRev =
    @runProgramOutcomeLoop AnyEvent spike4WindowsRuntime
      (indexInstructions windowsTextBase Windows.spike4Instructions) fuel after nextEventsRev := by
  rw [afterEq, eventsEq]
  exact windows_phase_outcome_edge phase phaseBound fuel state eventsRev
    entryRip notFaulted rsp iat

theorem windows_prologue_outcome_edge_named (fuel : Nat)
    (state after : X86_64MachineState) (eventsRev : List AnyEvent)
    (entryRip : state.rip = windowsTextBase) (notFaulted : state.fault = none)
    (afterEq : after = windowsPrologueState state) :
    @runProgramOutcomeLoop AnyEvent spike4WindowsRuntime
      (indexInstructions windowsTextBase Windows.spike4Instructions) (fuel + 1) state eventsRev =
    @runProgramOutcomeLoop AnyEvent spike4WindowsRuntime
      (indexInstructions windowsTextBase Windows.spike4Instructions) fuel after eventsRev := by
  rw [afterEq]
  exact windows_prologue_outcome_edge fuel state eventsRev entryRip notFaulted

theorem windowsPhaseComplete_rip (phase : Nat) (phaseBound : phase < 5)
    (state : X86_64MachineState) (entryRip : state.rip = windowsPhaseEntry phase) :
    (windowsPhaseComplete phase state).rip = windowsPhaseEntry (phase + 1) := by
  let moved := { (state.setGpr32 .r9d phase.toUInt32) with rip := state.rip + 6 }
  let called := { (moved.push64 (moved.rip + 6)) with rip := windowsParserIat }
  have poppedRip : (popReturnAddress called).rip = moved.rip + 6 := by
    simp [popReturnAddress, called, X86_64MachineState.push64, X86_64MachineState.pop64,
      X86_64MachineState.rsp, X86_64MachineState.read64, X86_64MachineState.write64,
      X86_64Mem.read64_write64_same, X86_64MachineState.setGpr64]
  have completeRip : (windowsPhaseComplete phase state).rip = moved.rip + 6 := by
    change (windowsAfterPhase phase.toUInt64 called).rip = moved.rip + 6
    change (popReturnAddress called).rip = moved.rip + 6
    exact poppedRip
  rw [completeRip]
  have movedRip : moved.rip = windowsPhaseEntry phase + 6 := by simp [moved, entryRip]
  rw [movedRip]
  have cases : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 := by omega
  rcases cases with h | h | h | h | h <;> subst phase <;> native_decide

theorem windowsPhaseComplete_rsp (phase : Nat) (state : X86_64MachineState)
    (rsp : state.rsp = windowsRequestRsp) :
    (windowsPhaseComplete phase state).rsp = windowsRequestRsp := by
  let moved := { (state.setGpr32 .r9d phase.toUInt32) with rip := state.rip + 6 }
  let called := { (moved.push64 (moved.rip + 6)) with rip := windowsParserIat }
  have movedRsp : moved.rsp = windowsRequestRsp := by
    change state.rsp = windowsRequestRsp
    exact rsp
  have poppedRsp : (popReturnAddress called).rsp = moved.rsp := by
    simp [popReturnAddress, called, X86_64MachineState.push64, X86_64MachineState.pop64,
      X86_64MachineState.rsp, X86_64MachineState.setGpr64]
  change (windowsAfterPhase phase.toUInt64 called).rsp = windowsRequestRsp
  change (popReturnAddress called).rsp = windowsRequestRsp
  rw [poppedRsp, movedRsp]

theorem windowsPhaseComplete_iat (phase : Nat) (state : X86_64MachineState)
    (rsp : state.rsp = windowsRequestRsp)
    (iat : state.read64 windowsParserIat = windowsParserIat) :
    (windowsPhaseComplete phase state).read64 windowsParserIat = windowsParserIat := by
  let moved := { (state.setGpr32 .r9d phase.toUInt32) with rip := state.rip + 6 }
  have movedRsp : moved.rsp = windowsRequestRsp := by
    change state.rsp = windowsRequestRsp
    exact rsp
  have movedIat : moved.read64 windowsParserIat = windowsParserIat := by
    change state.read64 windowsParserIat = windowsParserIat
    exact iat
  have pushed := windows_push_preserves_parser_iat moved movedRsp movedIat (moved.rip + 6)
  change (moved.push64 (moved.rip + 6)).read64 windowsParserIat = windowsParserIat
  exact pushed

theorem windowsPhaseComplete_fault (phase : Nat) (state : X86_64MachineState)
    (notFaulted : state.fault = none) : (windowsPhaseComplete phase state).fault = none := by
  change state.fault = none
  exact notFaulted

theorem windowsPhaseComplete_requests (phase : Nat) (state : X86_64MachineState)
    (phaseBound : phase < 4) :
    (windowsPhaseComplete phase state).incomingRequests = state.incomingRequests := by
  have cases : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 := by omega
  rcases cases with h | h | h | h <;> subst phase <;>
    simp [windowsPhaseComplete, windowsPhaseStepped, windowsAfterPhase, popReturnAddress,
      X86_64MachineState.push64, X86_64MachineState.pop64,
      X86_64MachineState.setGpr32, X86_64MachineState.setGpr64]

def windowsLifecycleInitial (environment : Environment) : X86_64MachineState :=
  Platform.load (P := WindowsX86_64 AnyEvent) spike4WindowsArtifact environment

def windowsLifecyclePrologue (environment : Environment) : X86_64MachineState :=
  windowsPrologueState (windowsLifecycleInitial environment)

def windowsLifecycleState1 (environment : Environment) : X86_64MachineState :=
  windowsPhaseComplete 0 (windowsLifecyclePrologue environment)

def windowsLifecycleState2 (environment : Environment) : X86_64MachineState :=
  windowsPhaseComplete 1 (windowsLifecycleState1 environment)

def windowsLifecycleState3 (environment : Environment) : X86_64MachineState :=
  windowsPhaseComplete 2 (windowsLifecycleState2 environment)

def windowsLifecycleState4 (environment : Environment) : X86_64MachineState :=
  windowsPhaseComplete 3 (windowsLifecycleState3 environment)

def windowsLifecycleState5 (environment : Environment) : X86_64MachineState :=
  windowsPhaseComplete 4 (windowsLifecycleState4 environment)

def windowsLifecycleEvents1 (environment : Environment) : List AnyEvent :=
  appendRuntimeEventRev [] (windowsPhaseEvent 0 (windowsLifecyclePrologue environment))

def windowsLifecycleEvents2 (environment : Environment) : List AnyEvent :=
  appendRuntimeEventRev (windowsLifecycleEvents1 environment)
    (windowsPhaseEvent 1 (windowsLifecycleState1 environment))

def windowsLifecycleEvents3 (environment : Environment) : List AnyEvent :=
  appendRuntimeEventRev (windowsLifecycleEvents2 environment)
    (windowsPhaseEvent 2 (windowsLifecycleState2 environment))

def windowsLifecycleEvents4 (environment : Environment) : List AnyEvent :=
  appendRuntimeEventRev (windowsLifecycleEvents3 environment)
    (windowsPhaseEvent 3 (windowsLifecycleState3 environment))

def windowsLifecycleEvents5 (environment : Environment) : List AnyEvent :=
  appendRuntimeEventRev (windowsLifecycleEvents4 environment)
    (windowsPhaseEvent 4 (windowsLifecycleState4 environment))

structure Spike4WindowsLifecycleCertificate (environment : Environment) where
  finalState : X86_64MachineState
  events : List AnyEvent
  outcome :
    let initial := Platform.load (P := WindowsX86_64 AnyEvent) spike4WindowsArtifact environment
    @runProgramOutcomeWithLoops AnyEvent spike4WindowsRuntime windowsTextBase
      Windows.spike4Instructions 50000 initial = .returned finalState events
  eventsSpec : events = serverEnvironmentSpec environment

set_option maxHeartbeats 400000 in
theorem windows_lifecycle_outcome (environment : Environment) :
    @runProgramOutcomeWithLoops AnyEvent spike4WindowsRuntime windowsTextBase
      Windows.spike4Instructions 50000 (windowsLifecycleInitial environment) =
        .returned (windowsLifecycleState5 environment) (windowsLifecycleEvents5 environment).reverse := by
  letI := spike4WindowsRuntime
  let initial := windowsLifecycleInitial environment
  let prologue := windowsLifecyclePrologue environment
  let s1 := windowsLifecycleState1 environment
  let s2 := windowsLifecycleState2 environment
  let s3 := windowsLifecycleState3 environment
  let s4 := windowsLifecycleState4 environment
  let s5 := windowsLifecycleState5 environment
  have hprologue : prologue = windowsPrologueState initial := rfl
  have hs1 : s1 = windowsPhaseComplete 0 prologue := rfl
  have hs2 : s2 = windowsPhaseComplete 1 s1 := rfl
  have hs3 : s3 = windowsPhaseComplete 2 s2 := rfl
  have hs4 : s4 = windowsPhaseComplete 3 s3 := rfl
  have hs5 : s5 = windowsPhaseComplete 4 s4 := rfl
  have initialRip : initial.rip = windowsTextBase := rfl
  have initialFault : initial.fault = none := rfl
  have initialRsp : initial.rsp = 140737488289800 := rfl
  have initialIat : initial.read64 windowsParserIat = windowsParserIat := by
    change Windows.spike4Executable.load.read64 windowsParserIat = windowsParserIat
    native_decide
  have initialRequests : initial.incomingRequests = environment.incomingRequests := rfl
  have prologueRip : prologue.rip = windowsPhaseEntry 0 :=
    windowsPrologue_rip initial initialRip
  have prologueFault : prologue.fault = none := by
    change initial.fault = none
    exact initialFault
  have prologueRsp : prologue.rsp = windowsRequestRsp :=
    windowsPrologue_rsp initial initialRsp
  have prologueIat : prologue.read64 windowsParserIat = windowsParserIat := by
    change initial.read64 windowsParserIat = windowsParserIat
    exact initialIat
  have s1Rip : s1.rip = windowsPhaseEntry 1 :=
    windowsPhaseComplete_rip 0 (by omega) prologue prologueRip
  have s2Rip : s2.rip = windowsPhaseEntry 2 :=
    windowsPhaseComplete_rip 1 (by omega) s1 s1Rip
  have s3Rip : s3.rip = windowsPhaseEntry 3 :=
    windowsPhaseComplete_rip 2 (by omega) s2 s2Rip
  have s4Rip : s4.rip = windowsPhaseEntry 4 :=
    windowsPhaseComplete_rip 3 (by omega) s3 s3Rip
  have s5Rip : s5.rip = windowsPhaseEntry 5 :=
    windowsPhaseComplete_rip 4 (by omega) s4 s4Rip
  have s1Fault := windowsPhaseComplete_fault 0 prologue prologueFault
  have s2Fault := windowsPhaseComplete_fault 1 s1 s1Fault
  have s3Fault := windowsPhaseComplete_fault 2 s2 s2Fault
  have s4Fault := windowsPhaseComplete_fault 3 s3 s3Fault
  have s1Rsp := windowsPhaseComplete_rsp 0 prologue prologueRsp
  have s2Rsp := windowsPhaseComplete_rsp 1 s1 s1Rsp
  have s3Rsp := windowsPhaseComplete_rsp 2 s2 s2Rsp
  have s4Rsp := windowsPhaseComplete_rsp 3 s3 s3Rsp
  have s1Iat := windowsPhaseComplete_iat 0 prologue prologueRsp prologueIat
  have s2Iat := windowsPhaseComplete_iat 1 s1 s1Rsp s1Iat
  have s3Iat := windowsPhaseComplete_iat 2 s2 s2Rsp s2Iat
  have s4Iat := windowsPhaseComplete_iat 3 s3 s3Rsp s3Iat
  let r1 := windowsLifecycleEvents1 environment
  let r2 := windowsLifecycleEvents2 environment
  let r3 := windowsLifecycleEvents3 environment
  let r4 := windowsLifecycleEvents4 environment
  let r5 := windowsLifecycleEvents5 environment
  have hr1 : r1 = (windowsPhaseEvent 0 prologue).elim [] (fun event => [event]) := by
    exact appendRuntimeEventRev_eq [] (windowsPhaseEvent 0 prologue)
  have hr2 : r2 = (windowsPhaseEvent 1 s1).elim r1 (fun event => event :: r1) := by
    exact appendRuntimeEventRev_eq r1 (windowsPhaseEvent 1 s1)
  have hr3 : r3 = (windowsPhaseEvent 2 s2).elim r2 (fun event => event :: r2) := by
    exact appendRuntimeEventRev_eq r2 (windowsPhaseEvent 2 s2)
  have hr4 : r4 = (windowsPhaseEvent 3 s3).elim r3 (fun event => event :: r3) := by
    exact appendRuntimeEventRev_eq r3 (windowsPhaseEvent 3 s3)
  have hr5 : r5 = (windowsPhaseEvent 4 s4).elim r4 (fun event => event :: r4) := by
    exact appendRuntimeEventRev_eq r4 (windowsPhaseEvent 4 s4)
  have done : instructionAtRipIndexed (indexInstructions windowsTextBase Windows.spike4Instructions)
      s5.rip = none := by rw [s5Rip]; rfl
  have outcome : @runProgramOutcomeWithLoops AnyEvent spike4WindowsRuntime windowsTextBase
      Windows.spike4Instructions 50000 initial = .returned s5 r5.reverse := by
    unfold runProgramOutcomeWithLoops
    calc
      @runProgramOutcomeLoop AnyEvent spike4WindowsRuntime
          (indexInstructions windowsTextBase Windows.spike4Instructions) 50000 initial [] =
        @runProgramOutcomeLoop AnyEvent spike4WindowsRuntime
          (indexInstructions windowsTextBase Windows.spike4Instructions) 49999 prologue [] := by
            have edge := windows_prologue_outcome_edge_named 49999 initial prologue []
              initialRip initialFault hprologue
            rw [show 49999 + 1 = 50000 by omega] at edge
            exact edge
      _ = @runProgramOutcomeLoop AnyEvent spike4WindowsRuntime
          (indexInstructions windowsTextBase Windows.spike4Instructions) 49997 s1 r1 := by
            have edge := windows_phase_outcome_edge_named 0 (by omega) 49997 prologue s1 [] r1
              prologueRip prologueFault prologueRsp prologueIat hs1 hr1
            rw [show 49997 + 2 = 49999 by omega] at edge
            exact edge
      _ = @runProgramOutcomeLoop AnyEvent spike4WindowsRuntime
          (indexInstructions windowsTextBase Windows.spike4Instructions) 49995 s2 r2 := by
            have edge := windows_phase_outcome_edge_named 1 (by omega) 49995 s1 s2 r1 r2
              s1Rip s1Fault s1Rsp s1Iat hs2 hr2
            rw [show 49995 + 2 = 49997 by omega] at edge
            exact edge
      _ = @runProgramOutcomeLoop AnyEvent spike4WindowsRuntime
          (indexInstructions windowsTextBase Windows.spike4Instructions) 49993 s3 r3 := by
            have edge := windows_phase_outcome_edge_named 2 (by omega) 49993 s2 s3 r2 r3
              s2Rip s2Fault s2Rsp s2Iat hs3 hr3
            rw [show 49993 + 2 = 49995 by omega] at edge
            exact edge
      _ = @runProgramOutcomeLoop AnyEvent spike4WindowsRuntime
          (indexInstructions windowsTextBase Windows.spike4Instructions) 49991 s4 r4 := by
            have edge := windows_phase_outcome_edge_named 3 (by omega) 49991 s3 s4 r3 r4
              s3Rip s3Fault s3Rsp s3Iat hs4 hr4
            rw [show 49991 + 2 = 49993 by omega] at edge
            exact edge
      _ = @runProgramOutcomeLoop AnyEvent spike4WindowsRuntime
          (indexInstructions windowsTextBase Windows.spike4Instructions) 49989 s5 r5 := by
            have edge := windows_phase_outcome_edge_named 4 (by omega) 49989 s4 s5 r4 r5
              s4Rip s4Fault s4Rsp s4Iat hs5 hr5
            rw [show 49989 + 2 = 49991 by omega] at edge
            exact edge
      _ = .returned s5 r5.reverse := by
        rw [show 49989 = 49988 + 1 by omega]
        rw [runProgramOutcomeLoop, done]
  exact outcome

theorem windowsLifecycleInitial_requests (environment : Environment) :
    (windowsLifecycleInitial environment).incomingRequests = environment.incomingRequests := rfl

theorem windowsLifecyclePrologue_requests (environment : Environment) :
    (windowsLifecyclePrologue environment).incomingRequests =
      (windowsLifecycleInitial environment).incomingRequests := rfl

theorem windowsLifecycleState1_requests (environment : Environment) :
    (windowsLifecycleState1 environment).incomingRequests =
      (windowsLifecycleInitial environment).incomingRequests := by
  rw [show windowsLifecycleState1 environment =
    windowsPhaseComplete 0 (windowsLifecyclePrologue environment) by rfl]
  rw [windowsPhaseComplete_requests 0 (windowsLifecyclePrologue environment) (by omega)]
  exact windowsLifecyclePrologue_requests environment

theorem windowsLifecycleState2_requests (environment : Environment) :
    (windowsLifecycleState2 environment).incomingRequests =
      (windowsLifecycleInitial environment).incomingRequests := by
  rw [show windowsLifecycleState2 environment =
    windowsPhaseComplete 1 (windowsLifecycleState1 environment) by rfl]
  rw [windowsPhaseComplete_requests 1 (windowsLifecycleState1 environment) (by omega)]
  exact windowsLifecycleState1_requests environment

theorem windowsLifecycleState3_requests (environment : Environment) :
    (windowsLifecycleState3 environment).incomingRequests =
      (windowsLifecycleInitial environment).incomingRequests := by
  rw [show windowsLifecycleState3 environment =
    windowsPhaseComplete 2 (windowsLifecycleState2 environment) by rfl]
  rw [windowsPhaseComplete_requests 2 (windowsLifecycleState2 environment) (by omega)]
  exact windowsLifecycleState2_requests environment

theorem windowsLifecycleState4_requests (environment : Environment) :
    (windowsLifecycleState4 environment).incomingRequests =
      (windowsLifecycleInitial environment).incomingRequests := by
  rw [show windowsLifecycleState4 environment =
    windowsPhaseComplete 3 (windowsLifecycleState3 environment) by rfl]
  rw [windowsPhaseComplete_requests 3 (windowsLifecycleState3 environment) (by omega)]
  exact windowsLifecycleState3_requests environment

theorem windowsLifecycleEvent1_eq (environment : Environment) :
    windowsPhaseEvent 1 (windowsLifecycleState1 environment) =
      windowsPhaseEvent 1 (windowsLifecyclePrologue environment) := by
  simp only [windowsPhaseEvent]
  rw [windowsLifecycleState1_requests, windowsLifecyclePrologue_requests]

theorem windowsLifecycleEvent2_eq (environment : Environment) :
    windowsPhaseEvent 2 (windowsLifecycleState2 environment) =
      windowsPhaseEvent 2 (windowsLifecyclePrologue environment) := by
  simp only [windowsPhaseEvent]
  rw [windowsLifecycleState2_requests, windowsLifecyclePrologue_requests]

theorem windowsLifecycleEvent3_eq (environment : Environment) :
    windowsPhaseEvent 3 (windowsLifecycleState3 environment) =
      windowsPhaseEvent 3 (windowsLifecyclePrologue environment) := by
  simp only [windowsPhaseEvent]
  rw [windowsLifecycleState3_requests, windowsLifecyclePrologue_requests]

theorem windowsLifecycleEvent4_eq (environment : Environment) :
    windowsPhaseEvent 4 (windowsLifecycleState4 environment) =
      windowsPhaseEvent 4 (windowsLifecyclePrologue environment) := by
  simp only [windowsPhaseEvent]
  rw [windowsLifecycleState4_requests, windowsLifecyclePrologue_requests]

theorem windowsLifecycleEvents1_fold (environment : Environment) :
    windowsLifecycleEvents1 environment =
      [windowsPhaseEvent 0 (windowsLifecyclePrologue environment)].foldl
        appendRuntimeEventRev [] := rfl

theorem windowsLifecycleEvents2_fold (environment : Environment) :
    windowsLifecycleEvents2 environment =
      [windowsPhaseEvent 0 (windowsLifecyclePrologue environment),
       windowsPhaseEvent 1 (windowsLifecycleState1 environment)].foldl
        appendRuntimeEventRev [] := rfl

theorem windowsLifecycleEvents3_fold (environment : Environment) :
    windowsLifecycleEvents3 environment =
      [windowsPhaseEvent 0 (windowsLifecyclePrologue environment),
       windowsPhaseEvent 1 (windowsLifecycleState1 environment),
       windowsPhaseEvent 2 (windowsLifecycleState2 environment)].foldl
        appendRuntimeEventRev [] := rfl

theorem windowsLifecycleEvents4_fold (environment : Environment) :
    windowsLifecycleEvents4 environment =
      [windowsPhaseEvent 0 (windowsLifecyclePrologue environment),
       windowsPhaseEvent 1 (windowsLifecycleState1 environment),
       windowsPhaseEvent 2 (windowsLifecycleState2 environment),
       windowsPhaseEvent 3 (windowsLifecycleState3 environment)].foldl
        appendRuntimeEventRev [] := rfl

theorem windowsLifecycleEvents5_fold (environment : Environment) :
    windowsLifecycleEvents5 environment =
      [windowsPhaseEvent 0 (windowsLifecyclePrologue environment),
       windowsPhaseEvent 1 (windowsLifecycleState1 environment),
       windowsPhaseEvent 2 (windowsLifecycleState2 environment),
       windowsPhaseEvent 3 (windowsLifecycleState3 environment),
       windowsPhaseEvent 4 (windowsLifecycleState4 environment)].foldl
        appendRuntimeEventRev [] := rfl

theorem windows_lifecycle_events_spec (environment : Environment) :
    (windowsLifecycleEvents5 environment).reverse = serverEnvironmentSpec environment := by
  rw [windowsLifecycleEvents5_fold, reverse_five_optional_events]
  rw [windowsLifecycleEvent1_eq, windowsLifecycleEvent2_eq,
    windowsLifecycleEvent3_eq, windowsLifecycleEvent4_eq]
  rw [← requestRuntimeSchedule_eq environment]
  simp only [requestRuntimeSchedule, windowsPhaseEvent, windowsLifecyclePrologue_requests,
    windowsLifecycleInitial_requests]
  simp [Nat.toUInt64]

def spike4_windows_lifecycle_certificate (environment : Environment) :
    Spike4WindowsLifecycleCertificate environment :=
  { finalState := windowsLifecycleState5 environment
    events := (windowsLifecycleEvents5 environment).reverse
    outcome := by
      change @runProgramOutcomeWithLoops AnyEvent spike4WindowsRuntime windowsTextBase
        Windows.spike4Instructions 50000 (windowsLifecycleInitial environment) = _
      exact windows_lifecycle_outcome environment
    eventsSpec := windows_lifecycle_events_spec environment }

theorem spike4_windows_runtime_trace_equivalence (environment : Environment) :
    windowsRuntimeTraceFor environment = serverEnvironmentSpec environment := by
  let certificate := spike4_windows_lifecycle_certificate environment
  unfold windowsRuntimeTraceFor
  dsimp only
  have outcome := certificate.outcome
  simp only [windowsTextBase] at outcome
  rw [outcome]
  exact certificate.eventsSpec

theorem spike4_windows_runtime_admissible (environment : Environment) :
    let initial := Platform.load (P := WindowsX86_64 AnyEvent) spike4WindowsArtifact environment
    (@runProgramOutcomeWithLoops AnyEvent spike4WindowsRuntime windowsTextBase
      Windows.spike4Instructions 50000 initial).isAdmissible false := by
  let certificate := spike4_windows_lifecycle_certificate environment
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
