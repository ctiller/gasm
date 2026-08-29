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

import Spikes.Spike5Gzip.Runtime

namespace Spikes.Spike5Gzip

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.Windows
open Stdlib.Zlib

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem trace_step_event {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (baseRip : UInt64) (instructions : List X86_64Instr) (fuel : Nat)
    (state hooked : X86_64MachineState) (instruction : X86_64Instr) (event : Event)
    (hlookup : instructionAtRipIndexed (indexInstructions baseRip instructions) state.rip =
      some instruction)
    (hintercept : interceptor.interceptCall
      (X86_64Instruction.step instruction state).rip
      (X86_64Instruction.step instruction state) = some (hooked, some event))
    (hfault : hooked.faulted = false) :
    runProgramTraceWithLoops baseRip instructions (fuel + 1) state =
      event :: runProgramTraceWithLoops baseRip instructions fuel hooked := by
  simp [runProgramTraceWithLoops, runProgramTraceWithLoops.loop, hlookup,
    hintercept, hfault]

theorem trace_step_silent {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (baseRip : UInt64) (instructions : List X86_64Instr) (fuel : Nat)
    (state hooked : X86_64MachineState) (instruction : X86_64Instr)
    (hlookup : instructionAtRipIndexed (indexInstructions baseRip instructions) state.rip =
      some instruction)
    (hintercept : interceptor.interceptCall
      (X86_64Instruction.step instruction state).rip
      (X86_64Instruction.step instruction state) = some (hooked, (none : Option Event)))
    (hfault : hooked.faulted = false) :
    runProgramTraceWithLoops (Event := Event) baseRip instructions (fuel + 1) state =
      runProgramTraceWithLoops (Event := Event) baseRip instructions fuel hooked := by
  simp [runProgramTraceWithLoops, runProgramTraceWithLoops.loop, hlookup,
    hintercept, hfault]

theorem trace_complete {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (baseRip : UInt64) (instructions : List X86_64Instr) (fuel : Nat)
    (state : X86_64MachineState)
    (hlookup : instructionAtRipIndexed (indexInstructions baseRip instructions) state.rip = none) :
    runProgramTraceWithLoops (Event := Event) baseRip instructions (fuel + 1) state = [] := by
  simp [runProgramTraceWithLoops, runProgramTraceWithLoops.loop, hlookup]

theorem outcome_step_event {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (indexed : List (Address × X86_64Instr)) (fuel : Nat)
    (state hooked : X86_64MachineState) (instruction : X86_64Instr)
    (eventsRev : List Event) (event : Event)
    (hlookup : instructionAtRipIndexed indexed state.rip = some instruction)
    (hintercept : interceptor.interceptCall
      (X86_64Instruction.step instruction state).rip
      (X86_64Instruction.step instruction state) = some (hooked, some event))
    (hfault : hooked.faulted = false) :
    runProgramOutcomeWithLoops.loop indexed (fuel + 1) state eventsRev =
      runProgramOutcomeWithLoops.loop indexed fuel hooked (event :: eventsRev) := by
  simp [runProgramOutcomeWithLoops.loop, hlookup, hintercept, hfault]

theorem outcome_step_silent {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (indexed : List (Address × X86_64Instr)) (fuel : Nat)
    (state hooked : X86_64MachineState) (instruction : X86_64Instr)
    (eventsRev : List Event)
    (hlookup : instructionAtRipIndexed indexed state.rip = some instruction)
    (hintercept : interceptor.interceptCall
      (X86_64Instruction.step instruction state).rip
      (X86_64Instruction.step instruction state) = some (hooked, none))
    (hfault : hooked.faulted = false) :
    runProgramOutcomeWithLoops.loop indexed (fuel + 1) state eventsRev =
      runProgramOutcomeWithLoops.loop indexed fuel hooked eventsRev := by
  simp [runProgramOutcomeWithLoops.loop, hlookup, hintercept, hfault]

theorem outcome_complete {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (indexed : List (Address × X86_64Instr)) (fuel : Nat)
    (state : X86_64MachineState) (eventsRev : List Event)
    (hlookup : instructionAtRipIndexed indexed state.rip = none) :
    runProgramOutcomeWithLoops.loop indexed (fuel + 1) state eventsRev =
      .completed state eventsRev.reverse := by
  simp [runProgramOutcomeWithLoops.loop, hlookup]

/- Each native call edge is proved once from its source state to its destination
   state.  Whole-program certificates compose these local edges; they do not
   replay provider/linkage facts at every call site. -/
structure SilentNativeEdgeCertificate {Event : Type}
    (interceptor : ExternalCallInterceptor X86_64 Event)
    (baseRip : Address) (instructions : List X86_64Instr)
    (source destination : X86_64MachineState) where
  instruction : X86_64Instr
  lookup : instructionAtRipIndexed (indexInstructions baseRip instructions) source.rip =
    some instruction
  intercept : let stepped := X86_64Instruction.step instruction source
    interceptor.interceptCall stepped.rip stepped =
      some (destination, none)
  safe : destination.faulted = false

theorem lookup_first_instruction (baseRip : Address) (instruction : X86_64Instr)
    (rest : List X86_64Instr) :
    instructionAtRipIndexed (indexInstructions baseRip (instruction :: rest)) baseRip =
      some instruction := by
  change (if baseRip == baseRip then some instruction else _) = some instruction
  simp

@[simp] theorem call_rel32_step_rip (state : X86_64MachineState)
    (displacement : Int32) :
    (X86_64Instruction.step (call_rel32 displacement) state).rip =
      state.rip + 5 + signExtend32To64 displacement := by
  rfl

theorem withPhase_call_rel32_rip (state : X86_64MachineState)
    (displacement : Int32) (phase : UInt64) :
    (withPhase (X86_64Instruction.step (call_rel32 displacement) state) phase).rip =
      state.rip + 5 := by
  change ((state.push64 (state.rip + 5)).pop64).1 = state.rip + 5
  exact (push64_pop64_roundtrip state (state.rip + 5)).1

def linuxStreamInitial (direction : CodecDirection) (environment : Environment) :=
  Platform.load (P := LinuxX86_64 AnyEvent) (linuxStreamArtifact direction) environment

def linuxStreamEntry (direction : CodecDirection) (environment : Environment) :
    StreamingInvocationContext :=
  .mk direction environment.stdin spike5AllocationScope (linuxStreamInitial direction environment).rip

def linuxStep0 (direction : CodecDirection) (environment : Environment) :=
  X86_64Instruction.step (call_rel32 0x10000) (linuxStreamInitial direction environment)

def linuxState1 (direction : CodecDirection) (environment : Environment) :=
  withPhase (linuxStep0 direction environment) 1

def linuxStep1 (direction : CodecDirection) (environment : Environment) :=
  X86_64Instruction.step (call_rel32 0x20000) (linuxState1 direction environment)

def linuxState2 (direction : CodecDirection) (environment : Environment) :=
  withPhase (linuxStep1 direction environment) 2

def linuxStep2 (direction : CodecDirection) (environment : Environment) :=
  X86_64Instruction.step (call_rel32 0x30000) (linuxState2 direction environment)

def linuxState3 (direction : CodecDirection) (environment : Environment) :=
  withPhase (linuxStep2 direction environment) 3

def linuxStep3 (direction : CodecDirection) (environment : Environment) :=
  X86_64Instruction.step (call_rel32 0x40000) (linuxState3 direction environment)

theorem linux_initial_rip (direction : CodecDirection) (environment : Environment) :
    (linuxStreamInitial direction environment).rip = linuxStreamLinked.executable.load.rip := by
  rfl

theorem linux_lookup_zero (direction : CodecDirection) (environment : Environment) :
    instructionAtRipIndexed
      (indexInstructions (linuxStreamInitial direction environment).rip linuxStreamInstructions)
      (linuxStreamInitial direction environment).rip = some (call_rel32 0x10000) := by
  exact lookup_first_instruction _ _ _

theorem linux_intercept_zero (direction : CodecDirection) (environment : Environment) :
    @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxStep0 direction environment).rip (linuxStep0 direction environment) =
        some (linuxState1 direction environment, none) := by
  change streamingNativeCall _ _ _ _ = _
  rw [show (linuxStep0 direction environment).rip = linuxStaticCallTarget 0 by
    unfold linuxStep0
    rw [call_rel32_step_rip, linux_initial_rip]
    rfl]
  simp [linuxStreamingInterceptor, linuxState1, linux_find_call_zero, streamingNativeCall]

theorem linux_state1_rip (direction : CodecDirection) (environment : Environment) :
    (linuxState1 direction environment).rip =
      (linuxStreamInitial direction environment).rip + 5 := by
  exact withPhase_call_rel32_rip _ _ _

theorem linux_lookup_one (direction : CodecDirection) (environment : Environment) :
    instructionAtRipIndexed
      (indexInstructions (linuxStreamInitial direction environment).rip linuxStreamInstructions)
      (linuxState1 direction environment).rip = some (call_rel32 0x20000) := by
  rw [linux_state1_rip, linux_initial_rip]
  rfl

theorem call_rel32_preserves_r15 (state : X86_64MachineState) (displacement : Int32) :
    (X86_64Instruction.step (call_rel32 displacement) state).gprs .r15 =
      state.gprs .r15 := by
  rfl

theorem withPhase_r15 (state : X86_64MachineState) (phase : UInt64) :
    (withPhase state phase).gprs .r15 = phase := by
  simp [withPhase, X86_64MachineState.setGpr64]

theorem linux_intercept_one (direction : CodecDirection) (environment : Environment) :
    @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxStep1 direction environment).rip (linuxStep1 direction environment) =
        some (linuxState2 direction environment, none) := by
  change streamingNativeCall _ _ _ _ = _
  rw [show (linuxStep1 direction environment).rip = linuxStaticCallTarget 1 by
    unfold linuxStep1
    rw [call_rel32_step_rip, linux_state1_rip, linux_initial_rip]
    rfl]
  have hphase : (linuxStep1 direction environment).gprs .r15 = 1 := by
    unfold linuxStep1
    rw [call_rel32_preserves_r15]
    exact withPhase_r15 _ _
  simp [linuxState2, linux_find_call_one, streamingNativeCall, hphase]

theorem linux_state2_rip (direction : CodecDirection) (environment : Environment) :
    (linuxState2 direction environment).rip =
      (linuxStreamInitial direction environment).rip + 10 := by
  unfold linuxState2 linuxStep1
  rw [withPhase_call_rel32_rip, linux_state1_rip]
  simp [UInt64.add_assoc]

theorem linux_lookup_two (direction : CodecDirection) (environment : Environment) :
    instructionAtRipIndexed
      (indexInstructions (linuxStreamInitial direction environment).rip linuxStreamInstructions)
      (linuxState2 direction environment).rip = some (call_rel32 0x30000) := by
  rw [linux_state2_rip, linux_initial_rip]
  rfl

def linuxResultState (direction : CodecDirection) (environment : Environment) :
    X86_64MachineState :=
  if (streamResultEvent (linuxStreamEntry direction environment)).snd then
    linuxState3 direction environment
  else
    linuxStep2 direction environment

theorem linux_intercept_two (direction : CodecDirection) (environment : Environment) :
    @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxStep2 direction environment).rip (linuxStep2 direction environment) =
        some (linuxResultState direction environment,
          (streamResultEvent (linuxStreamEntry direction environment)).fst) := by
  change streamingNativeCall _ _ _ _ = _
  rw [show (linuxStep2 direction environment).rip = linuxStaticCallTarget 2 by
    unfold linuxStep2
    rw [call_rel32_step_rip, linux_state2_rip, linux_initial_rip]
    rfl]
  have hphase : (linuxStep2 direction environment).gprs .r15 = 2 := by
    unfold linuxStep2
    rw [call_rel32_preserves_r15]
    exact withPhase_r15 _ _
  cases hcontinue : (streamResultEvent (linuxStreamEntry direction environment)).snd <;>
    simp [linuxStreamingInterceptor, linuxResultState, linuxState3,
      linux_find_call_two, streamingNativeCall, hphase, hcontinue]

theorem linux_state3_rip (direction : CodecDirection) (environment : Environment) :
    (linuxState3 direction environment).rip =
      (linuxStreamInitial direction environment).rip + 15 := by
  unfold linuxState3 linuxStep2
  rw [withPhase_call_rel32_rip, linux_state2_rip]
  simp [UInt64.add_assoc]

theorem linux_lookup_three (direction : CodecDirection) (environment : Environment) :
    instructionAtRipIndexed
      (indexInstructions (linuxStreamInitial direction environment).rip linuxStreamInstructions)
      (linuxState3 direction environment).rip = some (call_rel32 0x40000) := by
  rw [linux_state3_rip, linux_initial_rip]
  rfl

theorem linux_intercept_three (direction : CodecDirection) (environment : Environment) :
    @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxStep3 direction environment).rip (linuxStep3 direction environment) =
        some (linuxStep3 direction environment,
          some (Inject.inject (ProcessEvent.exit 0))) := by
  change streamingNativeCall _ _ _ _ = _
  rw [show (linuxStep3 direction environment).rip = linuxStaticCallTarget 3 by
    unfold linuxStep3
    rw [call_rel32_step_rip, linux_state3_rip, linux_initial_rip]
    rfl]
  have hphase : (linuxStep3 direction environment).gprs .r15 = 3 := by
    unfold linuxStep3
    rw [call_rel32_preserves_r15]
    exact withPhase_r15 _ _
  simp [linuxStreamingInterceptor, linux_find_call_three, streamingNativeCall, hphase]

@[simp] theorem call_rel32_step_faulted (state : X86_64MachineState)
    (displacement : Int32) :
    (X86_64Instruction.step (call_rel32 displacement) state).faulted = state.faulted := by
  rfl

@[simp] theorem withPhase_faulted (state : X86_64MachineState) (phase : UInt64) :
    (withPhase state phase).faulted = state.faulted := by
  rfl

theorem linux_initial_safe (direction : CodecDirection) (environment : Environment) :
    (linuxStreamInitial direction environment).faulted = false := by
  rfl

theorem linux_state1_safe (direction : CodecDirection) (environment : Environment) :
    (linuxState1 direction environment).faulted = false := by
  simp [linuxState1, linuxStep0, linux_initial_safe]

theorem linux_state2_safe (direction : CodecDirection) (environment : Environment) :
    (linuxState2 direction environment).faulted = false := by
  simp [linuxState2, linuxStep1, linux_state1_safe]

theorem linux_state3_safe (direction : CodecDirection) (environment : Environment) :
    (linuxState3 direction environment).faulted = false := by
  simp [linuxState3, linuxStep2, linux_state2_safe]

theorem linux_step2_safe (direction : CodecDirection) (environment : Environment) :
    (linuxStep2 direction environment).faulted = false := by
  simp [linuxStep2, linux_state2_safe]

theorem linux_step3_safe (direction : CodecDirection) (environment : Environment) :
    (linuxStep3 direction environment).faulted = false := by
  simp [linuxStep3, linux_state3_safe]

theorem linux_lookup_after_two (direction : CodecDirection) (environment : Environment) :
    instructionAtRipIndexed
      (indexInstructions (linuxStreamInitial direction environment).rip linuxStreamInstructions)
      (linuxStep2 direction environment).rip = none := by
  rw [show (linuxStep2 direction environment).rip = linuxStaticCallTarget 2 by
    unfold linuxStep2
    rw [call_rel32_step_rip, linux_state2_rip, linux_initial_rip]
    rfl]
  rw [linux_initial_rip]
  rfl

theorem linux_lookup_after_three (direction : CodecDirection) (environment : Environment) :
    instructionAtRipIndexed
      (indexInstructions (linuxStreamInitial direction environment).rip linuxStreamInstructions)
      (linuxStep3 direction environment).rip = none := by
  rw [show (linuxStep3 direction environment).rip = linuxStaticCallTarget 3 by
    unfold linuxStep3
    rw [call_rel32_step_rip, linux_state3_rip, linux_initial_rip]
    rfl]
  rw [linux_initial_rip]
  rfl

def linuxStartEdge (direction : CodecDirection) (environment : Environment) :
    @SilentNativeEdgeCertificate AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxStreamInitial direction environment).rip linuxStreamInstructions
      (linuxStreamInitial direction environment) (linuxState1 direction environment) where
  instruction := call_rel32 0x10000
  lookup := linux_lookup_zero direction environment
  intercept := linux_intercept_zero direction environment
  safe := linux_state1_safe direction environment

def linuxPushEdge (direction : CodecDirection) (environment : Environment) :
    @SilentNativeEdgeCertificate AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxStreamInitial direction environment).rip linuxStreamInstructions
      (linuxState1 direction environment) (linuxState2 direction environment) where
  instruction := call_rel32 0x20000
  lookup := linux_lookup_one direction environment
  intercept := linux_intercept_one direction environment
  safe := linux_state2_safe direction environment

def linuxIndexed (direction : CodecDirection) (environment : Environment) :=
  indexInstructions (linuxStreamInitial direction environment).rip linuxStreamInstructions

theorem linux_outcome_prefix (direction : CodecDirection) (environment : Environment)
    (eventsRev : List AnyEvent) :
    @runProgramOutcomeWithLoops.loop AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxIndexed direction environment) 50000
      (linuxStreamInitial direction environment) eventsRev =
    @runProgramOutcomeWithLoops.loop AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxIndexed direction environment) 49998
      (linuxState2 direction environment) eventsRev := by
  let start := linuxStartEdge direction environment
  let push := linuxPushEdge direction environment
  calc
    _ = @runProgramOutcomeWithLoops.loop AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxIndexed direction environment) 49999
        (linuxState1 direction environment) eventsRev :=
      @outcome_step_silent AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxIndexed direction environment) 49999
        (linuxStreamInitial direction environment) (linuxState1 direction environment)
        start.instruction eventsRev start.lookup start.intercept start.safe
    _ = _ :=
      @outcome_step_silent AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxIndexed direction environment) 49998
        (linuxState1 direction environment) (linuxState2 direction environment)
        push.instruction eventsRev push.lookup push.intercept push.safe

theorem linux_outcome_stops_after_result (direction : CodecDirection)
    (environment : Environment) (eventsRev : List AnyEvent) (event : AnyEvent)
    (hhook : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxStep2 direction environment).rip (linuxStep2 direction environment) =
        some (linuxStep2 direction environment, some event)) :
    @runProgramOutcomeWithLoops.loop AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxIndexed direction environment) 49998
      (linuxState2 direction environment) eventsRev =
        .completed (linuxStep2 direction environment) (event :: eventsRev).reverse := by
  calc
    _ = @runProgramOutcomeWithLoops.loop AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxIndexed direction environment) 49997
        (linuxStep2 direction environment) (event :: eventsRev) :=
      @outcome_step_event AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxIndexed direction environment) 49997
        (linuxState2 direction environment) (linuxStep2 direction environment)
        (call_rel32 0x30000) eventsRev event (linux_lookup_two direction environment)
        hhook (linux_step2_safe direction environment)
    _ = _ := @outcome_complete AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxIndexed direction environment) 49996 (linuxStep2 direction environment)
      (event :: eventsRev) (linux_lookup_after_two direction environment)

theorem linux_outcome_continues_after_result (direction : CodecDirection)
    (environment : Environment) (eventsRev : List AnyEvent) (event : AnyEvent)
    (hhook : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxStep2 direction environment).rip (linuxStep2 direction environment) =
        some (linuxState3 direction environment, some event)) :
    @runProgramOutcomeWithLoops.loop AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxIndexed direction environment) 49998
      (linuxState2 direction environment) eventsRev =
        .completed (linuxStep3 direction environment)
          (Inject.inject (ProcessEvent.exit 0) :: event :: eventsRev).reverse := by
  calc
    _ = @runProgramOutcomeWithLoops.loop AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxIndexed direction environment) 49997
        (linuxState3 direction environment) (event :: eventsRev) :=
      @outcome_step_event AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxIndexed direction environment) 49997
        (linuxState2 direction environment) (linuxState3 direction environment)
        (call_rel32 0x30000) eventsRev event (linux_lookup_two direction environment)
        hhook (linux_state3_safe direction environment)
    _ = @runProgramOutcomeWithLoops.loop AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxIndexed direction environment) 49996
        (linuxStep3 direction environment)
        (Inject.inject (ProcessEvent.exit 0) :: event :: eventsRev) :=
      @outcome_step_event AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxIndexed direction environment) 49996
        (linuxState3 direction environment) (linuxStep3 direction environment)
        (call_rel32 0x40000) (event :: eventsRev) (Inject.inject (ProcessEvent.exit 0))
        (linux_lookup_three direction environment) (linux_intercept_three direction environment)
        (linux_step3_safe direction environment)
    _ = _ := @outcome_complete AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxIndexed direction environment) 49995 (linuxStep3 direction environment)
      (Inject.inject (ProcessEvent.exit 0) :: event :: eventsRev)
      (linux_lookup_after_three direction environment)

theorem linux_trace_prefix (direction : CodecDirection) (environment : Environment) :
    @runProgramTraceWithLoops AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxStreamInitial direction environment).rip linuxStreamInstructions 50000
      (linuxStreamInitial direction environment) =
    @runProgramTraceWithLoops AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxStreamInitial direction environment).rip linuxStreamInstructions 49998
      (linuxState2 direction environment) := by
  let start := linuxStartEdge direction environment
  let push := linuxPushEdge direction environment
  calc
    _ = @runProgramTraceWithLoops AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxStreamInitial direction environment).rip linuxStreamInstructions 49999
        (linuxState1 direction environment) :=
      @trace_step_silent AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxStreamInitial direction environment).rip linuxStreamInstructions 49999
        (linuxStreamInitial direction environment) (linuxState1 direction environment)
        start.instruction start.lookup start.intercept start.safe
    _ = _ :=
      @trace_step_silent AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxStreamInitial direction environment).rip linuxStreamInstructions 49998
        (linuxState1 direction environment) (linuxState2 direction environment)
        push.instruction push.lookup push.intercept push.safe

theorem linux_trace_stops_after_result (direction : CodecDirection)
    (environment : Environment) (event : AnyEvent)
    (hhook : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxStep2 direction environment).rip (linuxStep2 direction environment) =
        some (linuxStep2 direction environment, some event)) :
    @runProgramTraceWithLoops AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxStreamInitial direction environment).rip linuxStreamInstructions 49998
      (linuxState2 direction environment) = [event] := by
  calc
    _ = event :: @runProgramTraceWithLoops AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxStreamInitial direction environment).rip linuxStreamInstructions 49997
        (linuxStep2 direction environment) :=
      @trace_step_event AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxStreamInitial direction environment).rip linuxStreamInstructions 49997
        (linuxState2 direction environment) (linuxStep2 direction environment)
        (call_rel32 0x30000) event (linux_lookup_two direction environment) hhook
        (linux_step2_safe direction environment)
    _ = [event] := by
      rw [@trace_complete AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxStreamInitial direction environment).rip linuxStreamInstructions 49996
        (linuxStep2 direction environment) (linux_lookup_after_two direction environment)]

theorem linux_trace_continues_after_result (direction : CodecDirection)
    (environment : Environment) (event : AnyEvent)
    (hhook : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxStep2 direction environment).rip (linuxStep2 direction environment) =
        some (linuxState3 direction environment, some event)) :
    @runProgramTraceWithLoops AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxStreamInitial direction environment).rip linuxStreamInstructions 49998
      (linuxState2 direction environment) =
        [event, Inject.inject (ProcessEvent.exit 0)] := by
  calc
    _ = event :: @runProgramTraceWithLoops AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxStreamInitial direction environment).rip linuxStreamInstructions 49997
        (linuxState3 direction environment) :=
      @trace_step_event AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxStreamInitial direction environment).rip linuxStreamInstructions 49997
        (linuxState2 direction environment) (linuxState3 direction environment)
        (call_rel32 0x30000) event (linux_lookup_two direction environment) hhook
        (linux_state3_safe direction environment)
    _ = event :: Inject.inject (ProcessEvent.exit 0) ::
        @runProgramTraceWithLoops AnyEvent
          (linuxStreamingInterceptor (linuxStreamEntry direction environment))
          (linuxStreamInitial direction environment).rip linuxStreamInstructions 49996
          (linuxStep3 direction environment) := by
      rw [@trace_step_event AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxStreamInitial direction environment).rip linuxStreamInstructions 49996
        (linuxState3 direction environment) (linuxStep3 direction environment)
        (call_rel32 0x40000) (Inject.inject (ProcessEvent.exit 0))
        (linux_lookup_three direction environment) (linux_intercept_three direction environment)
        (linux_step3_safe direction environment)]
    _ = [event, Inject.inject (ProcessEvent.exit 0)] := by
      rw [@trace_complete AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxStreamInitial direction environment).rip linuxStreamInstructions 49995
        (linuxStep3 direction environment) (linux_lookup_after_three direction environment)]

def linuxStreamingSpec (direction : CodecDirection) (environment : Environment) :
    List AnyEvent :=
  streamingInvocationTrace direction spike5AllocationScope environment.stdin

theorem linux_platform_run (runtime : ExternalCallInterceptor X86_64 AnyEvent)
    (artifact : LinuxX86_64Artifact) (state : X86_64MachineState) :
    Platform.run (P := LinuxX86_64 AnyEvent) runtime artifact state =
      @runAsmTrace AnyEvent runtime artifact.instructions state 50000 := by
  rfl

theorem linux_platform_admissible (runtime : ExternalCallInterceptor X86_64 AnyEvent)
    (artifact : LinuxX86_64Artifact) (state : X86_64MachineState) :
    Platform.admissible (P := LinuxX86_64 AnyEvent) runtime artifact state =
      (@runProgramOutcomeWithLoops AnyEvent runtime state.rip artifact.instructions 50000 state).isAdmissible := by
  rfl

theorem linux_stream_realize (direction : CodecDirection)
    (artifact : LinuxX86_64Artifact) (context : StreamingInvocationContext) :
    (linuxStreamingCapabilities direction).realize artifact context =
      linuxStreamingInterceptor context := by
  rfl

theorem linux_streaming_trace_equivalence (direction : CodecDirection)
    (environment : Environment) :
    Platform.run
      ((linuxStreamingCapabilities direction).realize (linuxStreamArtifact direction)
        (linuxStreamEntry direction environment))
      (linuxStreamArtifact direction)
      (Platform.load (P := LinuxX86_64 AnyEvent) (linuxStreamArtifact direction) environment) =
        linuxStreamingSpec direction environment := by
  rw [linux_platform_run, linux_stream_realize]
  change @runProgramTraceWithLoops AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxStreamInitial direction environment).rip linuxStreamInstructions 50000
      (linuxStreamInitial direction environment) = _
  rw [linux_trace_prefix]
  cases direction with
  | compress =>
    cases hresult : compressAll bufferedStreamingZlibCapability
      spike5AllocationScope environment.stdin with
    | rejected error scope => nomatch error
    | resourceExhausted scope =>
      have hhook := linux_intercept_two .compress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (linuxStreamingInterceptor (linuxStreamEntry .compress environment))
          (linuxStep2 .compress environment).rip (linuxStep2 .compress environment) =
            some (linuxStep2 .compress environment,
              some (Inject.inject (ProcessEvent.exit 2))) := by
        simpa [streamResultEvent, linuxStreamEntry, linuxResultState, hresult] using hhook
      rw [linux_trace_stops_after_result .compress environment _ hhook']
      simp [linuxStreamingSpec, streamingInvocationTrace, hresult, exhaustedStreamTrace]
    | success output scope =>
      have hhook := linux_intercept_two .compress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (linuxStreamingInterceptor (linuxStreamEntry .compress environment))
          (linuxStep2 .compress environment).rip (linuxStep2 .compress environment) =
            some (linuxState3 .compress environment,
              some (Inject.inject (ConsoleEvent.out (bytesAsString output)))) := by
        simpa [streamResultEvent, linuxStreamEntry, linuxResultState, hresult] using hhook
      rw [linux_trace_continues_after_result .compress environment _ hhook']
      simp [linuxStreamingSpec, streamingInvocationTrace, hresult, successfulStreamTrace]
  | decompress =>
    cases hresult : decompressAll bufferedStreamingZlibCapability
      spike5AllocationScope environment.stdin with
    | rejected message scope =>
      have hhook := linux_intercept_two .decompress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (linuxStreamingInterceptor (linuxStreamEntry .decompress environment))
          (linuxStep2 .decompress environment).rip (linuxStep2 .decompress environment) =
            some (linuxStep2 .decompress environment,
              some (Inject.inject (ProcessEvent.exit 1))) := by
        simpa [streamResultEvent, linuxStreamEntry, linuxResultState, hresult] using hhook
      rw [linux_trace_stops_after_result .decompress environment _ hhook']
      simp [linuxStreamingSpec, streamingInvocationTrace, hresult, malformedStreamTrace]
    | resourceExhausted scope =>
      have hhook := linux_intercept_two .decompress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (linuxStreamingInterceptor (linuxStreamEntry .decompress environment))
          (linuxStep2 .decompress environment).rip (linuxStep2 .decompress environment) =
            some (linuxStep2 .decompress environment,
              some (Inject.inject (ProcessEvent.exit 2))) := by
        simpa [streamResultEvent, linuxStreamEntry, linuxResultState, hresult] using hhook
      rw [linux_trace_stops_after_result .decompress environment _ hhook']
      simp [linuxStreamingSpec, streamingInvocationTrace, hresult, exhaustedStreamTrace]
    | success output scope =>
      have hhook := linux_intercept_two .decompress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (linuxStreamingInterceptor (linuxStreamEntry .decompress environment))
          (linuxStep2 .decompress environment).rip (linuxStep2 .decompress environment) =
            some (linuxState3 .decompress environment,
              some (Inject.inject (ConsoleEvent.out (bytesAsString output)))) := by
        simpa [streamResultEvent, linuxStreamEntry, linuxResultState, hresult] using hhook
      rw [linux_trace_continues_after_result .decompress environment _ hhook']
      simp [linuxStreamingSpec, streamingInvocationTrace, hresult, successfulStreamTrace]

theorem linux_streaming_admissible (direction : CodecDirection) (environment : Environment) :
    Platform.admissible
      ((linuxStreamingCapabilities direction).realize (linuxStreamArtifact direction)
        (linuxStreamEntry direction environment))
      (linuxStreamArtifact direction)
      (Platform.load (P := LinuxX86_64 AnyEvent) (linuxStreamArtifact direction) environment) := by
  rw [linux_platform_admissible, linux_stream_realize]
  unfold runProgramOutcomeWithLoops
  change (@runProgramOutcomeWithLoops.loop AnyEvent
    (linuxStreamingInterceptor (linuxStreamEntry direction environment))
    (linuxIndexed direction environment) 50000
    (linuxStreamInitial direction environment) []).isAdmissible
  rw [linux_outcome_prefix]
  cases direction with
  | compress =>
    cases hresult : compressAll bufferedStreamingZlibCapability
      spike5AllocationScope environment.stdin with
    | rejected error scope => nomatch error
    | resourceExhausted scope =>
      have hhook := linux_intercept_two .compress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (linuxStreamingInterceptor (linuxStreamEntry .compress environment))
          (linuxStep2 .compress environment).rip (linuxStep2 .compress environment) =
            some (linuxStep2 .compress environment,
              some (Inject.inject (ProcessEvent.exit 2))) := by
        simpa [streamResultEvent, linuxStreamEntry, linuxResultState, hresult] using hhook
      rw [linux_outcome_stops_after_result .compress environment [] _ hhook']
      simp [NativeRunOutcome.isAdmissible]
    | success output scope =>
      have hhook := linux_intercept_two .compress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (linuxStreamingInterceptor (linuxStreamEntry .compress environment))
          (linuxStep2 .compress environment).rip (linuxStep2 .compress environment) =
            some (linuxState3 .compress environment,
              some (Inject.inject (ConsoleEvent.out (bytesAsString output)))) := by
        simpa [streamResultEvent, linuxStreamEntry, linuxResultState, hresult] using hhook
      rw [linux_outcome_continues_after_result .compress environment [] _ hhook']
      simp [NativeRunOutcome.isAdmissible]
  | decompress =>
    cases hresult : decompressAll bufferedStreamingZlibCapability
      spike5AllocationScope environment.stdin with
    | rejected message scope =>
      have hhook := linux_intercept_two .decompress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (linuxStreamingInterceptor (linuxStreamEntry .decompress environment))
          (linuxStep2 .decompress environment).rip (linuxStep2 .decompress environment) =
            some (linuxStep2 .decompress environment,
              some (Inject.inject (ProcessEvent.exit 1))) := by
        simpa [streamResultEvent, linuxStreamEntry, linuxResultState, hresult] using hhook
      rw [linux_outcome_stops_after_result .decompress environment [] _ hhook']
      simp [NativeRunOutcome.isAdmissible]
    | resourceExhausted scope =>
      have hhook := linux_intercept_two .decompress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (linuxStreamingInterceptor (linuxStreamEntry .decompress environment))
          (linuxStep2 .decompress environment).rip (linuxStep2 .decompress environment) =
            some (linuxStep2 .decompress environment,
              some (Inject.inject (ProcessEvent.exit 2))) := by
        simpa [streamResultEvent, linuxStreamEntry, linuxResultState, hresult] using hhook
      rw [linux_outcome_stops_after_result .decompress environment [] _ hhook']
      simp [NativeRunOutcome.isAdmissible]
    | success output scope =>
      have hhook := linux_intercept_two .decompress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (linuxStreamingInterceptor (linuxStreamEntry .decompress environment))
          (linuxStep2 .decompress environment).rip (linuxStep2 .decompress environment) =
            some (linuxState3 .decompress environment,
              some (Inject.inject (ConsoleEvent.out (bytesAsString output)))) := by
        simpa [streamResultEvent, linuxStreamEntry, linuxResultState, hresult] using hhook
      rw [linux_outcome_continues_after_result .decompress environment [] _ hhook']
      simp [NativeRunOutcome.isAdmissible]

def linuxStreamExports (direction : CodecDirection) :=
  VerifiedExportSet.empty Unit Unit (LinuxX86_64 AnyEvent) emptyBoundarySpec
    (emptyBoundarySemantics (LinuxX86_64 AnyEvent) X86_64MachineState) ()
    (by rfl) (by rfl) (by rfl)

theorem linux_stream_artifact_connected (direction : CodecDirection) :
    Platform.artifactConnected (P := LinuxX86_64 AnyEvent)
      (linuxStreamArtifact direction) := by
  rfl

@[simp] theorem linux_provider_call_zero (direction : CodecDirection) :
    linuxProviderCallTarget (linuxStreamArtifact direction) 0 =
      some (linuxStaticCallTarget 0) := by
  rfl

@[simp] theorem linux_provider_call_one (direction : CodecDirection) :
    linuxProviderCallTarget (linuxStreamArtifact direction) 1 =
      some (linuxStaticCallTarget 1) := by
  rfl

@[simp] theorem linux_provider_call_two (direction : CodecDirection) :
    linuxProviderCallTarget (linuxStreamArtifact direction) 2 =
      some (linuxStaticCallTarget 2) := by
  rfl

@[simp] theorem linux_provider_call_three (direction : CodecDirection) :
    linuxProviderCallTarget (linuxStreamArtifact direction) 3 =
      some (linuxStaticCallTarget 3) := by
  rfl

def linuxStreamingArtifactCertificate (direction : CodecDirection) :
    ProgramArtifactCertificate (LinuxX86_64 AnyEvent) where
  artifact := linuxStreamArtifact direction
  exports := linuxStreamExports direction
  exportsArtifact := rfl
  artifactConnection := linux_stream_artifact_connected direction

def linuxStreamingProviderCertificate (direction : CodecDirection) :
    ProgramProviderCertificate (LinuxX86_64 AnyEvent)
      (linuxStreamingCapabilities direction) (linuxStreamArtifact direction) where
  importsCovered := by
    intro imported himport
    change imported ∈ linuxStreamRequirements direction at himport
    cases direction <;>
      simp [linuxStreamRequirements, streamImportNames] at himport
    all_goals
      rcases himport with rfl | rfl | rfl | rfl <;>
        simp [linuxStreamingCapabilities, linuxStreamingCapability, linuxStreamProviders,
          linuxStreamRequirements, streamImportNames, nativeProviderProtocol,
          Platform.providerProvides]
  providersLinked := by
    intro provider hprovider
    change provider ∈ linuxStreamProviders direction at hprovider
    cases direction <;>
      simp [linuxStreamProviders, linuxStreamRequirements, streamImportNames,
        nativeProviderProtocol] at hprovider
    all_goals
      rcases hprovider with rfl | rfl | rfl | rfl
    all_goals
      constructor
      · simp [linuxStreamArtifact, linuxStreamRequirements, streamImportNames]
      · first
        | simpa only [linuxStreamArtifact] using
            linux_provider_call_zero CodecDirection.compress
        | simpa only [linuxStreamArtifact] using
            linux_provider_call_zero CodecDirection.decompress
        | simpa only [linuxStreamArtifact] using
            linux_provider_call_one CodecDirection.compress
        | simpa only [linuxStreamArtifact] using
            linux_provider_call_one CodecDirection.decompress
        | simpa only [linuxStreamArtifact] using
            linux_provider_call_two CodecDirection.compress
        | simpa only [linuxStreamArtifact] using
            linux_provider_call_two CodecDirection.decompress
        | simpa only [linuxStreamArtifact] using
            linux_provider_call_three CodecDirection.compress
        | simpa only [linuxStreamArtifact] using
            linux_provider_call_three CodecDirection.decompress

def linuxStreamingEntryCertificate (direction : CodecDirection) :
    ProgramEntryCertificate (LinuxX86_64 AnyEvent)
      (linuxStreamingCapabilities direction) (linuxStreamArtifact direction) where
  entryContext := linuxStreamEntry direction
  entryEstablished := by intro environment; exact ⟨rfl, rfl⟩

@[simp] theorem linux_streaming_entry_context (direction : CodecDirection)
    (environment : Environment) :
    (linuxStreamingEntryCertificate direction).entryContext environment =
      linuxStreamEntry direction environment := by
  rfl

def linuxStreamingAdmissibilityCertificate (direction : CodecDirection) :
    ProgramAdmissibilityCertificate (LinuxX86_64 AnyEvent)
      (linuxStreamingCapabilities direction) (linuxStreamArtifact direction)
      (linuxStreamingEntryCertificate direction) where
  platformAdmissible := by
    intro environment
    rw [linux_streaming_entry_context]
    exact linux_streaming_admissible direction environment

def linuxStreamingBehaviorCertificate (direction : CodecDirection) :
    ProgramBehaviorCertificate (LinuxX86_64 AnyEvent)
      (linuxStreamingCapabilities direction) (linuxStreamArtifact direction)
      (linuxStreamingEntryCertificate direction) where
  spec := linuxStreamingSpec direction
  traceEquivalence := by
    intro environment
    rw [linux_streaming_entry_context]
    exact linux_streaming_trace_equivalence direction environment

def linuxStreamingVerifiedProgram (direction : CodecDirection) :
    VerifiedProgram (LinuxX86_64 AnyEvent) (linuxStreamingCapabilities direction) :=
  VerifiedProgram.compose
    (match direction with
      | .compress => "spike5_gzip_linux"
      | .decompress => "spike5_gunzip_linux")
    (linuxStreamingArtifactCertificate direction)
    (linuxStreamingProviderCertificate direction)
    (linuxStreamingEntryCertificate direction)
    (linuxStreamingAdmissibilityCertificate direction)
    (linuxStreamingBehaviorCertificate direction)

end Spikes.Spike5Gzip
