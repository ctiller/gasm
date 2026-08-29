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
import Spikes.Spike3SortLines.Windows.IATLemmas

namespace Spikes.Spike5Gzip

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.Windows
open Stdlib.Zlib
open Spikes.Spike3SortLines.Windows

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
  simp [runProgramTraceWithLoops, runProgramTraceLoop, hlookup,
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
  simp [runProgramTraceWithLoops, runProgramTraceLoop, hlookup,
    hintercept, hfault]

theorem trace_complete {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (baseRip : UInt64) (instructions : List X86_64Instr) (fuel : Nat)
    (state : X86_64MachineState)
    (hlookup : instructionAtRipIndexed (indexInstructions baseRip instructions) state.rip = none) :
    runProgramTraceWithLoops (Event := Event) baseRip instructions (fuel + 1) state = [] := by
  simp [runProgramTraceWithLoops, runProgramTraceLoop, hlookup]

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
    runProgramOutcomeLoop indexed (fuel + 1) state eventsRev =
      runProgramOutcomeLoop indexed fuel hooked (event :: eventsRev) := by
  have hfault' : hooked.fault = none := by
    cases h : hooked.fault <;> simp [X86_64MachineState.faulted, h] at hfault ⊢
  simp [runProgramOutcomeLoop, nativeOutcomeTransition, hlookup, hintercept, hfault']

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
    runProgramOutcomeLoop indexed (fuel + 1) state eventsRev =
      runProgramOutcomeLoop indexed fuel hooked eventsRev := by
  have hfault' : hooked.fault = none := by
    cases h : hooked.fault <;> simp [X86_64MachineState.faulted, h] at hfault ⊢
  simp [runProgramOutcomeLoop, nativeOutcomeTransition, hlookup, hintercept, hfault']

theorem outcome_complete {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (indexed : List (Address × X86_64Instr)) (fuel : Nat)
    (state : X86_64MachineState) (eventsRev : List Event)
    (hlookup : instructionAtRipIndexed indexed state.rip = none) :
    runProgramOutcomeLoop indexed (fuel + 1) state eventsRev =
      .returned state eventsRev.reverse := by
  simp [runProgramOutcomeLoop, hlookup]

/- A call writes only its return slot.  This structural read-over-write lemma
   is the memory-frame leaf used by every later Windows IAT edge. -/
theorem X86_64Mem.read64_write64_disjoint_before
    (readAddr writeAddr value : UInt64) (memory : X86_64Memory)
    (hwrite : writeAddr.toNat + 8 ≤ 2 ^ 64)
    (hread : readAddr.toNat + 8 ≤ writeAddr.toNat) :
    X86_64Mem.read .w64 readAddr (X86_64Mem.write .w64 writeAddr value memory) =
      X86_64Mem.read .w64 readAddr memory := by
  simp only [X86_64Mem.read]
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory readAddr hwrite (by omega)]
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory (readAddr + 1) hwrite (by
    left
    have hbound : readAddr.toNat + 1 < 2 ^ 64 := by omega
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt hbound]
    omega)]
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory (readAddr + 2) hwrite (by
    left
    have hbound : readAddr.toNat + 2 < 2 ^ 64 := by omega
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt hbound]
    omega)]
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory (readAddr + 3) hwrite (by
    left
    have hbound : readAddr.toNat + 3 < 2 ^ 64 := by omega
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt hbound]
    omega)]
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory (readAddr + 4) hwrite (by
    left
    have hbound : readAddr.toNat + 4 < 2 ^ 64 := by omega
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt hbound]
    omega)]
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory (readAddr + 5) hwrite (by
    left
    have hbound : readAddr.toNat + 5 < 2 ^ 64 := by omega
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt hbound]
    omega)]
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory (readAddr + 6) hwrite (by
    left
    have hbound : readAddr.toNat + 6 < 2 ^ 64 := by omega
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt hbound]
    omega)]
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory (readAddr + 7) hwrite (by
    left
    have hbound : readAddr.toNat + 7 < 2 ^ 64 := by omega
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt hbound]
    omega)]

theorem withPhase_call_rip_read64_preserved
    (state : X86_64MachineState) (displacement : Int32) (phase : UInt64)
    (readAddr : Address)
    (hwrite : (state.rsp - 8).toNat + 8 ≤ 2 ^ 64)
    (hread : readAddr.toNat + 8 ≤ (state.rsp - 8).toNat) :
    (withPhase (X86_64Instruction.step (call_rip displacement) state) phase).read64 readAddr =
      state.read64 readAddr := by
  change X86_64Mem.read .w64 readAddr
      (X86_64Mem.write .w64 (state.rsp - 8) (state.rip + 6) state.memory) =
    X86_64Mem.read .w64 readAddr state.memory
  exact X86_64Mem.read64_write64_disjoint_before _ _ _ _ hwrite hread

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
    @runProgramOutcomeLoop AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxIndexed direction environment) 50000
      (linuxStreamInitial direction environment) eventsRev =
    @runProgramOutcomeLoop AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxIndexed direction environment) 49998
      (linuxState2 direction environment) eventsRev := by
  let start := linuxStartEdge direction environment
  let push := linuxPushEdge direction environment
  calc
    _ = @runProgramOutcomeLoop AnyEvent
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
    @runProgramOutcomeLoop AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxIndexed direction environment) 49998
      (linuxState2 direction environment) eventsRev =
        .returned (linuxStep2 direction environment) (event :: eventsRev).reverse := by
  calc
    _ = @runProgramOutcomeLoop AnyEvent
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
    @runProgramOutcomeLoop AnyEvent
      (linuxStreamingInterceptor (linuxStreamEntry direction environment))
      (linuxIndexed direction environment) 49998
      (linuxState2 direction environment) eventsRev =
        .returned (linuxStep3 direction environment)
          (Inject.inject (ProcessEvent.exit 0) :: event :: eventsRev).reverse := by
  calc
    _ = @runProgramOutcomeLoop AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxIndexed direction environment) 49997
        (linuxState3 direction environment) (event :: eventsRev) :=
      @outcome_step_event AnyEvent
        (linuxStreamingInterceptor (linuxStreamEntry direction environment))
        (linuxIndexed direction environment) 49997
        (linuxState2 direction environment) (linuxState3 direction environment)
        (call_rel32 0x30000) eventsRev event (linux_lookup_two direction environment)
        hhook (linux_state3_safe direction environment)
    _ = @runProgramOutcomeLoop AnyEvent
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
      (@runProgramOutcomeWithLoops AnyEvent runtime state.rip artifact.instructions 50000 state).events := by
  rfl

theorem linux_platform_admissible (runtime : ExternalCallInterceptor X86_64 AnyEvent)
    (artifact : LinuxX86_64Artifact) (state : X86_64MachineState) :
    Platform.admissible (P := LinuxX86_64 AnyEvent) runtime artifact state =
      (@runProgramOutcomeWithLoops AnyEvent runtime state.rip artifact.instructions 50000 state).isAdmissible true := by
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
  rw [@runProgramOutcomeWithLoops_events AnyEvent
    (linuxStreamingInterceptor (linuxStreamEntry direction environment))]
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
  change (@runProgramOutcomeLoop AnyEvent
    (linuxStreamingInterceptor (linuxStreamEntry direction environment))
    (linuxIndexed direction environment) 50000
    (linuxStreamInitial direction environment) []).isAdmissible true
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

theorem windows_stream_text_size (direction : CodecDirection) :
    (windowsStreamArtifact direction).executable.textBytes.size = 24 := by
  cases direction <;> decide

theorem windows_stream_rdata_size (direction : CodecDirection) :
    (windowsStreamArtifact direction).executable.rdataBytes.size = 0 := by
  cases direction <;> decide

theorem windows_stream_layout (direction : CodecDirection) :
    computeSectionLayout (windowsStreamArtifact direction).executable.textBytes.size
      (windowsStreamArtifact direction).executable.rdataBytes.size 512 =
      { textRva := 0x1000, textRawSize := 512, rdataRva := 0x2000, rdataRawSize := 512,
        idataRva := 0x3000, idataRawSize := 512, sizeOfImage := 0x4000 } := by
  rw [windows_stream_text_size, windows_stream_rdata_size]
  decide

theorem windows_stream_imports (direction : CodecDirection) :
    (windowsStreamArtifact direction).executable.imports = streamWindowsImports direction := by
  cases direction <;> rfl

theorem windows_stream_image_base (direction : CodecDirection) :
    (windowsStreamArtifact direction).executable.imageBase = (0x140000000 : Address) := by
  rfl

theorem windows_stream_iat_slots (direction : CodecDirection) :
    (windowsStreamArtifact direction).executable.iatFunctionSlots 0x3000 =
      [(0x140000000 : Address) + 0x3000, (0x140000000 : Address) + 0x3008,
       (0x140000000 : Address) + 0x3010, (0x140000000 : Address) + 0x3018] := by
  unfold WindowsExecutable.iatFunctionSlots
  rw [windows_stream_imports, windows_stream_image_base]
  cases direction <;> rfl

theorem windows_executable_load_read64_of_layout (executable : WindowsExecutable)
    (layout : SectionLayout)
    (hlayout : computeSectionLayout executable.textBytes.size executable.rdataBytes.size 512 =
      layout)
    (address : Address) :
    executable.load.read64 address =
      X86_64Mem.read .w64 address
        (X86_64Mem.initRegion (loadMemory executable.imageBase
          [(layout.textRva, executable.textBytes), (layout.rdataRva, executable.rdataBytes)]
          executable.imports layout.idataRva)) := by
  unfold WindowsExecutable.load
  rw [hlayout]
  rfl

syntax "prove_spike5_selfref " term " at " term : tactic
macro_rules
  | `(tactic| prove_spike5_selfref $direction:term at $addr:term) =>
    `(tactic|
      (rw [read64_initRegion_generic]
       have key0 := loadMemory_excludes_sections
         (0x1000 : UInt32) (0x2000 : UInt32) (0x3000 : UInt32) (0x140000000 : Address)
         (windowsStreamArtifact $direction).executable.textBytes
         (windowsStreamArtifact $direction).executable.rdataBytes
         (windowsStreamArtifact $direction).executable.imports ($addr)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
       have key1 := loadMemory_excludes_sections
         (0x1000 : UInt32) (0x2000 : UInt32) (0x3000 : UInt32) (0x140000000 : Address)
         (windowsStreamArtifact $direction).executable.textBytes
         (windowsStreamArtifact $direction).executable.rdataBytes
         (windowsStreamArtifact $direction).executable.imports ($addr + 1)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
       have key2 := loadMemory_excludes_sections
         (0x1000 : UInt32) (0x2000 : UInt32) (0x3000 : UInt32) (0x140000000 : Address)
         (windowsStreamArtifact $direction).executable.textBytes
         (windowsStreamArtifact $direction).executable.rdataBytes
         (windowsStreamArtifact $direction).executable.imports ($addr + 2)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
       have key3 := loadMemory_excludes_sections
         (0x1000 : UInt32) (0x2000 : UInt32) (0x3000 : UInt32) (0x140000000 : Address)
         (windowsStreamArtifact $direction).executable.textBytes
         (windowsStreamArtifact $direction).executable.rdataBytes
         (windowsStreamArtifact $direction).executable.imports ($addr + 3)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
       have key4 := loadMemory_excludes_sections
         (0x1000 : UInt32) (0x2000 : UInt32) (0x3000 : UInt32) (0x140000000 : Address)
         (windowsStreamArtifact $direction).executable.textBytes
         (windowsStreamArtifact $direction).executable.rdataBytes
         (windowsStreamArtifact $direction).executable.imports ($addr + 4)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
       have key5 := loadMemory_excludes_sections
         (0x1000 : UInt32) (0x2000 : UInt32) (0x3000 : UInt32) (0x140000000 : Address)
         (windowsStreamArtifact $direction).executable.textBytes
         (windowsStreamArtifact $direction).executable.rdataBytes
         (windowsStreamArtifact $direction).executable.imports ($addr + 5)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
       have key6 := loadMemory_excludes_sections
         (0x1000 : UInt32) (0x2000 : UInt32) (0x3000 : UInt32) (0x140000000 : Address)
         (windowsStreamArtifact $direction).executable.textBytes
         (windowsStreamArtifact $direction).executable.rdataBytes
         (windowsStreamArtifact $direction).executable.imports ($addr + 6)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
       have key7 := loadMemory_excludes_sections
         (0x1000 : UInt32) (0x2000 : UInt32) (0x3000 : UInt32) (0x140000000 : Address)
         (windowsStreamArtifact $direction).executable.textBytes
         (windowsStreamArtifact $direction).executable.rdataBytes
         (windowsStreamArtifact $direction).executable.imports ($addr + 7)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
         (by rw [windows_stream_text_size]; decide) (by rw [windows_stream_rdata_size]; decide)
       rw [key0, key1, key2, key3, key4, key5, key6, key7]
       decide))

set_option maxHeartbeats 8000000 in
theorem windows_iat0_compress_selfref :
    X86_64Mem.read .w64 ((0x140000000 : Address) + 0x3000)
      (X86_64Mem.initRegion (loadMemory (0x140000000 : Address)
        [((0x1000 : UInt32), (windowsStreamArtifact .compress).executable.textBytes),
         ((0x2000 : UInt32), (windowsStreamArtifact .compress).executable.rdataBytes)]
        (windowsStreamArtifact .compress).executable.imports (0x3000 : UInt32))) =
      (0x140000000 : Address) + 0x3000 := by
  prove_spike5_selfref .compress at ((0x140000000 : Address) + 0x3000)

set_option maxHeartbeats 8000000 in
theorem windows_iat1_compress_selfref :
    X86_64Mem.read .w64 ((0x140000000 : Address) + 0x3008)
      (X86_64Mem.initRegion (loadMemory (0x140000000 : Address)
        [((0x1000 : UInt32), (windowsStreamArtifact .compress).executable.textBytes),
         ((0x2000 : UInt32), (windowsStreamArtifact .compress).executable.rdataBytes)]
        (windowsStreamArtifact .compress).executable.imports (0x3000 : UInt32))) =
      (0x140000000 : Address) + 0x3008 := by
  prove_spike5_selfref .compress at ((0x140000000 : Address) + 0x3008)

set_option maxHeartbeats 8000000 in
theorem windows_iat2_compress_selfref :
    X86_64Mem.read .w64 ((0x140000000 : Address) + 0x3010)
      (X86_64Mem.initRegion (loadMemory (0x140000000 : Address)
        [((0x1000 : UInt32), (windowsStreamArtifact .compress).executable.textBytes),
         ((0x2000 : UInt32), (windowsStreamArtifact .compress).executable.rdataBytes)]
        (windowsStreamArtifact .compress).executable.imports (0x3000 : UInt32))) =
      (0x140000000 : Address) + 0x3010 := by
  prove_spike5_selfref .compress at ((0x140000000 : Address) + 0x3010)

set_option maxHeartbeats 8000000 in
theorem windows_iat3_compress_selfref :
    X86_64Mem.read .w64 ((0x140000000 : Address) + 0x3018)
      (X86_64Mem.initRegion (loadMemory (0x140000000 : Address)
        [((0x1000 : UInt32), (windowsStreamArtifact .compress).executable.textBytes),
         ((0x2000 : UInt32), (windowsStreamArtifact .compress).executable.rdataBytes)]
        (windowsStreamArtifact .compress).executable.imports (0x3000 : UInt32))) =
      (0x140000000 : Address) + 0x3018 := by
  prove_spike5_selfref .compress at ((0x140000000 : Address) + 0x3018)

set_option maxHeartbeats 8000000 in
theorem windows_iat0_decompress_selfref :
    X86_64Mem.read .w64 ((0x140000000 : Address) + 0x3000)
      (X86_64Mem.initRegion (loadMemory (0x140000000 : Address)
        [((0x1000 : UInt32), (windowsStreamArtifact .decompress).executable.textBytes),
         ((0x2000 : UInt32), (windowsStreamArtifact .decompress).executable.rdataBytes)]
        (windowsStreamArtifact .decompress).executable.imports (0x3000 : UInt32))) =
      (0x140000000 : Address) + 0x3000 := by
  prove_spike5_selfref .decompress at ((0x140000000 : Address) + 0x3000)

set_option maxHeartbeats 8000000 in
theorem windows_iat1_decompress_selfref :
    X86_64Mem.read .w64 ((0x140000000 : Address) + 0x3008)
      (X86_64Mem.initRegion (loadMemory (0x140000000 : Address)
        [((0x1000 : UInt32), (windowsStreamArtifact .decompress).executable.textBytes),
         ((0x2000 : UInt32), (windowsStreamArtifact .decompress).executable.rdataBytes)]
        (windowsStreamArtifact .decompress).executable.imports (0x3000 : UInt32))) =
      (0x140000000 : Address) + 0x3008 := by
  prove_spike5_selfref .decompress at ((0x140000000 : Address) + 0x3008)

set_option maxHeartbeats 8000000 in
theorem windows_iat2_decompress_selfref :
    X86_64Mem.read .w64 ((0x140000000 : Address) + 0x3010)
      (X86_64Mem.initRegion (loadMemory (0x140000000 : Address)
        [((0x1000 : UInt32), (windowsStreamArtifact .decompress).executable.textBytes),
         ((0x2000 : UInt32), (windowsStreamArtifact .decompress).executable.rdataBytes)]
        (windowsStreamArtifact .decompress).executable.imports (0x3000 : UInt32))) =
      (0x140000000 : Address) + 0x3010 := by
  prove_spike5_selfref .decompress at ((0x140000000 : Address) + 0x3010)

set_option maxHeartbeats 8000000 in
theorem windows_iat3_decompress_selfref :
    X86_64Mem.read .w64 ((0x140000000 : Address) + 0x3018)
      (X86_64Mem.initRegion (loadMemory (0x140000000 : Address)
        [((0x1000 : UInt32), (windowsStreamArtifact .decompress).executable.textBytes),
         ((0x2000 : UInt32), (windowsStreamArtifact .decompress).executable.rdataBytes)]
        (windowsStreamArtifact .decompress).executable.imports (0x3000 : UInt32))) =
      (0x140000000 : Address) + 0x3018 := by
  prove_spike5_selfref .decompress at ((0x140000000 : Address) + 0x3018)

/- Windows uses the same logical CFG.  Only each call edge's target realization
   differs: the PE loader supplies the exact artifact IAT slot proven by the
   provider certificate. -/
def windowsConcreteStreamInstructions : List X86_64Instr :=
  [call_rip 8186, call_rip 8188, call_rip 8190, call_rip 8192]

theorem windows_stream_instructions_eq (direction : CodecDirection) :
    (windowsStreamArtifact direction).instructions = windowsConcreteStreamInstructions := by
  cases direction <;> rfl

def windowsStreamInitial (direction : CodecDirection) (environment : Environment) :=
  Platform.load (P := WindowsX86_64 AnyEvent) (windowsStreamArtifact direction) environment

def windowsStreamEntry (direction : CodecDirection) (environment : Environment) :
    StreamingInvocationContext :=
  .mk direction environment.stdin spike5AllocationScope (windowsStreamInitial direction environment).rip

def windowsStep0 (direction : CodecDirection) (environment : Environment) :=
  X86_64Instruction.step (call_rip 8186) (windowsStreamInitial direction environment)

def windowsState1 (direction : CodecDirection) (environment : Environment) :=
  withPhase (windowsStep0 direction environment) 1

def windowsStep1 (direction : CodecDirection) (environment : Environment) :=
  X86_64Instruction.step (call_rip 8188) (windowsState1 direction environment)

def windowsState2 (direction : CodecDirection) (environment : Environment) :=
  withPhase (windowsStep1 direction environment) 2

def windowsStep2 (direction : CodecDirection) (environment : Environment) :=
  X86_64Instruction.step (call_rip 8190) (windowsState2 direction environment)

def windowsState3 (direction : CodecDirection) (environment : Environment) :=
  withPhase (windowsStep2 direction environment) 3

def windowsStep3 (direction : CodecDirection) (environment : Environment) :=
  X86_64Instruction.step (call_rip 8192) (windowsState3 direction environment)

theorem withPhase_call_rip_rip (state : X86_64MachineState)
    (displacement : Int32) (phase : UInt64) :
    (withPhase (X86_64Instruction.step (call_rip displacement) state) phase).rip =
      state.rip + 6 := by
  change ((state.push64 (state.rip + 6)).pop64).1 = state.rip + 6
  exact (push64_pop64_roundtrip state (state.rip + 6)).1

theorem withPhase_call_rip_rsp (state : X86_64MachineState)
    (displacement : Int32) (phase : UInt64) :
    (withPhase (X86_64Instruction.step (call_rip displacement) state) phase).rsp =
      state.rsp := by
  change (state.push64 (state.rip + 6)).pop64.2.rsp = state.rsp
  exact (push64_pop64_roundtrip state (state.rip + 6)).2.1

@[simp] theorem call_rip_step_rip (state : X86_64MachineState)
    (displacement : Int32) :
    (X86_64Instruction.step (call_rip displacement) state).rip =
      state.read64 (state.rip + 6 + signExtend32To64 displacement) := by
  rfl

@[simp] theorem call_rip_preserves_r15 (state : X86_64MachineState)
    (displacement : Int32) :
    (X86_64Instruction.step (call_rip displacement) state).gprs .r15 =
      state.gprs .r15 := by
  rfl

@[simp] theorem call_rip_step_faulted (state : X86_64MachineState)
    (displacement : Int32) :
    (X86_64Instruction.step (call_rip displacement) state).faulted = state.faulted := by
  rfl

theorem windows_initial_rip (direction : CodecDirection) (environment : Environment) :
    (windowsStreamInitial direction environment).rip =
      (windowsStreamArtifact direction).executable.load.rip := by
  rfl

theorem windows_initial_rsp (direction : CodecDirection) (environment : Environment) :
    (windowsStreamInitial direction environment).rsp =
      (windowsStreamArtifact direction).executable.load.rsp := by
  rfl

theorem windows_initial_read64 (direction : CodecDirection) (environment : Environment)
    (address : Address) :
    (windowsStreamInitial direction environment).read64 address =
      (windowsStreamArtifact direction).executable.load.read64 address := by
  rfl

theorem windows_lookup_zero (direction : CodecDirection) (environment : Environment) :
    instructionAtRipIndexed
      (indexInstructions (windowsStreamInitial direction environment).rip
        windowsConcreteStreamInstructions)
      (windowsStreamInitial direction environment).rip = some (call_rip 8186) :=
  lookup_first_instruction _ _ _

theorem windows_step0_resolves (direction : CodecDirection) (environment : Environment) :
    let executable := (windowsStreamArtifact direction).executable
    let layout := computeSectionLayout executable.textBytes.size executable.rdataBytes.size 512
    let iatBase := executable.imageBase + layout.idataRva.toUInt64
    let index := (((windowsStep0 direction environment).rip - iatBase) / 8).toNat
    (if index < 4 then some index else none) = some 0 := by
  cases direction <;>
    change (let executable := (windowsStreamArtifact _).executable
      let layout := computeSectionLayout executable.textBytes.size executable.rdataBytes.size 512
      let iatBase := executable.imageBase + layout.idataRva.toUInt64
      let stepped := X86_64Instruction.step (call_rip 8186) executable.load
      let index := ((stepped.rip - iatBase) / 8).toNat
      if index < 4 then some index else none) = some 0 <;>
    decide

theorem streamingNativeCall_zero
    (resolveCall : Address → X86_64MachineState → Option Nat)
    (context : StreamingInvocationContext) (address : Address)
    (state : X86_64MachineState) (hresolve : resolveCall address state = some 0) :
    streamingNativeCall resolveCall context address state =
      some (withPhase state 1, none) := by
  simp [streamingNativeCall, hresolve]

theorem windows_intercept_zero (direction : CodecDirection) (environment : Environment) :
    @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStep0 direction environment).rip (windowsStep0 direction environment) =
        some (windowsState1 direction environment, none) := by
  change streamingNativeCall _ _ _ _ = _
  apply streamingNativeCall_zero
  exact windows_step0_resolves direction environment

theorem windows_state1_rip (direction : CodecDirection) (environment : Environment) :
    (windowsState1 direction environment).rip =
      (windowsStreamInitial direction environment).rip + 6 :=
  withPhase_call_rip_rip _ _ _

theorem windows_lookup_one (direction : CodecDirection) (environment : Environment) :
    instructionAtRipIndexed
      (indexInstructions (windowsStreamInitial direction environment).rip
        windowsConcreteStreamInstructions)
      (windowsState1 direction environment).rip = some (call_rip 8188) := by
  rw [windows_state1_rip, windows_initial_rip]
  cases direction <;> rfl

theorem windows_state1_rsp (direction : CodecDirection) (environment : Environment) :
    (windowsState1 direction environment).rsp =
      (windowsStreamInitial direction environment).rsp :=
  withPhase_call_rip_rsp _ _ _

theorem windows_step1_target (direction : CodecDirection) (environment : Environment) :
    let executable := (windowsStreamArtifact direction).executable
    let layout := computeSectionLayout executable.textBytes.size executable.rdataBytes.size 512
    let iatBase := executable.imageBase + layout.idataRva.toUInt64
    (windowsStep1 direction environment).rip = iatBase + 8 := by
  unfold windowsStep1
  rw [call_rip_step_rip]
  have hpreserved := withPhase_call_rip_read64_preserved
    (windowsStreamInitial direction environment) 8186 1
    ((windowsState1 direction environment).rip + 6 + signExtend32To64 8188)
    (by
      rw [windows_initial_rsp]
      cases direction <;> decide)
    (by
      rw [windows_state1_rip, windows_initial_rip, windows_initial_rsp]
      cases direction <;> decide)
  have hpreserved' :
      (windowsState1 direction environment).read64
          ((windowsState1 direction environment).rip + 6 + signExtend32To64 8188) =
        (windowsStreamInitial direction environment).read64
          ((windowsState1 direction environment).rip + 6 + signExtend32To64 8188) := by
    simpa only [windowsState1, windowsStep0] using hpreserved
  rw [hpreserved']
  rw [windows_initial_read64, windows_state1_rip, windows_initial_rip]
  simp only
  rw [windows_stream_layout]
  rw [windows_executable_load_read64_of_layout _ _ (windows_stream_layout direction)]
  cases direction
  · exact windows_iat1_compress_selfref
  · exact windows_iat1_decompress_selfref

theorem windows_step1_resolves (direction : CodecDirection) (environment : Environment) :
    let executable := (windowsStreamArtifact direction).executable
    let layout := computeSectionLayout executable.textBytes.size executable.rdataBytes.size 512
    let iatBase := executable.imageBase + layout.idataRva.toUInt64
    let index := (((windowsStep1 direction environment).rip - iatBase) / 8).toNat
    (if index < 4 then some index else none) = some 1 := by
  rw [windows_step1_target]
  cases direction <;> decide

theorem streamingNativeCall_one
    (resolveCall : Address → X86_64MachineState → Option Nat)
    (context : StreamingInvocationContext) (address : Address)
    (state : X86_64MachineState) (hresolve : resolveCall address state = some 1)
    (hphase : state.gprs .r15 = 1) :
    streamingNativeCall resolveCall context address state =
      some (withPhase state 2, none) := by
  simp [streamingNativeCall, hresolve, hphase]

theorem windows_intercept_one (direction : CodecDirection) (environment : Environment) :
    @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStep1 direction environment).rip (windowsStep1 direction environment) =
        some (windowsState2 direction environment, none) := by
  change streamingNativeCall _ _ _ _ = _
  apply streamingNativeCall_one
  · exact windows_step1_resolves direction environment
  · unfold windowsStep1
    rw [call_rip_preserves_r15]
    exact withPhase_r15 _ _

theorem windows_state2_rip (direction : CodecDirection) (environment : Environment) :
    (windowsState2 direction environment).rip =
      (windowsStreamInitial direction environment).rip + 12 := by
  unfold windowsState2 windowsStep1
  rw [withPhase_call_rip_rip, windows_state1_rip]
  simp [UInt64.add_assoc]

theorem windows_lookup_two (direction : CodecDirection) (environment : Environment) :
    instructionAtRipIndexed
      (indexInstructions (windowsStreamInitial direction environment).rip
        windowsConcreteStreamInstructions)
      (windowsState2 direction environment).rip = some (call_rip 8190) := by
  rw [windows_state2_rip, windows_initial_rip]
  cases direction <;> rfl

theorem windows_state2_rsp (direction : CodecDirection) (environment : Environment) :
    (windowsState2 direction environment).rsp =
      (windowsStreamInitial direction environment).rsp := by
  unfold windowsState2 windowsStep1
  rw [withPhase_call_rip_rsp, windows_state1_rsp]

theorem windows_step2_target (direction : CodecDirection) (environment : Environment) :
    let executable := (windowsStreamArtifact direction).executable
    let layout := computeSectionLayout executable.textBytes.size executable.rdataBytes.size 512
    let iatBase := executable.imageBase + layout.idataRva.toUInt64
    (windowsStep2 direction environment).rip = iatBase + 16 := by
  unfold windowsStep2
  rw [call_rip_step_rip]
  have hpreserved1 := withPhase_call_rip_read64_preserved
    (windowsState1 direction environment) 8188 2
    ((windowsState2 direction environment).rip + 6 + signExtend32To64 8190)
    (by
      rw [windows_state1_rsp, windows_initial_rsp]
      cases direction <;> decide)
    (by
      rw [windows_state2_rip, windows_initial_rip, windows_state1_rsp, windows_initial_rsp]
      cases direction <;> decide)
  have hpreserved1' :
      (windowsState2 direction environment).read64
          ((windowsState2 direction environment).rip + 6 + signExtend32To64 8190) =
        (windowsState1 direction environment).read64
          ((windowsState2 direction environment).rip + 6 + signExtend32To64 8190) := by
    simpa only [windowsState2, windowsStep1] using hpreserved1
  rw [hpreserved1']
  have hpreserved0 := withPhase_call_rip_read64_preserved
    (windowsStreamInitial direction environment) 8186 1
    ((windowsState2 direction environment).rip + 6 + signExtend32To64 8190)
    (by
      rw [windows_initial_rsp]
      cases direction <;> decide)
    (by
      rw [windows_state2_rip, windows_initial_rip, windows_initial_rsp]
      cases direction <;> decide)
  have hpreserved0' :
      (windowsState1 direction environment).read64
          ((windowsState2 direction environment).rip + 6 + signExtend32To64 8190) =
        (windowsStreamInitial direction environment).read64
          ((windowsState2 direction environment).rip + 6 + signExtend32To64 8190) := by
    simpa only [windowsState1, windowsStep0] using hpreserved0
  rw [hpreserved0']
  rw [windows_initial_read64, windows_state2_rip, windows_initial_rip]
  simp only
  rw [windows_stream_layout]
  rw [windows_executable_load_read64_of_layout _ _ (windows_stream_layout direction)]
  cases direction
  · exact windows_iat2_compress_selfref
  · exact windows_iat2_decompress_selfref

theorem windows_step2_resolves (direction : CodecDirection) (environment : Environment) :
    let executable := (windowsStreamArtifact direction).executable
    let layout := computeSectionLayout executable.textBytes.size executable.rdataBytes.size 512
    let iatBase := executable.imageBase + layout.idataRva.toUInt64
    let index := (((windowsStep2 direction environment).rip - iatBase) / 8).toNat
    (if index < 4 then some index else none) = some 2 := by
  rw [windows_step2_target]
  cases direction <;> decide

def windowsResultState (direction : CodecDirection) (environment : Environment) :
    X86_64MachineState :=
  if (streamResultEvent (windowsStreamEntry direction environment)).snd then
    windowsState3 direction environment
  else
    windowsStep2 direction environment

theorem streamingNativeCall_two
    (resolveCall : Address → X86_64MachineState → Option Nat)
    (context : StreamingInvocationContext) (address : Address)
    (state : X86_64MachineState) (hresolve : resolveCall address state = some 2)
    (hphase : state.gprs .r15 = 2) :
    streamingNativeCall resolveCall context address state =
      some (if (streamResultEvent context).snd then withPhase state 3 else state,
        (streamResultEvent context).fst) := by
  cases hcontinue : (streamResultEvent context).snd <;>
    simp [streamingNativeCall, hresolve, hphase, hcontinue]

theorem windows_intercept_two (direction : CodecDirection) (environment : Environment) :
    @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStep2 direction environment).rip (windowsStep2 direction environment) =
        some (windowsResultState direction environment,
          (streamResultEvent (windowsStreamEntry direction environment)).fst) := by
  change streamingNativeCall _ _ _ _ = _
  rw [streamingNativeCall_two _ _ _ _ (windows_step2_resolves direction environment)]
  · rfl
  · unfold windowsStep2
    rw [call_rip_preserves_r15]
    exact withPhase_r15 _ _

theorem windows_state3_rip (direction : CodecDirection) (environment : Environment) :
    (windowsState3 direction environment).rip =
      (windowsStreamInitial direction environment).rip + 18 := by
  unfold windowsState3 windowsStep2
  rw [withPhase_call_rip_rip, windows_state2_rip]
  simp [UInt64.add_assoc]

theorem windows_lookup_three (direction : CodecDirection) (environment : Environment) :
    instructionAtRipIndexed
      (indexInstructions (windowsStreamInitial direction environment).rip
        windowsConcreteStreamInstructions)
      (windowsState3 direction environment).rip = some (call_rip 8192) := by
  rw [windows_state3_rip, windows_initial_rip]
  cases direction <;> rfl

theorem windows_state3_rsp (direction : CodecDirection) (environment : Environment) :
    (windowsState3 direction environment).rsp =
      (windowsStreamInitial direction environment).rsp := by
  unfold windowsState3 windowsStep2
  rw [withPhase_call_rip_rsp, windows_state2_rsp]

theorem windows_step3_target (direction : CodecDirection) (environment : Environment) :
    let executable := (windowsStreamArtifact direction).executable
    let layout := computeSectionLayout executable.textBytes.size executable.rdataBytes.size 512
    let iatBase := executable.imageBase + layout.idataRva.toUInt64
    (windowsStep3 direction environment).rip = iatBase + 24 := by
  unfold windowsStep3
  rw [call_rip_step_rip]
  have hpreserved2 := withPhase_call_rip_read64_preserved
    (windowsState2 direction environment) 8190 3
    ((windowsState3 direction environment).rip + 6 + signExtend32To64 8192)
    (by
      rw [windows_state2_rsp, windows_initial_rsp]
      cases direction <;> decide)
    (by
      rw [windows_state3_rip, windows_initial_rip, windows_state2_rsp, windows_initial_rsp]
      cases direction <;> decide)
  have hpreserved2' :
      (windowsState3 direction environment).read64
          ((windowsState3 direction environment).rip + 6 + signExtend32To64 8192) =
        (windowsState2 direction environment).read64
          ((windowsState3 direction environment).rip + 6 + signExtend32To64 8192) := by
    simpa only [windowsState3, windowsStep2] using hpreserved2
  rw [hpreserved2']
  have hpreserved1 := withPhase_call_rip_read64_preserved
    (windowsState1 direction environment) 8188 2
    ((windowsState3 direction environment).rip + 6 + signExtend32To64 8192)
    (by
      rw [windows_state1_rsp, windows_initial_rsp]
      cases direction <;> decide)
    (by
      rw [windows_state3_rip, windows_initial_rip, windows_state1_rsp, windows_initial_rsp]
      cases direction <;> decide)
  have hpreserved1' :
      (windowsState2 direction environment).read64
          ((windowsState3 direction environment).rip + 6 + signExtend32To64 8192) =
        (windowsState1 direction environment).read64
          ((windowsState3 direction environment).rip + 6 + signExtend32To64 8192) := by
    simpa only [windowsState2, windowsStep1] using hpreserved1
  rw [hpreserved1']
  have hpreserved0 := withPhase_call_rip_read64_preserved
    (windowsStreamInitial direction environment) 8186 1
    ((windowsState3 direction environment).rip + 6 + signExtend32To64 8192)
    (by
      rw [windows_initial_rsp]
      cases direction <;> decide)
    (by
      rw [windows_state3_rip, windows_initial_rip, windows_initial_rsp]
      cases direction <;> decide)
  have hpreserved0' :
      (windowsState1 direction environment).read64
          ((windowsState3 direction environment).rip + 6 + signExtend32To64 8192) =
        (windowsStreamInitial direction environment).read64
          ((windowsState3 direction environment).rip + 6 + signExtend32To64 8192) := by
    simpa only [windowsState1, windowsStep0] using hpreserved0
  rw [hpreserved0']
  rw [windows_initial_read64, windows_state3_rip, windows_initial_rip]
  simp only
  rw [windows_stream_layout]
  rw [windows_executable_load_read64_of_layout _ _ (windows_stream_layout direction)]
  cases direction
  · exact windows_iat3_compress_selfref
  · exact windows_iat3_decompress_selfref

theorem windows_step3_resolves (direction : CodecDirection) (environment : Environment) :
    let executable := (windowsStreamArtifact direction).executable
    let layout := computeSectionLayout executable.textBytes.size executable.rdataBytes.size 512
    let iatBase := executable.imageBase + layout.idataRva.toUInt64
    let index := (((windowsStep3 direction environment).rip - iatBase) / 8).toNat
    (if index < 4 then some index else none) = some 3 := by
  rw [windows_step3_target]
  cases direction <;> decide

theorem streamingNativeCall_three
    (resolveCall : Address → X86_64MachineState → Option Nat)
    (context : StreamingInvocationContext) (address : Address)
    (state : X86_64MachineState) (hresolve : resolveCall address state = some 3)
    (hphase : state.gprs .r15 = 3) :
    streamingNativeCall resolveCall context address state =
      some (state, some (Inject.inject (ProcessEvent.exit 0))) := by
  simp [streamingNativeCall, hresolve, hphase]

theorem windows_intercept_three (direction : CodecDirection) (environment : Environment) :
    @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStep3 direction environment).rip (windowsStep3 direction environment) =
        some (windowsStep3 direction environment,
          some (Inject.inject (ProcessEvent.exit 0))) := by
  change streamingNativeCall _ _ _ _ = _
  apply streamingNativeCall_three
  · exact windows_step3_resolves direction environment
  · unfold windowsStep3
    rw [call_rip_preserves_r15]
    exact withPhase_r15 _ _

theorem windows_initial_safe (direction : CodecDirection) (environment : Environment) :
    (windowsStreamInitial direction environment).faulted = false := by
  rfl

theorem windows_state1_safe (direction : CodecDirection) (environment : Environment) :
    (windowsState1 direction environment).faulted = false := by
  simp [windowsState1, windowsStep0, windows_initial_safe]

theorem windows_state2_safe (direction : CodecDirection) (environment : Environment) :
    (windowsState2 direction environment).faulted = false := by
  simp [windowsState2, windowsStep1, windows_state1_safe]

theorem windows_state3_safe (direction : CodecDirection) (environment : Environment) :
    (windowsState3 direction environment).faulted = false := by
  simp [windowsState3, windowsStep2, windows_state2_safe]

theorem windows_step2_safe (direction : CodecDirection) (environment : Environment) :
    (windowsStep2 direction environment).faulted = false := by
  simp [windowsStep2, windows_state2_safe]

theorem windows_step3_safe (direction : CodecDirection) (environment : Environment) :
    (windowsStep3 direction environment).faulted = false := by
  simp [windowsStep3, windows_state3_safe]

theorem windows_lookup_after_two (direction : CodecDirection) (environment : Environment) :
    instructionAtRipIndexed
      (indexInstructions (windowsStreamInitial direction environment).rip
        windowsConcreteStreamInstructions)
      (windowsStep2 direction environment).rip = none := by
  rw [windows_step2_target, windows_initial_rip]
  cases direction <;> rfl

theorem windows_lookup_after_three (direction : CodecDirection) (environment : Environment) :
    instructionAtRipIndexed
      (indexInstructions (windowsStreamInitial direction environment).rip
        windowsConcreteStreamInstructions)
      (windowsStep3 direction environment).rip = none := by
  rw [windows_step3_target, windows_initial_rip]
  cases direction <;> rfl

def windowsStartEdge (direction : CodecDirection) (environment : Environment) :
    @SilentNativeEdgeCertificate AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions
      (windowsStreamInitial direction environment) (windowsState1 direction environment) where
  instruction := call_rip 8186
  lookup := windows_lookup_zero direction environment
  intercept := windows_intercept_zero direction environment
  safe := windows_state1_safe direction environment

def windowsPushEdge (direction : CodecDirection) (environment : Environment) :
    @SilentNativeEdgeCertificate AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions
      (windowsState1 direction environment) (windowsState2 direction environment) where
  instruction := call_rip 8188
  lookup := windows_lookup_one direction environment
  intercept := windows_intercept_one direction environment
  safe := windows_state2_safe direction environment

def windowsIndexed (direction : CodecDirection) (environment : Environment) :=
  indexInstructions (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions

theorem windows_outcome_prefix (direction : CodecDirection) (environment : Environment)
    (eventsRev : List AnyEvent) :
    @runProgramOutcomeLoop AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsIndexed direction environment) 50000
      (windowsStreamInitial direction environment) eventsRev =
    @runProgramOutcomeLoop AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsIndexed direction environment) 49998
      (windowsState2 direction environment) eventsRev := by
  let start := windowsStartEdge direction environment
  let push := windowsPushEdge direction environment
  calc
    _ = @runProgramOutcomeLoop AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsIndexed direction environment) 49999
        (windowsState1 direction environment) eventsRev :=
      @outcome_step_silent AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsIndexed direction environment) 49999
        (windowsStreamInitial direction environment) (windowsState1 direction environment)
        start.instruction eventsRev start.lookup start.intercept start.safe
    _ = _ := @outcome_step_silent AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsIndexed direction environment) 49998
      (windowsState1 direction environment) (windowsState2 direction environment)
      push.instruction eventsRev push.lookup push.intercept push.safe

theorem windows_outcome_stops_after_result (direction : CodecDirection)
    (environment : Environment) (eventsRev : List AnyEvent) (event : AnyEvent)
    (hhook : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStep2 direction environment).rip (windowsStep2 direction environment) =
        some (windowsStep2 direction environment, some event)) :
    @runProgramOutcomeLoop AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsIndexed direction environment) 49998
      (windowsState2 direction environment) eventsRev =
        .returned (windowsStep2 direction environment) (event :: eventsRev).reverse := by
  calc
    _ = @runProgramOutcomeLoop AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsIndexed direction environment) 49997
        (windowsStep2 direction environment) (event :: eventsRev) :=
      @outcome_step_event AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsIndexed direction environment) 49997
        (windowsState2 direction environment) (windowsStep2 direction environment)
        (call_rip 8190) eventsRev event
        (windows_lookup_two direction environment) hhook
        (windows_step2_safe direction environment)
    _ = _ := @outcome_complete AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsIndexed direction environment) 49996 (windowsStep2 direction environment)
      (event :: eventsRev) (windows_lookup_after_two direction environment)

theorem windows_outcome_continues_after_result (direction : CodecDirection)
    (environment : Environment) (eventsRev : List AnyEvent) (event : AnyEvent)
    (hhook : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStep2 direction environment).rip (windowsStep2 direction environment) =
        some (windowsState3 direction environment, some event)) :
    @runProgramOutcomeLoop AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsIndexed direction environment) 49998
      (windowsState2 direction environment) eventsRev =
        .returned (windowsStep3 direction environment)
          (Inject.inject (ProcessEvent.exit 0) :: event :: eventsRev).reverse := by
  calc
    _ = @runProgramOutcomeLoop AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsIndexed direction environment) 49997
        (windowsState3 direction environment) (event :: eventsRev) :=
      @outcome_step_event AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsIndexed direction environment) 49997
        (windowsState2 direction environment) (windowsState3 direction environment)
        (call_rip 8190) eventsRev event
        (windows_lookup_two direction environment) hhook
        (windows_state3_safe direction environment)
    _ = @runProgramOutcomeLoop AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsIndexed direction environment) 49996
        (windowsStep3 direction environment)
        (Inject.inject (ProcessEvent.exit 0) :: event :: eventsRev) :=
      @outcome_step_event AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsIndexed direction environment) 49996
        (windowsState3 direction environment) (windowsStep3 direction environment)
        (call_rip 8192) (event :: eventsRev) (Inject.inject (ProcessEvent.exit 0))
        (windows_lookup_three direction environment)
        (windows_intercept_three direction environment) (windows_step3_safe direction environment)
    _ = _ := @outcome_complete AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsIndexed direction environment) 49995 (windowsStep3 direction environment)
      (Inject.inject (ProcessEvent.exit 0) :: event :: eventsRev)
      (windows_lookup_after_three direction environment)

theorem windows_trace_prefix (direction : CodecDirection) (environment : Environment) :
    @runProgramTraceWithLoops AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 50000
      (windowsStreamInitial direction environment) =
    @runProgramTraceWithLoops AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 49998
      (windowsState2 direction environment) := by
  let start := windowsStartEdge direction environment
  let push := windowsPushEdge direction environment
  calc
    _ = @runProgramTraceWithLoops AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 49999
        (windowsState1 direction environment) :=
      @trace_step_silent AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 49999
        (windowsStreamInitial direction environment) (windowsState1 direction environment)
        start.instruction start.lookup start.intercept start.safe
    _ = _ := @trace_step_silent AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 49998
      (windowsState1 direction environment) (windowsState2 direction environment)
      push.instruction push.lookup push.intercept push.safe

theorem windows_trace_stops_after_result (direction : CodecDirection)
    (environment : Environment) (event : AnyEvent)
    (hhook : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStep2 direction environment).rip (windowsStep2 direction environment) =
        some (windowsStep2 direction environment, some event)) :
    @runProgramTraceWithLoops AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 49998
      (windowsState2 direction environment) = [event] := by
  calc
    _ = event :: @runProgramTraceWithLoops AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 49997
        (windowsStep2 direction environment) :=
      @trace_step_event AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 49997
        (windowsState2 direction environment) (windowsStep2 direction environment)
        (call_rip 8190) event
        (windows_lookup_two direction environment) hhook (windows_step2_safe direction environment)
    _ = [event] := by
      rw [@trace_complete AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 49996
        (windowsStep2 direction environment) (windows_lookup_after_two direction environment)]

theorem windows_trace_continues_after_result (direction : CodecDirection)
    (environment : Environment) (event : AnyEvent)
    (hhook : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStep2 direction environment).rip (windowsStep2 direction environment) =
        some (windowsState3 direction environment, some event)) :
    @runProgramTraceWithLoops AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 49998
      (windowsState2 direction environment) =
        [event, Inject.inject (ProcessEvent.exit 0)] := by
  calc
    _ = event :: @runProgramTraceWithLoops AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 49997
        (windowsState3 direction environment) :=
      @trace_step_event AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 49997
        (windowsState2 direction environment) (windowsState3 direction environment)
        (call_rip 8190) event
        (windows_lookup_two direction environment) hhook (windows_state3_safe direction environment)
    _ = event :: Inject.inject (ProcessEvent.exit 0) ::
        @runProgramTraceWithLoops AnyEvent
          (windowsStreamingInterceptor (windowsStreamArtifact direction)
            (windowsStreamEntry direction environment))
          (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 49996
          (windowsStep3 direction environment) := by
      rw [@trace_step_event AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 49996
        (windowsState3 direction environment) (windowsStep3 direction environment)
        (call_rip 8192) (Inject.inject (ProcessEvent.exit 0))
        (windows_lookup_three direction environment)
        (windows_intercept_three direction environment) (windows_step3_safe direction environment)]
    _ = [event, Inject.inject (ProcessEvent.exit 0)] := by
      rw [@trace_complete AnyEvent
        (windowsStreamingInterceptor (windowsStreamArtifact direction)
          (windowsStreamEntry direction environment))
        (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 49995
        (windowsStep3 direction environment)
        (windows_lookup_after_three direction environment)]

def windowsStreamingSpec (direction : CodecDirection) (environment : Environment) :
    List AnyEvent :=
  streamingInvocationTrace direction spike5AllocationScope environment.stdin

theorem windows_platform_run (runtime : ExternalCallInterceptor X86_64 AnyEvent)
    (artifact : WindowsX86_64Artifact) (state : X86_64MachineState) :
    Platform.run (P := WindowsX86_64 AnyEvent) runtime artifact state =
      (@runProgramOutcomeWithLoops AnyEvent runtime state.rip artifact.instructions 50000 state).events := by
  rfl

theorem windows_platform_admissible (runtime : ExternalCallInterceptor X86_64 AnyEvent)
    (artifact : WindowsX86_64Artifact) (state : X86_64MachineState) :
    Platform.admissible (P := WindowsX86_64 AnyEvent) runtime artifact state =
      (@runProgramOutcomeWithLoops AnyEvent runtime state.rip artifact.instructions 50000 state).isAdmissible false := by
  rfl

theorem windows_stream_realize (direction : CodecDirection)
    (artifact : WindowsX86_64Artifact) (context : StreamingInvocationContext) :
    (windowsStreamingCapabilities direction).realize artifact context =
      windowsStreamingInterceptor artifact context := by
  rfl

theorem windows_streaming_trace_equivalence (direction : CodecDirection)
    (environment : Environment) :
    Platform.run
      ((windowsStreamingCapabilities direction).realize (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStreamArtifact direction)
      (Platform.load (P := WindowsX86_64 AnyEvent) (windowsStreamArtifact direction) environment) =
        windowsStreamingSpec direction environment := by
  rw [windows_platform_run, windows_stream_realize, windows_stream_instructions_eq]
  rw [@runProgramOutcomeWithLoops_events AnyEvent
    (windowsStreamingInterceptor (windowsStreamArtifact direction)
      (windowsStreamEntry direction environment))]
  change @runProgramTraceWithLoops AnyEvent
      (windowsStreamingInterceptor (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStreamInitial direction environment).rip windowsConcreteStreamInstructions 50000
      (windowsStreamInitial direction environment) = _
  rw [windows_trace_prefix]
  cases direction with
  | compress =>
    cases hresult : compressAll bufferedStreamingZlibCapability
      spike5AllocationScope environment.stdin with
    | rejected error scope => nomatch error
    | resourceExhausted scope =>
      have hhook := windows_intercept_two .compress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (windowsStreamingInterceptor (windowsStreamArtifact .compress)
            (windowsStreamEntry .compress environment))
          (windowsStep2 .compress environment).rip (windowsStep2 .compress environment) =
            some (windowsStep2 .compress environment,
              some (Inject.inject (ProcessEvent.exit 2))) := by
        simpa [streamResultEvent, windowsStreamEntry, windowsResultState, hresult] using hhook
      rw [windows_trace_stops_after_result .compress environment _ hhook']
      simp [windowsStreamingSpec, streamingInvocationTrace, hresult, exhaustedStreamTrace]
    | success output scope =>
      have hhook := windows_intercept_two .compress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (windowsStreamingInterceptor (windowsStreamArtifact .compress)
            (windowsStreamEntry .compress environment))
          (windowsStep2 .compress environment).rip (windowsStep2 .compress environment) =
            some (windowsState3 .compress environment,
              some (Inject.inject (ConsoleEvent.out (bytesAsString output)))) := by
        simpa [streamResultEvent, windowsStreamEntry, windowsResultState, hresult] using hhook
      rw [windows_trace_continues_after_result .compress environment _ hhook']
      simp [windowsStreamingSpec, streamingInvocationTrace, hresult, successfulStreamTrace]
  | decompress =>
    cases hresult : decompressAll bufferedStreamingZlibCapability
      spike5AllocationScope environment.stdin with
    | rejected message scope =>
      have hhook := windows_intercept_two .decompress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (windowsStreamingInterceptor (windowsStreamArtifact .decompress)
            (windowsStreamEntry .decompress environment))
          (windowsStep2 .decompress environment).rip (windowsStep2 .decompress environment) =
            some (windowsStep2 .decompress environment,
              some (Inject.inject (ProcessEvent.exit 1))) := by
        simpa [streamResultEvent, windowsStreamEntry, windowsResultState, hresult] using hhook
      rw [windows_trace_stops_after_result .decompress environment _ hhook']
      simp [windowsStreamingSpec, streamingInvocationTrace, hresult, malformedStreamTrace]
    | resourceExhausted scope =>
      have hhook := windows_intercept_two .decompress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (windowsStreamingInterceptor (windowsStreamArtifact .decompress)
            (windowsStreamEntry .decompress environment))
          (windowsStep2 .decompress environment).rip (windowsStep2 .decompress environment) =
            some (windowsStep2 .decompress environment,
              some (Inject.inject (ProcessEvent.exit 2))) := by
        simpa [streamResultEvent, windowsStreamEntry, windowsResultState, hresult] using hhook
      rw [windows_trace_stops_after_result .decompress environment _ hhook']
      simp [windowsStreamingSpec, streamingInvocationTrace, hresult, exhaustedStreamTrace]
    | success output scope =>
      have hhook := windows_intercept_two .decompress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (windowsStreamingInterceptor (windowsStreamArtifact .decompress)
            (windowsStreamEntry .decompress environment))
          (windowsStep2 .decompress environment).rip (windowsStep2 .decompress environment) =
            some (windowsState3 .decompress environment,
              some (Inject.inject (ConsoleEvent.out (bytesAsString output)))) := by
        simpa [streamResultEvent, windowsStreamEntry, windowsResultState, hresult] using hhook
      rw [windows_trace_continues_after_result .decompress environment _ hhook']
      simp [windowsStreamingSpec, streamingInvocationTrace, hresult, successfulStreamTrace]

theorem windows_streaming_admissible (direction : CodecDirection) (environment : Environment) :
    Platform.admissible
      ((windowsStreamingCapabilities direction).realize (windowsStreamArtifact direction)
        (windowsStreamEntry direction environment))
      (windowsStreamArtifact direction)
      (Platform.load (P := WindowsX86_64 AnyEvent) (windowsStreamArtifact direction) environment) := by
  rw [windows_platform_admissible, windows_stream_realize, windows_stream_instructions_eq]
  unfold runProgramOutcomeWithLoops
  change (@runProgramOutcomeLoop AnyEvent
    (windowsStreamingInterceptor (windowsStreamArtifact direction)
      (windowsStreamEntry direction environment))
    (windowsIndexed direction environment) 50000
    (windowsStreamInitial direction environment) []).isAdmissible false
  rw [windows_outcome_prefix]
  cases direction with
  | compress =>
    cases hresult : compressAll bufferedStreamingZlibCapability
      spike5AllocationScope environment.stdin with
    | rejected error scope => nomatch error
    | resourceExhausted scope =>
      have hhook := windows_intercept_two .compress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (windowsStreamingInterceptor (windowsStreamArtifact .compress)
            (windowsStreamEntry .compress environment))
          (windowsStep2 .compress environment).rip (windowsStep2 .compress environment) =
            some (windowsStep2 .compress environment,
              some (Inject.inject (ProcessEvent.exit 2))) := by
        simpa [streamResultEvent, windowsStreamEntry, windowsResultState, hresult] using hhook
      rw [windows_outcome_stops_after_result .compress environment [] _ hhook']
      simp [NativeRunOutcome.isAdmissible]
    | success output scope =>
      have hhook := windows_intercept_two .compress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (windowsStreamingInterceptor (windowsStreamArtifact .compress)
            (windowsStreamEntry .compress environment))
          (windowsStep2 .compress environment).rip (windowsStep2 .compress environment) =
            some (windowsState3 .compress environment,
              some (Inject.inject (ConsoleEvent.out (bytesAsString output)))) := by
        simpa [streamResultEvent, windowsStreamEntry, windowsResultState, hresult] using hhook
      rw [windows_outcome_continues_after_result .compress environment [] _ hhook']
      simp [NativeRunOutcome.isAdmissible]
  | decompress =>
    cases hresult : decompressAll bufferedStreamingZlibCapability
      spike5AllocationScope environment.stdin with
    | rejected message scope =>
      have hhook := windows_intercept_two .decompress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (windowsStreamingInterceptor (windowsStreamArtifact .decompress)
            (windowsStreamEntry .decompress environment))
          (windowsStep2 .decompress environment).rip (windowsStep2 .decompress environment) =
            some (windowsStep2 .decompress environment,
              some (Inject.inject (ProcessEvent.exit 1))) := by
        simpa [streamResultEvent, windowsStreamEntry, windowsResultState, hresult] using hhook
      rw [windows_outcome_stops_after_result .decompress environment [] _ hhook']
      simp [NativeRunOutcome.isAdmissible]
    | resourceExhausted scope =>
      have hhook := windows_intercept_two .decompress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (windowsStreamingInterceptor (windowsStreamArtifact .decompress)
            (windowsStreamEntry .decompress environment))
          (windowsStep2 .decompress environment).rip (windowsStep2 .decompress environment) =
            some (windowsStep2 .decompress environment,
              some (Inject.inject (ProcessEvent.exit 2))) := by
        simpa [streamResultEvent, windowsStreamEntry, windowsResultState, hresult] using hhook
      rw [windows_outcome_stops_after_result .decompress environment [] _ hhook']
      simp [NativeRunOutcome.isAdmissible]
    | success output scope =>
      have hhook := windows_intercept_two .decompress environment
      have hhook' : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent
          (windowsStreamingInterceptor (windowsStreamArtifact .decompress)
            (windowsStreamEntry .decompress environment))
          (windowsStep2 .decompress environment).rip (windowsStep2 .decompress environment) =
            some (windowsState3 .decompress environment,
              some (Inject.inject (ConsoleEvent.out (bytesAsString output)))) := by
        simpa [streamResultEvent, windowsStreamEntry, windowsResultState, hresult] using hhook
      rw [windows_outcome_continues_after_result .decompress environment [] _ hhook']
      simp [NativeRunOutcome.isAdmissible]

def windowsStreamExports (direction : CodecDirection) :=
  VerifiedExportSet.empty Unit Unit (WindowsX86_64 AnyEvent) emptyBoundarySpec
    (emptyBoundarySemantics (WindowsX86_64 AnyEvent) X86_64MachineState) ()
    (by rfl) (by rfl) (by rfl)

theorem windows_stream_artifact_connected (direction : CodecDirection) :
    Platform.artifactConnected (P := WindowsX86_64 AnyEvent)
      (windowsStreamArtifact direction) := by
  rfl

def windowsStreamingArtifactCertificate (direction : CodecDirection) :
    ProgramArtifactCertificate (WindowsX86_64 AnyEvent) where
  artifact := windowsStreamArtifact direction
  exports := windowsStreamExports direction
  exportsArtifact := rfl
  artifactConnection := windows_stream_artifact_connected direction

def windowsStreamingProviderCertificate (direction : CodecDirection) :
    ProgramProviderCertificate (WindowsX86_64 AnyEvent)
      (windowsStreamingCapabilities direction) (windowsStreamArtifact direction) where
  importsCovered := by
    intro imported himport
    change imported ∈ (windowsStreamArtifact direction).executable.imports at himport
    rw [windows_stream_imports] at himport
    cases direction <;> simp [streamWindowsImports, streamImportNames] at himport
    all_goals
      rcases himport with rfl | rfl | rfl | rfl <;>
        simp [windowsStreamingCapabilities, windowsStreamingCapability, windowsStreamProviders,
          streamWindowsImports, streamImportNames, nativeProviderProtocol,
          Platform.providerProvides]
  providersLinked := by
    intro provider hprovider
    change provider ∈ windowsStreamProviders direction at hprovider
    cases direction <;>
      simp [windowsStreamProviders, streamWindowsImports, streamImportNames,
        nativeProviderProtocol] at hprovider
    all_goals rcases hprovider with rfl | rfl | rfl | rfl
    all_goals
      change _ ∧ _
      constructor
      · rw [windows_stream_imports]
        decide
      · simp only
        rw [windows_stream_layout]
        rw [windows_stream_iat_slots]
        rw [windows_stream_image_base]
        simp

def windowsStreamingEntryCertificate (direction : CodecDirection) :
    ProgramEntryCertificate (WindowsX86_64 AnyEvent)
      (windowsStreamingCapabilities direction) (windowsStreamArtifact direction) where
  entryContext := windowsStreamEntry direction
  entryEstablished := by intro environment; exact ⟨rfl, rfl⟩

@[simp] theorem windows_streaming_entry_context (direction : CodecDirection)
    (environment : Environment) :
    (windowsStreamingEntryCertificate direction).entryContext environment =
      windowsStreamEntry direction environment := by
  rfl

def windowsStreamingAdmissibilityCertificate (direction : CodecDirection) :
    ProgramAdmissibilityCertificate (WindowsX86_64 AnyEvent)
      (windowsStreamingCapabilities direction) (windowsStreamArtifact direction)
      (windowsStreamingEntryCertificate direction) where
  platformAdmissible := by
    intro environment
    rw [windows_streaming_entry_context]
    exact windows_streaming_admissible direction environment

def windowsStreamingBehaviorCertificate (direction : CodecDirection) :
    ProgramBehaviorCertificate (WindowsX86_64 AnyEvent)
      (windowsStreamingCapabilities direction) (windowsStreamArtifact direction)
      (windowsStreamingEntryCertificate direction) where
  spec := windowsStreamingSpec direction
  traceEquivalence := by
    intro environment
    rw [windows_streaming_entry_context]
    exact windows_streaming_trace_equivalence direction environment

def windowsStreamingVerifiedProgram (direction : CodecDirection) :
    VerifiedProgram (WindowsX86_64 AnyEvent) (windowsStreamingCapabilities direction) :=
  VerifiedProgram.compose
    (match direction with
      | .compress => "spike5_gzip_windows"
      | .decompress => "spike5_gunzip_windows")
    (windowsStreamingArtifactCertificate direction)
    (windowsStreamingProviderCertificate direction)
    (windowsStreamingEntryCertificate direction)
    (windowsStreamingAdmissibilityCertificate direction)
    (windowsStreamingBehaviorCertificate direction)

end Spikes.Spike5Gzip
