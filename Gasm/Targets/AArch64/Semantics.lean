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
import Gasm.Core.Arch
import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.Addressing
import Gasm.Targets.AArch64.MemoryCell
import Gasm.Targets.AArch64.Machine
import Gasm.Targets.AArch64.Instructions

namespace Gasm.Targets.AArch64

open Gasm.Core
open Gasm.Targets.AArch64.Instructions

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Pure single-step operational transition function for AArch64 machine instructions via typeclass dispatch. -/
def step (instr : AnyAArch64Instruction) (s : AArch64MachineState) : AArch64MachineState :=
  AArch64Instruction.step instr s

/- REF: docs/TARGETS/ARM64.md#machine-state -/
instance : TargetArch AArch64 where
  wordWidth    := 8
  MachineState := AArch64MachineState
  Instruction  := AnyAArch64Instruction
  stepPure pkg s := AArch64Instruction.step pkg s

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Open external call interceptor typeclass allowing target platform ABI hooks (e.g. Linux syscalls or bare-metal UART). -/
class ExternalCallInterceptor (Arch : Type) (Event : Type) where
  interceptCall : UInt64 → AArch64MachineState → Option (AArch64MachineState × Option Event)

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Pure single-step transition function for AArch64 machine instructions with dynamic interception. -/
def stepAArch64 {Event : Type} [interceptor : ExternalCallInterceptor AArch64 Event]
    (instr : AnyAArch64Instruction) (s : AArch64MachineState) : AArch64MachineState × Option Event :=
  let s' := step instr s
  match interceptor.interceptCall s'.pc s' with
  | some (s_hooked, evt) => (s_hooked, evt)
  | none => (s', none)

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Resolves the instruction positioned at targetPc dynamically from an instruction list starting at basePc. -/
def instructionAtPc (basePc : UInt64) (instructions : List AnyAArch64Instruction) (targetPc : UInt64) : Option AnyAArch64Instruction :=
  let rec loop (curPc : UInt64) : List AnyAArch64Instruction → Option AnyAArch64Instruction
    | [] => none
    | instr :: rest =>
      if curPc == targetPc then some instr
      else loop (curPc + 4) rest
  loop basePc instructions

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Computes byte offsets for each instruction in a sequence with fixed 4-byte stride. -/
def indexInstructions (basePc : UInt64) (instructions : List AnyAArch64Instruction) : List (UInt64 × AnyAArch64Instruction) :=
  let rec loop (curPc : UInt64) : List AnyAArch64Instruction → List (UInt64 × AnyAArch64Instruction)
    | [] => []
    | instr :: rest =>
      (curPc, instr) :: loop (curPc + 4) rest
  loop basePc instructions

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Resolves an instruction from pre-indexed address-instruction pairs without re-traversal. -/
def instructionAtPcIndexed : List (UInt64 × AnyAArch64Instruction) → UInt64 → Option AnyAArch64Instruction
  | [], _ => none
  | (pc, instr) :: rest, targetPc =>
    if pc == targetPc then some instr
    else instructionAtPcIndexed rest targetPc

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Proves that recursive indexing loop matches the linear instruction search loop. -/
theorem instructionAtPcIndexed_loop_eq (curPc : UInt64) (instructions : List AnyAArch64Instruction) (targetPc : UInt64) :
    instructionAtPcIndexed (indexInstructions.loop curPc instructions) targetPc =
    instructionAtPc.loop targetPc curPc instructions := by
  induction instructions generalizing curPc with
  | nil => rfl
  | cons i rest ih =>
    unfold indexInstructions.loop instructionAtPc.loop instructionAtPcIndexed
    split
    · rfl
    · exact ih (curPc + 4)

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Proves that pre-indexed instruction lookup is strictly equivalent to dynamic linear search. -/
theorem instructionAtPcIndexed_eq_instructionAtPc (basePc : UInt64) (instructions : List AnyAArch64Instruction) (targetPc : UInt64) :
    instructionAtPcIndexed (indexInstructions basePc instructions) targetPc =
    instructionAtPc basePc instructions targetPc := by
  exact instructionAtPcIndexed_loop_eq basePc instructions targetPc

theorem instructionAtPcIndexed_some_mem_snd
    {indexed : List (UInt64 × AnyAArch64Instruction)} {pc : UInt64}
    {instruction : AnyAArch64Instruction}
    (lookup : instructionAtPcIndexed indexed pc = some instruction) :
    instruction ∈ indexed.map Prod.snd := by
  induction indexed with
  | nil => simp [instructionAtPcIndexed] at lookup
  | cons entry rest ih =>
      rcases entry with ⟨entryPc, candidate⟩
      simp only [instructionAtPcIndexed] at lookup
      by_cases same : entryPc == pc
      · simp [same] at lookup
        subst candidate
        simp
      · simp [same] at lookup
        exact List.mem_cons_of_mem _ (ih lookup)

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Executes an AArch64 instruction sequence supporting branches and loops with fuel-based termination. -/
def runProgramWithLoops (basePc : UInt64) (instructions : List AnyAArch64Instruction) (fuel : Nat) (s : AArch64MachineState) : AArch64MachineState :=
  let indexed := indexInstructions basePc instructions
  let rec loop (fuel : Nat) (s : AArch64MachineState) : AArch64MachineState :=
    match fuel with
    | 0 => s
    | fuel + 1 =>
      match instructionAtPcIndexed indexed s.pc with
      | none => s
      | some instr =>
        let s' := step instr s
        if s'.isHalted then s'
        else loop fuel s'
  loop fuel s

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Initializes a clean AArch64 machine state conforming to AAPCS64. -/
def initMachineState (entryPc : UInt64) (args : List UInt64 := []) (stackTop : UInt64 := 0x7FFFFFFF0000) : AArch64MachineState :=
  let argGprs : List Reg64 := aapcs64ArgRegs
  let rec setArgs (remGprs : List Reg64) (remArgs : List UInt64) (s : AArch64MachineState) : AArch64MachineState :=
    match remGprs, remArgs with
    | g :: grest, a :: arest => setArgs grest arest (s.setReg64 g a)
    | _, _ => s
  let s0 : AArch64MachineState := {
    pc := entryPc,
    gprs := fun _ => 0,
    sp := stackTop,
    nzcv := default,
    memory := default
  }
  setArgs argGprs args s0

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Named recursive core of the AArch64 trace evaluator. Public induction uses the production
    transition rather than a proof-only replay. -/
def runProgramTraceLoop {Event : Type} [interceptor : ExternalCallInterceptor AArch64 Event]
    (indexed : List (UInt64 × AnyAArch64Instruction)) (fuel : Nat)
    (state : AArch64MachineState) : List Event :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match instructionAtPcIndexed indexed state.pc with
    | none => []
    | some instr =>
      let stepped := AArch64Instruction.step instr state
      match interceptor.interceptCall stepped.pc stepped with
      | some (hooked, some event) =>
        if hooked.terminated || hooked.fault.isSome then [event]
        else event :: runProgramTraceLoop indexed fuel hooked
      | some (hooked, none) =>
        if hooked.terminated || hooked.fault.isSome then []
        else runProgramTraceLoop indexed fuel hooked
      | none =>
        if stepped.terminated || stepped.fault.isSome then []
        else runProgramTraceLoop indexed fuel stepped

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Trace evaluator executing an AArch64 program with dynamic branches, loops, and external API interception. -/
def runProgramTraceWithLoops {Event : Type} [ExternalCallInterceptor AArch64 Event]
    (basePc : UInt64) (instructions : List AnyAArch64Instruction) (fuel : Nat)
    (state : AArch64MachineState) : List Event :=
  runProgramTraceLoop (indexInstructions basePc instructions) fuel state

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Trace evaluator executing a list of lowered AArch64 instructions with dynamic control flow. -/
def runAArch64Trace {Event : Type} [ExternalCallInterceptor AArch64 Event]
    (instructions : List AnyAArch64Instruction) (s : AArch64MachineState) (fuel : Nat := 50000) : List Event :=
  runProgramTraceWithLoops s.pc instructions fuel s

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Fault- and fuel-honest AArch64 execution outcome used by platform admissibility. -/
inductive AArch64RunOutcome (Event : Type) where
  | completed (state : AArch64MachineState) (events : List Event)
  | faulted (state : AArch64MachineState) (events : List Event)
  | fuelExhausted (state : AArch64MachineState) (events : List Event)

def runAArch64OutcomeLoop {Event : Type}
    [interceptor : ExternalCallInterceptor AArch64 Event]
    (indexed : List (UInt64 × AnyAArch64Instruction)) (fuel : Nat)
    (state : AArch64MachineState) (eventsRev : List Event) : AArch64RunOutcome Event :=
  match fuel with
  | 0 => .fuelExhausted state eventsRev.reverse
  | fuel + 1 =>
    match instructionAtPcIndexed indexed state.pc with
    | none => .completed state eventsRev.reverse
    | some instr =>
      let stepped := AArch64Instruction.step instr state
      match interceptor.interceptCall stepped.pc stepped with
      | some (hooked, event) =>
        let eventsRev' := match event with | some emitted => emitted :: eventsRev | none => eventsRev
        if hooked.fault.isSome then .faulted hooked eventsRev'.reverse
        else if hooked.terminated then .completed hooked eventsRev'.reverse
        else runAArch64OutcomeLoop indexed fuel hooked eventsRev'
      | none =>
        if stepped.fault.isSome then .faulted stepped eventsRev.reverse
        else if stepped.terminated then .completed stepped eventsRev.reverse
        else runAArch64OutcomeLoop indexed fuel stepped eventsRev

def runAArch64Outcome {Event : Type} [ExternalCallInterceptor AArch64 Event]
    (basePc : UInt64) (instructions : List AnyAArch64Instruction) (fuel : Nat)
    (initial : AArch64MachineState) : AArch64RunOutcome Event :=
  runAArch64OutcomeLoop (indexInstructions basePc instructions) fuel initial []

namespace AArch64RunOutcome

def events : AArch64RunOutcome Event → List Event
  | .completed _ emitted | .faulted _ emitted | .fuelExhausted _ emitted => emitted

end AArch64RunOutcome

def AArch64RunOutcome.isAdmissible : AArch64RunOutcome Event → Prop
  | .completed _ _ => True
  | .faulted _ _ | .fuelExhausted _ _ => False

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The explicit outcome evaluator retains exactly the production trace evaluator's observations. -/
theorem runAArch64OutcomeLoop_events {Event : Type}
    [interceptor : ExternalCallInterceptor AArch64 Event]
    (indexed : List (UInt64 × AnyAArch64Instruction)) (fuel : Nat)
    (state : AArch64MachineState) (eventsRev : List Event) :
    (runAArch64OutcomeLoop indexed fuel state eventsRev).events =
      eventsRev.reverse ++ runProgramTraceLoop indexed fuel state := by
  induction fuel generalizing state eventsRev with
  | zero => simp [runAArch64OutcomeLoop, runProgramTraceLoop, AArch64RunOutcome.events]
  | succ fuel ih =>
      cases hlookup : instructionAtPcIndexed indexed state.pc with
      | none =>
          simp [runAArch64OutcomeLoop, runProgramTraceLoop, hlookup,
            AArch64RunOutcome.events]
      | some instruction =>
          let stepped := AArch64Instruction.step instruction state
          cases hintercept : interceptor.interceptCall stepped.pc stepped with
          | none =>
              by_cases hfault : stepped.fault.isSome
              · simp [runAArch64OutcomeLoop, runProgramTraceLoop, hlookup, hintercept,
                  stepped, hfault, AArch64RunOutcome.events]
              · by_cases hterminated : stepped.terminated
                · simp [runAArch64OutcomeLoop, runProgramTraceLoop, hlookup, hintercept,
                    stepped, hfault, hterminated, AArch64RunOutcome.events]
                · simp only [runAArch64OutcomeLoop, runProgramTraceLoop, hlookup, hintercept,
                    stepped, hfault, hterminated, Bool.false_or, ↓reduceIte]
                  exact ih stepped eventsRev
          | some result =>
              rcases result with ⟨hooked, emitted⟩
              cases emitted with
              | none =>
                  by_cases hfault : hooked.fault.isSome
                  · simp [runAArch64OutcomeLoop, runProgramTraceLoop, hlookup, hintercept,
                      stepped, hfault, AArch64RunOutcome.events]
                  · by_cases hterminated : hooked.terminated
                    · simp [runAArch64OutcomeLoop, runProgramTraceLoop, hlookup, hintercept,
                        stepped, hfault, hterminated, AArch64RunOutcome.events]
                    · simp only [runAArch64OutcomeLoop, runProgramTraceLoop, hlookup, hintercept,
                        stepped, hfault, hterminated, Bool.false_or, ↓reduceIte]
                      exact ih hooked eventsRev
              | some event =>
                  by_cases hfault : hooked.fault.isSome
                  · simp [runAArch64OutcomeLoop, runProgramTraceLoop, hlookup, hintercept,
                      stepped, hfault, AArch64RunOutcome.events, List.reverse_cons,
                      List.append_assoc]
                  · by_cases hterminated : hooked.terminated
                    · simp [runAArch64OutcomeLoop, runProgramTraceLoop, hlookup, hintercept,
                        stepped, hfault, hterminated, AArch64RunOutcome.events,
                        List.reverse_cons, List.append_assoc]
                    · simp only [runAArch64OutcomeLoop, runProgramTraceLoop, hlookup, hintercept,
                        stepped, hfault, hterminated, Bool.false_or, ↓reduceIte]
                      simpa [List.reverse_cons, List.append_assoc] using ih hooked (event :: eventsRev)

theorem runAArch64Outcome_events {Event : Type}
    [ExternalCallInterceptor AArch64 Event]
    (basePc : UInt64) (instructions : List AnyAArch64Instruction) (fuel : Nat)
    (state : AArch64MachineState) :
    (runAArch64Outcome (Event := Event) basePc instructions fuel state).events =
      runProgramTraceWithLoops (Event := Event) basePc instructions fuel state := by
  simpa [runAArch64Outcome, runProgramTraceWithLoops] using
    runAArch64OutcomeLoop_events (Event := Event)
      (indexInstructions basePc instructions) fuel state []

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
def AArch64MachineState.withExternalInputs (state : AArch64MachineState)
    (stdin : ByteArray) (requests : List ByteArray) : AArch64MachineState :=
  { state with stdinBuffer := stdin, incomingRequests := requests }

@[simp] theorem AArch64MachineState.withExternalInputs_pc
    (state : AArch64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).pc = state.pc := rfl

@[simp] theorem AArch64MachineState.withExternalInputs_fault
    (state : AArch64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).fault = state.fault := rfl

@[simp] theorem AArch64MachineState.withExternalInputs_terminated
    (state : AArch64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).terminated = state.terminated := rfl

@[simp] theorem AArch64MachineState.withExternalInputs_gprs
    (state : AArch64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).gprs = state.gprs := rfl

@[simp] theorem AArch64MachineState.withExternalInputs_sp
    (state : AArch64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).sp = state.sp := rfl

@[simp] theorem AArch64MachineState.withExternalInputs_nzcv
    (state : AArch64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).nzcv = state.nzcv := rfl

@[simp] theorem AArch64MachineState.withExternalInputs_memory
    (state : AArch64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).memory = state.memory := rfl

@[simp] theorem AArch64MachineState.withExternalInputs_exitCode
    (state : AArch64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).exitCode = state.exitCode := rfl

@[simp] theorem AArch64MachineState.withExternalInputs_syscallReturnPc
    (state : AArch64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).syscallReturnPc = state.syscallReturnPc := rfl

@[simp] theorem AArch64MachineState.withExternalInputs_getReg64
    (state : AArch64MachineState) (stdin : ByteArray) (requests : List ByteArray)
    (reg : Reg64) :
    (state.withExternalInputs stdin requests).getReg64 reg = state.getReg64 reg := rfl

@[simp] theorem AArch64MachineState.withExternalInputs_stdinBuffer
    (state : AArch64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).stdinBuffer = stdin := rfl

@[simp] theorem AArch64MachineState.withExternalInputs_incomingRequests
    (state : AArch64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).incomingRequests = requests := rfl

/-- The open AArch64 instruction wrapper enforces this architectural frame for every package. -/
def InstructionPreservesExternalInputFrame (instruction : AnyAArch64Instruction) : Prop :=
  ∀ state stdin requests,
    AArch64Instruction.step instruction (state.withExternalInputs stdin requests) =
      (AArch64Instruction.step instruction state).withExternalInputs stdin requests

theorem instruction_preserves_external_input_frame (instruction : AnyAArch64Instruction) :
    InstructionPreservesExternalInputFrame instruction := by
  intro state stdin requests
  cases instruction
  rfl

/-- Congruence is required only for the host boundaries selected by the artifact certificate. -/
def InterceptorPreservesExternalInputFrame {Event : Type}
    [interceptor : ExternalCallInterceptor AArch64 Event]
    (selected : UInt64 → AArch64MachineState → Bool) : Prop :=
  ∀ address state stdin requests, selected address state = true →
    interceptor.interceptCall address (state.withExternalInputs stdin requests) =
      (interceptor.interceptCall address state).map
        (fun result => (result.1.withExternalInputs stdin requests, result.2))

def AArch64RunOutcome.withExternalInputs (stdin : ByteArray) (requests : List ByteArray) :
    AArch64RunOutcome Event → AArch64RunOutcome Event
  | .completed state emitted => .completed (state.withExternalInputs stdin requests) emitted
  | .faulted state emitted => .faulted (state.withExternalInputs stdin requests) emitted
  | .fuelExhausted state emitted =>
      .fuelExhausted (state.withExternalInputs stdin requests) emitted

@[simp] theorem AArch64RunOutcome.withExternalInputs_events
    (outcome : AArch64RunOutcome Event) (stdin : ByteArray) (requests : List ByteArray) :
    (outcome.withExternalInputs stdin requests).events = outcome.events := by
  cases outcome <;> rfl

@[simp] theorem AArch64RunOutcome.withExternalInputs_isAdmissible
    (outcome : AArch64RunOutcome Event) (stdin : ByteArray) (requests : List ByteArray) :
    (outcome.withExternalInputs stdin requests).isAdmissible ↔ outcome.isAdmissible := by
  cases outcome <;> rfl

/-- Executable selected-host-call termination certificate for one exact indexed artifact. -/
def selectedExecutionTerminates {Event : Type}
    [interceptor : ExternalCallInterceptor AArch64 Event]
    (selected : UInt64 → AArch64MachineState → Bool)
    (indexed : List (UInt64 × AnyAArch64Instruction)) (fuel : Nat)
    (state : AArch64MachineState) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    match instructionAtPcIndexed indexed state.pc with
    | none => true
    | some instruction =>
      let stepped := AArch64Instruction.step instruction state
      if !selected stepped.pc stepped then false
      else
        match interceptor.interceptCall stepped.pc stepped with
        | some (hooked, _) =>
          if hooked.fault.isSome then false
          else if hooked.terminated then true
          else selectedExecutionTerminates (Event := Event) selected indexed fuel hooked
        | none =>
          if stepped.fault.isSome then false
          else if stepped.terminated then true
          else selectedExecutionTerminates (Event := Event) selected indexed fuel stepped

structure SelectedTerminationCertificate {Event : Type}
    [ExternalCallInterceptor AArch64 Event]
    (selected : UInt64 → AArch64MachineState → Bool)
    (basePc : UInt64) (instructions : List AnyAArch64Instruction)
    (initial : AArch64MachineState) where
  fuel : Nat
  verifies : selectedExecutionTerminates (Event := Event) selected
    (indexInstructions basePc instructions) fuel initial = true

theorem selectedExecutionTerminates_isAdmissible {Event : Type}
    [interceptor : ExternalCallInterceptor AArch64 Event]
    (selected : UInt64 → AArch64MachineState → Bool)
    (indexed : List (UInt64 × AnyAArch64Instruction)) (fuel : Nat)
    (state : AArch64MachineState) (eventsRev : List Event)
    (certificate : selectedExecutionTerminates (Event := Event) selected indexed fuel state = true) :
    (runAArch64OutcomeLoop indexed fuel state eventsRev).isAdmissible := by
  induction fuel generalizing state eventsRev with
  | zero => simp [selectedExecutionTerminates] at certificate
  | succ fuel ih =>
      cases hlookup : instructionAtPcIndexed indexed state.pc with
      | none => simp [runAArch64OutcomeLoop, hlookup, AArch64RunOutcome.isAdmissible]
      | some instruction =>
          let stepped := AArch64Instruction.step instruction state
          by_cases hselected : selected stepped.pc stepped = true
          · cases hintercept : interceptor.interceptCall stepped.pc stepped with
            | none =>
                cases hfault : stepped.fault with
                | some fault =>
                    simp [selectedExecutionTerminates, hlookup, stepped, hselected,
                      hintercept, hfault] at certificate
                | none =>
                  by_cases hterminated : stepped.terminated
                  · simp [runAArch64OutcomeLoop, hlookup, stepped, hintercept, hfault,
                      hterminated, AArch64RunOutcome.isAdmissible]
                  · have hrecursive : selectedExecutionTerminates (Event := Event)
                        selected indexed fuel stepped = true := by
                      simpa [selectedExecutionTerminates, hlookup, stepped, hselected,
                        hintercept, hfault, hterminated] using certificate
                    simp [runAArch64OutcomeLoop, hlookup, stepped, hintercept, hfault,
                      hterminated]
                    exact ih _ _ hrecursive
            | some result =>
                rcases result with ⟨hooked, emitted⟩
                cases hfault : hooked.fault with
                | some fault =>
                    simp [selectedExecutionTerminates, hlookup, stepped, hselected,
                      hintercept, hfault] at certificate
                | none =>
                  by_cases hterminated : hooked.terminated
                  · simp [runAArch64OutcomeLoop, hlookup, stepped, hintercept, hfault,
                      hterminated, AArch64RunOutcome.isAdmissible]
                  · have hrecursive : selectedExecutionTerminates (Event := Event)
                        selected indexed fuel hooked = true := by
                      simpa [selectedExecutionTerminates, hlookup, stepped, hselected,
                        hintercept, hfault, hterminated] using certificate
                    simp [runAArch64OutcomeLoop, hlookup, stepped, hintercept, hfault,
                      hterminated]
                    exact ih _ _ hrecursive
          · have hselectedFalse : selected stepped.pc stepped = false := by
              cases hvalue : selected stepped.pc stepped with
              | false => rfl
              | true => exact False.elim (hselected hvalue)
            simp [selectedExecutionTerminates, hlookup, stepped, hselectedFalse] at certificate

private theorem outcomeTransition_external_input_frame {Event : Type}
    [interceptor : ExternalCallInterceptor AArch64 Event]
    (selected : UInt64 → AArch64MachineState → Bool)
    (instruction : AnyAArch64Instruction) (state : AArch64MachineState)
    (hinstruction : InstructionPreservesExternalInputFrame instruction)
    (hinterceptor : InterceptorPreservesExternalInputFrame (Event := Event) selected)
    (hselected : selected (AArch64Instruction.step instruction state).pc
      (AArch64Instruction.step instruction state) = true)
    (stdin : ByteArray) (requests : List ByteArray) :
    let stepped := AArch64Instruction.step instruction state
    (AArch64Instruction.step instruction (state.withExternalInputs stdin requests),
      interceptor.interceptCall
        (AArch64Instruction.step instruction (state.withExternalInputs stdin requests)).pc
        (AArch64Instruction.step instruction (state.withExternalInputs stdin requests))) =
    (stepped.withExternalInputs stdin requests,
      (interceptor.interceptCall stepped.pc stepped).map
        (fun result => (result.1.withExternalInputs stdin requests, result.2))) := by
  dsimp only
  rw [hinstruction state stdin requests]
  simp only [AArch64MachineState.withExternalInputs_pc]
  rw [hinterceptor _ _ stdin requests hselected]

theorem runAArch64OutcomeLoop_external_input_frame {Event : Type}
    [interceptor : ExternalCallInterceptor AArch64 Event]
    (selected : UInt64 → AArch64MachineState → Bool)
    (indexed : List (UInt64 × AnyAArch64Instruction))
    (hinstructions : ∀ instruction, instruction ∈ indexed.map Prod.snd →
      InstructionPreservesExternalInputFrame instruction)
    (hinterceptor : InterceptorPreservesExternalInputFrame (Event := Event) selected)
    (fuel : Nat) (state : AArch64MachineState) (eventsRev : List Event)
    (certificate : selectedExecutionTerminates (Event := Event) selected indexed fuel state = true)
    (stdin : ByteArray) (requests : List ByteArray) :
    runAArch64OutcomeLoop indexed fuel (state.withExternalInputs stdin requests) eventsRev =
      (runAArch64OutcomeLoop indexed fuel state eventsRev).withExternalInputs stdin requests := by
  induction fuel generalizing state eventsRev with
  | zero => simp [selectedExecutionTerminates] at certificate
  | succ fuel ih =>
      cases hlookup : instructionAtPcIndexed indexed state.pc with
      | none => simp [runAArch64OutcomeLoop, hlookup, AArch64RunOutcome.withExternalInputs]
      | some instruction =>
          have hmember : instruction ∈ indexed.map Prod.snd :=
            instructionAtPcIndexed_some_mem_snd hlookup
          have hinstruction := hinstructions instruction hmember
          let stepped := AArch64Instruction.step instruction state
          by_cases hselected : selected stepped.pc stepped = true
          ·
            simp only [runAArch64OutcomeLoop, AArch64MachineState.withExternalInputs_pc, hlookup]
            rw [hinstruction state stdin requests]
            simp only [AArch64MachineState.withExternalInputs_pc]
            rw [hinterceptor _ _ stdin requests hselected]
            cases hintercept : interceptor.interceptCall stepped.pc stepped with
            | none =>
                simp only [Option.map_none]
                cases hfault : stepped.fault with
                | some fault =>
                    simp [stepped, hfault, AArch64MachineState.withExternalInputs_fault,
                      AArch64RunOutcome.withExternalInputs]
                | none =>
                  by_cases hterminated : stepped.terminated
                  · simp [stepped, hfault, hterminated, AArch64RunOutcome.withExternalInputs]
                  · have hrecursive : selectedExecutionTerminates (Event := Event)
                        selected indexed fuel stepped = true := by
                      simpa [selectedExecutionTerminates, hlookup, stepped, hselected,
                        hintercept, hfault, hterminated] using certificate
                    simp only [stepped, AArch64MachineState.withExternalInputs_fault,
                      AArch64MachineState.withExternalInputs_terminated, hfault, hterminated,
                      Bool.false_or, ↓reduceIte]
                    exact ih _ _ hrecursive
            | some result =>
                rcases result with ⟨hooked, emitted⟩
                simp only [Option.map_some]
                cases hfault : hooked.fault with
                | some fault =>
                    simp [hfault, AArch64MachineState.withExternalInputs_fault,
                      AArch64RunOutcome.withExternalInputs]
                | none =>
                  by_cases hterminated : hooked.terminated
                  · simp [hfault, hterminated, AArch64RunOutcome.withExternalInputs]
                  · have hrecursive : selectedExecutionTerminates (Event := Event)
                        selected indexed fuel hooked = true := by
                      simpa [selectedExecutionTerminates, hlookup, stepped, hselected,
                        hintercept, hfault, hterminated] using certificate
                    simp only [AArch64MachineState.withExternalInputs_fault,
                      AArch64MachineState.withExternalInputs_terminated, hfault, hterminated,
                      Bool.false_or, ↓reduceIte]
                    cases emitted with
                    | none => exact ih _ _ hrecursive
                    | some event => exact ih _ _ hrecursive
          · have hselectedFalse : selected stepped.pc stepped = false := by
              cases hvalue : selected stepped.pc stepped with
              | false => rfl
              | true => exact False.elim (hselected hvalue)
            simp [selectedExecutionTerminates, hlookup, stepped, hselectedFalse] at certificate

theorem SelectedTerminationCertificate.isAdmissible {Event : Type}
    [ExternalCallInterceptor AArch64 Event]
    {selected : UInt64 → AArch64MachineState → Bool}
    {basePc : UInt64} {instructions : List AnyAArch64Instruction}
    {initial : AArch64MachineState}
    (certificate : SelectedTerminationCertificate (Event := Event)
      selected basePc instructions initial) :
    (runAArch64Outcome (Event := Event) basePc instructions certificate.fuel initial).isAdmissible :=
  selectedExecutionTerminates_isAdmissible selected _ certificate.fuel initial []
    certificate.verifies

theorem SelectedTerminationCertificate.externalInputFrame {Event : Type}
    [ExternalCallInterceptor AArch64 Event]
    {selected : UInt64 → AArch64MachineState → Bool}
    {basePc : UInt64} {instructions : List AnyAArch64Instruction}
    {initial : AArch64MachineState}
    (certificate : SelectedTerminationCertificate (Event := Event)
      selected basePc instructions initial)
    (hinterceptor : InterceptorPreservesExternalInputFrame (Event := Event) selected)
    (stdin : ByteArray) (requests : List ByteArray) :
    runAArch64Outcome (Event := Event) basePc instructions certificate.fuel
        (initial.withExternalInputs stdin requests) =
      AArch64RunOutcome.withExternalInputs stdin requests
        (runAArch64Outcome (Event := Event) basePc instructions certificate.fuel initial) := by
  exact runAArch64OutcomeLoop_external_input_frame selected _
    (fun instruction _ => instruction_preserves_external_input_frame instruction)
    hinterceptor certificate.fuel initial [] certificate.verifies stdin requests

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Invokes an AArch64 subroutine with arguments and returns the 64-bit return value in X0. -/
def callSubroutine (instructions : List AnyAArch64Instruction) (args : List UInt64) (fuel : Nat := 1000) (entryPc : UInt64 := 0x400000) : UInt64 :=
  let s0 := initMachineState entryPc args
  let finalState := runProgramWithLoops entryPc instructions fuel s0
  finalState.getReg64 .x0

end Gasm.Targets.AArch64
