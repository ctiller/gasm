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
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base

namespace Gasm.Targets.X86_64

open Gasm.Core
open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Open external call interceptor typeclass allowing target platform ABI hooks (e.g. Win32 API). -/
class ExternalCallInterceptor (Arch : Type) (Event : Type) where
  interceptCall : Address → X86_64MachineState → Option (X86_64MachineState × Option Event)

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Pure single-step transition function for x86-64 machine instructions with dynamic interception. -/
def stepX86_64 {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (instr : X86_64Instr) (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let s' := X86_64Instruction.step instr s
  match interceptor.interceptCall s'.rip s' with
  | some (s_hooked, evt) => (s_hooked, evt)
  | none => (s', none)

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Resolves the instruction positioned at targetRip dynamically from an instruction list starting at baseRip. -/
def instructionAtRip (baseRip : UInt64) (instructions : List X86_64Instr) (targetRip : UInt64) : Option X86_64Instr :=
  let rec loop (curRip : UInt64) : List X86_64Instr → Option X86_64Instr
    | [] => none
    | instr :: rest =>
      if curRip == targetRip then some instr
      else
        let sz := (X86_64Instruction.encode instr).size
        loop (curRip + sz.toUInt64) rest
  loop baseRip instructions

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Computes byte offsets for each instruction in a sequence, eliminating O(M*N) re-encoding in the simulator. -/
def indexInstructions (baseRip : UInt64) (instructions : List X86_64Instr) : List (UInt64 × X86_64Instr) :=
  let rec loop (curRip : UInt64) : List X86_64Instr → List (UInt64 × X86_64Instr)
    | [] => []
    | instr :: rest =>
      let sz := (X86_64Instruction.encode instr).size
      (curRip, instr) :: loop (curRip + sz.toUInt64) rest
  loop baseRip instructions

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Resolves an instruction from pre-indexed address-instruction pairs without re-encoding. -/
def instructionAtRipIndexed : List (UInt64 × X86_64Instr) → UInt64 → Option X86_64Instr
  | [], _ => none
  | (rip, instr) :: rest, targetRip =>
    if rip == targetRip then some instr
    else instructionAtRipIndexed rest targetRip

/-- A successful indexed lookup returns an instruction stored in the index. -/
theorem instructionAtRipIndexed_some_mem_snd
    {indexed : List (UInt64 × X86_64Instr)} {targetRip : UInt64} {instr : X86_64Instr}
    (h : instructionAtRipIndexed indexed targetRip = some instr) :
    instr ∈ indexed.map Prod.snd := by
  induction indexed with
  | nil => simp [instructionAtRipIndexed] at h
  | cons head rest ih =>
    rcases head with ⟨rip, candidate⟩
    simp only [instructionAtRipIndexed] at h
    split at h
    · cases h
      simp
    · simp [ih h]

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Proves that recursive indexing loop matches the linear instruction search loop. -/
theorem instructionAtRipIndexed_loop_eq (curRip : UInt64) (instructions : List X86_64Instr) (targetRip : UInt64) :
    instructionAtRipIndexed (indexInstructions.loop curRip instructions) targetRip =
    instructionAtRip.loop targetRip curRip instructions := by
  induction instructions generalizing curRip with
  | nil => rfl
  | cons i rest ih =>
    unfold indexInstructions.loop instructionAtRip.loop instructionAtRipIndexed
    split
    · rfl
    · exact ih (curRip + (X86_64Instruction.encode i).size.toUInt64)

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Proves that pre-indexed instruction lookup is strictly equivalent to dynamic linear search for all programs and addresses. -/
theorem instructionAtRipIndexed_eq_instructionAtRip (baseRip : UInt64) (instructions : List X86_64Instr) (targetRip : UInt64) :
    instructionAtRipIndexed (indexInstructions baseRip instructions) targetRip =
    instructionAtRip baseRip instructions targetRip := by
  exact instructionAtRipIndexed_loop_eq baseRip instructions targetRip

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Named recursive core of the historical trace projection.  Keeping the indexed table explicit
    lets the explicit-outcome evaluator prove that it is a conservative strengthening of this
    exact production behavior. -/
def runProgramTraceLoop {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (indexed : List (UInt64 × X86_64Instr)) (fuel : Nat) (s : X86_64MachineState) : List Event :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match instructionAtRipIndexed indexed s.rip with
    | none => []
    | some instr =>
      let s' := X86_64Instruction.step instr s
      match interceptor.interceptCall s'.rip s' with
      | some (s_hooked, some evt) =>
        if s_hooked.faulted then [evt]
        else evt :: runProgramTraceLoop indexed fuel s_hooked
      | some (s_hooked, none) =>
        if s_hooked.faulted then []
        else runProgramTraceLoop indexed fuel s_hooked
      | none =>
        if s'.faulted then []
        else runProgramTraceLoop indexed fuel s'

/-- Trace evaluator executing an x86-64 program with dynamic branches, loops, and external API interception. -/
def runProgramTraceWithLoops {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (baseRip : UInt64) (instructions : List X86_64Instr) (fuel : Nat) (s : X86_64MachineState) : List Event :=
  runProgramTraceLoop (indexInstructions baseRip instructions) fuel s

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Trace evaluator executing a list of lowered x86-64 instructions with dynamic control flow. -/
def runAsmTrace {Event : Type} [ExternalCallInterceptor X86_64 Event]
    (instructions : List X86_64Instr) (s : X86_64MachineState) (fuel : Nat := 50000) : List Event :=
  runProgramTraceWithLoops s.rip instructions fuel s

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- A non-fault terminal cause selected by the platform profile. -/
inductive NativeTerminalCause where
  | processExit (code : UInt32)
  | architecturalHalt
  deriving DecidableEq, Repr, Inhabited

/-- The reason a fuel-bounded native execution stopped.  A host process exit and an architectural
    HLT have distinct typed causes.  `fuelExhausted` is evaluator evidence, never an admissible
    emitted-program behavior unless a future platform profile supplies artifact-enforced budget
    evidence and models that resource outcome separately. -/
inductive NativeRunOutcome (Event : Type) where
  | returned (state : X86_64MachineState) (events : List Event)
  | terminated (cause : NativeTerminalCause) (state : X86_64MachineState) (events : List Event)
  | faulted (state : X86_64MachineState) (events : List Event)
  | fuelExhausted (state : X86_64MachineState) (events : List Event)

namespace NativeRunOutcome

/-- Events are projected only after the stop reason has been retained. -/
def events : NativeRunOutcome Event → List Event
  | .returned _ emitted | .terminated _ _ emitted | .faulted _ emitted |
      .fuelExhausted _ emitted => emitted

/-- The final physical state is retained in the full outcome.  Resource/recovery contracts must
    be stated over this outcome before callers project it to `NativeObservable`. -/
def finalState : NativeRunOutcome Event → X86_64MachineState
  | .returned state _ | .terminated _ state _ | .faulted state _ |
      .fuelExhausted state _ => state

/-- A resource/recovery postcondition for a typed process exit.  Unlike `NativeObservable`, this
    predicate retains the final physical state, so an artifact can prove cleanup, reclamation, or
    request-local recovery before publishing the exit observation. -/
def processExitPostcondition (code : UInt32) (post : X86_64MachineState → Prop) :
    NativeRunOutcome Event → Prop
  | .terminated (.processExit observed) state _ => observed = code ∧ post state
  | _ => False

/-- Profile-sensitive native machine safety.  Process exits are always typed terminal outcomes;
    `allowArchitecturalHalt` governs only the x86 HLT instruction.  Evaluator fuel exhaustion is
    never admissible emission behavior: it records an insufficient proof bound, not an artifact
    resource failure.  Real resource recovery contracts inspect `finalState` on the full outcome
    before any observation projection. -/
def isAdmissible (allowArchitecturalHalt : Bool) : NativeRunOutcome Event → Prop
  | .returned _ _ => True
  | .terminated (.processExit _) _ _ => True
  | .terminated .architecturalHalt _ _ => allowArchitecturalHalt = true
  | .faulted _ _ => False
  | .fuelExhausted _ _ => False

end NativeRunOutcome

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The caller-visible native outcome.  It erases machine-internal final state only after
    retaining every stop classification and its event prefix; in particular, a partial trace from
    fuel exhaustion or a fault cannot be confused with a successful return. -/
inductive NativeObservable (Event : Type) where
  | returned (events : List Event) : NativeObservable Event
  | processExited (code : UInt32) (events : List Event) : NativeObservable Event
  | architecturalHalted (events : List Event) : NativeObservable Event
  | faulted (events : List Event) : NativeObservable Event
  | fuelExhausted (events : List Event) : NativeObservable Event
  deriving DecidableEq, BEq

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Externally observes an explicit native run without projecting away why it stopped. -/
def NativeRunOutcome.observable : NativeRunOutcome Event → NativeObservable Event
  | .returned _ emitted => .returned emitted
  | .terminated (.processExit code) _ emitted => .processExited code emitted
  | .terminated .architecturalHalt _ emitted => .architecturalHalted emitted
  | .faulted _ emitted => .faulted emitted
  | .fuelExhausted _ emitted => .fuelExhausted emitted

/-- The event payload remains available for diagnostics, but its stop classification is never
    discarded by this projection. -/
def NativeObservable.events : NativeObservable Event → List Event
  | .returned emitted | .processExited _ emitted | .architecturalHalted emitted |
      .faulted emitted | .fuelExhausted emitted => emitted

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- One production native transition, including selected host interception and event accumulation. -/
def nativeOutcomeTransition {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (instr : X86_64Instr) (state : X86_64MachineState) (eventsRev : List Event) :
    X86_64MachineState × List Event :=
  let stepped := X86_64Instruction.step instr state
  match interceptor.interceptCall stepped.rip stepped with
  | some (hooked, event) =>
    (hooked, event.elim eventsRev (fun emitted => emitted :: eventsRev))
  | none => (stepped, eventsRev)

/-- Recursive core of the indexed native outcome evaluator.  Keeping this as a named definition
    makes induction over an execution certificate use the exact production transition rather than
    a parallel proof-only interpreter. -/
def runProgramOutcomeLoop {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (indexed : List (UInt64 × X86_64Instr)) (fuel : Nat)
    (state : X86_64MachineState) (eventsRev : List Event) : NativeRunOutcome Event :=
  match fuel with
  | 0 => .fuelExhausted state eventsRev.reverse
  | fuel + 1 =>
    match instructionAtRipIndexed indexed state.rip with
    | none => .returned state eventsRev.reverse
    | some instr =>
      let nextEventsRevAndState := nativeOutcomeTransition instr state eventsRev
      match nextEventsRevAndState.1.fault with
      | none => runProgramOutcomeLoop indexed fuel nextEventsRevAndState.1 nextEventsRevAndState.2
      | some (.processExit code) => .terminated (.processExit code)
          nextEventsRevAndState.1 nextEventsRevAndState.2.reverse
      | some .halted => .terminated .architecturalHalt
          nextEventsRevAndState.1 nextEventsRevAndState.2.reverse
      | some .divideError => .faulted nextEventsRevAndState.1 nextEventsRevAndState.2.reverse
      | some (.memFault _ _ _) => .faulted nextEventsRevAndState.1 nextEventsRevAndState.2.reverse

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- One production runner step when exact lookup succeeds, the runtime does not intercept, and the
    ordinary instruction remains nonfaulted. This is shared target semantics, not a frontend-local
    replay of the evaluator. -/
theorem runProgramOutcomeLoop_step_none {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (indexed : List (UInt64 × X86_64Instr)) (fuel : Nat)
    (state : X86_64MachineState) (eventsRev : List Event) (instruction : X86_64Instr)
    (lookup : instructionAtRipIndexed indexed state.rip = some instruction)
    (silent : interceptor.interceptCall
      (X86_64Instruction.step instruction state).rip
      (X86_64Instruction.step instruction state) = none)
    (safe : (X86_64Instruction.step instruction state).fault = none) :
    runProgramOutcomeLoop indexed (fuel + 1) state eventsRev =
      runProgramOutcomeLoop indexed fuel
        (X86_64Instruction.step instruction state) eventsRev := by
  simp [runProgramOutcomeLoop, lookup, nativeOutcomeTransition, silent, safe]

/-- The indexed native evaluator used by platform verification.  It executes exactly the same
    instruction/interceptor transition as `runAsmTrace`, but carries an explicit, non-silent
    termination reason. -/
def runProgramOutcomeWithLoops {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (baseRip : UInt64) (instructions : List X86_64Instr) (fuel : Nat)
    (initial : X86_64MachineState) : NativeRunOutcome Event :=
  runProgramOutcomeLoop (indexInstructions baseRip instructions) fuel initial []

/-- The explicit termination evaluator preserves the historical event projection exactly.  This
    theorem is structural in fuel and applies to the production transition, so existing closed
    trace theorems can be reused without hiding faults or fuel exhaustion. -/
theorem runProgramOutcomeLoop_events {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (indexed : List (UInt64 × X86_64Instr)) (fuel : Nat)
    (state : X86_64MachineState) (eventsRev : List Event) :
    (runProgramOutcomeLoop indexed fuel state eventsRev).events =
      eventsRev.reverse ++ runProgramTraceLoop indexed fuel state := by
  induction fuel generalizing state eventsRev with
  | zero => simp [runProgramOutcomeLoop, runProgramTraceLoop, NativeRunOutcome.events]
  | succ fuel ih =>
      cases hlookup : instructionAtRipIndexed indexed state.rip with
      | none => simp [runProgramOutcomeLoop, runProgramTraceLoop, hlookup,
          NativeRunOutcome.events]
      | some instr =>
          simp only [runProgramOutcomeLoop, runProgramTraceLoop, hlookup]
          unfold nativeOutcomeTransition
          cases hintercept : interceptor.interceptCall
              (X86_64Instruction.step instr state).rip
              (X86_64Instruction.step instr state) with
          | none =>
              cases hfault : (X86_64Instruction.step instr state).fault with
              | none =>
                  simp [hintercept, hfault, X86_64MachineState.faulted]
                  exact ih _ _
              | some fault =>
                  cases fault <;>
                    simp [hintercept, hfault, X86_64MachineState.faulted,
                      NativeRunOutcome.events]
          | some result =>
              rcases result with ⟨hooked, emitted⟩
              cases emitted with
              | none =>
                  cases hfault : hooked.fault with
                  | none =>
                      simp [hintercept, hfault, X86_64MachineState.faulted]
                      exact ih _ _
                  | some fault =>
                      cases fault <;>
                        simp [hintercept, hfault, X86_64MachineState.faulted,
                          NativeRunOutcome.events]
              | some event =>
                  cases hfault : hooked.fault with
                  | none =>
                      simp [hintercept, hfault, X86_64MachineState.faulted]
                      rw [ih hooked (event :: eventsRev)]
                      simp [List.reverse_cons, List.append_assoc]
                  | some fault =>
                      cases fault <;>
                        simp [hintercept, hfault, X86_64MachineState.faulted,
                          NativeRunOutcome.events, List.reverse_cons, List.append_assoc]

theorem runProgramOutcomeWithLoops_events {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (baseRip : UInt64) (instructions : List X86_64Instr) (fuel : Nat)
    (initial : X86_64MachineState) :
    (runProgramOutcomeWithLoops (Event := Event) baseRip instructions fuel initial).events =
      runProgramTraceWithLoops (Event := Event) baseRip instructions fuel initial := by
  simpa [runProgramOutcomeWithLoops, runProgramTraceWithLoops] using
    runProgramOutcomeLoop_events (Event := Event) (indexInstructions baseRip instructions)
      fuel initial ([] : List Event)

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- A native artifact's explicit termination certificate states the exact non-exhausted outcome
    reached within a declared budget.  This is evidence consumed by `VerifiedProgram`, not a
    trace-only check from which fuel exhaustion could be erased. -/
structure NativeTerminationCertificate {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (baseRip : UInt64) (instructions : List X86_64Instr)
    (initial : X86_64MachineState) where
  fuel : Nat
  outcome : NativeRunOutcome Event
  verifies : runProgramOutcomeWithLoops baseRip instructions fuel initial = outcome
  terminated : match outcome with
    | .returned _ _ | .terminated _ _ _ => True
    | .faulted _ _ | .fuelExhausted _ _ => False

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Replaces only the two external input queues while preserving every observational machine
    component: RIP, registers, flags, memory, and the terminal/fault reason. -/
def X86_64MachineState.withExternalInputs (state : X86_64MachineState)
    (stdin : ByteArray) (requests : List ByteArray) : X86_64MachineState :=
  { state with stdinBuffer := stdin, incomingRequests := requests }

@[simp] theorem X86_64MachineState.withExternalInputs_rip
    (state : X86_64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).rip = state.rip := rfl

@[simp] theorem X86_64MachineState.withExternalInputs_fault
    (state : X86_64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).fault = state.fault := rfl

@[simp] theorem X86_64MachineState.withExternalInputs_gprs
    (state : X86_64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).gprs = state.gprs := rfl

@[simp] theorem X86_64MachineState.withExternalInputs_flags
    (state : X86_64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).flags = state.flags := rfl

@[simp] theorem X86_64MachineState.withExternalInputs_memory
    (state : X86_64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).memory = state.memory := rfl

@[simp] theorem X86_64MachineState.withExternalInputs_rsp
    (state : X86_64MachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).rsp = state.rsp := rfl

@[simp] theorem X86_64MachineState.withExternalInputs_read64
    (state : X86_64MachineState) (stdin : ByteArray) (requests : List ByteArray) (address : Address) :
    (state.withExternalInputs stdin requests).read64 address = state.read64 address := rfl

@[simp] theorem X86_64MachineState.withExternalInputs_readString
    (state : X86_64MachineState) (stdin : ByteArray) (requests : List ByteArray)
    (address : Address) (length : Nat) :
    (state.withExternalInputs stdin requests).readString address length =
      state.readString address length := rfl

/-- Ordinary-instruction frame law used by input-independent artifacts.  It is deliberately an
    artifact obligation: the open existential instruction interface permits future instruction
    semantics, so the core cannot unsoundly assert this for arbitrary instances. -/
def InstructionPreservesExternalInputFrame (instr : X86_64Instr) : Prop :=
  ∀ state stdin requests,
    X86_64Instruction.step instr (state.withExternalInputs stdin requests) =
      (X86_64Instruction.step instr state).withExternalInputs stdin requests

/-- Every packaged x86-64 instruction satisfies the host-input frame law by the architectural
    boundary enforced in `AnyX86_64Instruction`'s step instance. -/
theorem instruction_preserves_external_input_frame (instr : X86_64Instr) :
    InstructionPreservesExternalInputFrame instr := by
  intro state stdin requests
  cases instr
  rfl

/-- Selected host-interceptor frame law.  The boolean selector is checked at every reached call
    boundary by `SelectedTerminationCertificate`; input-taking calls are therefore excluded rather
    than hidden under a false global congruence claim. -/
def InterceptorPreservesExternalInputFrame {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (selected : Address → X86_64MachineState → Bool) : Prop :=
  ∀ address state stdin requests, selected address state = true →
    interceptor.interceptCall address (state.withExternalInputs stdin requests) =
      (interceptor.interceptCall address state).map
        (fun result => (result.1.withExternalInputs stdin requests, result.2))

/-- Applies an external-input frame to the terminal machine state without changing the explicit
    stop reason or emitted observations. -/
def NativeRunOutcome.withExternalInputs (stdin : ByteArray) (requests : List ByteArray) :
    NativeRunOutcome Event → NativeRunOutcome Event
  | .returned state emitted => .returned (state.withExternalInputs stdin requests) emitted
  | .terminated cause state emitted =>
      .terminated cause (state.withExternalInputs stdin requests) emitted
  | .faulted state emitted => .faulted (state.withExternalInputs stdin requests) emitted
  | .fuelExhausted state emitted => .fuelExhausted (state.withExternalInputs stdin requests) emitted

@[simp] theorem NativeRunOutcome.withExternalInputs_events
    (outcome : NativeRunOutcome Event) (stdin : ByteArray) (requests : List ByteArray) :
    (outcome.withExternalInputs stdin requests).events = outcome.events := by
  cases outcome <;> rfl

@[simp] theorem NativeRunOutcome.withExternalInputs_observable
    (outcome : NativeRunOutcome Event) (stdin : ByteArray) (requests : List ByteArray) :
    (outcome.withExternalInputs stdin requests).observable = outcome.observable := by
  cases outcome <;> try rfl
  rename_i cause _ _
  cases cause <;> rfl

@[simp] theorem NativeRunOutcome.withExternalInputs_isAdmissible
    (outcome : NativeRunOutcome Event) (allowArchitecturalHalt : Bool)
    (stdin : ByteArray) (requests : List ByteArray) :
    (outcome.withExternalInputs stdin requests).isAdmissible allowArchitecturalHalt ↔
      outcome.isAdmissible allowArchitecturalHalt := by
  cases outcome <;> try rfl
  rename_i cause _ _
  cases cause <;> rfl

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Executable checker for the two facts a native universal proof needs from its closed reference
    run: every reached host boundary is in the selected congruent subset, and execution reaches a
    return, typed process exit, or selected architectural halt before evaluator fuel is exhausted. -/
def selectedExecutionTerminates {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (allowHalted : Bool)
    (selected : Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr)) (fuel : Nat)
    (state : X86_64MachineState) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    match instructionAtRipIndexed indexed state.rip with
    | none => true
    | some instr =>
      let stepped := X86_64Instruction.step instr state
      if !selected stepped.rip stepped then false
      else
        let next := (nativeOutcomeTransition (Event := Event) instr state []).1
        match next.fault with
        | none => selectedExecutionTerminates (Event := Event) allowHalted selected indexed fuel next
        | some (.processExit _) => true
        | some .halted => allowHalted
        | some .divideError | some (.memFault _ _ _) => false

/-- First-class selected-call and termination certificate for a concrete native artifact. -/
structure SelectedTerminationCertificate {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (allowHalted : Bool)
    (selected : Address → X86_64MachineState → Bool)
    (baseRip : UInt64) (instructions : List X86_64Instr)
    (initial : X86_64MachineState) where
  fuel : Nat
  verifies : selectedExecutionTerminates (Event := Event) allowHalted selected
    (indexInstructions baseRip instructions)
    fuel initial = true

theorem nativeOutcomeTransition_fst_independent_events {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (instr : X86_64Instr) (state : X86_64MachineState) (left right : List Event) :
    (nativeOutcomeTransition instr state left).1 =
      (nativeOutcomeTransition instr state right).1 := by
  unfold nativeOutcomeTransition
  cases h : interceptor.interceptCall (X86_64Instruction.step instr state).rip
      (X86_64Instruction.step instr state) <;> simp [h]

/-- A successful selected-call certificate also proves the profile-sensitive explicit
    termination judgment used by `Platform.admissible`. -/
theorem selectedExecutionTerminates_isAdmissible {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (allowHalted : Bool) (selected : Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr)) (fuel : Nat)
    (state : X86_64MachineState) (eventsRev : List Event)
    (hcertificate : selectedExecutionTerminates (Event := Event) allowHalted selected indexed
      fuel state = true) :
    (runProgramOutcomeLoop (Event := Event) indexed fuel state eventsRev).isAdmissible
      allowHalted := by
  induction fuel generalizing state eventsRev with
  | zero => simp [selectedExecutionTerminates] at hcertificate
  | succ fuel ih =>
      cases hlookup : instructionAtRipIndexed indexed state.rip with
      | none => simp [runProgramOutcomeLoop, hlookup, NativeRunOutcome.isAdmissible]
      | some instr =>
          simp only [selectedExecutionTerminates, hlookup] at hcertificate
          have hfst := nativeOutcomeTransition_fst_independent_events
            (Event := Event) instr state eventsRev []
          simp only [runProgramOutcomeLoop, hlookup]
          rw [hfst]
          by_cases hselected : selected (X86_64Instruction.step instr state).rip
              (X86_64Instruction.step instr state) = true
          · simp [hselected] at hcertificate

            cases hfault : (nativeOutcomeTransition (Event := Event) instr state []).1.fault with
            | none =>
                simp [hfault] at hcertificate
                simp [runProgramOutcomeLoop, hlookup, hfault]
                exact ih _ _ hcertificate
            | some fault =>
                cases fault with
                | processExit code =>
                    simp [runProgramOutcomeLoop, hlookup, hfault,
                      NativeRunOutcome.isAdmissible]
                | halted =>
                    simpa [runProgramOutcomeLoop, hlookup, hfault,
                      NativeRunOutcome.isAdmissible] using hcertificate
                | divideError => simp [hfault] at hcertificate
                | memFault kind width address => simp [hfault] at hcertificate
          · simp [hselected] at hcertificate

private theorem nativeOutcomeTransition_external_input_frame {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (selected : Address → X86_64MachineState → Bool)
    (instr : X86_64Instr) (state : X86_64MachineState) (eventsRev : List Event)
    (hinstr : InstructionPreservesExternalInputFrame instr)
    (hinterceptor : InterceptorPreservesExternalInputFrame (Event := Event) selected)
    (hselected : selected (X86_64Instruction.step instr state).rip
      (X86_64Instruction.step instr state) = true)
    (stdin : ByteArray) (requests : List ByteArray) :
    nativeOutcomeTransition instr (state.withExternalInputs stdin requests) eventsRev =
      ((nativeOutcomeTransition instr state eventsRev).1.withExternalInputs stdin requests,
        (nativeOutcomeTransition instr state eventsRev).2) := by
  unfold nativeOutcomeTransition
  rw [hinstr state stdin requests]
  simp only [X86_64MachineState.withExternalInputs_rip]
  rw [hinterceptor _ _ stdin requests hselected]
  cases h : interceptor.interceptCall (X86_64Instruction.step instr state).rip
      (X86_64Instruction.step instr state) <;> simp [h]

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- A selected-call termination certificate transports the exact production outcome across
    arbitrary stdin/request queues.  This is the structural congruence result missing from the
    former closed evaluators. -/
theorem runProgramOutcomeLoop_external_input_frame {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (selected : Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr))
    (hinstructions : ∀ instr, instr ∈ indexed.map Prod.snd →
      InstructionPreservesExternalInputFrame instr)
    (hinterceptor : InterceptorPreservesExternalInputFrame (Event := Event) selected)
    (fuel : Nat) (state : X86_64MachineState) (eventsRev : List Event)
    (allowHalted : Bool)
    (hcertificate : selectedExecutionTerminates (Event := Event) allowHalted selected indexed
      fuel state = true)
    (stdin : ByteArray) (requests : List ByteArray) :
    runProgramOutcomeLoop indexed fuel (state.withExternalInputs stdin requests) eventsRev =
      (runProgramOutcomeLoop indexed fuel state eventsRev).withExternalInputs stdin requests := by
  induction fuel generalizing state eventsRev with
  | zero => simp [selectedExecutionTerminates] at hcertificate
  | succ fuel ih =>
    cases hlookup : instructionAtRipIndexed indexed state.rip with
    | none =>
      simp [runProgramOutcomeLoop, hlookup, NativeRunOutcome.withExternalInputs]
    | some instr =>
      have hmem : instr ∈ indexed.map Prod.snd := instructionAtRipIndexed_some_mem_snd hlookup
      have hinstr := hinstructions instr hmem
      have hcert := hcertificate
      simp only [selectedExecutionTerminates, hlookup] at hcert
      by_cases hselected : selected (X86_64Instruction.step instr state).rip
          (X86_64Instruction.step instr state) = true
      · simp [hselected] at hcert

        have htransition := nativeOutcomeTransition_external_input_frame
          selected instr state eventsRev hinstr hinterceptor hselected stdin requests
        have hfst := nativeOutcomeTransition_fst_independent_events
          (Event := Event) instr state eventsRev []
        rw [← hfst] at hcert
        simp only [runProgramOutcomeLoop, X86_64MachineState.withExternalInputs_rip, hlookup]
        rw [htransition]
        cases hfault : (nativeOutcomeTransition instr state eventsRev).1.fault with
        | none =>
          simp [hfault] at hcert
          simp only [X86_64MachineState.withExternalInputs_fault, hfault]
          rw [ih _ _ hcert]
        | some fault =>
          cases fault with
          | processExit code => simp [hfault, NativeRunOutcome.withExternalInputs]
          | halted => simp [hfault, NativeRunOutcome.withExternalInputs]
          | divideError => simp [hfault] at hcert
          | memFault kind width address => simp [hfault] at hcert
      · simp [hselected] at hcert

/-- Artifact-facing admissibility projection.  The platform proves the generic induction once;
    each program supplies only its concrete executable certificate. -/
theorem SelectedTerminationCertificate.isAdmissible {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    {allowHalted : Bool} {selected : Address → X86_64MachineState → Bool}
    {baseRip : UInt64} {instructions : List X86_64Instr} {initial : X86_64MachineState}
    (certificate : SelectedTerminationCertificate (Event := Event) allowHalted selected
      baseRip instructions initial) :
    (runProgramOutcomeWithLoops (Event := Event) baseRip instructions certificate.fuel
      initial).isAdmissible allowHalted := by
  exact selectedExecutionTerminates_isAdmissible allowHalted selected
    (indexInstructions baseRip instructions) certificate.fuel initial [] certificate.verifies

/-- Artifact-facing universal-environment transport.  Instruction and interceptor frame laws stay
    at their owning layers; a caller only combines them with its concrete termination certificate. -/
theorem SelectedTerminationCertificate.externalInputFrame {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    {allowHalted : Bool} {selected : Address → X86_64MachineState → Bool}
    {baseRip : UInt64} {instructions : List X86_64Instr} {initial : X86_64MachineState}
    (certificate : SelectedTerminationCertificate (Event := Event) allowHalted selected
      baseRip instructions initial)
    (hinstructions : ∀ instr, instr ∈ (indexInstructions baseRip instructions).map Prod.snd →
      InstructionPreservesExternalInputFrame instr)
    (hinterceptor : InterceptorPreservesExternalInputFrame (Event := Event) selected)
    (stdin : ByteArray) (requests : List ByteArray) :
    runProgramOutcomeWithLoops (Event := Event) baseRip instructions certificate.fuel
        (initial.withExternalInputs stdin requests) =
      (runProgramOutcomeWithLoops (Event := Event) baseRip instructions certificate.fuel
        initial).withExternalInputs stdin requests := by
  exact runProgramOutcomeLoop_external_input_frame selected
    (indexInstructions baseRip instructions) hinstructions hinterceptor certificate.fuel initial []
    allowHalted certificate.verifies stdin requests

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Executes an x86-64 instruction sequence supporting branches and loops with fuel-based termination. -/
def runProgramWithLoops (baseRip : UInt64) (instructions : List X86_64Instr) (fuel : Nat) (s : X86_64MachineState) : X86_64MachineState :=
  let indexed := indexInstructions baseRip instructions
  let rec loop (fuel : Nat) (s : X86_64MachineState) : X86_64MachineState :=
    match fuel with
    | 0 => s
    | fuel + 1 =>
      match instructionAtRipIndexed indexed s.rip with
      | none => s
      | some instr =>
        let s' := X86_64Instruction.step instr s
        if s'.faulted then s'
        else loop fuel s'
  loop fuel s

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Executes an x86-64 instruction sequence supporting external call interception in addition to branches and loops. -/
def runProgramWithLoopsIntercept {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (baseRip : UInt64) (instructions : List X86_64Instr) (fuel : Nat) (s : X86_64MachineState) : X86_64MachineState :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
    match instructionAtRip baseRip instructions s.rip with
    | none => s
    | some instr =>
      let s' := X86_64Instruction.step instr s
      let (s'', _) :=
        match interceptor.interceptCall s'.rip s' with
        | some (interceptedState, evt) => (interceptedState, evt)
        | none => (s', none)
      if s''.faulted then s''
      else runProgramWithLoopsIntercept (Event := Event) baseRip instructions fuel s''

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Initializes a clean x86-64 machine state for function invocation with arguments. -/
def initMachineState (entryRip : Address) (args : List UInt64 := []) (stackTop : Address := 0x7FFFFFFF0008) : X86_64MachineState :=
  let argGprs : List Reg64 := [.rcx, .rdx, .r8, .r9]
  let rec setArgs (remGprs : List Reg64) (remArgs : List UInt64) (s : X86_64MachineState) : X86_64MachineState :=
    match remGprs, remArgs with
    | g :: grest, a :: arest => setArgs grest arest (s.setGpr64 g a)
    | _, _ => s
  let s0 : X86_64MachineState := {
    rip := entryRip,
    gprs := fun r => if r == .rsp then stackTop else 0,
    flags := 0,
    memory := X86_64Mem.zero
  }
  setArgs argGprs args s0

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Invokes an x86-64 subroutine with the given arguments and returns the 64-bit return value in RAX. -/
def callSubroutine (instructions : List X86_64Instr) (args : List UInt64) (fuel : Nat := 1000) (entryRip : Address := 0x1000) : UInt64 :=
  let s0 := initMachineState entryRip args
  let finalState := runProgramWithLoops entryRip instructions fuel s0
  finalState.gprs .rax

end Gasm.Targets.X86_64
