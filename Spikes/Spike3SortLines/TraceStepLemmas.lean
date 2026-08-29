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
import Gasm.Targets.X86_64.Semantics

/-!
# Generic single-step unfolding lemmas for `runProgramTraceWithLoops`

`Spikes/Spike2Fibonacci/Windows/LoopInvariant.lean` (PA15) built `runProgramWithLoops_step` /
`runProgramWithLoops_stuck`: generic, routine-independent facts about the state-only interpreter
`runProgramWithLoops`, letting a loop-invariant induction peel one instruction off the fuel budget
via `rfl`/`generalize` instead of asking the kernel to reduce the whole composed trace as one term.

Spike 3 (and Spike 5) need the *trace-producing* interpreter `runProgramTraceWithLoops` /
`runAsmTrace` instead (`Gasm/Targets/X86_64/Semantics.lean:94-121`) -- the version with
`ExternalCallInterceptor` hooks for Win32/Linux syscalls, used to prove `List Event` equalities
rather than final-state equalities. No prior proof in this repo builds the trace-loop analogue of
PA15's two lemmas (confirmed by search: `runProgramTraceWithLoops` is referenced only in its own
definition and doc-comment cross-references elsewhere). This file supplies that analogue.

`runProgramTraceWithLoops`'s single step has one more branch than `runProgramWithLoops`'s (it must
also case on `interceptor.interceptCall`'s three possible outcomes), so peeling one instruction
needs three "continues" lemmas instead of one, plus the same "stuck" lemma:

1. `runProgramTraceWithLoops_step_silent` -- ordinary instruction, `interceptCall` returns `none`
   (the vast majority of steps: any address that is not a recognized IAT slot / syscall entry).
2. `runProgramTraceWithLoops_step_hooked_silent` -- the stepped instruction's resulting `rip` *is*
   a recognized external-call address, but the hook emits no event (e.g. Windows `GetStdHandle`,
   `VirtualAlloc`, `ReadFile`: they mutate state and pop the return address themselves, but are not
   externally observable effects).
3. `runProgramTraceWithLoops_step_event` -- the hook emits an event (e.g. Windows `WriteFile`,
   `ExitProcess`), which is prepended to the trace.
4. `runProgramTraceWithLoops_stuck` -- once the fetch loop can no longer find an instruction at the
   current `rip` (e.g. it is left permanently parked on a non-code IAT slot address, as
   `exitProcessHook` deliberately does not clear), every remaining unit of fuel is a no-op and the
   trace is exactly what has been emitted so far -- this is what lets a "ran to completion in
   exactly N steps" fact be padded up to `runAsmTrace`'s default fuel (`50000`) without re-deriving
   the trace, exactly mirroring `runProgramWithLoops_stuck`'s role in PA15.

Every lemma here is stated with no reference to any spike's instructions/state at all -- reusable
verbatim by Spike 3 Linux (a different `ExternalCallInterceptor` instance, same generic shape) and
by Spike 5.
-/

namespace Spikes.Spike3SortLines

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Peels one instruction off `runProgramTraceWithLoops`'s fuel when the resulting `rip` is an
    ordinary code address (`interceptCall` recognizes nothing there) and execution has not
    faulted: the trace continues silently from the stepped state. -/
theorem runProgramTraceWithLoops_step_silent {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {base : Address} {instrs : List X86_64Instr} {fuel : Nat}
    {s : X86_64MachineState} {instr : X86_64Instr}
    (hfetch : instructionAtRip base instrs s.rip = some instr)
    (hnone : interceptor.interceptCall (X86_64Instruction.step instr s).rip (X86_64Instruction.step instr s) = none)
    (hnf : (X86_64Instruction.step instr s).faulted = false) :
    runProgramTraceWithLoops (Event := Event) base instrs (fuel + 1) s =
      runProgramTraceWithLoops (Event := Event) base instrs fuel (X86_64Instruction.step instr s) := by
  have hfetch' : instructionAtRipIndexed (indexInstructions base instrs) s.rip = some instr := by
    rw [instructionAtRipIndexed_eq_instructionAtRip]; exact hfetch
  simp only [runProgramTraceWithLoops, runProgramTraceLoop, hfetch', hnone, hnf,
    Bool.false_eq_true, if_false]

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Peels one instruction off `runProgramTraceWithLoops`'s fuel when the resulting `rip` lands on a
    recognized external-call address whose hook emits no event, and the hooked state has not
    faulted: the trace continues silently from the *hooked* state (not the raw stepped state --
    the hook's own state mutation, e.g. popping a return address, takes effect). -/
theorem runProgramTraceWithLoops_step_hooked_silent {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {base : Address} {instrs : List X86_64Instr} {fuel : Nat}
    {s : X86_64MachineState} {instr : X86_64Instr} {s_hooked : X86_64MachineState}
    (hfetch : instructionAtRip base instrs s.rip = some instr)
    (hhook : interceptor.interceptCall (X86_64Instruction.step instr s).rip (X86_64Instruction.step instr s) =
      some (s_hooked, none))
    (hnf : s_hooked.faulted = false) :
    runProgramTraceWithLoops (Event := Event) base instrs (fuel + 1) s =
      runProgramTraceWithLoops (Event := Event) base instrs fuel s_hooked := by
  have hfetch' : instructionAtRipIndexed (indexInstructions base instrs) s.rip = some instr := by
    rw [instructionAtRipIndexed_eq_instructionAtRip]; exact hfetch
  simp only [runProgramTraceWithLoops, runProgramTraceLoop, hfetch', hhook, hnf,
    Bool.false_eq_true, if_false]

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Peels one instruction off `runProgramTraceWithLoops`'s fuel when the resulting `rip` lands on a
    recognized external-call address whose hook emits an event, and the hooked state has not
    faulted: the event is prepended and the trace continues from the hooked state. -/
theorem runProgramTraceWithLoops_step_event {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {base : Address} {instrs : List X86_64Instr} {fuel : Nat}
    {s : X86_64MachineState} {instr : X86_64Instr} {s_hooked : X86_64MachineState} {evt : Event}
    (hfetch : instructionAtRip base instrs s.rip = some instr)
    (hhook : interceptor.interceptCall (X86_64Instruction.step instr s).rip (X86_64Instruction.step instr s) =
      some (s_hooked, some evt))
    (hnf : s_hooked.faulted = false) :
    runProgramTraceWithLoops (Event := Event) base instrs (fuel + 1) s =
      evt :: runProgramTraceWithLoops (Event := Event) base instrs fuel s_hooked := by
  have hfetch' : instructionAtRipIndexed (indexInstructions base instrs) s.rip = some instr := by
    rw [instructionAtRipIndexed_eq_instructionAtRip]; exact hfetch
  simp only [runProgramTraceWithLoops, runProgramTraceLoop, hfetch', hhook, hnf,
    Bool.false_eq_true, if_false]

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Once the fetch loop is permanently stuck (no instruction at the current `rip`), every
    remaining unit of fuel is a no-op: `runProgramTraceWithLoops` returns `[]` regardless of how
    much fuel is left. Mirrors `runProgramWithLoops_stuck` (PA15); lets a "trace is exactly these
    N events, reached in exactly K steps" fact be padded up to `runAsmTrace`'s default fuel budget
    (`50000`) for free. -/
theorem runProgramTraceWithLoops_stuck {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {base : Address} {instrs : List X86_64Instr} {s : X86_64MachineState}
    (hstuck : instructionAtRip base instrs s.rip = none) (fuel : Nat) :
    runProgramTraceWithLoops (Event := Event) base instrs fuel s = [] := by
  have hstuck' : instructionAtRipIndexed (indexInstructions base instrs) s.rip = none := by
    rw [instructionAtRipIndexed_eq_instructionAtRip]; exact hstuck
  cases fuel with
  | zero => rfl
  | succ f => simp only [runProgramTraceWithLoops, runProgramTraceLoop, hstuck']

end Spikes.Spike3SortLines
