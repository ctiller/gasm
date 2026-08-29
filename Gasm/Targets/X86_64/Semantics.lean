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
/-- The real, byte-accurate length of an instruction -- exactly the function `instructionAtRip`
    (above) and `Assembler.buildSymbolTable` themselves fold over an instruction list to lay out
    addresses. Reusable machinery for any spike/pathfinder that needs to state a fetch fact's
    address structurally (as a fold over the real instruction list) instead of a hand-summed
    byte-offset literal -- see `instructionAtRip_of_drop` below. -/
def instrSize (i : X86_64Instr) : Nat := (X86_64Instruction.encode i).size

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Cumulative real encoded length of an instruction prefix -- `instrSize` folded over
    `List.take`/`List.map`/`List.sum`, never a hand-summed numeral. `instructionAtRip_of_drop`
    below is stated in terms of this so that "the address of the instruction at list position `k`"
    is always a fold over the actual instruction list, not arithmetic a human performed and typed
    in. -/
def cumLen (instrs : List X86_64Instr) : Nat := (instrs.map instrSize).sum

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- **The one structural fetch lemma.** If `instrs.drop k = instr :: rest` (`instr` sits at list
    position `k` -- the only literal this lemma ever needs, and it is directly checkable against
    the source instruction list by inspection or `decide`, unlike a byte offset), and the address
    reached after `base` plus the real cumulative encoded length of the first `k` instructions
    never overflows `UInt64` (`hbound`), with every one of those first `k` instructions having
    positive encoded length (`hpos` -- both trivially `decide`d for any concrete, closed
    instruction list), then `instr` is exactly what `instructionAtRip` finds at that address. The
    address is computed by folding the REAL per-instruction length function (`instrSize`) over the
    REAL instruction list via `cumLen` -- never a hand-summed numeral or a hand-counted
    "N instructions back" offset. Proved once, here, for any target/spike doing this style of
    loop-invariant induction to reuse verbatim; each fetch fact elsewhere is then a single
    `apply instructionAtRip_of_drop` against a concrete list position. -/
theorem instructionAtRip_of_drop (base : Address) (instrs : List X86_64Instr) (k : Nat)
    (instr : X86_64Instr) (rest : List X86_64Instr)
    (hdrop : instrs.drop k = instr :: rest)
    (hbound : base.toNat + cumLen (instrs.take k) < 2 ^ 64)
    (hpos : ∀ i ∈ instrs.take k, 0 < instrSize i) :
    instructionAtRip base instrs (base + (cumLen (instrs.take k) : Nat).toUInt64) = some instr := by
  induction instrs generalizing base k with
  | nil => simp at hdrop
  | cons i0 instrs' ih =>
    cases k with
    | zero =>
      simp only [List.drop_zero] at hdrop
      injection hdrop with h1 h2
      subst h1; subst h2
      show instructionAtRip base (i0 :: instrs') (base + (cumLen ((i0 :: instrs').take 0) : Nat).toUInt64) = some i0
      simp only [List.take_zero, cumLen, List.map_nil, List.sum_nil, show (0 : Nat).toUInt64 = 0 from rfl,
        UInt64.add_zero]
      simp only [instructionAtRip, instructionAtRip.loop, BEq.rfl, if_true]
    | succ k =>
      simp only [List.drop_succ_cons] at hdrop
      have htake : (i0 :: instrs').take (k + 1) = i0 :: instrs'.take k := by simp
      have hcumcons : cumLen (i0 :: instrs'.take k) = instrSize i0 + cumLen (instrs'.take k) := by
        simp [cumLen, instrSize]
      rw [htake] at hbound hpos
      rw [hcumcons] at hbound
      have hbound' : (base + (instrSize i0 : Nat).toUInt64).toNat + cumLen (instrs'.take k) < 2 ^ 64 := by
        have hb1 : base.toNat + instrSize i0 < 2 ^ 64 := by omega
        have : (base + (instrSize i0 : Nat).toUInt64).toNat = base.toNat + instrSize i0 := by
          simp [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat',
            Nat.mod_eq_of_lt (show instrSize i0 < 2 ^ 64 by omega), Nat.mod_eq_of_lt hb1]
        omega
      have hpos' : ∀ i ∈ instrs'.take k, 0 < instrSize i := fun i hi => hpos i (List.mem_cons_of_mem _ hi)
      have hi0pos : 0 < instrSize i0 := hpos i0 (by simp)
      have key := ih (base + (instrSize i0 : Nat).toUInt64) k hdrop hbound' hpos'
      have htarget : base + (cumLen ((i0 :: instrs').take (k + 1)) : Nat).toUInt64
          = (base + (instrSize i0 : Nat).toUInt64) + (cumLen (instrs'.take k) : Nat).toUInt64 := by
        rw [htake, hcumcons, Nat.toUInt64_eq, Nat.toUInt64_eq, Nat.toUInt64_eq, UInt64.ofNat_add,
          UInt64.add_assoc]
      have hne : base ≠ base + (cumLen ((i0 :: instrs').take (k + 1)) : Nat).toUInt64 := by
        rw [htake, hcumcons]
        intro heq
        have hc : 0 < instrSize i0 + cumLen (instrs'.take k) := by omega
        have heqn : (base + (instrSize i0 + cumLen (instrs'.take k) : Nat).toUInt64).toNat
            = base.toNat + (instrSize i0 + cumLen (instrs'.take k)) := by
          simp [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat',
            Nat.mod_eq_of_lt (show instrSize i0 + cumLen (instrs'.take k) < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt hbound]
        rw [← heq] at heqn
        omega
      show instructionAtRip base (i0 :: instrs')
          (base + (cumLen ((i0 :: instrs').take (k + 1)) : Nat).toUInt64) = some instr
      rw [htarget]
      have hboolfalse : (base == (base + (instrSize i0 : Nat).toUInt64) + (cumLen (instrs'.take k) : Nat).toUInt64)
          = false := by
        rw [← htarget]; simpa using hne
      simp only [instructionAtRip, instructionAtRip.loop, hboolfalse, Bool.false_eq_true, if_false]
      exact key

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
/-- Trace evaluator executing an x86-64 program with dynamic branches, loops, and external API interception. -/
def runProgramTraceWithLoops {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (baseRip : UInt64) (instructions : List X86_64Instr) (fuel : Nat) (s : X86_64MachineState) : List Event :=
  let indexed := indexInstructions baseRip instructions
  let rec loop (fuel : Nat) (s : X86_64MachineState) : List Event :=
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
          else evt :: loop fuel s_hooked
        | some (s_hooked, none) =>
          if s_hooked.faulted then []
          else loop fuel s_hooked
        | none =>
          if s'.faulted then []
          else loop fuel s'
  loop fuel s

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Trace evaluator executing a list of lowered x86-64 instructions with dynamic control flow. -/
def runAsmTrace {Event : Type} [ExternalCallInterceptor X86_64 Event]
    (instructions : List X86_64Instr) (s : X86_64MachineState) (fuel : Nat := 50000) : List Event :=
  runProgramTraceWithLoops s.rip instructions fuel s

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
