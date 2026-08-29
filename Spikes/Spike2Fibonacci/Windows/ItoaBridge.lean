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
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Semantics
import Spikes.Spike2Fibonacci.Windows.Program
import Spikes.Spike2Fibonacci.Windows.LoopInvariant
import Stdlib.Fmt.Basic

/-!
# ItoaBridge: connecting `spike2Instructions`' hardware itoa to `Stdlib.Fmt`

`Spikes/Spike2Fibonacci/Windows/Program.lean`'s `spike2SymbolicProgram` formats each Fibonacci
value into decimal via a hand-written hardware itoa (`digit_extract_loop`/`digit_write_loop`),
independently of `Stdlib.Fmt.digits`/`formatDecimal` (a from-scratch, proved decimal codec built
for exactly this purpose -- see `Stdlib/Fmt/Basic.lean`'s module docstring and
`docs/STDLIB_FMT.md` §6). This file proves the two loops actually compute `Stdlib.Fmt.digits`/
`formatDecimal`, following the same shape as `Stdlib/Zlib/ContainerRoundtrip.lean`'s
`byteArray_forIn_push_spec`/`zlibCompress_spec`/`zlib_roundtrip_soundness`: a pointwise, closed-
form characterization of each loop's effect (proved by induction, no evaluation of either loop on
concrete data), then a connection theorem tying the pair to `Stdlib.Fmt` directly.

## Structure

1. `digitExtractLoop_spec` -- pointwise/closed-form: starting with `rax = n`, `r10 = 10`, running
   `digit_extract_loop` to completion pushes `(digits n).reverse` (as ASCII bytes, low byte only)
   onto the stack and leaves `rax = 0`, `rcx` advanced by `(digits n).length`.
2. `digitWriteLoop_spec` -- pointwise/closed-form, content-agnostic in the pushed list `L`:
   starting with `rcx = L.length` and the stack holding `L` (top-down), running
   `digit_write_loop` to completion writes `L` into the buffer at `rdi` in order.
3. `itoaLoops_spec` -- the connection theorem: composing (1) and (2) directly gives
   `formatDecimal n` written into the buffer, citing `Stdlib.Fmt.digits_foldl_eq`/
   `digits_length_le_UInt64` rather than re-deriving digit-list facts.

Only after this file are (3)'s facts composed with the fixed literal bytes ("Fib(", ") = "), the
loop-index one/two-digit formatting (`Stdlib.Fmt.digits_single`/`digits_length_two`), and the
existing PA15 Fibonacci-recurrence facts into the whole-program trace theorem that replaces
`spike2_canonical_effect_trace_equivalence`'s `native_decide` body.
-/

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.Windows
open Gasm.Targets.Windows.Linker
open Spikes.Spike2Fibonacci

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

/-
## Part 0: concrete addresses

Every address in this file is `spike2Executable.load.rip + cumLen (spike2Instructions.take k)` for
a concrete real-instruction list POSITION `k` -- `cumLen`/`instrSize`
(`Gasm/Targets/X86_64/Semantics.lean`) fold the REAL per-instruction encoded-length function over
the REAL instruction list via `List.take`/`List.map`/`List.sum`, never a hand-summed byte offset or
an independent absolute numeral. `digit_extract_loop` starts at position 43 (`xor edx, edx`) and
`digit_write_loop` at position 50 (`pop rdx`) in `spike2Instructions` -- probed once against the
real assembled program (labels are zero-width and contribute no position of their own) -- the only
literals this file's addressing ever needs, each directly checkable against
`spike2SymbolicProgram`'s instruction order by inspection. `digitExtractLoopAddr`/
`digitWriteLoopAddr`/`digitWriteLoopAddrEnd` are named `def`s over this structural form purely for
readability at use sites; `instructionAtRip_of_drop` (Part 2) is what actually ties a position to
its fetched instruction, and needs no separate numeral bridging step at all.
-/

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- Address of `digit_extract_loop`'s first instruction (`xor edx, edx`): real-instruction
    position 43 in `spike2Instructions`. -/
def digitExtractLoopAddr : Address :=
  spike2Executable.load.rip + (cumLen (spike2Instructions.take 43) : Nat).toUInt64

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- Address of `digit_write_loop`'s first instruction (`pop rdx`): real-instruction position 50. -/
def digitWriteLoopAddr : Address :=
  spike2Executable.load.rip + (cumLen (spike2Instructions.take 50) : Nat).toUInt64

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- Address immediately after `digit_write_loop`'s last instruction (the `\r\n`-append code that
    follows): real-instruction position 55. -/
def digitWriteLoopAddrEnd : Address :=
  spike2Executable.load.rip + (cumLen (spike2Instructions.take 55) : Nat).toUInt64

/-
## Part 1: per-instruction step facts not already covered by `LoopInvariant.lean`

`step_xor_r32`, `step_cmp_r64_imm8`, `setFlagsCmp64_zero_zf`, `step_sub_r64_imm8`,
`runProgramWithLoops_step`, `runProgramWithLoops_stuck` are reused directly from
`Windows.LoopInvariant` -- every one of them is already stated generically (no Fibonacci-specific
content), exactly the reuse `docs/STDLIB_FMT.md` asks for.
-/

/- REF: intel-sdm#vol=2;instr=DIV;part=operation -/
/-- `div r10` with `rdx = 0` and `r10 = 10` beforehand (exactly the extract loop's own precondition,
    established by `xor edx,edx` and `mov r10,10`): never faults (`10 ≠ 0`, and the quotient of any
    `UInt64` dividend by `10` never exceeds `UInt64`'s range), and computes plain `Nat` div/mod by
    `10` on `rax`'s value. -/
theorem step_div_r64_by10 (s : X86_64MachineState) (hrdx : s.gprs .rdx = 0) (hr10 : s.gprs .r10 = 10) :
    X86_64Instruction.step (div_r64 .r10) s =
      { (s.setGpr64 .rax (((s.gprs .rax).toNat / 10 : Nat)).toUInt64
          |>.setGpr64 .rdx (((s.gprs .rax).toNat % 10 : Nat)).toUInt64) with rip := s.rip + 3 } := by
  have hbase : X86_64Instruction.step (div_r64 .r10) s =
      (if (s.gprs .r10) == 0 then { s with fault := some .divideError }
       else
         let dividendNat : Nat := (s.gprs .rdx).toNat * 18446744073709551616 + (s.gprs .rax).toNat
         let divisorNat : Nat := (s.gprs .r10).toNat
         let quotNat := dividendNat / divisorNat
         let remNat := dividendNat % divisorNat
         if quotNat > 0xFFFFFFFFFFFFFFFF then { s with fault := some .divideError }
         else
           let s' := s.setGpr64 .rax (UInt64.ofNat quotNat)
           let s'' := s'.setGpr64 .rdx (UInt64.ofNat remNat)
           { s'' with rip := s.rip + 3 }) := rfl
  rw [hbase]
  have hne : (s.gprs .r10 == (0 : UInt64)) = false := by rw [hr10]; decide
  rw [hne]
  simp only [Bool.false_eq_true, if_false]
  have hdividend : (s.gprs .rdx).toNat * 18446744073709551616 + (s.gprs .rax).toNat
      = (s.gprs .rax).toNat := by rw [hrdx]; simp
  have hdivisor : (s.gprs .r10).toNat = 10 := by rw [hr10]; rfl
  simp only [hdividend, hdivisor]
  have hbound : (s.gprs .rax).toNat < 18446744073709551616 := by
    have h := (s.gprs .rax).toNat_lt_size
    simpa using h
  have hdiv : (s.gprs .rax).toNat / 10 ≤ (s.gprs .rax).toNat := Nat.div_le_self _ _
  rw [if_neg (by omega)]

/- REF: intel-sdm#vol=2;instr=ADD;part=operation -/
theorem step_add_r64_imm8 (dst : Reg64) (imm : UInt8) (s : X86_64MachineState) :
    X86_64Instruction.step (add_r64_imm8 dst imm) s =
      { (s.setGpr64 dst (s.gprs dst + signExtend8To64 imm)).setFlagsAdd64 (s.gprs dst)
          (signExtend8To64 imm) with rip := s.rip + 4 } := rfl

/- REF: intel-sdm#vol=2;instr=PUSH;part=operation -/
/-- Specialized to `.rdx` (the only register `digit_extract_loop` ever pushes): `PushR64`'s
    encoded length depends on whether the register needs a REX extension byte (1 byte for `.rdx`,
    2 for `r8`-`r15`), so the length does not reduce by `rfl` for a fully generic register -- only
    once a concrete register fixes `ext`. -/
theorem step_push_rdx (s : X86_64MachineState) :
    X86_64Instruction.step (push_r64 .rdx) s = { s.push64 (s.gprs .rdx) with rip := s.rip + 1 } := rfl

/- REF: intel-sdm#vol=2;instr=POP;part=operation -/
/-- Specialized to `.rdx`, same rationale as `step_push_rdx`. -/
theorem step_pop_rdx (s : X86_64MachineState) :
    X86_64Instruction.step (pop_r64 .rdx) s =
      { (s.pop64.2.setGpr64 .rdx s.pop64.1) with rip := s.rip + 1 } := rfl

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
/-- Specialized to `.rdi .rdx` (the only pair `digit_write_loop` ever uses): `MovMem8Reg8`'s
    encoded length depends on both operands' REX-extension and whether the pointer register is
    `rsp`/`r12` or `rbp`/`r13` (needing an extra SIB/disp8 byte), none of which reduce for fully
    generic registers. -/
theorem step_mov_mem8_rdi_rdx (s : X86_64MachineState) :
    X86_64Instruction.step (mov_mem8 .rdi .rdx) s =
      { s.write8 (s.gprs .rdi) (s.gprs .rdx).toUInt8 with rip := s.rip + 2 } := rfl

/- REF: intel-sdm#vol=2;instr=Jcc;part=operation -/
theorem step_jne_rel8 (disp : UInt8) (s : X86_64MachineState) :
    X86_64Instruction.step (jne_rel8 disp) s =
      { s with rip := if !s.zf then s.rip + 2 + signExtend8To64 disp else s.rip + 2 } := rfl

/-
## Part 2: fetch facts

Every fetch fact below is an application of `instructionAtRip_of_drop`
(`Gasm/Targets/X86_64/Semantics.lean`) to a concrete real-instruction-list POSITION in
`spike2Instructions` -- never a hand-typed address literal or a hand-summed byte offset.
`digitExtractLoopAddr`/`digitWriteLoopAddr`/`digitWriteLoopAddrEnd` are *definitionally* the
`cumLen`-computed address of their position (Part 0), so each `_eq` bridging fact below is exactly
`rfl`, and every jump target composes real-instruction positions (`49 -> 50`, `54 -> 55`) rather
than reconstructing a byte offset by hand. -/

theorem digitExtractLoopAddr_eq :
    digitExtractLoopAddr =
      spike2Executable.load.rip + (cumLen (spike2Instructions.take 43) : Nat).toUInt64 := rfl

theorem digitWriteLoopAddr_eq :
    digitWriteLoopAddr =
      spike2Executable.load.rip + (cumLen (spike2Instructions.take 50) : Nat).toUInt64 := rfl

theorem digitWriteLoopAddrEnd_eq :
    digitWriteLoopAddrEnd =
      spike2Executable.load.rip + (cumLen (spike2Instructions.take 55) : Nat).toUInt64 := rfl

theorem iFetch_xor : instructionAtRip spike2Executable.load.rip spike2Instructions
    digitExtractLoopAddr = some (xor_r32 .edx .edx) := by
  rw [digitExtractLoopAddr_eq]; apply instructionAtRip_of_drop
  all_goals first | rfl | decide

theorem iFetch_div : instructionAtRip spike2Executable.load.rip spike2Instructions
    (spike2Executable.load.rip + (cumLen (spike2Instructions.take 44) : Nat).toUInt64) =
    some (div_r64 .r10) := by
  apply instructionAtRip_of_drop
  all_goals first | rfl | decide

theorem iFetch_addImm : instructionAtRip spike2Executable.load.rip spike2Instructions
    (spike2Executable.load.rip + (cumLen (spike2Instructions.take 45) : Nat).toUInt64) =
    some (add_r64_imm8 .rdx 0x30) := by
  apply instructionAtRip_of_drop
  all_goals first | rfl | decide

theorem iFetch_push : instructionAtRip spike2Executable.load.rip spike2Instructions
    (spike2Executable.load.rip + (cumLen (spike2Instructions.take 46) : Nat).toUInt64) =
    some (push_r64 .rdx) := by
  apply instructionAtRip_of_drop
  all_goals first | rfl | decide

theorem iFetch_addRcx : instructionAtRip spike2Executable.load.rip spike2Instructions
    (spike2Executable.load.rip + (cumLen (spike2Instructions.take 47) : Nat).toUInt64) =
    some (add_r64_imm8 .rcx 1) := by
  apply instructionAtRip_of_drop
  all_goals first | rfl | decide

theorem iFetch_cmpAx : instructionAtRip spike2Executable.load.rip spike2Instructions
    (spike2Executable.load.rip + (cumLen (spike2Instructions.take 48) : Nat).toUInt64) =
    some (cmp_r64_imm8 .rax 0) := by
  apply instructionAtRip_of_drop
  all_goals first | rfl | decide

theorem iFetch_jneExtract : instructionAtRip spike2Executable.load.rip spike2Instructions
    (spike2Executable.load.rip + (cumLen (spike2Instructions.take 49) : Nat).toUInt64) =
    some (jne_rel8 (Assembler.toDisp8 digitExtractLoopAddr digitWriteLoopAddr)) := by
  rw [digitExtractLoopAddr_eq, digitWriteLoopAddr_eq]
  apply instructionAtRip_of_drop
  all_goals first | rfl | decide

theorem iFetch_pop : instructionAtRip spike2Executable.load.rip spike2Instructions
    digitWriteLoopAddr = some (pop_r64 .rdx) := by
  rw [digitWriteLoopAddr_eq]; apply instructionAtRip_of_drop
  all_goals first | rfl | decide

theorem iFetch_movMem : instructionAtRip spike2Executable.load.rip spike2Instructions
    (spike2Executable.load.rip + (cumLen (spike2Instructions.take 51) : Nat).toUInt64) =
    some (mov_mem8 .rdi .rdx) := by
  apply instructionAtRip_of_drop
  all_goals first | rfl | decide

theorem iFetch_addRdi : instructionAtRip spike2Executable.load.rip spike2Instructions
    (spike2Executable.load.rip + (cumLen (spike2Instructions.take 52) : Nat).toUInt64) =
    some (add_r64_imm8 .rdi 1) := by
  apply instructionAtRip_of_drop
  all_goals first | rfl | decide

theorem iFetch_subRcx : instructionAtRip spike2Executable.load.rip spike2Instructions
    (spike2Executable.load.rip + (cumLen (spike2Instructions.take 53) : Nat).toUInt64) =
    some (sub_r64_imm8 .rcx 1) := by
  apply instructionAtRip_of_drop
  all_goals first | rfl | decide

theorem iFetch_jneWrite : instructionAtRip spike2Executable.load.rip spike2Instructions
    (spike2Executable.load.rip + (cumLen (spike2Instructions.take 54) : Nat).toUInt64) =
    some (jne_rel8 (Assembler.toDisp8 digitWriteLoopAddr digitWriteLoopAddrEnd)) := by
  rw [digitWriteLoopAddr_eq, digitWriteLoopAddrEnd_eq]
  apply instructionAtRip_of_drop
  all_goals first | rfl | decide

/-- The extract loop's back-edge (position 49's `jne`) lands exactly on `digitExtractLoopAddr`
    (position 43), from the address of position 50 (its own successor). -/
theorem jneExtract_target :
    (spike2Executable.load.rip + (cumLen (spike2Instructions.take 49) : Nat).toUInt64) + 2 +
      signExtend8To64 (Assembler.toDisp8 digitExtractLoopAddr digitWriteLoopAddr) =
      digitExtractLoopAddr := by
  rw [digitExtractLoopAddr_eq, digitWriteLoopAddr_eq]; decide

/-- The write loop's back-edge (position 54's `jne`) lands exactly on `digitWriteLoopAddr`
    (position 50), from the address of position 55 (`digitWriteLoopAddrEnd`, its own successor). -/
theorem jneWrite_target :
    (spike2Executable.load.rip + (cumLen (spike2Instructions.take 54) : Nat).toUInt64) + 2 +
      signExtend8To64 (Assembler.toDisp8 digitWriteLoopAddr digitWriteLoopAddrEnd) =
      digitWriteLoopAddr := by
  rw [digitWriteLoopAddr_eq, digitWriteLoopAddrEnd_eq]; decide

/-
## Part 3: `StackHolds`, a pointwise/closed-form stack-content predicate

`StackHolds mem top L` says the qword-aligned slots `top, top+8, top+16, ...` hold exactly `L`
(each byte zero-extended to a `UInt64`, matching how `push_r64`/`pop_r64` always move a whole
64-bit register whose upper 56 bits are provably zero here -- see `digitExtractLoop_run` below).
Recursive on `L`, mirroring `Stdlib.Fmt.digits`'s own recursion shape, deliberately -- this is the
"declarative fact about the end state" the `Stdlib/Zlib` pattern asks for, not a step-by-step trace
comparison: nothing here evaluates the loop on any concrete `n`.
-/

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
def StackHolds (mem : X86_64Memory) (top : Address) : List UInt8 → Prop
  | [] => True
  | b :: rest => X86_64Mem.read .w64 top mem = b.toUInt64 ∧ StackHolds mem (top + 8) rest

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- `StackHolds` splits over list append the same way `digits n = digits (n/10) ++ [n%10]` does --
    the one fact that lets the induction below compose "this iteration's own digit" with "every
    digit the recursive call already placed". Pure address algebra (`ring`), no overflow
    side-condition: `UInt64` addition/multiplication commute and associate mod `2^64` regardless of
    wraparound. -/
theorem StackHolds_append (mem : X86_64Memory) (top : Address) (L1 : List UInt8) :
    ∀ L2 : List UInt8,
      StackHolds mem top (L1 ++ L2) ↔
        StackHolds mem top L1 ∧ StackHolds mem (top + 8 * L1.length.toUInt64) L2 := by
  induction L1 generalizing top with
  | nil => intro L2; simp [StackHolds]
  | cons b rest ih =>
    intro L2
    simp only [List.cons_append, StackHolds]
    rw [ih]
    have haddr : top + 8 * (b :: rest).length.toUInt64 = top + 8 + 8 * rest.length.toUInt64 := by
      have hlen : (b :: rest).length.toUInt64 = rest.length.toUInt64 + 1 := by
        simp only [List.length_cons]
        simp [Nat.toUInt64]
      rw [hlen, UInt64.mul_add, UInt64.mul_one, UInt64.add_assoc,
        UInt64.add_comm ((8 : UInt64) * rest.length.toUInt64) 8, ← UInt64.add_assoc]
    rw [haddr, and_assoc]

/-
## Part 4: `digit_extract_loop`'s pointwise closed-form characterization

By strong induction on `n` (the value in `rax` at loop entry), mirroring `Stdlib.Fmt.digits`'
own `Nat.strongRecOn` recursion (`digits_lt_ten`/`digits_foldl_eq`'s proof shape) rather than
`fibLoop_iteration`/`loop_correct`'s externally-supplied fixed trip count: the extract loop's own
trip count (`(digits n).length`) is *derived from* the value being divided, not passed in, exactly
the "variable trip count" case `docs/STDLIB_FMT.md` §6.2 names as having no direct PA15 precedent.
-/

/- REF: docs/STDLIB_FMT.md#2-digit-grammar -/
/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- `UInt64` has no `sub_sub` lemma of its own (confirmed by searching the Lean 4 core source
    tree), but the underlying `BitVec 64` does (`BitVec.sub_sub`). Routed through
    `UInt64.toBitVec`/`UInt64.eq_of_toBitVec_eq`, the same bridge `and_or_distrib`
    (`Windows/LoopInvariant.lean`) uses for bitwise identities. Pure ring algebra, no overflow
    side-condition (subtraction wraps consistently mod `2^64` regardless of order). -/
theorem UInt64.sub_sub (a b c : UInt64) : a - b - c = a - (b + c) := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_sub, UInt64.toBitVec_add]
  exact BitVec.sub_sub _ _ _

/-- The one arithmetic fact bridging the assembly's `add rdx, 0x30` (widened `UInt64` addition) to
    `Stdlib.Fmt.byteOfDigit` (a `UInt8`-truncating `Nat` computation): for any genuine digit
    `d < 10`, they agree. Finite case split on `d`'s 10 possible values (`formatDecimal_range`'s own
    proof in `Stdlib/Fmt/Basic.lean` uses the identical idiom), each closed by `decide` -- not a
    re-derivation of digit-list correctness, just a byte-representation reconciliation. -/
theorem digit_byte_toUInt64 (d : Nat) (hd : d < 10) :
    (d.toUInt64 + (0x30 : UInt64)) = (Stdlib.Fmt.byteOfDigit d).toUInt64 := by
  unfold Stdlib.Fmt.byteOfDigit
  have h9 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by
    omega
  rcases h9 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- **One iteration of `digit_extract_loop`.** For an arbitrary `n` (never a concrete literal):
    the 7-instruction body advances `rax` from `n` to `n / 10`, `rcx` by one, decrements `rsp` by 8,
    pushes `byteOfDigit (n % 10)` onto the newly-opened stack slot, leaves every other register and
    every byte at or above the entry `rsp` untouched, and lands back at `digitExtractLoopAddr` if
    `n / 10 ≠ 0` (more iterations remain) or falls through to `digitWriteLoopAddr` if `n / 10 = 0`
    (extraction is complete) -- exactly the `cmp rax,0`/`jne` branch the assembly encodes, restated
    without executing it. This is the reusable "one step of the loop" fact the induction below
    chains; the case split on `n / 10 = 0` is what makes `Stdlib.Fmt.digits`' own
    `if n < 10 then [n] else digits (n / 10) ++ [n % 10]` recursion and this loop's control flow
    correspond exactly. -/
theorem digitExtractLoop_oneIter (n c fuel : Nat) (s : X86_64MachineState)
    (hrip : s.rip = digitExtractLoopAddr) (hrax : s.gprs .rax = n.toUInt64)
    (hn : n < 18446744073709551616) (hr10 : s.gprs .r10 = 10) (hrcx : s.gprs .rcx = c.toUInt64)
    (hfault : s.fault = none) (hrspBound : 8 ≤ s.rsp.toNat) :
    ∃ s1,
      runProgramWithLoops spike2Executable.load.rip spike2Instructions (fuel + 7) s =
        runProgramWithLoops spike2Executable.load.rip spike2Instructions fuel s1 ∧
      s1.rip = (if n / 10 = 0 then digitWriteLoopAddr else digitExtractLoopAddr) ∧
      s1.gprs .rax = (n / 10).toUInt64 ∧
      s1.gprs .rcx = (c + 1).toUInt64 ∧
      s1.rsp = s.rsp - 8 ∧
      s1.fault = none ∧
      X86_64Mem.read .w64 s1.rsp s1.memory = (Stdlib.Fmt.byteOfDigit (n % 10)).toUInt64 ∧
      (∀ a : Address, a.toNat ≥ s.rsp.toNat →
        X86_64Mem.read .w8 a s1.memory = X86_64Mem.read .w8 a s.memory) ∧
      (∀ r : Reg64, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .rsp → s1.gprs r = s.gprs r) := by
  -- step 1: xor edx, edx
  have hfaulted0 : s.faulted = false := X86_64MachineState.faulted_of_fault_none hfault
  have hfetch1 : instructionAtRip spike2Executable.load.rip spike2Instructions s.rip =
      some (xor_r32 .edx .edx) := by rw [hrip]; exact iFetch_xor
  rw [show fuel + 7 = fuel + 6 + 1 from rfl, runProgramWithLoops_step hfetch1 hfaulted0]
  generalize hs1 : X86_64Instruction.step (xor_r32 .edx .edx) s = s1
  have hrip1 : s1.rip = digitExtractLoopAddr + 2 := by
    rw [← hs1, step_xor_r32, hrip]; rfl
  have hfault1 : s1.fault = none := by rw [← hs1]; exact hfault
  have hrdx1 : s1.gprs .rdx = 0 := by
    rw [← hs1, step_xor_r32]; simp only [uint32_xor_self]; rfl
  have hrax1 : s1.gprs .rax = n.toUInt64 := by rw [← hs1, step_xor_r32]; exact hrax
  have hr10_1 : s1.gprs .r10 = 10 := by rw [← hs1, step_xor_r32]; exact hr10
  have hrcx1 : s1.gprs .rcx = c.toUInt64 := by rw [← hs1, step_xor_r32]; exact hrcx
  have hrsp1 : s1.rsp = s.rsp := by rw [← hs1, step_xor_r32]; rfl
  have hmem1 : s1.memory = s.memory := by rw [← hs1, step_xor_r32]; rfl
  have hfaulted1 : s1.faulted = false := X86_64MachineState.faulted_of_fault_none hfault1
  -- step 2: div r10 (rdx = 0, r10 = 10). `step_div_r64_by10`'s proof (a genuine case split on
  -- the divide-fault/overflow checks) is invoked exactly ONCE here (`hs2eq`); every fact below is
  -- a cheap projection off that single concrete record literal, not a fresh re-elaboration of the
  -- lemma -- re-`rw`ing a case-split lemma at each of 7 downstream call sites is what made an
  -- earlier draft of this step time out during `lake build`.
  have hraxNat : (s1.gprs .rax).toNat = n := by rw [hrax1]; simp [Nat.toUInt64, hn]
  have hs2eq : X86_64Instruction.step (div_r64 .r10) s1 =
      { (s1.setGpr64 .rax (n / 10 : Nat).toUInt64 |>.setGpr64 .rdx (n % 10 : Nat).toUInt64) with
        rip := s1.rip + 3 } := by
    rw [step_div_r64_by10 s1 hrdx1 hr10_1, hraxNat]
  have hfetch2 : instructionAtRip spike2Executable.load.rip spike2Instructions s1.rip =
      some (div_r64 .r10) := by rw [hrip1]; exact iFetch_div
  have hnf2 : (X86_64Instruction.step (div_r64 .r10) s1).faulted = false := by
    rw [hs2eq]; exact hfaulted1
  rw [show fuel + 6 = fuel + 5 + 1 from rfl, runProgramWithLoops_step hfetch2 hnf2]
  generalize hs2 : X86_64Instruction.step (div_r64 .r10) s1 = s2
  rw [hs2eq] at hs2
  have hrip2 : s2.rip = digitExtractLoopAddr + 5 := by
    rw [← hs2]
    show s1.rip + 3 = digitExtractLoopAddr + 5
    rw [hrip1, UInt64.add_assoc]; rfl
  have hfault2 : s2.fault = none := by rw [← hs2]; exact hfault1
  have hrax2 : s2.gprs .rax = (n / 10).toUInt64 := by rw [← hs2]; rfl
  have hrdx2 : s2.gprs .rdx = (n % 10).toUInt64 := by rw [← hs2]; rfl
  have hrcx2 : s2.gprs .rcx = c.toUInt64 := by rw [← hs2]; exact hrcx1
  have hrsp2 : s2.rsp = s.rsp := by rw [← hs2]; exact hrsp1
  have hmem2 : s2.memory = s.memory := by rw [← hs2]; exact hmem1
  have hfaulted2 : s2.faulted = false := X86_64MachineState.faulted_of_fault_none hfault2
  -- step 3: add rdx, 0x30
  have hfetch3 : instructionAtRip spike2Executable.load.rip spike2Instructions s2.rip =
      some (add_r64_imm8 .rdx 0x30) := by rw [hrip2]; exact iFetch_addImm
  rw [show fuel + 5 = fuel + 4 + 1 from rfl, runProgramWithLoops_step hfetch3 hfaulted2]
  generalize hs3 : X86_64Instruction.step (add_r64_imm8 .rdx 0x30) s2 = s3
  have hrip3 : s3.rip = digitExtractLoopAddr + 9 := by
    rw [← hs3, step_add_r64_imm8]
    show s2.rip + 4 = digitExtractLoopAddr + 9
    rw [hrip2, UInt64.add_assoc]; rfl
  have hfault3 : s3.fault = none := by rw [← hs3, step_add_r64_imm8]; exact hfault2
  have hrdx3 : s3.gprs .rdx = (Stdlib.Fmt.byteOfDigit (n % 10)).toUInt64 := by
    rw [← hs3, step_add_r64_imm8]
    show s2.gprs .rdx + signExtend8To64 (0x30 : UInt8) = _
    rw [hrdx2, show signExtend8To64 (0x30 : UInt8) = 0x30 from rfl]
    exact digit_byte_toUInt64 (n % 10) (Nat.mod_lt n (by omega))
  have hrax3 : s3.gprs .rax = (n / 10).toUInt64 := by
    rw [← hs3, step_add_r64_imm8]; exact hrax2
  have hrcx3 : s3.gprs .rcx = c.toUInt64 := by rw [← hs3, step_add_r64_imm8]; exact hrcx2
  have hrsp3 : s3.rsp = s.rsp := by rw [← hs3, step_add_r64_imm8]; exact hrsp2
  have hmem3 : s3.memory = s.memory := by rw [← hs3, step_add_r64_imm8]; exact hmem2
  have hfaulted3 : s3.faulted = false := X86_64MachineState.faulted_of_fault_none hfault3
  -- step 4: push rdx
  have hfetch4 : instructionAtRip spike2Executable.load.rip spike2Instructions s3.rip =
      some (push_r64 .rdx) := by rw [hrip3]; exact iFetch_push
  rw [show fuel + 4 = fuel + 3 + 1 from rfl, runProgramWithLoops_step hfetch4 hfaulted3]
  generalize hs4 : X86_64Instruction.step (push_r64 .rdx) s3 = s4
  have hrip4 : s4.rip = digitExtractLoopAddr + 10 := by
    rw [← hs4, step_push_rdx]
    show s3.rip + 1 = digitExtractLoopAddr + 10
    rw [hrip3, UInt64.add_assoc]; rfl
  have hfault4 : s4.fault = none := by rw [← hs4, step_push_rdx]; exact hfault3
  have hrsp4 : s4.rsp = s3.rsp - 8 := by
    rw [← hs4, step_push_rdx]
    show (s3.push64 (s3.gprs .rdx)).rsp = s3.rsp - 8
    rfl
  have hpushed : X86_64Mem.read .w64 s4.rsp s4.memory = (Stdlib.Fmt.byteOfDigit (n % 10)).toUInt64 := by
    rw [← hs4, step_push_rdx]
    show X86_64Mem.read .w64 (s3.push64 (s3.gprs .rdx)).rsp (s3.push64 (s3.gprs .rdx)).memory =
      (Stdlib.Fmt.byteOfDigit (n % 10)).toUInt64
    rw [hrdx3]
    show X86_64Mem.read .w64 (s3.setGpr64 .rsp (s3.rsp - 8)).rsp
      (X86_64Mem.write .w64 (s3.setGpr64 .rsp (s3.rsp - 8)).rsp (Stdlib.Fmt.byteOfDigit (n%10)).toUInt64 s3.memory) =
      (Stdlib.Fmt.byteOfDigit (n % 10)).toUInt64
    exact X86_64Mem.read64_write64_same _ _ _
  have hrax4 : s4.gprs .rax = (n / 10).toUInt64 := by
    rw [← hs4, step_push_rdx]
    show (s3.push64 (s3.gprs .rdx)).gprs .rax = (n/10).toUInt64
    rw [show (s3.push64 (s3.gprs .rdx)).gprs .rax = s3.gprs .rax from rfl]
    exact hrax3
  have hrcx4 : s4.gprs .rcx = c.toUInt64 := by
    rw [← hs4, step_push_rdx]
    show (s3.push64 (s3.gprs .rdx)).gprs .rcx = c.toUInt64
    rw [show (s3.push64 (s3.gprs .rdx)).gprs .rcx = s3.gprs .rcx from rfl]
    exact hrcx3
  have hmemFrame4 : ∀ a : Address, a.toNat ≥ s.rsp.toNat →
      X86_64Mem.read .w8 a s4.memory = X86_64Mem.read .w8 a s.memory := by
    intro a ha
    rw [← hs4, step_push_rdx]
    show X86_64Mem.read .w8 a (s3.push64 (s3.gprs .rdx)).memory = X86_64Mem.read .w8 a s.memory
    rw [hrdx3]
    show X86_64Mem.read .w8 a
      (X86_64Mem.write .w64 (s3.setGpr64 .rsp (s3.rsp - 8)).rsp (Stdlib.Fmt.byteOfDigit (n%10)).toUInt64 s3.memory)
      = X86_64Mem.read .w8 a s.memory
    have hwaddr : (s3.setGpr64 .rsp (s3.rsp - 8)).rsp = s3.rsp - 8 := rfl
    rw [hwaddr]
    have hsub : (s.rsp - 8).toNat = s.rsp.toNat - 8 := by
      have hlt : s.rsp.toNat < 18446744073709551616 := s.rsp.toNat_lt_size
      have hdiv : (18446744073709551608 + s.rsp.toNat) / 18446744073709551616 = 1 := by omega
      simp [UInt64.toNat_sub, UInt64.size, hdiv]
      omega
    have hne : a.toNat < (s3.rsp - 8).toNat ∨ (s3.rsp-8).toNat + (MemWidth.w64).bytes ≤ a.toNat := by
      right
      rw [hrsp3, hsub]
      simp only [MemWidth.bytes]
      omega
    have hsub3 : (s3.rsp - 8).toNat = s.rsp.toNat - 8 := by rw [hrsp3]; exact hsub
    have hno : (s3.rsp - 8).toNat + (MemWidth.w64).bytes ≤ 18446744073709551616 := by
      have hb : (MemWidth.w64).bytes = 8 := rfl
      have h2 : (s3.rsp - 8).toNat ≤ 18446744073709551608 := by
        rw [hsub3]
        have hup : s.rsp.toNat < 18446744073709551616 := s.rsp.toNat_lt_size
        omega
      omega
    show (X86_64Mem.readByte
      (X86_64Mem.write .w64 (s3.rsp - 8) (Stdlib.Fmt.byteOfDigit (n % 10)).toUInt64 s3.memory) a).toUInt64
      = (X86_64Mem.readByte s.memory a).toUInt64
    rw [X86_64Mem.readByte_write_disjoint .w64 _ _ s3.memory a hno hne]
    rw [hmem3]
  have hregFrame4 : ∀ r : Reg64, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .rsp → s4.gprs r = s.gprs r := by
    intro r hra hrd hrc hrs
    rw [← hs4, step_push_rdx]
    show (s3.push64 (s3.gprs .rdx)).gprs r = s.gprs r
    rw [show (s3.push64 (s3.gprs .rdx)).gprs r = s3.gprs r from by
      show (s3.setGpr64 .rsp (s3.rsp - 8) |>.write64 _ _).gprs r = s3.gprs r
      simp [X86_64MachineState.write64, X86_64MachineState.setGpr64, hrs, Ne.symm hrs]]
    rw [show s3.gprs r = s2.gprs r from by
      rw [← hs3, step_add_r64_imm8]
      simp [X86_64MachineState.setGpr64, X86_64MachineState.setFlagsAdd64, hrd, Ne.symm hrd]]
    rw [show s2.gprs r = s1.gprs r from by
      rw [← hs2]
      show ((s1.setGpr64 .rax _).setGpr64 .rdx _).gprs r = s1.gprs r
      simp [X86_64MachineState.setGpr64, hrd, Ne.symm hrd, hra, Ne.symm hra]]
    rw [show s1.gprs r = s.gprs r from by
      rw [← hs1, step_xor_r32]
      simp [X86_64MachineState.setGpr32, X86_64MachineState.setFlagsLogic, reg32To64,
        hrd, Ne.symm hrd]]
  -- step 5: add rcx, 1
  have hfaulted4 : s4.faulted = false := X86_64MachineState.faulted_of_fault_none hfault4
  have hfetch5 : instructionAtRip spike2Executable.load.rip spike2Instructions s4.rip =
      some (add_r64_imm8 .rcx 1) := by rw [hrip4]; exact iFetch_addRcx
  rw [show fuel + 3 = fuel + 2 + 1 from rfl, runProgramWithLoops_step hfetch5 hfaulted4]
  generalize hs5 : X86_64Instruction.step (add_r64_imm8 .rcx 1) s4 = s5
  have hrip5 : s5.rip = digitExtractLoopAddr + 14 := by
    rw [← hs5, step_add_r64_imm8]
    show s4.rip + 4 = digitExtractLoopAddr + 14
    rw [hrip4, UInt64.add_assoc]; rfl
  have hfault5 : s5.fault = none := by rw [← hs5, step_add_r64_imm8]; exact hfault4
  have hrcx5 : s5.gprs .rcx = (c + 1).toUInt64 := by
    rw [← hs5, step_add_r64_imm8]
    show s4.gprs .rcx + signExtend8To64 (1 : UInt8) = (c + 1).toUInt64
    rw [hrcx4, show signExtend8To64 (1 : UInt8) = 1 from rfl]
    simp [Nat.toUInt64]
  have hrax5 : s5.gprs .rax = (n / 10).toUInt64 := by
    rw [← hs5, step_add_r64_imm8]; exact hrax4
  have hrsp5 : s5.rsp = s.rsp - 8 := by
    rw [← hs5, step_add_r64_imm8]
    show s4.rsp = s.rsp - 8
    rw [hrsp4, hrsp3]
  have hmemFrame5 : ∀ a : Address, a.toNat ≥ s.rsp.toNat →
      X86_64Mem.read .w8 a s5.memory = X86_64Mem.read .w8 a s.memory := by
    intro a ha; rw [← hs5, step_add_r64_imm8]; exact hmemFrame4 a ha
  have hpushed5 : X86_64Mem.read .w64 s5.rsp s5.memory = (Stdlib.Fmt.byteOfDigit (n % 10)).toUInt64 := by
    rw [← hs5, step_add_r64_imm8]; exact hpushed
  have hfaulted5 : s5.faulted = false := X86_64MachineState.faulted_of_fault_none hfault5
  -- step 6: cmp rax, 0
  have hfetch6 : instructionAtRip spike2Executable.load.rip spike2Instructions s5.rip =
      some (cmp_r64_imm8 .rax 0) := by rw [hrip5]; exact iFetch_cmpAx
  rw [show fuel + 2 = fuel + 1 + 1 from rfl, runProgramWithLoops_step hfetch6 hfaulted5]
  generalize hs6 : X86_64Instruction.step (cmp_r64_imm8 .rax 0) s5 = s6
  have hrip6 : s6.rip = digitExtractLoopAddr + 18 := by
    rw [← hs6, step_cmp_r64_imm8]
    show s5.rip + 4 = digitExtractLoopAddr + 18
    rw [hrip5, UInt64.add_assoc]; rfl
  have hfault6 : s6.fault = none := by rw [← hs6, step_cmp_r64_imm8]; exact hfault5
  have hzf6 : s6.zf = ((n / 10).toUInt64 == 0) := by
    have hz : s6.zf = (s5.setFlagsCmp64 (s5.gprs .rax) (signExtend8To64 (0 : UInt8))).zf := by
      rw [← hs6]; rfl
    rw [hz, show signExtend8To64 (0 : UInt8) = 0 from rfl, setFlagsCmp64_zero_zf, hrax5]
  have hrcx6 : s6.gprs .rcx = (c + 1).toUInt64 := by rw [← hs6, step_cmp_r64_imm8]; exact hrcx5
  have hrax6 : s6.gprs .rax = (n / 10).toUInt64 := by rw [← hs6, step_cmp_r64_imm8]; exact hrax5
  have hrsp6 : s6.rsp = s.rsp - 8 := by rw [← hs6, step_cmp_r64_imm8]; exact hrsp5
  have hmemFrame6 : ∀ a : Address, a.toNat ≥ s.rsp.toNat →
      X86_64Mem.read .w8 a s6.memory = X86_64Mem.read .w8 a s.memory := by
    intro a ha; rw [← hs6, step_cmp_r64_imm8]; exact hmemFrame5 a ha
  have hpushed6 : X86_64Mem.read .w64 s6.rsp s6.memory = (Stdlib.Fmt.byteOfDigit (n % 10)).toUInt64 := by
    rw [← hs6, step_cmp_r64_imm8]; exact hpushed5
  have hfaulted6 : s6.faulted = false := X86_64MachineState.faulted_of_fault_none hfault6
  -- step 7: jne (branches back to digitExtractLoopAddr if n/10 ≠ 0, else falls through to
  -- digitWriteLoopAddr)
  have hfetch7 : instructionAtRip spike2Executable.load.rip spike2Instructions s6.rip =
      some (jne_rel8 (Assembler.toDisp8 digitExtractLoopAddr digitWriteLoopAddr)) := by
    rw [hrip6]; exact iFetch_jneExtract
  have hnf7 : (X86_64Instruction.step
      (jne_rel8 (Assembler.toDisp8 digitExtractLoopAddr digitWriteLoopAddr)) s6).faulted = false := by
    rw [step_jne_rel8]; exact hfaulted6
  rw [show fuel + 1 = fuel + 0 + 1 from rfl, runProgramWithLoops_step hfetch7 hnf7]
  generalize hs7 : X86_64Instruction.step
    (jne_rel8 (Assembler.toDisp8 digitExtractLoopAddr digitWriteLoopAddr)) s6 = s7
  have hfault7 : s7.fault = none := by rw [← hs7, step_jne_rel8]; exact hfault6
  have hrcx7 : s7.gprs .rcx = (c + 1).toUInt64 := by rw [← hs7, step_jne_rel8]; exact hrcx6
  have hrax7 : s7.gprs .rax = (n / 10).toUInt64 := by rw [← hs7, step_jne_rel8]; exact hrax6
  have hrsp7 : s7.rsp = s.rsp - 8 := by rw [← hs7, step_jne_rel8]; exact hrsp6
  have hmemFrame7 : ∀ a : Address, a.toNat ≥ s.rsp.toNat →
      X86_64Mem.read .w8 a s7.memory = X86_64Mem.read .w8 a s.memory := by
    intro a ha; rw [← hs7, step_jne_rel8]; exact hmemFrame6 a ha
  have hpushed7 : X86_64Mem.read .w64 s7.rsp s7.memory = (Stdlib.Fmt.byteOfDigit (n % 10)).toUInt64 := by
    rw [← hs7, step_jne_rel8]; exact hpushed6
  have hregFrame7 : ∀ r : Reg64, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .rsp → s7.gprs r = s.gprs r := by
    intro r hra hrd hrc hrs
    rw [← hs7, step_jne_rel8]
    show s6.gprs r = s.gprs r
    rw [show s6.gprs r = s5.gprs r from by rw [← hs6, step_cmp_r64_imm8]; rfl]
    rw [show s5.gprs r = s4.gprs r from by
      rw [← hs5, step_add_r64_imm8]
      simp [X86_64MachineState.setGpr64, X86_64MachineState.setFlagsAdd64, hrc, Ne.symm hrc]]
    exact hregFrame4 r hra hrd hrc hrs
  have hrip7 : s7.rip = if n / 10 = 0 then digitWriteLoopAddr else digitExtractLoopAddr := by
    rw [← hs7, step_jne_rel8]
    show (if !s6.zf then s6.rip + 2 + signExtend8To64 (Assembler.toDisp8 digitExtractLoopAddr
      digitWriteLoopAddr) else s6.rip + 2) = _
    rw [hzf6, hrip6]
    by_cases hz : n / 10 = 0
    · rw [if_pos hz, hz]
      show (if !((0 : UInt64) == 0) then _ else digitExtractLoopAddr + 18 + 2) = digitWriteLoopAddr
      rw [digitWriteLoopAddr_eq, digitExtractLoopAddr_eq]; decide
    · rw [if_neg hz]
      have hne0 : ((n / 10).toUInt64 == (0 : UInt64)) = false := by
        have hpos : n / 10 ≠ 0 := hz
        have hbnd : n / 10 < 18446744073709551616 := by omega
        simp only [beq_eq_false_iff_ne, ne_eq, ← UInt64.toNat_inj]
        simp [Nat.toUInt64, hbnd]
        omega
      rw [hne0]
      show digitExtractLoopAddr + 18 + 2 +
        signExtend8To64 (Assembler.toDisp8 digitExtractLoopAddr digitWriteLoopAddr) =
        digitExtractLoopAddr
      exact jneExtract_target
  exact ⟨s7, rfl, hrip7, hrax7, hrcx7, hrsp7, hfault7, hpushed7, hmemFrame7, hregFrame7⟩

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- **The extract-loop induction.** Starting at `digitExtractLoopAddr` with `rax = n`, `r10 = 10`,
    `rcx = c`, running exactly `7 * (digits n).length` more steps reaches `digitWriteLoopAddr` with
    `rax = 0`, `rcx` advanced by `(digits n).length`, `rsp` decremented by `8 * (digits n).length`,
    the newly-opened stack region holding `formatDecimal n` (`StackHolds`), and -- the frame
    conjunct every recursive step needs to hand its caller -- every byte at or above the ENTRY
    `rsp`, and every register besides `rax`/`rdx`/`rcx`/`rsp`, exactly as it was on entry (the loop
    body's 7 instructions never touch anything else). Proved by strong induction on `n`
    (`Nat.strongRecOn`, `n / 10 < n` whenever `n ≥ 10` -- `Stdlib.Fmt.digits`'s own termination
    measure), composing exactly one iteration's step facts (`digitExtractLoop_oneIter`) with the
    recursive call via `StackHolds_append`, never executing the loop concretely. -/
theorem digitExtractLoop_run (n : Nat) (hn : n < 18446744073709551616) :
    ∀ (c fuel : Nat) (s : X86_64MachineState),
    s.rip = digitExtractLoopAddr →
    s.gprs .rax = n.toUInt64 →
    s.gprs .r10 = 10 →
    s.gprs .rcx = c.toUInt64 →
    s.fault = none →
    8 * (Stdlib.Fmt.digits n).length ≤ s.rsp.toNat →
    s.rsp.toNat < 18446744073709551608 →
    ∃ s',
      runProgramWithLoops spike2Executable.load.rip spike2Instructions
          (fuel + 7 * (Stdlib.Fmt.digits n).length) s =
        runProgramWithLoops spike2Executable.load.rip spike2Instructions fuel s' ∧
      s'.rip = digitWriteLoopAddr ∧
      s'.gprs .rax = 0 ∧
      s'.gprs .rcx = (c + (Stdlib.Fmt.digits n).length).toUInt64 ∧
      s'.rsp = s.rsp - 8 * (Stdlib.Fmt.digits n).length.toUInt64 ∧
      s'.fault = none ∧
      StackHolds s'.memory s'.rsp (Stdlib.Fmt.formatDecimal n) ∧
      (∀ a : Address, a.toNat ≥ s.rsp.toNat →
        X86_64Mem.read .w8 a s'.memory = X86_64Mem.read .w8 a s.memory) ∧
      (∀ r : Reg64, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .rsp → s'.gprs r = s.gprs r) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro c fuel s hrip hrax hr10 hrcx hfault hrspBound hrspTop
  have hrspBound8 : 8 ≤ s.rsp.toNat := by
    have h1 : 1 ≤ (Stdlib.Fmt.digits n).length := by
      have := Stdlib.Fmt.digits_ne_nil n
      cases hd : Stdlib.Fmt.digits n with
      | nil => exact absurd hd this
      | cons _ _ => simp [hd]
    omega
  by_cases hz : n / 10 = 0
  · -- base case: n < 10, one iteration suffices
    obtain ⟨s1, heq1, hrip1, hrax1, hrcx1, hrsp1, hfault1, hpushed1, hframe1, hregframe1⟩ :=
      digitExtractLoop_oneIter n c fuel s hrip hrax hn hr10 hrcx hfault hrspBound8
    have hn10 : n < 10 := by omega
    have hdig : Stdlib.Fmt.digits n = [n] := Stdlib.Fmt.digits_single n hn10
    have hfmt : Stdlib.Fmt.formatDecimal n = [Stdlib.Fmt.byteOfDigit n] := by
      unfold Stdlib.Fmt.formatDecimal; rw [hdig]; rfl
    have hmod : n % 10 = n := Nat.mod_eq_of_lt hn10
    rw [if_pos hz] at hrip1
    refine ⟨s1, ?_, hrip1, ?_, ?_, ?_, hfault1, ?_, hframe1, hregframe1⟩
    · rw [hdig]; simpa using heq1
    · rw [hz] at hrax1; simpa using hrax1
    · rw [hdig]; simpa using hrcx1
    · rw [hdig]; simpa using hrsp1
    · rw [hfmt]
      show StackHolds s1.memory s1.rsp [Stdlib.Fmt.byteOfDigit n]
      rw [hmod] at hpushed1
      exact ⟨hpushed1, trivial⟩
  · -- step case: recurse on n / 10 < n
    have hn0 : n ≠ 0 := by rintro rfl; simp at hz
    have hlt : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
    have hn10bound : n / 10 < 18446744073709551616 := by omega
    have hdig : Stdlib.Fmt.digits n = Stdlib.Fmt.digits (n / 10) ++ [n % 10] := by
      generalize hd : Stdlib.Fmt.digits (n / 10) = d
      unfold Stdlib.Fmt.digits
      rw [dif_neg (show ¬ n < 10 by omega), hd]
    have hlen : (Stdlib.Fmt.digits n).length = (Stdlib.Fmt.digits (n / 10)).length + 1 := by
      rw [hdig]; simp
    obtain ⟨s1, heq1, hrip1, hrax1, hrcx1, hrsp1, hfault1, hpushed1, hframe1, hregframe1⟩ :=
      digitExtractLoop_oneIter n c (fuel + 7 * (Stdlib.Fmt.digits (n / 10)).length) s
        hrip hrax hn hr10 hrcx hfault hrspBound8
    have hr10_1 : s1.gprs .r10 = 10 := by
      rw [hregframe1 .r10 (by decide) (by decide) (by decide) (by decide)]; exact hr10
    rw [if_neg hz] at hrip1
    have hrspBound' : 8 * (Stdlib.Fmt.digits (n / 10)).length ≤ s1.rsp.toNat := by
      rw [hrsp1]
      have : 8 * (Stdlib.Fmt.digits n).length ≤ s.rsp.toNat := hrspBound
      have hs8 : (s.rsp - 8).toNat = s.rsp.toNat - 8 := by
        have hb : (8:Nat) ≤ s.rsp.toNat := hrspBound8
        have hup : s.rsp.toNat < 18446744073709551616 := s.rsp.toNat_lt_size
        simp [UInt64.toNat_sub, UInt64.size]
        omega
      rw [hs8]
      omega
    have hrspTop' : s1.rsp.toNat < 18446744073709551608 := by
      rw [hrsp1]
      have hs8 : (s.rsp - 8).toNat = s.rsp.toNat - 8 := by
        have hb : (8:Nat) ≤ s.rsp.toNat := hrspBound8
        have hup : s.rsp.toNat < 18446744073709551616 := s.rsp.toNat_lt_size
        simp [UInt64.toNat_sub, UInt64.size]
        omega
      rw [hs8]; omega
    obtain ⟨s', heq', hrip', hrax', hrcx', hrsp', hfault', hpushed', hframe', hregframe'⟩ :=
      ih (n / 10) hlt hn10bound (c + 1) fuel s1 hrip1 hrax1 hr10_1 hrcx1 hfault1 hrspBound' hrspTop'
    refine ⟨s', ?_, hrip', ?_, ?_, ?_, hfault', ?_, ?_, ?_⟩
    · rw [hlen, show fuel + 7 * ((Stdlib.Fmt.digits (n / 10)).length + 1)
        = (fuel + 7 * (Stdlib.Fmt.digits (n / 10)).length) + 7 from by omega, heq1, heq']
    · exact hrax'
    · rw [hlen]
      show s'.gprs .rcx = (c + ((Stdlib.Fmt.digits (n / 10)).length + 1)).toUInt64
      rw [show c + ((Stdlib.Fmt.digits (n / 10)).length + 1) = (c + 1) + (Stdlib.Fmt.digits (n / 10)).length
        from by omega]
      exact hrcx'
    · rw [hlen]
      show s'.rsp = s.rsp - 8 * ((Stdlib.Fmt.digits (n / 10)).length + 1 : Nat).toUInt64
      rw [hrsp', hrsp1]
      have hlenCast : ((Stdlib.Fmt.digits (n / 10)).length + 1 : Nat).toUInt64
          = (Stdlib.Fmt.digits (n / 10)).length.toUInt64 + 1 := by
        simp [Nat.toUInt64]
      rw [hlenCast, UInt64.mul_add, UInt64.mul_one, UInt64.sub_sub,
        UInt64.add_comm (8 : UInt64) (8 * (Stdlib.Fmt.digits (n / 10)).length.toUInt64)]
    · show StackHolds s'.memory s'.rsp (Stdlib.Fmt.formatDecimal n)
      unfold Stdlib.Fmt.formatDecimal
      rw [hdig, List.map_append]
      show StackHolds s'.memory s'.rsp
        ((Stdlib.Fmt.digits (n / 10)).map Stdlib.Fmt.byteOfDigit ++ [Stdlib.Fmt.byteOfDigit (n % 10)])
      rw [StackHolds_append]
      refine ⟨?_, ?_⟩
      · exact hpushed'
      · have hlen' : ((Stdlib.Fmt.digits (n / 10)).map Stdlib.Fmt.byteOfDigit).length
            = (Stdlib.Fmt.digits (n / 10)).length := by simp
        rw [hlen']
        have haddr : s'.rsp + 8 * (Stdlib.Fmt.digits (n / 10)).length.toUInt64 = s1.rsp := by
          rw [hrsp', UInt64.sub_add_cancel]
        rw [haddr]
        have hread64 : X86_64Mem.read .w64 s1.rsp s'.memory = X86_64Mem.read .w64 s1.rsp s1.memory := by
          apply X86_64Mem.read_congr'
          intro k hk
          apply hframe'
          have hk8 : k < 8 := by simpa [MemWidth.bytes] using hk
          have hup : s1.rsp.toNat < 18446744073709551608 := hrspTop'
          have hadd : (s1.rsp + k.toUInt64).toNat = s1.rsp.toNat + k := by
            simp [UInt64.toNat_add, UInt64.size, Nat.toUInt64]
            omega
          omega
        exact ⟨hread64.trans hpushed1, trivial⟩
    · intro a ha
      have haS1 : a.toNat ≥ s1.rsp.toNat := by
        rw [hrsp1]
        have hs8 : (s.rsp - 8).toNat = s.rsp.toNat - 8 := by
          have hb : (8 : Nat) ≤ s.rsp.toNat := hrspBound8
          have hup : s.rsp.toNat < 18446744073709551616 := s.rsp.toNat_lt_size
          simp [UInt64.toNat_sub, UInt64.size]; omega
        rw [hs8]; omega
      rw [hframe' a haS1, hframe1 a ha]
    · intro r hra hrd hrc hrs
      rw [hregframe' r hra hrd hrc hrs, hregframe1 r hra hrd hrc hrs]

end Spikes.Spike2Fibonacci.Windows
