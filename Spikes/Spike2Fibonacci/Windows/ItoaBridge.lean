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

/-- Bridges `digitWriteLoopAddr + <offset>` (the relational form used by the write-loop
    induction) to the `cumLen`-position form `iFetch_movMem`/`iFetch_addRdi`/`iFetch_subRcx`/
    `iFetch_jneWrite` are stated against. -/
theorem writeMovAddr_eq :
    digitWriteLoopAddr + 1 = spike2Executable.load.rip + (cumLen (spike2Instructions.take 51) : Nat).toUInt64 := by
  rw [digitWriteLoopAddr_eq]; decide

theorem writeAddRdiAddr_eq :
    digitWriteLoopAddr + 3 = spike2Executable.load.rip + (cumLen (spike2Instructions.take 52) : Nat).toUInt64 := by
  rw [digitWriteLoopAddr_eq]; decide

theorem writeSubRcxAddr_eq :
    digitWriteLoopAddr + 7 = spike2Executable.load.rip + (cumLen (spike2Instructions.take 53) : Nat).toUInt64 := by
  rw [digitWriteLoopAddr_eq]; decide

theorem writeJneAddr_eq :
    digitWriteLoopAddr + 11 = spike2Executable.load.rip + (cumLen (spike2Instructions.take 54) : Nat).toUInt64 := by
  rw [digitWriteLoopAddr_eq]; decide

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

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- `BufHolds mem start L` says the byte-granular slots `start, start+1, start+2, ...` hold
    exactly `L` -- the `digit_write_loop` output-buffer counterpart of `StackHolds` (step 1,
    width `.w8`, instead of step 8, width `.w64`). -/
def BufHolds (mem : X86_64Memory) (start : Address) : List UInt8 → Prop
  | [] => True
  | b :: rest => X86_64Mem.read .w8 start mem = b.toUInt64 ∧ BufHolds mem (start + 1) rest

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
theorem BufHolds_append (mem : X86_64Memory) (start : Address) (L1 : List UInt8) :
    ∀ L2 : List UInt8,
      BufHolds mem start (L1 ++ L2) ↔
        BufHolds mem start L1 ∧ BufHolds mem (start + L1.length.toUInt64) L2 := by
  induction L1 generalizing start with
  | nil => intro L2; simp [BufHolds]
  | cons b rest ih =>
    intro L2
    simp only [List.cons_append, BufHolds]
    rw [ih]
    have haddr : start + (b :: rest).length.toUInt64 = start + 1 + rest.length.toUInt64 := by
      have hlen : (b :: rest).length.toUInt64 = rest.length.toUInt64 + 1 := by
        simp only [List.length_cons]
        simp [Nat.toUInt64]
      rw [hlen, UInt64.add_assoc,
        UInt64.add_comm (rest.length.toUInt64) 1, ← UInt64.add_assoc]
    rw [haddr, and_assoc]

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- A single-byte write far enough below an address (`buf` at or above the entire `.w64`-aligned
    span `[top, top + 8*L.length)`) never disturbs what `StackHolds` reads there -- the fact
    `digit_write_loop`'s single `mov [rdi], dl` byte write needs to leave the still-unpopped
    stack region readable exactly as before. -/
theorem StackHolds_write8_disjoint (mem : X86_64Memory) (top buf : Address) (byte : UInt64)
    (L : List UInt8) (hdisj : buf.toNat ≥ top.toNat + 8 * L.length) :
    StackHolds (X86_64Mem.write .w8 buf byte mem) top L = StackHolds mem top L := by
  induction L generalizing top with
  | nil => rfl
  | cons c rest ih =>
    have hlen : (c :: rest).length = rest.length + 1 := rfl
    rw [hlen] at hdisj
    have hbufBound : buf.toNat < 18446744073709551616 := buf.toNat_lt_size
    have htopBound8 : top.toNat + 8 < 18446744073709551616 := by omega
    show (X86_64Mem.read .w64 top (X86_64Mem.write .w8 buf byte mem) = c.toUInt64 ∧
        StackHolds (X86_64Mem.write .w8 buf byte mem) (top + 8) rest) =
      (X86_64Mem.read .w64 top mem = c.toUInt64 ∧ StackHolds mem (top + 8) rest)
    have hread : X86_64Mem.read .w64 top (X86_64Mem.write .w8 buf byte mem) =
        X86_64Mem.read .w64 top mem := by
      apply X86_64Mem.read_congr
      intro k hk
      have hk8 : k < 8 := by simpa [MemWidth.bytes] using hk
      have hadd : (top + k.toUInt64).toNat = top.toNat + k := by
        have hkbound : k < 18446744073709551616 := by omega
        simp [UInt64.toNat_add, UInt64.size, Nat.toUInt64]
        omega
      apply X86_64Mem.readByte_write_disjoint .w8 buf byte mem (top + k.toUInt64)
        (by simp only [MemWidth.bytes]; omega)
      left
      omega
    have htopAdd : (top + (8 : UInt64)).toNat = top.toNat + 8 := by
      simp [UInt64.toNat_add, UInt64.size, Nat.toUInt64]
      omega
    rw [hread, ih (top + 8) (by omega)]

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

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- `digit_write_loop`'s branch test (`sub rcx, 1` immediately followed by `jne`, no separate
    `cmp`, unlike `fibIterInstructions`'s loop) needs ZF after subtracting `1`, not `0` --
    `setFlagsCmp64_zero_zf` (`Windows/LoopInvariant.lean`) doesn't cover this. `setFlagsSub64` is
    definitionally `setFlagsCmp64` (`Registers.lean`), so the same bit-6-isolation lemma set
    applies; the only new piece is including `if_bit6_zero` for CF's own `if a < 1 then ... else
    ...` branch (bit 0, trivially bit-6-transparent either way via `decide`) instead of
    eliminating that case split the way the `b = 0` specialization does -- CF's `a < 1` truth
    value is never needed. -/
theorem setFlagsSub64_one_zf (s : X86_64MachineState) (a : UInt64) :
    (s.setFlagsSub64 a 1).zf = (a == 1) := by
  unfold X86_64MachineState.setFlagsSub64 X86_64MachineState.setFlagsCmp64 X86_64MachineState.zf
  dsimp only
  generalize hcf : (if a < (1 : UInt64) then (1 : UInt64) <<< 0 else 0) = cf
  have hcfbit6 : cf &&& ((1 : UInt64) <<< 6) = 0 := by
    rw [← hcf]; split <;> decide
  simp only [and_or_distrib, preserved_bit6, computeParity8_bit6, computeAuxCarry_bit6, hcfbit6,
    if_bit6_zero _ ((1 : UInt64) <<< 7) (by decide), if_bit6_zero _ ((1 : UInt64) <<< 11) (by decide),
    UInt64.zero_or, UInt64.or_zero]
  by_cases h : a = 1
  · subst h; decide
  · have hne : a - 1 ≠ (0 : UInt64) := by
      intro hcontra
      apply h
      have := congrArg (· + (1 : UInt64)) hcontra
      simpa [UInt64.sub_add_cancel] using this
    simp [hne, h]

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

/-
## Part 5: `digit_write_loop`'s pointwise closed-form characterization

Content-agnostic in the popped list (never tied to digit extraction specifically): given the
stack holds an arbitrary `b :: rest`, `rcx = rest.length + 1`, and `rdi = buf`, one iteration
pops `b`, writes it to `[buf]`, advances `rdi`/`rsp`, decrements `rcx`, and continues (or falls
through to `digitWriteLoopAddrEnd` when `rest = []`) -- a decrementing-counter loop, driven by
`sub rcx, 1`'s own flags (no separate `cmp`, unlike `fibIterInstructions`'s loop), hence
`setFlagsSub64_one_zf` above.
-/

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- **One iteration of `digit_write_loop`.** -/
theorem digitWriteLoop_oneIter (b : UInt8) (rest : List UInt8) (buf : Address) (fuel : Nat)
    (s : X86_64MachineState)
    (hrip : s.rip = digitWriteLoopAddr)
    (hstack : StackHolds s.memory s.rsp (b :: rest))
    (hrcx : s.gprs .rcx = (rest.length + 1 : Nat).toUInt64)
    (hrdi : s.gprs .rdi = buf)
    (hdisj : buf.toNat ≥ s.rsp.toNat + 8 * (rest.length + 1))
    (hfault : s.fault = none) :
    ∃ s1,
      runProgramWithLoops spike2Executable.load.rip spike2Instructions (fuel + 5) s =
        runProgramWithLoops spike2Executable.load.rip spike2Instructions fuel s1 ∧
      s1.rip = (if rest.length = 0 then digitWriteLoopAddrEnd else digitWriteLoopAddr) ∧
      s1.gprs .rcx = rest.length.toUInt64 ∧
      s1.gprs .rdi = buf + 1 ∧
      s1.rsp = s.rsp + 8 ∧
      s1.fault = none ∧
      X86_64Mem.read .w8 buf s1.memory = b.toUInt64 ∧
      StackHolds s1.memory s1.rsp rest ∧
      (∀ a : Address, a ≠ buf → X86_64Mem.read .w8 a s1.memory = X86_64Mem.read .w8 a s.memory) ∧
      (∀ r : Reg64, r ≠ .rdx → r ≠ .rdi → r ≠ .rcx → r ≠ .rsp → s1.gprs r = s.gprs r) := by
  have hfaulted0 : s.faulted = false := X86_64MachineState.faulted_of_fault_none hfault
  -- step 1: pop rdx
  have hfetch1 : instructionAtRip spike2Executable.load.rip spike2Instructions s.rip =
      some (pop_r64 .rdx) := by rw [hrip]; exact iFetch_pop
  rw [show fuel + 5 = fuel + 4 + 1 from rfl, runProgramWithLoops_step hfetch1 hfaulted0]
  generalize hs1 : X86_64Instruction.step (pop_r64 .rdx) s = s1
  have hrip1 : s1.rip = digitWriteLoopAddr + 1 := by
    rw [← hs1, step_pop_rdx, hrip]
  have hfault1 : s1.fault = none := by rw [← hs1, step_pop_rdx]; exact hfault
  have hrdx1 : s1.gprs .rdx = b.toUInt64 := by
    rw [← hs1, step_pop_rdx]
    show s.pop64.1 = b.toUInt64
    exact hstack.1
  have hrsp1 : s1.rsp = s.rsp + 8 := by
    rw [← hs1, step_pop_rdx]
    show (s.pop64.2.setGpr64 .rdx s.pop64.1).rsp = s.rsp + 8
    rfl
  have hrdi1 : s1.gprs .rdi = buf := by
    rw [← hs1, step_pop_rdx]
    show (s.pop64.2.setGpr64 .rdx s.pop64.1).gprs .rdi = buf
    exact hrdi
  have hrcx1 : s1.gprs .rcx = (rest.length + 1 : Nat).toUInt64 := by
    rw [← hs1, step_pop_rdx]
    show (s.pop64.2.setGpr64 .rdx s.pop64.1).gprs .rcx = _
    exact hrcx
  have hstackRest1 : StackHolds s1.memory s1.rsp rest := by
    rw [← hs1, step_pop_rdx]
    show StackHolds (s.pop64.2.setGpr64 .rdx s.pop64.1).memory
      (s.pop64.2.setGpr64 .rdx s.pop64.1).rsp rest
    exact hstack.2
  have hmemFrame1 : ∀ a : Address, a ≠ buf →
      X86_64Mem.read .w8 a s1.memory = X86_64Mem.read .w8 a s.memory := by
    intro a _; rw [← hs1, step_pop_rdx]; rfl
  have hregFrame1 : ∀ r : Reg64, r ≠ .rdx → r ≠ .rdi → r ≠ .rcx → r ≠ .rsp →
      s1.gprs r = s.gprs r := by
    intro r hrdx' _ _ hrsp'
    rw [← hs1, step_pop_rdx]
    show (s.pop64.2.setGpr64 .rdx s.pop64.1).gprs r = s.gprs r
    simp [X86_64MachineState.setGpr64, hrdx', X86_64MachineState.pop64, hrsp']
  have hfaulted1 : s1.faulted = false := X86_64MachineState.faulted_of_fault_none hfault1
  -- step 2: mov [rdi], dl
  have hfetch2 : instructionAtRip spike2Executable.load.rip spike2Instructions s1.rip =
      some (mov_mem8 .rdi .rdx) := by
    rw [hrip1, writeMovAddr_eq]; exact iFetch_movMem
  rw [show fuel + 4 = fuel + 3 + 1 from rfl, runProgramWithLoops_step hfetch2 hfaulted1]
  generalize hs2 : X86_64Instruction.step (mov_mem8 .rdi .rdx) s1 = s2
  have hrip2 : s2.rip = digitWriteLoopAddr + 3 := by
    rw [← hs2, step_mov_mem8_rdi_rdx]
    show s1.rip + 2 = digitWriteLoopAddr + 3
    rw [hrip1, UInt64.add_assoc]; rfl
  have hfault2 : s2.fault = none := by rw [← hs2, step_mov_mem8_rdi_rdx]; exact hfault1
  have hwritten2 : X86_64Mem.read .w8 buf s2.memory = b.toUInt64 := by
    rw [← hs2, step_mov_mem8_rdi_rdx]
    show X86_64Mem.read .w8 buf (s1.write8 (s1.gprs .rdi) (s1.gprs .rdx).toUInt8).memory = b.toUInt64
    rw [hrdi1, hrdx1]
    show X86_64Mem.read .w8 buf (s1.write8 buf (b.toUInt64.toUInt8)).memory = b.toUInt64
    show (X86_64Mem.readByte (X86_64Mem.write .w8 buf (b.toUInt64.toUInt8).toUInt64 s1.memory) buf).toUInt64
      = b.toUInt64
    congr 1
    simp only [X86_64Mem.write, X86_64Mem.readByte_writeByte_same, UInt8.toUInt8_toUInt64]
  have hrdi2 : s2.gprs .rdi = buf := by
    rw [← hs2, step_mov_mem8_rdi_rdx]
    show (s1.write8 (s1.gprs .rdi) (s1.gprs .rdx).toUInt8).gprs .rdi = buf
    exact hrdi1
  have hrcx2 : s2.gprs .rcx = (rest.length + 1 : Nat).toUInt64 := by
    rw [← hs2, step_mov_mem8_rdi_rdx]
    show (s1.write8 (s1.gprs .rdi) (s1.gprs .rdx).toUInt8).gprs .rcx = _
    exact hrcx1
  have hrsp2 : s2.rsp = s.rsp + 8 := by
    rw [← hs2, step_mov_mem8_rdi_rdx]
    show (s1.write8 (s1.gprs .rdi) (s1.gprs .rdx).toUInt8).rsp = s.rsp + 8
    rw [show (s1.write8 (s1.gprs .rdi) (s1.gprs .rdx).toUInt8).rsp = s1.rsp from rfl]
    exact hrsp1
  have hstackRest2 : StackHolds s2.memory s2.rsp rest := by
    rw [← hs2, step_mov_mem8_rdi_rdx]
    show StackHolds (s1.write8 (s1.gprs .rdi) (s1.gprs .rdx).toUInt8).memory
      (s1.write8 (s1.gprs .rdi) (s1.gprs .rdx).toUInt8).rsp rest
    rw [show (s1.write8 (s1.gprs .rdi) (s1.gprs .rdx).toUInt8).rsp = s1.rsp from rfl]
    show StackHolds
      (X86_64Mem.write .w8 (s1.gprs .rdi) ((s1.gprs .rdx).toUInt8).toUInt64 s1.memory) s1.rsp rest
    rw [hrdi1, hrdx1]
    have hdisj1 : buf.toNat ≥ s1.rsp.toNat + 8 * rest.length := by
      have hbufBound : buf.toNat < 18446744073709551616 := buf.toNat_lt_size
      have hadd : s1.rsp.toNat = s.rsp.toNat + 8 := by
        rw [hrsp1]
        have hup : s.rsp.toNat < 18446744073709551608 := by omega
        simp [UInt64.toNat_add, UInt64.size, Nat.toUInt64]
        omega
      omega
    rw [StackHolds_write8_disjoint s1.memory s1.rsp buf (((b.toUInt64).toUInt8).toUInt64) rest hdisj1]
    exact hstackRest1
  have hregFrame2 : ∀ r : Reg64, r ≠ .rdx → r ≠ .rdi → r ≠ .rcx → r ≠ .rsp →
      s2.gprs r = s.gprs r := by
    intro r hrdx' hrdi' hrcx' hrsp'
    rw [← hs2, step_mov_mem8_rdi_rdx]
    show (s1.write8 (s1.gprs .rdi) (s1.gprs .rdx).toUInt8).gprs r = s.gprs r
    rw [show (s1.write8 (s1.gprs .rdi) (s1.gprs .rdx).toUInt8).gprs r = s1.gprs r from rfl]
    exact hregFrame1 r hrdx' hrdi' hrcx' hrsp'
  have hfaulted2 : s2.faulted = false := X86_64MachineState.faulted_of_fault_none hfault2
  -- step 3: add rdi, 1
  have hfetch3 : instructionAtRip spike2Executable.load.rip spike2Instructions s2.rip =
      some (add_r64_imm8 .rdi 1) := by
    rw [hrip2, writeAddRdiAddr_eq]; exact iFetch_addRdi
  rw [show fuel + 3 = fuel + 2 + 1 from rfl, runProgramWithLoops_step hfetch3 hfaulted2]
  generalize hs3 : X86_64Instruction.step (add_r64_imm8 .rdi 1) s2 = s3
  have hrip3 : s3.rip = digitWriteLoopAddr + 7 := by
    rw [← hs3, step_add_r64_imm8]
    show s2.rip + 4 = digitWriteLoopAddr + 7
    rw [hrip2, UInt64.add_assoc]; rfl
  have hfault3 : s3.fault = none := by rw [← hs3, step_add_r64_imm8]; exact hfault2
  have hrdi3 : s3.gprs .rdi = buf + 1 := by
    rw [← hs3, step_add_r64_imm8]
    show s2.gprs .rdi + signExtend8To64 (1 : UInt8) = buf + 1
    rw [hrdi2, show signExtend8To64 (1 : UInt8) = 1 from rfl]
  have hrcx3 : s3.gprs .rcx = (rest.length + 1 : Nat).toUInt64 := by
    rw [← hs3, step_add_r64_imm8]; exact hrcx2
  have hrsp3 : s3.rsp = s.rsp + 8 := by rw [← hs3, step_add_r64_imm8]; exact hrsp2
  have hwritten3 : X86_64Mem.read .w8 buf s3.memory = b.toUInt64 := by
    rw [← hs3, step_add_r64_imm8]; exact hwritten2
  have hstackRest3 : StackHolds s3.memory s3.rsp rest := by
    rw [← hs3, step_add_r64_imm8]; exact hstackRest2
  have hregFrame3 : ∀ r : Reg64, r ≠ .rdx → r ≠ .rdi → r ≠ .rcx → r ≠ .rsp →
      s3.gprs r = s.gprs r := by
    intro r hrdx' hrdi' hrcx' hrsp'
    rw [← hs3, step_add_r64_imm8]
    show (s2.setGpr64 .rdi (s2.gprs .rdi + signExtend8To64 (1:UInt8))).gprs r = s.gprs r
    rw [show (s2.setGpr64 .rdi (s2.gprs .rdi + signExtend8To64 (1:UInt8))).gprs r = s2.gprs r
      from by simp [X86_64MachineState.setGpr64, hrdi']]
    exact hregFrame2 r hrdx' hrdi' hrcx' hrsp'
  have hfaulted3 : s3.faulted = false := X86_64MachineState.faulted_of_fault_none hfault3
  -- step 4: sub rcx, 1
  have hfetch4 : instructionAtRip spike2Executable.load.rip spike2Instructions s3.rip =
      some (sub_r64_imm8 .rcx 1) := by
    rw [hrip3, writeSubRcxAddr_eq]; exact iFetch_subRcx
  rw [show fuel + 2 = fuel + 1 + 1 from rfl, runProgramWithLoops_step hfetch4 hfaulted3]
  generalize hs4 : X86_64Instruction.step (sub_r64_imm8 .rcx 1) s3 = s4
  have hrip4 : s4.rip = digitWriteLoopAddr + 11 := by
    rw [← hs4, step_sub_r64_imm8]
    show s3.rip + 4 = digitWriteLoopAddr + 11
    rw [hrip3, UInt64.add_assoc]; rfl
  have hfault4 : s4.fault = none := by rw [← hs4, step_sub_r64_imm8]; exact hfault3
  have hrcx4 : s4.gprs .rcx = rest.length.toUInt64 := by
    rw [← hs4, step_sub_r64_imm8]
    show s3.gprs .rcx - signExtend8To64 (1 : UInt8) = rest.length.toUInt64
    rw [hrcx3, show signExtend8To64 (1 : UInt8) = 1 from rfl]
    simp [Nat.toUInt64]
  have hzf4 : s4.zf = ((rest.length + 1 : Nat).toUInt64 == 1) := by
    have hz : s4.zf = (s3.setFlagsSub64 (s3.gprs .rcx) (signExtend8To64 (1 : UInt8))).zf := by
      rw [← hs4]; rfl
    rw [hz, show signExtend8To64 (1 : UInt8) = 1 from rfl, setFlagsSub64_one_zf, hrcx3]
  have hrdi4 : s4.gprs .rdi = buf + 1 := by rw [← hs4, step_sub_r64_imm8]; exact hrdi3
  have hrsp4 : s4.rsp = s.rsp + 8 := by rw [← hs4, step_sub_r64_imm8]; exact hrsp3
  have hwritten4 : X86_64Mem.read .w8 buf s4.memory = b.toUInt64 := by
    rw [← hs4, step_sub_r64_imm8]; exact hwritten3
  have hstackRest4 : StackHolds s4.memory s4.rsp rest := by
    rw [← hs4, step_sub_r64_imm8]; exact hstackRest3
  have hregFrame4 : ∀ r : Reg64, r ≠ .rdx → r ≠ .rdi → r ≠ .rcx → r ≠ .rsp →
      s4.gprs r = s.gprs r := by
    intro r hrdx' hrdi' hrcx' hrsp'
    rw [← hs4, step_sub_r64_imm8]
    show (s3.setGpr64 .rcx (s3.gprs .rcx - signExtend8To64 (1:UInt8))).gprs r = s.gprs r
    rw [show (s3.setGpr64 .rcx (s3.gprs .rcx - signExtend8To64 (1:UInt8))).gprs r = s3.gprs r
      from by simp [X86_64MachineState.setGpr64, hrcx']]
    exact hregFrame3 r hrdx' hrdi' hrcx' hrsp'
  have hfaulted4 : s4.faulted = false := X86_64MachineState.faulted_of_fault_none hfault4
  -- step 5: jne (branches back to digitWriteLoopAddr if rest ≠ [], else falls through to
  -- digitWriteLoopAddrEnd)
  have hfetch5 : instructionAtRip spike2Executable.load.rip spike2Instructions s4.rip =
      some (jne_rel8 (Assembler.toDisp8 digitWriteLoopAddr digitWriteLoopAddrEnd)) := by
    rw [hrip4, writeJneAddr_eq]; exact iFetch_jneWrite
  have hnf5 : (X86_64Instruction.step
      (jne_rel8 (Assembler.toDisp8 digitWriteLoopAddr digitWriteLoopAddrEnd)) s4).faulted = false := by
    rw [step_jne_rel8]; exact hfaulted4
  rw [show fuel + 1 = fuel + 0 + 1 from rfl, runProgramWithLoops_step hfetch5 hnf5]
  generalize hs5 : X86_64Instruction.step
    (jne_rel8 (Assembler.toDisp8 digitWriteLoopAddr digitWriteLoopAddrEnd)) s4 = s5
  have hfault5 : s5.fault = none := by rw [← hs5, step_jne_rel8]; exact hfault4
  have hrcx5 : s5.gprs .rcx = rest.length.toUInt64 := by rw [← hs5, step_jne_rel8]; exact hrcx4
  have hrdi5 : s5.gprs .rdi = buf + 1 := by rw [← hs5, step_jne_rel8]; exact hrdi4
  have hrsp5 : s5.rsp = s.rsp + 8 := by rw [← hs5, step_jne_rel8]; exact hrsp4
  have hwritten5 : X86_64Mem.read .w8 buf s5.memory = b.toUInt64 := by
    rw [← hs5, step_jne_rel8]; exact hwritten4
  have hstackRest5 : StackHolds s5.memory s5.rsp rest := by
    rw [← hs5, step_jne_rel8]; exact hstackRest4
  have hregFrame5 : ∀ r : Reg64, r ≠ .rdx → r ≠ .rdi → r ≠ .rcx → r ≠ .rsp →
      s5.gprs r = s.gprs r := by
    intro r hrdx' hrdi' hrcx' hrsp'
    rw [← hs5, step_jne_rel8]
    exact hregFrame4 r hrdx' hrdi' hrcx' hrsp'
  have hmemFrame5 : ∀ a : Address, a ≠ buf →
      X86_64Mem.read .w8 a s5.memory = X86_64Mem.read .w8 a s.memory := by
    intro a ha
    rw [← hs5, step_jne_rel8, ← hs4, step_sub_r64_imm8, ← hs3, step_add_r64_imm8, ← hs2,
      step_mov_mem8_rdi_rdx]
    show X86_64Mem.read .w8 a (s1.write8 (s1.gprs .rdi) (s1.gprs .rdx).toUInt8).memory
      = X86_64Mem.read .w8 a s.memory
    rw [show (s1.write8 (s1.gprs .rdi) (s1.gprs .rdx).toUInt8).memory
      = X86_64Mem.write .w8 (s1.gprs .rdi) ((s1.gprs .rdx).toUInt8).toUInt64 s1.memory from rfl,
      hrdi1]
    have hstep : X86_64Mem.read .w8 a
        (X86_64Mem.write .w8 buf ((s1.gprs .rdx).toUInt8).toUInt64 s1.memory) =
        X86_64Mem.read .w8 a s1.memory :=
      congrArg UInt8.toUInt64 (X86_64Mem.readByte_write_disjoint .w8 buf
        ((s1.gprs .rdx).toUInt8).toUInt64 s1.memory a
        (by have hb : buf.toNat < 18446744073709551616 := buf.toNat_lt_size
            simp only [MemWidth.bytes]; omega)
        (by
          have hne : a.toNat ≠ buf.toNat := fun he => ha (UInt64.toNat_inj.mp he)
          simp only [MemWidth.bytes]; omega))
    rw [hstep]
    exact hmemFrame1 a ha
  have hrip5 : s5.rip = if rest.length = 0 then digitWriteLoopAddrEnd else digitWriteLoopAddr := by
    rw [← hs5, step_jne_rel8]
    show (if !s4.zf then s4.rip + 2 +
      signExtend8To64 (Assembler.toDisp8 digitWriteLoopAddr digitWriteLoopAddrEnd) else s4.rip + 2) = _
    rw [hzf4, hrip4]
    by_cases hz : rest.length = 0
    · rw [if_pos hz, hz]
      show (if !((1 : UInt64) == 1) then _ else digitWriteLoopAddr + 11 + 2) = digitWriteLoopAddrEnd
      rw [digitWriteLoopAddrEnd_eq, digitWriteLoopAddr_eq]; decide
    · rw [if_neg hz]
      have hne0 : ((rest.length + 1 : Nat).toUInt64 == (1 : UInt64)) = false := by
        have hbufBound : buf.toNat < 18446744073709551616 := buf.toNat_lt_size
        have hbnd : rest.length + 1 < 18446744073709551616 := by omega
        simp only [beq_eq_false_iff_ne, ne_eq, ← UInt64.toNat_inj]
        simp [Nat.toUInt64, hbnd]
        omega
      rw [hne0]
      show digitWriteLoopAddr + 11 + 2 +
        signExtend8To64 (Assembler.toDisp8 digitWriteLoopAddr digitWriteLoopAddrEnd) =
        digitWriteLoopAddr
      exact jneWrite_target
  exact ⟨s5, rfl, hrip5, hrcx5, hrdi5, hrsp5, hfault5, hwritten5, hstackRest5, hmemFrame5, hregFrame5⟩

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- **Closed form for `digit_write_loop` over an arbitrary nonempty list.** Structural induction
    on the list (unlike `digitExtractLoop_run`'s well-founded recursion on a shrinking numeral):
    each iteration pops one byte and writes it forward into the output buffer, so the recursion
    measure is simply the list itself. `hbufTop` is the write-side analog of `digitExtractLoop_run`'s
    `hrspTop`: it rules out the output buffer's address range wrapping past `2⁶⁴`. -/
theorem digitWriteLoop_run :
    ∀ (L : List UInt8) (buf : Address) (fuel : Nat) (s : X86_64MachineState),
    L ≠ [] →
    s.rip = digitWriteLoopAddr →
    StackHolds s.memory s.rsp L →
    s.gprs .rcx = (L.length : Nat).toUInt64 →
    s.gprs .rdi = buf →
    buf.toNat ≥ s.rsp.toNat + 8 * L.length →
    buf.toNat + L.length < 18446744073709551616 →
    s.fault = none →
    ∃ s',
      runProgramWithLoops spike2Executable.load.rip spike2Instructions (fuel + 5 * L.length) s =
        runProgramWithLoops spike2Executable.load.rip spike2Instructions fuel s' ∧
      s'.rip = digitWriteLoopAddrEnd ∧
      s'.gprs .rcx = 0 ∧
      s'.gprs .rdi = buf + L.length.toUInt64 ∧
      s'.rsp = s.rsp + 8 * L.length.toUInt64 ∧
      s'.fault = none ∧
      BufHolds s'.memory buf L ∧
      (∀ a : Address, (a.toNat < buf.toNat ∨ a.toNat ≥ buf.toNat + L.length) →
        X86_64Mem.read .w8 a s'.memory = X86_64Mem.read .w8 a s.memory) ∧
      (∀ r : Reg64, r ≠ .rdx → r ≠ .rdi → r ≠ .rcx → r ≠ .rsp → s'.gprs r = s.gprs r) := by
  intro L
  induction L with
  | nil => intro buf fuel s hne; exact absurd rfl hne
  | cons b rest ih =>
    intro buf fuel s _ hrip hstack hrcx hrdi hdisj hbufTop hfault
    by_cases hz : rest.length = 0
    · -- base case: rest = [], one iteration finishes at digitWriteLoopAddrEnd
      have hrestNil : rest = [] := by
        cases rest with
        | nil => rfl
        | cons _ _ => simp at hz
      subst hrestNil
      obtain ⟨s1, heq1, hrip1, hrcx1, hrdi1, hrsp1, hfault1, hwritten1, hstackRest1, hmemFrame1,
        hregFrame1⟩ := digitWriteLoop_oneIter b [] buf fuel s hrip hstack hrcx hrdi hdisj hfault
      rw [if_pos hz] at hrip1
      refine ⟨s1, ?_, hrip1, ?_, ?_, ?_, hfault1, ?_, ?_, hregFrame1⟩
      · simpa using heq1
      · simpa using hrcx1
      · simpa using hrdi1
      · simpa using hrsp1
      · exact ⟨hwritten1, trivial⟩
      · intro a ha
        apply hmemFrame1
        simp only [List.length_cons, List.length_nil] at ha
        intro he
        subst he
        omega
    · -- step case: recurse on rest via ih
      have hrestNe : rest ≠ [] := by
        intro he; subst he; simp at hz
      have hlen0 : (b :: rest).length = rest.length + 1 := rfl
      rw [hlen0] at hdisj hbufTop
      obtain ⟨s1, heq1, hrip1, hrcx1, hrdi1, hrsp1, hfault1, hwritten1, hstackRest1, hmemFrame1,
        hregFrame1⟩ := digitWriteLoop_oneIter b rest buf (fuel + 5 * rest.length) s hrip hstack
          hrcx hrdi hdisj hfault
      rw [if_neg hz] at hrip1
      have hbufBound : buf.toNat < 18446744073709551616 := buf.toNat_lt_size
      have hbufToNat1 : (buf + (1:UInt64)).toNat = buf.toNat + 1 := by
        have hb : buf.toNat + 1 < 18446744073709551616 := by omega
        simp [UInt64.toNat_add, UInt64.size, Nat.toUInt64]
        omega
      have hrspToNat1 : s1.rsp.toNat = s.rsp.toNat + 8 := by
        rw [hrsp1]
        have hb : s.rsp.toNat + 8 < 18446744073709551616 := by omega
        simp [UInt64.toNat_add, UInt64.size, Nat.toUInt64]
        omega
      have hdisj1' : (buf + (1:UInt64)).toNat ≥ s1.rsp.toNat + 8 * rest.length := by
        rw [hbufToNat1, hrspToNat1]; omega
      have hbufTop1 : (buf + (1:UInt64)).toNat + rest.length < 18446744073709551616 := by
        rw [hbufToNat1]; omega
      obtain ⟨s', heq', hrip', hrcx', hrdi', hrsp', hfault', hbufHeld', hmemFrame', hregFrame'⟩ :=
        ih (buf + 1) fuel s1 hrestNe hrip1 hstackRest1 hrcx1 hrdi1 hdisj1' hbufTop1 hfault1
      have hlen1 : ((rest.length + 1 : Nat)).toUInt64 = rest.length.toUInt64 + 1 := by
        simp [Nat.toUInt64]
      refine ⟨s', ?_, hrip', hrcx', ?_, ?_, hfault', ?_, ?_, ?_⟩
      · show runProgramWithLoops spike2Executable.load.rip spike2Instructions
          (fuel + 5 * (rest.length + 1)) s =
          runProgramWithLoops spike2Executable.load.rip spike2Instructions fuel s'
        rw [show fuel + 5 * (rest.length + 1) = (fuel + 5 * rest.length) + 5 from by omega,
          heq1, heq']
      · show s'.gprs .rdi = buf + (rest.length + 1 : Nat).toUInt64
        rw [hlen1, hrdi', UInt64.add_assoc, UInt64.add_comm (1:UInt64) rest.length.toUInt64]
      · show s'.rsp = s.rsp + 8 * (rest.length + 1 : Nat).toUInt64
        rw [hlen1, UInt64.mul_add, UInt64.mul_one]
        rw [show s.rsp + (8 * rest.length.toUInt64 + 8) = (s.rsp + 8) + 8 * rest.length.toUInt64
          from by rw [UInt64.add_comm (8 * rest.length.toUInt64) 8, ← UInt64.add_assoc]]
        rw [← hrsp1]; exact hrsp'
      · show BufHolds s'.memory buf (b :: rest)
        show X86_64Mem.read .w8 buf s'.memory = b.toUInt64 ∧ BufHolds s'.memory (buf + 1) rest
        refine ⟨?_, hbufHeld'⟩
        have hbufIn : buf.toNat < (buf + (1:UInt64)).toNat := by rw [hbufToNat1]; omega
        rw [hmemFrame' buf (Or.inl hbufIn)]
        exact hwritten1
      · intro a ha
        simp only [List.length_cons] at ha
        rcases ha with ha | ha
        · have haNe : a ≠ buf := by intro he; subst he; omega
          have ha1 : a.toNat < (buf + (1:UInt64)).toNat := by rw [hbufToNat1]; omega
          rw [hmemFrame' a (Or.inl ha1), hmemFrame1 a haNe]
        · have haNe : a ≠ buf := by intro he; subst he; omega
          have ha1 : a.toNat ≥ (buf + (1:UInt64)).toNat + rest.length := by
            rw [hbufToNat1]; omega
          rw [hmemFrame' a (Or.inr ha1), hmemFrame1 a haNe]
      · intro r hne1 hne2 hne3 hne4
        rw [hregFrame' r hne1 hne2 hne3 hne4, hregFrame1 r hne1 hne2 hne3 hne4]

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- **Connection theorem**: `digit_extract_loop` immediately followed by `digit_write_loop`,
    starting from `digitExtractLoopAddr`, writes the exact decimal ASCII encoding of `n`
    (`Stdlib.Fmt.formatDecimal n`) into the buffer at `buf` and leaves the stack pointer exactly
    where it started -- the extract loop's push discipline and the write loop's matching pop
    discipline cancel out, so the stack is used purely as scratch space between the two loops. -/
theorem itoa_run (n : Nat) (hn : n < 18446744073709551616) (buf : Address) :
    ∀ (fuel : Nat) (s : X86_64MachineState),
    s.rip = digitExtractLoopAddr →
    s.gprs .rax = n.toUInt64 →
    s.gprs .r10 = 10 →
    s.gprs .rcx = 0 →
    s.gprs .rdi = buf →
    s.fault = none →
    8 * (Stdlib.Fmt.digits n).length ≤ s.rsp.toNat →
    s.rsp.toNat < 18446744073709551608 →
    buf.toNat ≥ s.rsp.toNat →
    buf.toNat + (Stdlib.Fmt.digits n).length < 18446744073709551616 →
    ∃ s',
      runProgramWithLoops spike2Executable.load.rip spike2Instructions
          (fuel + 7 * (Stdlib.Fmt.digits n).length + 5 * (Stdlib.Fmt.digits n).length) s =
        runProgramWithLoops spike2Executable.load.rip spike2Instructions fuel s' ∧
      s'.rip = digitWriteLoopAddrEnd ∧
      s'.rsp = s.rsp ∧
      s'.gprs .rdi = buf + (Stdlib.Fmt.digits n).length.toUInt64 ∧
      s'.fault = none ∧
      BufHolds s'.memory buf (Stdlib.Fmt.formatDecimal n) ∧
      (∀ r : Reg64, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .rdi → r ≠ .rsp → s'.gprs r = s.gprs r) := by
  intro fuel s hrip hrax hr10 hrcx hrdi hfault hrspBound hrspTop hbufGe hbufTop
  obtain ⟨s1, heq1, hrip1, hrax1, hrcx1, hrsp1, hfault1, hpushed1, hframe1, hregframe1⟩ :=
    digitExtractLoop_run n hn 0 (fuel + 5 * (Stdlib.Fmt.digits n).length) s hrip hrax hr10 hrcx
      hfault hrspBound hrspTop
  have hrdi1 : s1.gprs .rdi = buf := by
    rw [hregframe1 .rdi (by decide) (by decide) (by decide) (by decide)]; exact hrdi
  have hlenEq : (Stdlib.Fmt.formatDecimal n).length = (Stdlib.Fmt.digits n).length :=
    Stdlib.Fmt.formatDecimal_length_eq n
  have hrcx1' : s1.gprs .rcx = (Stdlib.Fmt.formatDecimal n).length.toUInt64 := by
    rw [hlenEq]; simpa using hrcx1
  have hne : Stdlib.Fmt.formatDecimal n ≠ [] := Stdlib.Fmt.formatDecimal_ne_nil n
  have hupBound : s.rsp.toNat < 18446744073709551616 := by omega
  have hlenBound : (Stdlib.Fmt.digits n).length < 18446744073709551616 := by omega
  have hmulCast : (8 * (Stdlib.Fmt.digits n).length.toUInt64).toNat
      = 8 * (Stdlib.Fmt.digits n).length := by
    simp [UInt64.toNat_mul, UInt64.size, Nat.toUInt64]
    omega
  have hs8 : (s.rsp - 8 * (Stdlib.Fmt.digits n).length.toUInt64).toNat
      = s.rsp.toNat - 8 * (Stdlib.Fmt.digits n).length := by
    have hdiv : (18446744073709551616 - 8 * (Stdlib.Fmt.digits n).length + s.rsp.toNat)
        / 18446744073709551616 = 1 := by omega
    simp [UInt64.toNat_sub, UInt64.size, hmulCast]
    omega
  have hrsp1Nat : s1.rsp.toNat = s.rsp.toNat - 8 * (Stdlib.Fmt.digits n).length := by
    rw [hrsp1]; exact hs8
  have hdisjRun : buf.toNat ≥ s1.rsp.toNat + 8 * (Stdlib.Fmt.formatDecimal n).length := by
    rw [hlenEq, hrsp1Nat]; omega
  have hbufTop1 : buf.toNat + (Stdlib.Fmt.formatDecimal n).length < 18446744073709551616 := by
    rw [hlenEq]; exact hbufTop
  obtain ⟨s', heq', hrip', hrcx', hrdi', hrsp', hfault', hbufHeld', hmemFrame', hregFrame'⟩ :=
    digitWriteLoop_run (Stdlib.Fmt.formatDecimal n) buf fuel s1 hne hrip1 hpushed1 hrcx1' hrdi1
      hdisjRun hbufTop1 hfault1
  rw [hlenEq] at heq' hrsp' hrdi'
  refine ⟨s', ?_, hrip', ?_, ?_, hfault', hbufHeld', ?_⟩
  · rw [show fuel + 7 * (Stdlib.Fmt.digits n).length + 5 * (Stdlib.Fmt.digits n).length
      = (fuel + 5 * (Stdlib.Fmt.digits n).length) + 7 * (Stdlib.Fmt.digits n).length from by omega,
      heq1, heq']
  · rw [hrsp', hrsp1, UInt64.sub_add_cancel]
  · rw [hrdi']
  · intro r hra hrd hrc hri hrs
    rw [hregFrame' r hrd hri hrc hrs, hregframe1 r hra hrd hrc hrs]

end Spikes.Spike2Fibonacci.Windows
