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
import Gasm.Targets.X86_64.Uop
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Push
import Gasm.Targets.X86_64.Instructions.Pop
import Gasm.Targets.X86_64.Instructions.Div
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Instructions.Or
import Gasm.Targets.X86_64.Instructions.Test
import Gasm.Targets.X86_64.Instructions.Not
import Gasm.Targets.X86_64.Instructions.Neg
import Gasm.Targets.X86_64.Instructions.Shift
import Gasm.Targets.X86_64.Instructions.Cmov
import Gasm.Targets.X86_64.Instructions.Xchg
import Gasm.Targets.X86_64.Instructions.Imul
import Gasm.Targets.X86_64.Performance

namespace Gasm.Targets.X86_64.Fuzzer

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Simple pseudo-random number generator state (Xorshift64). -/
structure FuzzerRng where
  seed : UInt64 := 88172645463325252
  deriving Repr, DecidableEq, Inhabited

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Generates the next pseudo-random UInt64 and advanced RNG state. -/
def FuzzerRng.next (rng : FuzzerRng) : Prod UInt64 FuzzerRng :=
  let x := rng.seed
  let x1 := x ^^^ (x <<< 13)
  let x2 := x1 ^^^ (x1 >>> 7)
  let x3 := x2 ^^^ (x2 <<< 17)
  let finalSeed := if x3 == 0 then 88172645463325252 else x3
  (finalSeed, { seed := finalSeed })

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Selects a random natural number in range [0, bound - 1]. -/
def FuzzerRng.nextNat (bound : Nat) (rng : FuzzerRng) : Prod Nat FuzzerRng :=
  if bound <= 1 then (0, rng)
  else
    let (v, nextRng) := rng.next
    ((v.toNat % bound), nextRng)

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Available 64-bit general-purpose registers for fuzzing. -/
def fuzzGprs64 : List Reg64 := [.rax, .rdx, .rbx, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Available 32-bit general-purpose registers for fuzzing. -/
def fuzzGprs32 : List Reg32 := [.eax, .ecx, .edx, .ebx, .esi, .edi, .r8d, .r9d, .r10d, .r11d, .r12d, .r13d, .r14d, .r15d]

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Synthesizes a pseudo-random valid x86-64 instruction. -/
def generateRandomInstruction (rng : FuzzerRng) : Prod AnyX86_64Instruction FuzzerRng :=
  let (catChoice, rng1) := rng.nextNat 32
  let (r1Idx, rng2) := rng1.nextNat fuzzGprs64.length
  let (r2Idx, rng3) := rng2.nextNat fuzzGprs64.length
  let (r32_1Idx, rng4) := rng3.nextNat fuzzGprs32.length
  let (r32_2Idx, rng5) := rng4.nextNat fuzzGprs32.length
  let (imm8Val, rng6) := rng5.nextNat 128
  let (imm32Val, rng7) := rng6.nextNat 65536

  let r1 := fuzzGprs64.getD r1Idx .rax
  let r2 := fuzzGprs64.getD r2Idx .rdx
  let r32_1 := fuzzGprs32.getD r32_1Idx .eax
  let r32_2 := fuzzGprs32.getD r32_2Idx .edx

  match catChoice with
  | 0  => (add_r64 r1 r2, rng7)
  | 1  => (add_r64_imm8 r1 (UInt8.ofNat imm8Val), rng7)
  | 2  => (sub_r64 r1 r2, rng7)
  | 3  => (sub_r64_imm8 r1 (UInt8.ofNat imm8Val), rng7)
  | 4  => (mov_r64 r1 r2, rng7)
  | 5  => (mov_r32 r32_1 (UInt32.ofNat imm32Val), rng7)
  | 6  => (xor_r32 r32_1 r32_2, rng7)
  | 7  => (cmp_r64 r1 r2, rng7)
  | 8  => (cmp_r64_imm8 r1 (UInt8.ofNat imm8Val), rng7)
  | 9  => (mov_rsp_byte (UInt8.ofNat (imm8Val % 32)) (UInt8.ofNat imm8Val), rng7)
  | 10 => (push_r64 r1, rng7)
  | 11 => (pop_r64 r1, rng7)
  | 12 => (and_r64 r1 r2, rng7)
  | 13 => (and_r64_imm8 r1 (UInt8.ofNat imm8Val), rng7)
  | 14 => (or_r64 r1 r2, rng7)
  | 15 => (or_r64_imm8 r1 (UInt8.ofNat imm8Val), rng7)
  | 16 => (or_r64_imm32 r1 (UInt32.ofNat imm32Val), rng7)
  | 17 => (test_r64 r1 r2, rng7)
  | 18 => (test_r64_imm32 r1 (UInt32.ofNat imm32Val), rng7)
  | 19 => (not_r64 r1, rng7)
  | 20 => (neg_r64 r1, rng7)
  | 21 => (shl_r64_imm8 r1 (UInt8.ofNat (imm8Val % 64)), rng7)
  | 22 => (shr_r64_imm8 r1 (UInt8.ofNat (imm8Val % 64)), rng7)
  | 23 => (sar_r64_imm8 r1 (UInt8.ofNat (imm8Val % 64)), rng7)
  | 24 => (cmove_r64 r1 r2, rng7)
  | 25 => (cmovne_r64 r1 r2, rng7)
  | 26 => (cmovl_r64 r1 r2, rng7)
  | 27 => (cmovle_r64 r1 r2, rng7)
  | 28 => (cmovg_r64 r1 r2, rng7)
  | 29 => (cmovge_r64 r1 r2, rng7)
  | 30 => (xchg_r64 r1 r2, rng7)
  | _  => (imul_r64 r1 r2, rng7)

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Generates a pseudo-random program sequence of the given length. -/
def generateRandomProgram (length : Nat) (rng : FuzzerRng) : Prod (List AnyX86_64Instruction) FuzzerRng := Id.run do
  let mut currentRng := rng
  let mut instrs : List AnyX86_64Instruction := []
  for _ in [0:length] do
    let (instr, nextRng) := generateRandomInstruction currentRng
    instrs := instrs ++ [instr]
    currentRng := nextRng
  (instrs, currentRng)

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Generates a structured loop executing a random body for `iterations` count. -/
def generateRandomLoopProgram (iterations : Nat) (bodyLength : Nat) (rng : FuzzerRng) : Prod (List AnyX86_64Instruction × Nat) FuzzerRng := Id.run do
  let (body, nextRng) := generateRandomProgram bodyLength rng
  let bodyUops := (body.map uopsRetired).foldl (· + ·) 0
  let mut loopInstrs : List AnyX86_64Instruction := []
  -- Unroll the loop body `iterations` times to simulate hardware execution trace
  for _ in [0:iterations] do
    loopInstrs := loopInstrs ++ body
  ( (loopInstrs, bodyUops), nextRng )

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Result structure for a single fuzzer invariant verification check. -/
structure FuzzerCheckResult where
  passed        : Bool
  progLength    : Nat
  totalUops     : Nat
  minCycles     : Nat
  nominalCycles : Nat
  maxCycles     : Nat
  errorMsg      : Option String := none
  deriving Repr, Inhabited

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Verifies microarchitectural cycle monotonicity, uop conservation, and non-vacuity on a basic block. -/
def verifyPerfInvariants (instrs : List AnyX86_64Instruction) (profile : MicroarchProfile := goldenCoveProfile) : FuzzerCheckResult :=
  let report := analyzePerformance instrs profile
  let totalUopsSum := (instrs.map uopsRetired).foldl (· + ·) 0

  -- 1. Invariant: Uop Conservation
  if report.totalUops != totalUopsSum then
    { passed := false, progLength := instrs.length, totalUops := report.totalUops,
      minCycles := report.bounds.minCycles, nominalCycles := report.bounds.nominalCycles, maxCycles := report.bounds.maxCycles,
      errorMsg := some s!"Uop Conservation Violation: report.totalUops ({report.totalUops}) != sum ({totalUopsSum})" }
  -- 2. Invariant: Cycle Monotonicity: 0 < minCycles <= nominalCycles <= maxCycles
  else if report.bounds.minCycles == 0 then
    { passed := false, progLength := instrs.length, totalUops := report.totalUops,
      minCycles := report.bounds.minCycles, nominalCycles := report.bounds.nominalCycles, maxCycles := report.bounds.maxCycles,
      errorMsg := some "Zero Cycle Bound Violation: minCycles is 0" }
  else if report.bounds.minCycles > report.bounds.nominalCycles then
    { passed := false, progLength := instrs.length, totalUops := report.totalUops,
      minCycles := report.bounds.minCycles, nominalCycles := report.bounds.nominalCycles, maxCycles := report.bounds.maxCycles,
      errorMsg := some s!"Monotonicity Violation: minCycles ({report.bounds.minCycles}) > nominalCycles ({report.bounds.nominalCycles})" }
  else if report.bounds.nominalCycles > report.bounds.maxCycles then
    { passed := false, progLength := instrs.length, totalUops := report.totalUops,
      minCycles := report.bounds.minCycles, nominalCycles := report.bounds.nominalCycles, maxCycles := report.bounds.maxCycles,
      errorMsg := some s!"Monotonicity Violation: nominalCycles ({report.bounds.nominalCycles}) > maxCycles ({report.bounds.maxCycles})" }
  else
    { passed := true, progLength := instrs.length, totalUops := report.totalUops,
      minCycles := report.bounds.minCycles, nominalCycles := report.bounds.nominalCycles, maxCycles := report.bounds.maxCycles }

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Verifies performance invariants and uop linearity across loop iterations. -/
def verifyLoopPerfInvariants (loopInstrs : List AnyX86_64Instruction) (iterations : Nat) (bodyUops : Nat) (profile : MicroarchProfile := goldenCoveProfile) : FuzzerCheckResult :=
  let baseResult := verifyPerfInvariants loopInstrs profile
  if !baseResult.passed then
    baseResult
  else
    let expectedUops := iterations * bodyUops
    if baseResult.totalUops != expectedUops then
      { baseResult with passed := false, errorMsg := some s!"Loop Uop Linearity Violation: totalUops ({baseResult.totalUops}) != expected ({expectedUops})" }
    else
      baseResult

end Gasm.Targets.X86_64.Fuzzer
