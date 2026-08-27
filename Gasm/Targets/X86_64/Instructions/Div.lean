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

namespace Gasm.Targets.X86_64.Instructions

open Gasm.Core
open Gasm.Targets.X86_64

/- REF: intel-sdm#vol=2;instr=DIV;part=description -/
/-- DIV r64: Unsigned divide RDX:RAX by 64-bit general-purpose register. -/
structure DivR64 where
  divisor : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=DIV;part=operation -/
instance : X86_64Instruction DivR64 where
  encode i :=
    let (code, ext) := reg64Code i.divisor
    let rex := makeRex true false false ext
    let modrm := makeModRM 3 6 code
    ByteArray.mk #[rex, 0xF7, modrm]

  step i s :=
    let divisorVal := s.gprs i.divisor
    if divisorVal == 0 then
      -- #DE (Divide Error Exception) - fault retains the faulting instruction RIP
      { s with faulted := true }
    else
      let dividendNat : Nat := (s.gprs .rdx).toNat * 18446744073709551616 + (s.gprs .rax).toNat
      let divisorNat : Nat := divisorVal.toNat
      let quotNat := dividendNat / divisorNat
      let remNat := dividendNat % divisorNat
      if quotNat > 0xFFFFFFFFFFFFFFFF then
        -- #DE (Quotient Overflow Exception) - fault retains the faulting instruction RIP
        { s with faulted := true }
      else
        let s' := s.setGpr64 .rax (UInt64.ofNat quotNat)
        let s'' := s'.setGpr64 .rdx (UInt64.ofNat remNat)
        { s'' with rip := s.rip + 3 }

  toUops _ := [
    { mnemonic := "DIV.prep", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "DIV.intDiv", uopClass := .intDiv, eligiblePorts := [.p0], latencyCycles := 14, reciprocalThroughput := 10.0 },
    { mnemonic := "DIV.splitQuot", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "DIV.splitRem", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "DIV.flags", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"div {i.divisor}"
  toLean i := s!"div_r64 .{i.divisor}"
  undefinedFlagsMask _ := arithmeticStatusMask -- All status flags are undefined after DIV according to Intel SDM
  -- `divisor` is read-only (DIV never writes it), but a `.rsp` divisor still feeds the harness's
  -- real, harness-pinned RSP value into RAX/RDX (both compared, non-flag registers) instead of
  -- the model's fuzzed value — see `hwSafeReg64`'s doc comment.
  canFuzzHardware i := hwSafeReg64 i.divisor
  generateFuzzStates i rng := Id.run do
    let mut states : List X86_64MachineState := []
    let divisors : List UInt64 := [0, 1, 2, 3, 5, 7, 0x10, 0x100, 0x7FFF, 0x8000, 0xFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF]
    let dividends : List UInt64 := [0, 1, 2, 10, 100, 0x1000, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]
    -- Quotient-overflow (#DE) vectors, placed first so they land inside the harness's default
    -- test-vector budget: RDX >= divisor makes the 128-bit dividend RDX:RAX >= divisor * 2^64,
    -- so quotNat is guaranteed to exceed 0xFFFFFFFFFFFFFFFF and the overflow fault path fires.
    -- RAX/RDX are written before i.divisor so that if the divisor register aliases RAX or RDX,
    -- the final write (the divisor) wins and the vector's fault-triggering intent survives.
    for d in divisors do
      if d != 0 then
        let s : X86_64MachineState := default
        let s := s.setGpr64 .rax 0
        let s := s.setGpr64 .rdx d
        let s := s.setGpr64 i.divisor d
        states := states ++ [s]
    -- Divide-by-zero (#DE) vectors with a nonzero RDX, confirming the divisor == 0 check
    -- fires regardless of the dividend's high half. Divisor is written last for the same
    -- aliasing-safety reason as above.
    for rdxVal in ([1, 0xFFFFFFFFFFFFFFFF] : List UInt64) do
      let s : X86_64MachineState := default
      let s := s.setGpr64 .rax 123
      let s := s.setGpr64 .rdx rdxVal
      let s := s.setGpr64 i.divisor 0
      states := states ++ [s]
    for d in divisors do
      for a in dividends do
        let s : X86_64MachineState := default
        let s := s.setGpr64 .rax a
        let s := s.setGpr64 .rdx 0
        let s := s.setGpr64 i.divisor d
        states := states ++ [s]
    (states, rng)
  roundtripCases := allReg64List.map DivR64.mk

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- DIV r64 helper. -/
def div_r64 (r : Reg64) : AnyX86_64Instruction :=
  ⟨DivR64.mk r⟩

end Gasm.Targets.X86_64.Instructions
