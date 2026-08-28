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
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Push
import Gasm.Targets.X86_64.Instructions.Pop
import Gasm.Targets.X86_64.Instructions.Div
import Gasm.Targets.X86_64.Instructions.Imul
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Instructions.Or
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Targets.X86_64.Instructions.Not
import Gasm.Targets.X86_64.Instructions.Neg
import Gasm.Targets.X86_64.Instructions.Shift
import Gasm.Targets.X86_64.Instructions.Test
import Gasm.Targets.X86_64.Instructions.Xchg
import Gasm.Targets.X86_64.Instructions.Cmov
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.Instructions.Syscall
import Gasm.Targets.X86_64.Decoder
import Gasm.Targets.X86_64.Disassembler
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.X86_64.Roundtrip
import Gasm.Targets.X86_64.Registry
import Gasm.Targets.X86_64.RoundtripGate.Common

namespace Gasm.Targets.X86_64.RoundtripTests

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.X86_64.Roundtrip
open Gasm.Targets.X86_64.Registry
open Gasm.Targets.X86_64.RoundtripGate

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Human-readable roundtrip check for one instruction: reports which specific invariant (decode
    success, length, re-encode, `toLean` rendering) failed and for which NASM mnemonic. This
    checks *exactly* the same four invariants as `RoundtripGate.decodesOk` — the diagnostic
    counterpart to the `RoundtripGate/*.lean` gate theorems, which are the actual correctness
    proof — this IO loop exists so a failure names the exact instruction and the exact invariant
    instead of only "some `decide` obligation is false". Previously this omitted the `toLean`
    check `decodesOk` has, so a gate failure in exactly the same soundness class as the `0x8B`
    REX.W bug (same bytes, different decoded structure) could show as a false PASS here even
    though the corresponding `RoundtripGate` shard would fail; it now cannot. -/
def checkRoundtrip (i : X86_64Instr) : IO Bool := do
  let encoded := X86_64Instruction.encode i
  match decodeX86_64Instr encoded 0 with
  | .error err =>
    IO.println s!"[FAIL] Decode error on {X86_64Instruction.toNASM i}: {err}"
    return false
  | .ok (decoded, len) =>
    if len != encoded.size then
      IO.println s!"[FAIL] Length mismatch on {X86_64Instruction.toNASM i}: expected {encoded.size} bytes, got {len}"
      return false
    let reEncoded := X86_64Instruction.encode decoded
    if reEncoded != encoded then
      IO.println s!"[FAIL] Re-encode mismatch on {X86_64Instruction.toNASM i}"
      return false
    if X86_64Instruction.toLean decoded != X86_64Instruction.toLean i then
      IO.println s!"[FAIL] toLean rendering mismatch on {X86_64Instruction.toNASM i}: decoded as \
        {X86_64Instruction.toLean decoded}, expected {X86_64Instruction.toLean i} (same bytes, \
        different structure — see decodesOk)"
      return false
    -- Cross-check against the gate's own predicate: these two must never disagree. Instantiated
    -- with the real dispatcher `decodeX86_64Instr` (Stage B: `decodesOk` is now generic over
    -- which decoder it checks — per-family `RoundtripGate/<Family>.lean` shards instantiate it
    -- with that family's own co-located `tryDecode`; this diagnostic loop instantiates it with
    -- the dispatcher, matching what `decodeX86_64Instr encoded 0` above already checked).
    if !decodesOk decodeX86_64Instr i then
      IO.println s!"[FAIL] decodesOk disagreed with the granular checks above on {X86_64Instruction.toNASM i}"
      return false
    return true

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Runs the exhaustive roundtrip check over `Registry.allEncodableInstructions` — the same
    complete case set the sharded `RoundtripGate/*.lean` gate theorems are proved over — plus a
    multi-instruction stream disassembly smoke test. Kept as a diagnostic executable (naming the
    exact failing NASM mnemonic) even though the gate theorems are what actually guarantee
    correctness at build time. -/
def runAllTests : IO UInt32 := do
  let mut totalTested : Nat := 0
  let mut totalPassed : Nat := 0

  IO.println "=== Starting x86-64 Disassembler Exhaustive Roundtrip Tests ==="
  IO.println s!"Registry size: {allEncodableInstructions.length} instructions (Registry.allEncodableInstructions)"

  for instr in allEncodableInstructions do
    totalTested := totalTested + 1
    if ← checkRoundtrip instr then totalPassed := totalPassed + 1

  -- Stream Disassembly and Lean Source Code Emission for Program Sequences
  let testProgram : List X86_64Instr := [
    sub_rsp 56,
    mov_r32 .ecx 0xFFFFFFF5,
    mov_r64 .rcx .rax,
    mov_r32 .r8d 15,
    lea_rsp .r9 0x28,
    mov_rsp64 0x20 0,
    xor_r32 .ecx .ecx,
    ret_op
  ]

  let bytes := serializeInstructions testProgram
  totalTested := totalTested + 1
  match disassembleX86_64 bytes with
  | .error err =>
    IO.println s!"[FAIL] Stream disassembly failed: {err}"
  | .ok disassembled =>
    if disassembled.length == testProgram.length then
      totalPassed := totalPassed + 1
      let dslString := toLeanProgramString disassembled
      IO.println "Generated Lean DSL Output:"
      IO.println dslString
    else
      IO.println s!"[FAIL] Disassembled length mismatch: expected {testProgram.length}, got {disassembled.length}"

  IO.println s!"=== Results: {totalPassed}/{totalTested} tests passed ==="
  if totalPassed == totalTested then
    IO.println "All roundtrip verification tests passed successfully!"
    return 0
  else
    return 1

end Gasm.Targets.X86_64.RoundtripTests

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
def main : IO UInt32 :=
  Gasm.Targets.X86_64.RoundtripTests.runAllTests
