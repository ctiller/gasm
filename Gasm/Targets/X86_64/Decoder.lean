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
import Gasm.Targets.X86_64.Instructions
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
import Gasm.Targets.X86_64.Instructions.In
import Gasm.Targets.X86_64.Instructions.Out
import Gasm.Targets.X86_64.Instructions.Hlt
import Gasm.Targets.X86_64.Instructions.Syscall

namespace Gasm.Targets.X86_64

open Gasm.Core
open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Stage B registry-driven dispatch table: every instruction family's own co-located
    `tryDecode` (defined next to its `encode` in `Instructions/<Family>.lean`), in one place.
    This is the thin dispatcher's sole routing data — adding a new family means adding one entry
    here, not adding a new branch to a monolithic pattern match. Order does not affect
    correctness (each family's `tryDecode` only claims byte patterns belonging to its own
    instructions and returns `.error` on anything else, verified per-family by the exhaustive
    `RoundtripGate/<Family>.lean` `decide` proof and, across families, by this module's own
    `RoundtripGate/DispatchExhaustive.lean` companion) — only dispatch cost, since earlier
    entries are tried first. -/
def allTryDecoders : List (ByteArray → Nat → Except String (AnyX86_64Instruction × Nat)) :=
  [retTryDecode, pushTryDecode, popTryDecode, jccTryDecode, movTryDecode, callTryDecode,
   syscallTryDecode, imulTryDecode, cmovTryDecode, addTryDecode, orTryDecode, andTryDecode,
   subTryDecode, xorTryDecode, cmpTryDecode, testTryDecode, xchgTryDecode, leaTryDecode,
   shiftTryDecode, notTryDecode, negTryDecode, divTryDecode, inTryDecode, outTryDecode,
   hltTryDecode]

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Tries each decoder in `fs` in order against `(bytes, offset)`, returning the first success.
    This is the entire routing logic of the thin dispatcher: no opcode is inspected here at all
    — that knowledge lives solely in each family's own `tryDecode`. -/
def tryDecoders (fs : List (ByteArray → Nat → Except String (AnyX86_64Instruction × Nat)))
    (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  match fs with
  | [] => .error s!"Unsupported x86-64 instruction at offset {offset}: no registered family's tryDecode claimed this byte pattern"
  | f :: rest =>
    match f bytes offset with
    | .ok r => .ok r
    | .error _ => tryDecoders rest bytes offset

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Decodes a single x86-64 instruction from a ByteArray starting at the specified byte offset.
    Returns the decoded instruction AST and the number of bytes consumed.

    Stage B: this used to be a single 700+-line pattern match owning every family's decode logic
    directly. It is now a thin registry-driven dispatcher — `allTryDecoders` lists every family's
    own co-located `tryDecode`, and this function just tries them in order. All REX-parsing,
    ModR/M-parsing, and per-opcode decode logic lives in `Instructions/<Family>.lean` next to
    that family's `encode`, not here. -/
def decodeX86_64Instr (bytes : ByteArray) (offset : Nat) : Except String (X86_64Instr × Nat) :=
  tryDecoders allTryDecoders bytes offset

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Disassembles a complete ByteArray stream of x86-64 instructions until the buffer is exhausted. -/
def disassembleX86_64 (bytes : ByteArray) : Except String (List X86_64Instr) :=
  let rec loop (fuel : Nat) (offset : Nat) (acc : List X86_64Instr) : Except String (List X86_64Instr) :=
    match fuel with
    | 0 => Except.error "Disassembly fuel exhausted"
    | fuel + 1 =>
      if offset >= bytes.size then
        Except.ok acc
      else
        match decodeX86_64Instr bytes offset with
        | .error err => Except.error err
        | .ok (instr, len) =>
          if len == 0 then
            Except.error s!"Zero-length instruction encountered at offset {offset}"
          else
            loop fuel (offset + len) (acc ++ [instr])
  loop (bytes.size + 1) 0 []

/- REF: docs/TARGETS/TARGET_MODEL.md#1-vertical-slice-target-structure -/
instance : DisassemblableArch X86_64 where
  decodeInstr := decodeX86_64Instr
  disassemble := disassembleX86_64

end Gasm.Targets.X86_64
