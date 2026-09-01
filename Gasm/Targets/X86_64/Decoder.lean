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
/-- All declarative decode rules aggregated from across all 25 instruction families. -/
def allDecodeRules : List DecodeRule :=
  retDecodeRules ++ pushDecodeRules ++ popDecodeRules ++ jccDecodeRules ++
  movDecodeRules ++ callDecodeRules ++ syscallDecodeRules ++ imulDecodeRules ++
  cmovDecodeRules ++ addDecodeRules ++ orDecodeRules ++ andDecodeRules ++
  subDecodeRules ++ xorDecodeRules ++ cmpDecodeRules ++ testDecodeRules ++
  xchgDecodeRules ++ leaDecodeRules ++ shiftDecodeRules ++ notDecodeRules ++
  negDecodeRules ++ divDecodeRules ++ inDecodeRules ++ outDecodeRules ++
  hltDecodeRules

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Table-driven opcode dispatcher: indexes candidate rules by primary opcode.
    Each opcode routes directly to its small bucket of matching rules (typically 1–4 rules)
    rather than scanning across unrelated families. In Lean 4, pattern matching on constructors
    and UInt8 values compiles to a decision tree evaluated by the kernel in O(1) reduction steps
    with minimal recursion depth. -/
def dispatchOpcode (op : DecodeOpcode) : List DecodeRule :=
  match op with
  | .one 0x01 => addDecodeRules.filter (·.opcode == op)
  | .one 0x09 => orDecodeRules.filter (·.opcode == op)
  | .one 0x21 => andDecodeRules.filter (·.opcode == op)
  | .one 0x29 => subDecodeRules.filter (·.opcode == op)
  | .one 0x31 => xorDecodeRules.filter (·.opcode == op)
  | .one 0x39 => cmpDecodeRules.filter (·.opcode == op)
  | .one 0x50 | .one 0x51 | .one 0x52 | .one 0x53
  | .one 0x54 | .one 0x55 | .one 0x56 | .one 0x57 =>
    pushDecodeRules.filter (·.opcode == op)
  | .one 0x58 | .one 0x59 | .one 0x5A | .one 0x5B
  | .one 0x5C | .one 0x5D | .one 0x5E | .one 0x5F =>
    popDecodeRules.filter (·.opcode == op)
  | .one 0x72 | .one 0x73 | .one 0x74 | .one 0x75
  | .one 0x76 | .one 0x77 | .one 0x7C | .one 0x7D
  | .one 0x7E | .one 0x7F | .one 0xEB | .one 0xE9 =>
    jccDecodeRules.filter (·.opcode == op)
  | .one 0x81 =>
    addDecodeRules.filter (·.opcode == op) ++
    orDecodeRules.filter (·.opcode == op) ++
    subDecodeRules.filter (·.opcode == op) ++
    cmpDecodeRules.filter (·.opcode == op)
  | .one 0x83 =>
    addDecodeRules.filter (·.opcode == op) ++
    orDecodeRules.filter (·.opcode == op) ++
    andDecodeRules.filter (·.opcode == op) ++
    subDecodeRules.filter (·.opcode == op) ++
    cmpDecodeRules.filter (·.opcode == op)
  | .one 0x85 => testDecodeRules.filter (·.opcode == op)
  | .one 0x87 => xchgDecodeRules.filter (·.opcode == op)
  | .one 0x88 | .one 0x89 | .one 0x8B
  | .one 0xB8 | .one 0xB9 | .one 0xBA | .one 0xBB
  | .one 0xBC | .one 0xBD | .one 0xBE | .one 0xBF
  | .one 0xC7 => movDecodeRules.filter (·.opcode == op)
  | .one 0xC6 => [movRuleC6]
  | .one 0x8D => leaDecodeRules.filter (·.opcode == op)
  | .one 0xC1 | .one 0xD3 => shiftDecodeRules.filter (·.opcode == op)
  | .one 0xC3 => retDecodeRules.filter (·.opcode == op)
  | .one 0xE4 | .one 0xE5 | .one 0xEC | .one 0xED => inDecodeRules.filter (·.opcode == op)
  | .one 0xE6 | .one 0xE7 | .one 0xEE | .one 0xEF => outDecodeRules.filter (·.opcode == op)
  | .one 0xE8 | .one 0xFF => callDecodeRules.filter (·.opcode == op)
  | .one 0xF4 => hltDecodeRules.filter (·.opcode == op)
  | .one 0xF7 =>
    testDecodeRules.filter (·.opcode == op) ++
    notDecodeRules.filter (·.opcode == op) ++
    negDecodeRules.filter (·.opcode == op) ++
    divDecodeRules.filter (·.opcode == op)
  | .two0F 0x05 => syscallDecodeRules.filter (·.opcode == op)
  | .two0F 0x42 | .two0F 0x43 | .two0F 0x44 | .two0F 0x45
  | .two0F 0x4C | .two0F 0x4D | .two0F 0x4E | .two0F 0x4F =>
    cmovDecodeRules.filter (·.opcode == op)
  | .two0F 0x82 | .two0F 0x83 | .two0F 0x84 | .two0F 0x85
  | .two0F 0x87 | .two0F 0x8D | .two0F 0x8E =>
    jccDecodeRules.filter (·.opcode == op)
  | .two0F 0xAF => imulDecodeRules.filter (·.opcode == op)
  | .two0F 0xB6 => movDecodeRules.filter (·.opcode == op)
  | _ => []

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Decodes a single x86-64 instruction from a ByteArray starting at the specified byte offset.
    Returns the decoded instruction AST and the number of bytes consumed.

    Uses table-driven dispatch indexed by primary opcode. -/
def decodeX86_64Instr (bytes : ByteArray) (offset : Nat) : Except String (X86_64Instr × Nat) :=
  decodeWithTable dispatchOpcode bytes offset

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
