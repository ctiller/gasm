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
import Gasm.Targets.Wasm.Types
import Gasm.Targets.Wasm.AST

namespace Gasm.Targets.Wasm

open Gasm.Core

/- REF: wasm-text-types#value-types -/
/-- Formats a value type in WAT syntax. -/
def formatValType : ValType → String
  | .i32 => "i32"
  | .i64 => "i64"
  | .f32 => "f32"
  | .f64 => "f64"

/- REF: wasm-text-instructions#control-instructions -/
/-- Formats a block return type in WAT syntax. -/
def formatBlockType : BlockType → String
  | .empty => ""
  | .val t => s!" (result {formatValType t})"

/- REF: docs/TARGETS/WASM_ORACLE_HARNESS.md#8-wat-text-formatting-conventions-non-spec -/
/-- Indents a string by n levels (2 spaces per level). -/
def indent (level : Nat) (s : String) : String :=
  String.ofList (List.replicate (level * 2) ' ') ++ s

/- REF: wasm-text-values#strings -/
/-- Formats a raw byte array as a valid WebAssembly Text (WAT) string literal with standard \hh hex escapes. -/
def formatWatDataString (bytes : ByteArray) : String := Id.run do
  let hexChars := "0123456789abcdef".toList
  let mut s := ""
  for b in bytes do
    let n := b.toNat
    if n == 0x22 then s := s ++ "\\\""
    else if n == 0x5C then s := s ++ "\\\\"
    else if n == 0x0A then s := s ++ "\\n"
    else if n == 0x0D then s := s ++ "\\r"
    else if n == 0x09 then s := s ++ "\\t"
    else if n >= 0x20 && n <= 0x7E then s := s.push (Char.ofNat n)
    else
      let h1 := hexChars.getD (n >>> 4) '0'
      let h2 := hexChars.getD (n &&& 0x0F) '0'
      s := s ++ s!"\\{h1}{h2}"
  return s

mutual
  /- REF: wasm-text-instructions#instructions -/
  /-- Formats a structured instruction into WAT text format with proper indentation. -/
  def formatInstr (level : Nat) (instr : WasmInstr) : List String :=
    match instr with
    | .unreachable => [indent level "unreachable"]
    | .nop         => [indent level "nop"]
    | .block bt body =>
      [indent level s!"block{formatBlockType bt}"] ++
      formatInstrList (level + 1) body ++
      [indent level "end"]
    | .loop bt body =>
      [indent level s!"loop{formatBlockType bt}"] ++
      formatInstrList (level + 1) body ++
      [indent level "end"]
    | .if_else bt thenBody elseBody =>
      if elseBody.isEmpty then
        [indent level s!"if{formatBlockType bt}"] ++
        formatInstrList (level + 1) thenBody ++
        [indent level "end"]
      else
        [indent level s!"if{formatBlockType bt}"] ++
        formatInstrList (level + 1) thenBody ++
        [indent level "else"] ++
        formatInstrList (level + 1) elseBody ++
        [indent level "end"]
    | .br depth       => [indent level s!"br {depth}"]
    | .br_if depth    => [indent level s!"br_if {depth}"]
    | .return_op      => [indent level "return"]
    | .call funcIdx   => [indent level s!"call {funcIdx}"]
    | .drop           => [indent level "drop"]
    | .select_op      => [indent level "select"]
    | .local_get idx  => [indent level s!"local.get {idx}"]
    | .local_set idx  => [indent level s!"local.set {idx}"]
    | .local_tee idx  => [indent level s!"local.tee {idx}"]
    | .global_get idx => [indent level s!"global.get {idx}"]
    | .global_set idx => [indent level s!"global.set {idx}"]

    | .i32_load align offset =>
      let alignStr := if align != 0 then s!" align={align}" else ""
      let offsetStr := if offset != 0 then s!" offset={offset}" else ""
      [indent level s!"i32.load{alignStr}{offsetStr}"]
    | .i32_load8_u align offset =>
      let alignStr := if align != 0 then s!" align={align}" else ""
      let offsetStr := if offset != 0 then s!" offset={offset}" else ""
      [indent level s!"i32.load8_u{alignStr}{offsetStr}"]
    | .i64_load align offset =>
      let alignStr := if align != 0 then s!" align={align}" else ""
      let offsetStr := if offset != 0 then s!" offset={offset}" else ""
      [indent level s!"i64.load{alignStr}{offsetStr}"]
    | .i32_store align offset =>
      let alignStr := if align != 0 then s!" align={align}" else ""
      let offsetStr := if offset != 0 then s!" offset={offset}" else ""
      [indent level s!"i32.store{alignStr}{offsetStr}"]
    | .i64_store align offset =>
      let alignStr := if align != 0 then s!" align={align}" else ""
      let offsetStr := if offset != 0 then s!" offset={offset}" else ""
      [indent level s!"i64.store{alignStr}{offsetStr}"]
    | .i32_store8 align offset =>
      let alignStr := if align != 0 then s!" align={align}" else ""
      let offsetStr := if offset != 0 then s!" offset={offset}" else ""
      [indent level s!"i32.store8{alignStr}{offsetStr}"]
    | .memory_size => [indent level "memory.size"]
    | .memory_grow => [indent level "memory.grow"]

    | .i32_const v => [indent level s!"i32.const {v}"]
    | .i64_const v => [indent level s!"i64.const {v}"]

    | .i32_eqz   => [indent level "i32.eqz"]
    | .i32_eq    => [indent level "i32.eq"]
    | .i32_ne    => [indent level "i32.ne"]
    | .i32_lt_u  => [indent level "i32.lt_u"]
    | .i32_gt_u  => [indent level "i32.gt_u"]
    | .i32_le_u  => [indent level "i32.le_u"]
    | .i32_ge_u  => [indent level "i32.ge_u"]
    | .i32_add   => [indent level "i32.add"]
    | .i32_sub   => [indent level "i32.sub"]
    | .i32_mul   => [indent level "i32.mul"]
    | .i32_div_u => [indent level "i32.div_u"]
    | .i32_rem_u => [indent level "i32.rem_u"]
    | .i32_and   => [indent level "i32.and"]
    | .i32_or    => [indent level "i32.or"]
    | .i32_xor   => [indent level "i32.xor"]
    | .i32_shl   => [indent level "i32.shl"]
    | .i32_shr_u => [indent level "i32.shr_u"]

    | .i64_eqz   => [indent level "i64.eqz"]
    | .i64_eq    => [indent level "i64.eq"]
    | .i64_ne    => [indent level "i64.ne"]
    | .i64_lt_u  => [indent level "i64.lt_u"]
    | .i64_gt_u  => [indent level "i64.gt_u"]
    | .i64_le_u  => [indent level "i64.le_u"]
    | .i64_ge_u  => [indent level "i64.ge_u"]
    | .i64_add   => [indent level "i64.add"]
    | .i64_sub   => [indent level "i64.sub"]
    | .i64_mul   => [indent level "i64.mul"]
    | .i64_div_u => [indent level "i64.div_u"]
    | .i64_rem_u => [indent level "i64.rem_u"]
    | .i64_and   => [indent level "i64.and"]
    | .i64_or    => [indent level "i64.or"]
    | .i64_xor   => [indent level "i64.xor"]
    | .i64_shl   => [indent level "i64.shl"]
    | .i64_shr_u => [indent level "i64.shr_u"]

    | .i32_wrap_i64     => [indent level "i32.wrap_i64"]
    | .i64_extend_i32_u => [indent level "i64.extend_i32_u"]

  /- REF: wasm-text-instructions#instructions -/
  /-- Formats a list of instructions into WAT format. -/
  def formatInstrList (level : Nat) (instrs : List WasmInstr) : List String :=
    instrs.flatMap (formatInstr level)
end

end Gasm.Targets.Wasm
