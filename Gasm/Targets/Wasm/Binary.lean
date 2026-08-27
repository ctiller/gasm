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
import Gasm.Targets.Wasm.LEB128

namespace Gasm.Targets.Wasm

open Gasm.Core

/- REF: wasm-binary-modules#modules-1 -/
/-- WebAssembly binary format magic bytes 0x00 0x61 0x73 0x6D ('\0asm'). -/
def wasmMagic : ByteArray :=
  ByteArray.mk #[0x00, 0x61, 0x73, 0x6D]

/- REF: wasm-binary-modules#modules-1 -/
/-- WebAssembly version 1 (0x01 0x00 0x00 0x00). -/
def wasmVersion : ByteArray :=
  ByteArray.mk #[0x01, 0x00, 0x00, 0x00]

/- REF: wasm-binary-modules#sections -/
/-- Serializes a section header and payload. -/
def encodeSection (sectionId : UInt8) (payload : ByteArray) : ByteArray :=
  ByteArray.mk #[sectionId] ++ encodeULEB128 payload.size ++ payload

/- REF: wasm-syntax-types#value-types -/
/-- Serializes a value type code. -/
def encodeValType : ValType → UInt8
  | .i32 => 0x7F
  | .i64 => 0x7E
  | .f32 => 0x7D
  | .f64 => 0x7C

/- REF: wasm-syntax-types#block-types -/
/-- Serializes a block return type descriptor. -/
def encodeBlockType : BlockType → ByteArray
  | .empty => ByteArray.mk #[0x40]
  | .val t => ByteArray.mk #[encodeValType t]

/- REF: wasm-syntax-types#composite-types -/
/-- Serializes a function signature into the binary type format. -/
def encodeFuncType (ft : FuncType) : ByteArray :=
  let paramsBytes := encodeULEB128 ft.params.length ++ ByteArray.mk (ft.params.map encodeValType).toArray
  let resultsBytes := encodeULEB128 ft.results.length ++ ByteArray.mk (ft.results.map encodeValType).toArray
  ByteArray.mk #[0x60] ++ paramsBytes ++ resultsBytes

/- REF: wasm-syntax-types#limits -/
/-- Serializes memory limits. -/
def encodeLimits (limits : Limits) : ByteArray :=
  match limits.max with
  | none => ByteArray.mk #[0x00] ++ encodeU32 limits.min
  | some m => ByteArray.mk #[0x01] ++ encodeU32 limits.min ++ encodeU32 m

/- REF: wasm-syntax-types#memory-types -/
/-- Serializes a memory type descriptor. -/
def encodeMemType (mem : MemType) : ByteArray :=
  encodeLimits mem.limits

/- REF: wasm-binary-values#integers -/
/-- Converts unsigned UInt32 to signed two's-complement Int for SLEB128 encoding. -/
def toSignedI32 (v : UInt32) : Int :=
  if v.toNat >= 0x80000000 then (Int.ofNat v.toNat) - 0x100000000 else Int.ofNat v.toNat

/- REF: wasm-binary-values#integers -/
/-- Converts unsigned UInt64 to signed two's-complement Int for SLEB128 encoding. -/
def toSignedI64 (v : UInt64) : Int :=
  if v.toNat >= 0x8000000000000000 then (Int.ofNat v.toNat) - 0x10000000000000000 else Int.ofNat v.toNat

mutual
  /- REF: wasm-binary-instructions#instructions -/
  /-- Serializes a single structured instruction into its binary byte sequence. -/
  def encodeInstr (instr : WasmInstr) : ByteArray :=
    match instr with
    | .unreachable => ByteArray.mk #[0x00]
    | .nop         => ByteArray.mk #[0x01]
    | .block bt body =>
      ByteArray.mk #[0x02] ++ encodeBlockType bt ++ encodeInstrList body ++ ByteArray.mk #[0x0B]
    | .loop bt body =>
      ByteArray.mk #[0x03] ++ encodeBlockType bt ++ encodeInstrList body ++ ByteArray.mk #[0x0B]
    | .if_else bt thenBody elseBody =>
      if elseBody.isEmpty then
        ByteArray.mk #[0x04] ++ encodeBlockType bt ++ encodeInstrList thenBody ++ ByteArray.mk #[0x0B]
      else
        ByteArray.mk #[0x04] ++ encodeBlockType bt ++ encodeInstrList thenBody ++ ByteArray.mk #[0x05] ++ encodeInstrList elseBody ++ ByteArray.mk #[0x0B]
    | .br depth       => ByteArray.mk #[0x0C] ++ encodeULEB128 depth
    | .br_if depth    => ByteArray.mk #[0x0D] ++ encodeULEB128 depth
    | .return_op      => ByteArray.mk #[0x0F]
    | .call funcIdx   => ByteArray.mk #[0x10] ++ encodeULEB128 funcIdx
    | .drop           => ByteArray.mk #[0x1A]
    | .select_op      => ByteArray.mk #[0x1B]

    | .local_get idx  => ByteArray.mk #[0x20] ++ encodeULEB128 idx
    | .local_set idx  => ByteArray.mk #[0x21] ++ encodeULEB128 idx
    | .local_tee idx  => ByteArray.mk #[0x22] ++ encodeULEB128 idx
    | .global_get idx => ByteArray.mk #[0x23] ++ encodeULEB128 idx
    | .global_set idx => ByteArray.mk #[0x24] ++ encodeULEB128 idx

    | .i32_load align offset => ByteArray.mk #[0x28] ++ encodeULEB128 align ++ encodeULEB128 offset
    | .i32_load8_u align offset => ByteArray.mk #[0x2D] ++ encodeULEB128 align ++ encodeULEB128 offset
    | .i64_load align offset => ByteArray.mk #[0x29] ++ encodeULEB128 align ++ encodeULEB128 offset
    | .i32_store align offset => ByteArray.mk #[0x36] ++ encodeULEB128 align ++ encodeULEB128 offset
    | .i64_store align offset => ByteArray.mk #[0x37] ++ encodeULEB128 align ++ encodeULEB128 offset
    | .i32_store8 align offset => ByteArray.mk #[0x3A] ++ encodeULEB128 align ++ encodeULEB128 offset
    | .memory_size => ByteArray.mk #[0x3F, 0x00]
    | .memory_grow => ByteArray.mk #[0x40, 0x00]

    | .i32_const v => ByteArray.mk #[0x41] ++ encodeI32SLEB128 (toSignedI32 v)
    | .i64_const v => ByteArray.mk #[0x42] ++ encodeI64SLEB128 (toSignedI64 v)

    | .i32_eqz   => ByteArray.mk #[0x45]
    | .i32_eq    => ByteArray.mk #[0x46]
    | .i32_ne    => ByteArray.mk #[0x47]
    | .i32_lt_u  => ByteArray.mk #[0x49]
    | .i32_gt_u  => ByteArray.mk #[0x4B]
    | .i32_le_u  => ByteArray.mk #[0x4D]
    | .i32_ge_u  => ByteArray.mk #[0x4F]
    | .i32_add   => ByteArray.mk #[0x6A]
    | .i32_sub   => ByteArray.mk #[0x6B]
    | .i32_mul   => ByteArray.mk #[0x6C]
    | .i32_div_u => ByteArray.mk #[0x6E]
    | .i32_rem_u => ByteArray.mk #[0x70]
    | .i32_and   => ByteArray.mk #[0x71]
    | .i32_or    => ByteArray.mk #[0x72]
    | .i32_xor   => ByteArray.mk #[0x73]
    | .i32_shl   => ByteArray.mk #[0x74]
    | .i32_shr_u => ByteArray.mk #[0x76]

    | .i64_eqz   => ByteArray.mk #[0x50]
    | .i64_eq    => ByteArray.mk #[0x51]
    | .i64_ne    => ByteArray.mk #[0x52]
    | .i64_lt_u  => ByteArray.mk #[0x54]
    | .i64_gt_u  => ByteArray.mk #[0x56]
    | .i64_le_u  => ByteArray.mk #[0x58]
    | .i64_ge_u  => ByteArray.mk #[0x5A]
    | .i64_add   => ByteArray.mk #[0x7C]
    | .i64_sub   => ByteArray.mk #[0x7D]
    | .i64_mul   => ByteArray.mk #[0x7E]
    | .i64_div_u => ByteArray.mk #[0x80]
    | .i64_rem_u => ByteArray.mk #[0x82]
    | .i64_and   => ByteArray.mk #[0x83]
    | .i64_or    => ByteArray.mk #[0x84]
    | .i64_xor   => ByteArray.mk #[0x85]
    | .i64_shl   => ByteArray.mk #[0x86]
    | .i64_shr_u => ByteArray.mk #[0x88]

    | .i32_wrap_i64     => ByteArray.mk #[0xA7]
    | .i64_extend_i32_u => ByteArray.mk #[0xAD]

  /- REF: wasm-binary-instructions#instructions -/
  /-- Serializes a list of instructions into binary format. -/
  def encodeInstrList (instrs : List WasmInstr) : ByteArray :=
    instrs.foldl (fun acc i => acc ++ encodeInstr i) ByteArray.empty
end

end Gasm.Targets.Wasm
