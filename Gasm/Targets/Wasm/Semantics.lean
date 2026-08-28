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
import Gasm.Core.Arch
import Gasm.Core.Types
import Gasm.Effects.Trace
import Gasm.Targets.Wasm.Types
import Gasm.Targets.Wasm.AST

namespace Gasm.Targets.Wasm

open Gasm.Core
open Gasm.Effects

/- REF: wasm-exec-runtime#values -/
/-- Runtime typed value representation on the operand stack and locals. -/
inductive WasmVal where
  | i32 : UInt32 → WasmVal
  | i64 : UInt64 → WasmVal
  deriving Repr, DecidableEq, BEq, Inhabited

/- REF: wasm-exec-runtime#configurations -/
/-- Pure machine state for the WebAssembly runtime interpreter. -/
structure WasmMachineState where
  stack            : List WasmVal := []
  locals           : List WasmVal := []
  memory           : ByteArray    := ByteArray.empty
  -- REF: wasm-exec-runtime#memory-instances -- "It is an invariant of the semantics that the
  -- length of the byte sequence, divided by page size, never exceeds the maximum size of
  -- memtype." `memMax` (in 64 KiB pages, matching the Wasm `mem.grow`/`Limits.max` unit) is that
  -- declared maximum for this machine's linear memory, threaded through from the module's
  -- `MemType`/`Limits` (`Types.lean`) at instantiation time; `none` means no maximum was
  -- declared (B8: previously this bound existed in `Limits.max` but was never consulted by
  -- `memory_grow` at all -- see that instruction's case in `evalInstr` below). Defaults to
  -- `none` so every existing state-literal (`{}`, `{ stack := ... }`, ...) built before this
  -- field existed keeps behaving exactly as it did (an unconstrained memory), not a silent
  -- behavior change.
  memMax           : Option UInt32 := none
  stdin            : ByteArray    := ByteArray.empty
  stdinPos         : Nat          := 0
  incomingRequests : List String  := []
  trapped          : Bool         := false
  exitCode         : Option UInt32 := none
  events           : List AnyEvent := []
  deriving Inhabited

/- REF: wasm-exec-runtime#stack -/
/-- Branch or return control flow signal during structured instruction evaluation. -/
inductive ControlSignal where
  | next : ControlSignal
  | br   : Nat → ControlSignal
  | ret  : ControlSignal
  deriving Repr, DecidableEq, BEq, Inhabited

/- REF: wasm-exec-runtime#stack -/
/-- Pops a 32-bit integer from the operand stack. -/
def popI32 (s : WasmMachineState) : UInt32 × WasmMachineState :=
  match s.stack with
  | .i32 v :: rest => (v, { s with stack := rest })
  | _ => (0, s)

/- REF: wasm-exec-runtime#stack -/
/-- Pops a 64-bit integer from the operand stack. -/
def popI64 (s : WasmMachineState) : UInt64 × WasmMachineState :=
  match s.stack with
  | .i64 v :: rest => (v, { s with stack := rest })
  | _ => (0, s)

/- REF: wasm-exec-runtime#stack -/
/-- Pushes a typed value onto the operand stack. -/
def pushVal (val : WasmVal) (s : WasmMachineState) : WasmMachineState :=
  { s with stack := val :: s.stack }

/- REF: wasm-exec-instructions#memory-instructions -/
/-- Reads an 8-bit byte from linear memory, IF `addr` is in bounds. Per the WebAssembly
    specification's reduction rule for `t.load` (`wasm-exec-instructions#memory-instructions`:
    "If `i + ao.offset + |nt|/8 > |mems[x].bytes|`, then: Trap."), an out-of-bounds read must trap
    the instruction, not silently return a default value. That bounds check belongs to `evalInstr`
    (its `.i32_load`/`.i32_load8_u`/`.i64_load` cases set `trapped := true` and never call this
    function when the access is out of bounds), so this helper only ever runs on an address
    already known in-bounds; it stays total (returns `0` for `addr >= mem.size`) purely as
    defense-in-depth for any future caller that forgets that precondition, not as a substitute for
    the trap. -/
def readMem8 (mem : ByteArray) (addr : Nat) : UInt8 :=
  if addr < mem.size then mem.get! addr else 0

/- REF: wasm-exec-runtime#memory-instances -/
/-- Reads a 32-bit little-endian integer from linear memory. -/
def readMem32 (mem : ByteArray) (addr : Nat) : UInt32 :=
  if addr + 4 <= mem.size then
    let b0 := (readMem8 mem addr).toUInt32
    let b1 := (readMem8 mem (addr + 1)).toUInt32
    let b2 := (readMem8 mem (addr + 2)).toUInt32
    let b3 := (readMem8 mem (addr + 3)).toUInt32
    b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
  else 0

/- REF: wasm-exec-runtime#memory-instances -/
/-- Reads an 8-byte 64-bit integer from linear memory. -/
def readMem64 (mem : ByteArray) (addr : Nat) : UInt64 :=
  let b0 : UInt64 := (readMem8 mem addr).toUInt64
  let b1 : UInt64 := (readMem8 mem (addr + 1)).toUInt64
  let b2 : UInt64 := (readMem8 mem (addr + 2)).toUInt64
  let b3 : UInt64 := (readMem8 mem (addr + 3)).toUInt64
  let b4 : UInt64 := (readMem8 mem (addr + 4)).toUInt64
  let b5 : UInt64 := (readMem8 mem (addr + 5)).toUInt64
  let b6 : UInt64 := (readMem8 mem (addr + 6)).toUInt64
  let b7 : UInt64 := (readMem8 mem (addr + 7)).toUInt64
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

/- REF: wasm-exec-instructions#memory-instructions -/
/-- Writes an 8-bit byte into linear memory, IF `addr` is in bounds. Per the WebAssembly
    specification's reduction rule for `t.store` (`wasm-exec-instructions#memory-instructions`:
    "If `i + ao.offset + |nt|/8 > |mems[x].bytes|`, then: Trap."), any out-of-bounds memory access
    must trap the whole instruction rather than mutate memory at all -- it must NOT silently grow
    the store to accommodate the address. That bounds check is `evalInstr`'s responsibility (its
    `.i32_store`/`.i32_store8`/`.i64_store` cases set `trapped := true` and never call this
    function at all when the access is out of bounds), so this helper only ever runs on an
    address already known in-bounds. It stays a total no-op (returns `mem` unchanged) for `addr >=
    mem.size` purely as defense-in-depth against a future caller that forgets that precondition --
    NOT as an alternate, silent way to "handle" an out-of-bounds write. This replaces the previous
    (B7) behaviour of zero-padding and growing `mem` to fit `addr`, which let an out-of-bounds
    write silently succeed and corrupt `memory_size`'s subsequent answers instead of trapping. -/
def writeMem8 (mem : ByteArray) (addr : Nat) (val : UInt8) : ByteArray :=
  if addr < mem.size then mem.set! addr val else mem

/- REF: wasm-exec-runtime#memory-instances -/
/-- Writes a 32-bit little-endian integer into linear memory. -/
def writeMem32 (mem : ByteArray) (addr : Nat) (val : UInt32) : ByteArray :=
  let b0 := (val &&& 0xFF).toUInt8
  let b1 := ((val >>> 8) &&& 0xFF).toUInt8
  let b2 := ((val >>> 16) &&& 0xFF).toUInt8
  let b3 := ((val >>> 24) &&& 0xFF).toUInt8
  let m0 := writeMem8 mem addr b0
  let m1 := writeMem8 m0 (addr + 1) b1
  let m2 := writeMem8 m1 (addr + 2) b2
  writeMem8 m2 (addr + 3) b3

/- REF: wasm-exec-runtime#memory-instances -/
/-- Writes an 8-byte 64-bit integer into linear memory. -/
def writeMem64 (mem : ByteArray) (addr : Nat) (val : UInt64) : ByteArray :=
  let b0 := (val &&& 0xFF).toUInt8
  let b1 := ((val >>> 8) &&& 0xFF).toUInt8
  let b2 := ((val >>> 16) &&& 0xFF).toUInt8
  let b3 := ((val >>> 24) &&& 0xFF).toUInt8
  let b4 := ((val >>> 32) &&& 0xFF).toUInt8
  let b5 := ((val >>> 40) &&& 0xFF).toUInt8
  let b6 := ((val >>> 48) &&& 0xFF).toUInt8
  let b7 := ((val >>> 56) &&& 0xFF).toUInt8
  let m0 := writeMem8 mem addr b0
  let m1 := writeMem8 m0 (addr + 1) b1
  let m2 := writeMem8 m1 (addr + 2) b2
  let m3 := writeMem8 m2 (addr + 3) b3
  let m4 := writeMem8 m3 (addr + 4) b4
  let m5 := writeMem8 m4 (addr + 5) b5
  let m6 := writeMem8 m5 (addr + 6) b6
  writeMem8 m6 (addr + 7) b7

mutual
  /- REF: wasm-exec-instructions#instructions -/
  /-- Operational evaluation for structured WebAssembly instruction execution. -/
  partial def evalInstr (instr : WasmInstr) (s : WasmMachineState)
      (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal) : WasmMachineState × ControlSignal :=
    if s.trapped || s.exitCode.isSome then
      (s, .next)
    else
      match instr with
      | .unreachable => ({ s with trapped := true }, .next)
      | .nop => (s, .next)
      | .i32_const v => (pushVal (.i32 v) s, .next)
      | .i64_const v => (pushVal (.i64 v) s, .next)
      | .drop =>
        match s.stack with
        | _ :: rest => ({ s with stack := rest }, .next)
        | [] => (s, .next)
      | .select_op =>
        let (c, s1) := popI32 s
        match s1.stack with
        | val2 :: val1 :: rest =>
          let chosen := if c != 0 then val1 else val2
          ({ s1 with stack := chosen :: rest }, .next)
        | _ => (s1, .next)
      | .local_get idx =>
        let val := s.locals.getD idx (.i32 0)
        (pushVal val s, .next)
      | .local_set idx =>
        match s.stack with
        | v :: rest =>
          let newLocals :=
            if idx < s.locals.length then
              s.locals.set idx v
            else
              s.locals ++ List.replicate (idx - s.locals.length) (.i32 0) ++ [v]
          ({ s with stack := rest, locals := newLocals }, .next)
        | [] => (s, .next)
      | .local_tee idx =>
        match s.stack with
        | v :: _ =>
          let newLocals :=
            if idx < s.locals.length then
              s.locals.set idx v
            else
              s.locals ++ List.replicate (idx - s.locals.length) (.i32 0) ++ [v]
          ({ s with locals := newLocals }, .next)
        | [] => (s, .next)

      -- 32-bit Arithmetic & Bitwise
      | .i32_add =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 + v2)) s2, .next)
      | .i32_sub =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 - v2)) s2, .next)
      | .i32_mul =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 * v2)) s2, .next)
      | .i32_div_u =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        if v2 == 0 then ({ s2 with trapped := true }, .next)
        else (pushVal (.i32 (v1 / v2)) s2, .next)
      | .i32_rem_u =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        if v2 == 0 then ({ s2 with trapped := true }, .next)
        else (pushVal (.i32 (v1 % v2)) s2, .next)
      | .i32_and =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 &&& v2)) s2, .next)
      | .i32_or =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 ||| v2)) s2, .next)
      | .i32_xor =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 ^^^ v2)) s2, .next)
      | .i32_shl =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 <<< (v2 % 32))) s2, .next)
      | .i32_shr_u =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 >>> (v2 % 32))) s2, .next)

      -- 32-bit Comparisons
      | .i32_eqz =>
        let (v, s1) := popI32 s
        (pushVal (.i32 (if v == 0 then 1 else 0)) s1, .next)
      | .i32_eq =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (if v1 == v2 then 1 else 0)) s2, .next)
      | .i32_ne =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (if v1 != v2 then 1 else 0)) s2, .next)
      | .i32_lt_u =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (if v1 < v2 then 1 else 0)) s2, .next)
      | .i32_gt_u =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (if v1 > v2 then 1 else 0)) s2, .next)
      | .i32_le_u =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (if v1 <= v2 then 1 else 0)) s2, .next)
      | .i32_ge_u =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (if v1 >= v2 then 1 else 0)) s2, .next)

      -- 64-bit Arithmetic & Bitwise
      | .i64_add =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 + v2)) s2, .next)
      | .i64_sub =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 - v2)) s2, .next)
      | .i64_mul =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 * v2)) s2, .next)
      | .i64_div_u =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        if v2 == 0 then ({ s2 with trapped := true }, .next)
        else (pushVal (.i64 (v1 / v2)) s2, .next)
      | .i64_rem_u =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        if v2 == 0 then ({ s2 with trapped := true }, .next)
        else (pushVal (.i64 (v1 % v2)) s2, .next)
      | .i64_and =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 &&& v2)) s2, .next)
      | .i64_or =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 ||| v2)) s2, .next)
      | .i64_xor =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 ^^^ v2)) s2, .next)
      | .i64_shl =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 <<< (v2 % 64))) s2, .next)
      | .i64_shr_u =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 >>> (v2 % 64))) s2, .next)

      -- 64-bit Comparisons
      | .i64_eqz =>
        let (v, s1) := popI64 s
        (pushVal (.i32 (if v == 0 then 1 else 0)) s1, .next)
      | .i64_eq =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i32 (if v1 == v2 then 1 else 0)) s2, .next)
      | .i64_ne =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i32 (if v1 != v2 then 1 else 0)) s2, .next)
      | .i64_lt_u =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i32 (if v1 < v2 then 1 else 0)) s2, .next)
      | .i64_gt_u =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i32 (if v1 > v2 then 1 else 0)) s2, .next)
      | .i64_le_u =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i32 (if v1 <= v2 then 1 else 0)) s2, .next)
      | .i64_ge_u =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i32 (if v1 >= v2 then 1 else 0)) s2, .next)

      -- Memory Loads & Stores
      -- REF: wasm-exec-instructions#memory-instructions -- every case below implements the exact
      -- reduction rule "If i + ao.offset + N/8 > |mems[x].bytes|, then: Trap." (B7): the bounds
      -- check happens HERE, before `writeMemN`/`readMemN` is ever invoked, so an out-of-bounds
      -- access sets `trapped := true` and never touches `memory` at all -- it can no longer
      -- silently grow the byte array or return a fabricated `0`, and a subsequent `memory_size`
      -- can no longer observe a size change that a trapped instruction never should have caused.
      | .i32_store _ offset =>
        let (val, s1) := popI32 s
        let (addr, s2) := popI32 s1
        let a := addr.toNat + offset
        if a + 4 > s2.memory.size then ({ s2 with trapped := true }, .next)
        else ({ s2 with memory := writeMem32 s2.memory a val }, .next)
      | .i32_store8 _ offset =>
        let (val, s1) := popI32 s
        let (addr, s2) := popI32 s1
        let a := addr.toNat + offset
        if a + 1 > s2.memory.size then ({ s2 with trapped := true }, .next)
        else ({ s2 with memory := writeMem8 s2.memory a (val.toUInt8) }, .next)
      | .i32_load _ offset =>
        let (addr, s1) := popI32 s
        let a := addr.toNat + offset
        if a + 4 > s1.memory.size then ({ s1 with trapped := true }, .next)
        else (pushVal (.i32 (readMem32 s1.memory a)) s1, .next)
      | .i32_load8_u _ offset =>
        let (addr, s1) := popI32 s
        let a := addr.toNat + offset
        if a + 1 > s1.memory.size then ({ s1 with trapped := true }, .next)
        else (pushVal (.i32 (readMem8 s1.memory a).toUInt32) s1, .next)
      | .i64_store _ offset =>
        let (val, s1) := popI64 s
        let (addr, s2) := popI32 s1
        let a := addr.toNat + offset
        if a + 8 > s2.memory.size then ({ s2 with trapped := true }, .next)
        else ({ s2 with memory := writeMem64 s2.memory a val }, .next)
      | .i64_load _ offset =>
        let (addr, s1) := popI32 s
        let a := addr.toNat + offset
        if a + 8 > s1.memory.size then ({ s1 with trapped := true }, .next)
        else (pushVal (.i64 (readMem64 s1.memory a)) s1, .next)
      | .memory_size =>
        let pages := (s.memory.size + 65535) / 65536
        (pushVal (.i32 pages.toUInt32) s, .next)
      | .memory_grow =>
        -- REF: wasm-exec-instructions#memory-instructions -- "The memory.grow instruction is
        -- non-deterministic. It may either succeed, returning the old memory size sz, or fail,
        -- returning -1. Failure MUST occur if the referenced memory instance has a maximum size
        -- defined that would be exceeded." (B8.) `s1.memMax` is that declared maximum (in pages,
        -- REF: wasm-exec-runtime#memory-instances's meminst-max invariant), threaded through from
        -- the module's `Limits.max` (`Types.lean`) at instantiation. `hardCeilingPages` additionally
        -- enforces the Wasm32 address-space ceiling of 2^16 pages (4 GiB): this model's `WasmArch`
        -- addresses linear memory with 32-bit (`i32`) offsets (`TargetArch.wordWidth := 32` below),
        -- so a page count beyond 2^16 could never be addressed by any load/store this interpreter
        -- accepts, independent of whatever `memMax` was (or wasn't) declared. Whichever bound
        -- fires, growth fails WITHOUT mutating `memory` at all -- unlike the pre-fix (B8) behaviour,
        -- which always grew unconditionally and never returned the `-1` sentinel.
        let (delta, s1) := popI32 s
        let oldPages := (s1.memory.size + 65535) / 65536
        let requestedPages := oldPages + delta.toNat
        let hardCeilingPages : Nat := 65536
        let exceedsDeclaredMax := match s1.memMax with
          | some maxP => requestedPages > maxP.toNat
          | none => false
        if exceedsDeclaredMax || requestedPages > hardCeilingPages then
          (pushVal (.i32 (0xFFFFFFFF : UInt32)) s1, .next)
        else
          let padding := ByteArray.mk (Array.mk (List.replicate (delta.toNat * 65536) (0 : UInt8)))
          (pushVal (.i32 oldPages.toUInt32) { s1 with memory := s1.memory ++ padding }, .next)

      -- Conversions
      | .i32_wrap_i64 =>
        let (v, s1) := popI64 s
        (pushVal (.i32 v.toUInt32) s1, .next)
      | .i64_extend_i32_u =>
        let (v, s1) := popI32 s
        (pushVal (.i64 v.toUInt64) s1, .next)

      -- Calls & Control
      | .call idx => hostCall idx s

      -- Structured Control Flow
      | .br depth => (s, .br depth)
      | .br_if depth =>
        let (c, s1) := popI32 s
        if c != 0 then (s1, .br depth) else (s1, .next)
      | .return_op => (s, .ret)
      | .block _ body =>
        let (s', sig) := evalInstrs body s hostCall
        match sig with
        | .br 0 => (s', .next)
        | .br (d + 1) => (s', .br d)
        | other => (s', other)
      | .loop _ body =>
        evalLoop body s hostCall
      | .if_else _ thenBody elseBody =>
        let (c, s1) := popI32 s
        let (s', sig) := if c != 0 then evalInstrs thenBody s1 hostCall
                         else evalInstrs elseBody s1 hostCall
        match sig with
        | .br 0 => (s', .next)
        | .br (d + 1) => (s', .br d)
        | other => (s', other)
      | _ => (s, .next)

  /- REF: wasm-exec-instructions#expressions -/
  /-- Evaluates a list of instructions in sequence. -/
  partial def evalInstrs (instrs : List WasmInstr) (st : WasmMachineState)
      (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal) : WasmMachineState × ControlSignal :=
    match instrs with
    | [] => (st, .next)
    | i :: rest =>
      let (st', sig) := evalInstr i st hostCall
      match sig with
      | .next => evalInstrs rest st' hostCall
      | other => (st', other)

  /- REF: wasm-exec-instructions#blocks -/
  /-- Evaluates a loop body repeatedly until loop exit. -/
  partial def evalLoop (body : List WasmInstr) (st : WasmMachineState)
      (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal) : WasmMachineState × ControlSignal :=
    let (st', sig) := evalInstrs body st hostCall
    match sig with
    | .next => (st', .next)
    | .br 0 => evalLoop body st' hostCall
    | .br (d + 1) => (st', .br d)
    | .ret => (st', .ret)
end

/- REF: wasm-exec-instructions#instructions -/
/-- Pure operational step evaluation for single instruction. -/
def stepWasm (instr : WasmInstr) (s : WasmMachineState) : WasmMachineState :=
  (evalInstr instr s (fun _ st => (st, .next))).1

/- REF: wasm-exec-instructions#function-calls -/
/-- Evaluates an entire sequence of structured WebAssembly instructions starting from initial locals. -/
def runWasmFunction (body : List WasmInstr) (locals : List WasmVal) : WasmMachineState :=
  let s : WasmMachineState := { locals := locals }
  (evalInstr (WasmInstr.block .empty body) s (fun _ st => (st, .next))).1

/- REF: docs/TARGETS/WASM.md#1-webassembly-machine-model -/
/-- Architecture tag for WebAssembly target. -/
structure WasmArch where

/- REF: docs/TARGETS/TARGET_MODEL.md#1-vertical-slice-target-structure -/
/-- TargetArch instance for WebAssembly. -/
instance : TargetArch WasmArch where
  wordWidth := 32
  MachineState := WasmMachineState
  Instruction := ULift WasmInstr
  stepPure pkg s := stepWasm pkg.down s

end Gasm.Targets.Wasm
