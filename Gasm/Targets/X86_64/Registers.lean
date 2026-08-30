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
import Gasm.Core.CFG
import Gasm.Targets.X86_64.MemoryCell

namespace Gasm.Targets.X86_64

open Gasm.Core

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Architecture tag for 64-bit x86. -/
structure X86_64

/- REF: intel-sdm#vol=1;sec=3.4;part=34-basic-program-execution-registers -/
/-- 64-bit general-purpose registers. -/
inductive Reg64 where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=1;sec=3.4;part=34-basic-program-execution-registers -/
/-- 32-bit sub-registers. -/
inductive Reg32 where
  | eax | ecx | edx | ebx | esp | ebp | esi | edi
  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=1;sec=3.4;part=34-basic-program-execution-registers -/
/-- Maps a 32-bit sub-register to its enclosing 64-bit general-purpose register. -/
def reg32To64 (r : Reg32) : Reg64 :=
  match r with
  | .eax => .rax | .ecx => .rcx | .edx => .rdx | .ebx => .rbx
  | .esp => .rsp | .ebp => .rbp | .esi => .rsi | .edi => .rdi
  | .r8d => .r8  | .r9d => .r9  | .r10d => .r10 | .r11d => .r11
  | .r12d => .r12 | .r13d => .r13 | .r14d => .r14 | .r15d => .r15

/- REF: docs/MEMORY_HOOK.md#6-faults-and-observability -/
/-- Distinguishable x86-64 stop reasons carried by `X86_64MachineState.fault`. `divideError` is
    DIV/IDIV's #DE; `memFault` is the data-carrying memory fault the design names (unreachable
    today -- no memory-map model exists yet, `docs/MEMORY_HOOK.md` §6 stage 2 -- but distinct in
    the type from the day it exists rather than a third indistinguishable outcome). `halted` is
    an honest addition beyond the design's two-constructor sketch: the evidence base the design
    reasoned from (§1.1: "only Div.lean sets it") undercounted the writer sites -- `Hlt.lean`'s
    HLT, `Linux/Syscall.lean`'s `sysExitHook`, and `BareMetal/Device.lean`'s HLT/debug-exit port
    also set the old `faulted := true` to stop the trace/loop evaluators, and none of those is a
    divide error. Folding them into `.divideError` would mislabel a clean halt as a CPU exception;
    `.halted` keeps every one of those honestly distinct while preserving the exact prior
    `faulted` boolean behavior (see `X86_64MachineState.faulted` below). -/
inductive X86_64Fault where
  | divideError
  | memFault (kind : MemAccessKind) (width : MemWidth) (addr : Address)
  | halted
  /-- A selected host process termination marker.  This stops the machine loop but is classified
      as `NativeTerminalCause.processExit`, never as a CPU fault or architectural HLT. -/
  | processExit (code : UInt32)
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Native machine execution state for x86-64 with unified general-purpose registers. `memory` is
    the sealed `X86_64Memory` cell (`docs/MEMORY_HOOK.md` §3.2): no code outside
    `MemoryCell.lean` can construct or project it directly, so `X86_64Mem.read`/`write` are the
    only way to observe or change machine memory bytes. -/
structure X86_64MachineState where
  rip              : Address
  gprs             : Reg64 → UInt64
  flags            : UInt64
  memory           : X86_64Memory
  stdinBuffer      : ByteArray := ByteArray.empty
  -- F1 (Law 9 root fix): the request queue holds raw octet strings, matching `stdinBuffer` above.
  -- See `Gasm.Effects.TraceState.incomingRequests` for why `List String` made the honest
  -- `∀ (request : ByteArray)` claim unstatable.
  incomingRequests : List ByteArray := []
  fault            : Option X86_64Fault := none

/- REF: docs/MEMORY_HOOK.md#6-faults-and-observability -/
/-- Whether the machine has stopped (a real fault, or a halt/exit signal) -- every existing
    `if s.faulted then ...` reader compiles unchanged against this `def` since Lean 4 dot-notation
    resolves the same way whether `faulted` is a field or a function. -/
def X86_64MachineState.faulted (s : X86_64MachineState) : Bool := s.fault.isSome

/- REF: docs/MEMORY_HOOK.md#6-faults-and-observability -/
/-- `faulted` in terms of `.fault`, proved once as a small, `s`-abstract lemma. Applying this to a
    concrete (possibly large, e.g. a record update carrying a near-2⁶⁴ constant) state term only
    needs the cheap `.fault = none` fact as an argument -- it does not require the elaborator or
    kernel to separately re-derive the `isSome` unfold against that concrete term's full shape,
    which is what makes a bare `.faulted = false` goal expensive in exactly that situation
    (`Spikes/Spike2Fibonacci/Windows/LoopInvariant.lean`'s `fibLoop_iteration` hit this). -/
theorem X86_64MachineState.faulted_of_fault_none {s : X86_64MachineState} (h : s.fault = none) :
    s.faulted = false := by
  unfold X86_64MachineState.faulted; rw [h]; rfl

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
instance : Inhabited X86_64MachineState where
  default := { rip := 0x401000, gprs := fun _ => 0, flags := 0x202, memory := X86_64Mem.zero }

/- REF: intel-sdm#vol=1;sec=3.4;part=34-basic-program-execution-registers -/
/-- Retrieves the 64-bit stack pointer (RSP). -/
def X86_64MachineState.rsp (s : X86_64MachineState) : Address :=
  s.gprs .rsp

/- REF: intel-sdm#vol=1;sec=3.4;part=34-basic-program-execution-registers -/
/-- Updates 64-bit general-purpose register value. -/
def X86_64MachineState.setGpr64 (s : X86_64MachineState) (r : Reg64) (val : UInt64) : X86_64MachineState :=
  { s with gprs := fun reg => if reg == r then val else s.gprs reg }

/- REF: docs/TARGETS/X86_64.md#11-general-purpose-registers-gprs-32-bit-zero-extension -/
/-- Updates 32-bit sub-register with mandatory 64-bit hardware zero-extension. -/
def X86_64MachineState.setGpr32 (s : X86_64MachineState) (r : Reg32) (val : UInt32) : X86_64MachineState :=
  { s with gprs := fun reg => if reg == reg32To64 r then val.toUInt64 else s.gprs reg }

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Reads zero flag (ZF). -/
def X86_64MachineState.zf (s : X86_64MachineState) : Bool :=
  (s.flags &&& ((1 : UInt64) <<< 6)) != 0

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Reads sign flag (SF). -/
def X86_64MachineState.sf (s : X86_64MachineState) : Bool :=
  (s.flags &&& ((1 : UInt64) <<< 7)) != 0

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Reads carry flag (CF). -/
def X86_64MachineState.cf (s : X86_64MachineState) : Bool :=
  (s.flags &&& ((1 : UInt64) <<< 0)) != 0

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Reads overflow flag (OF). -/
def X86_64MachineState.of_ (s : X86_64MachineState) : Bool :=
  (s.flags &&& ((1 : UInt64) <<< 11)) != 0

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Bitmask for all 6 standard arithmetic status flags (CF: bit 0, PF: bit 2, AF: bit 4, ZF: bit 6, SF: bit 7, OF: bit 11). -/
def arithmeticStatusMask : UInt64 :=
  ((1 : UInt64) <<< 0)  ||| -- CF (bit 0)
  ((1 : UInt64) <<< 2)  ||| -- PF (bit 2)
  ((1 : UInt64) <<< 4)  ||| -- AF (bit 4)
  ((1 : UInt64) <<< 6)  ||| -- ZF (bit 6)
  ((1 : UInt64) <<< 7)  ||| -- SF (bit 7)
  ((1 : UInt64) <<< 11)     -- OF (bit 11)

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Computes Parity Flag (PF: bit 2) for the least-significant 8 bits of a value according to Intel SDM. -/
def computeParity8 (v : UInt64) : UInt64 :=
  let b := v.toUInt8
  let count := (List.range 8).foldl (fun acc i => if (b &&& ((1 : UInt8) <<< i.toUInt8)) != 0 then acc + 1 else acc) 0
  if count % 2 == 0 then ((1 : UInt64) <<< 2) else 0

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Computes Auxiliary Carry Flag (AF: bit 4) for 64-bit addition or subtraction. -/
def computeAuxCarry (a b res : UInt64) : UInt64 :=
  if ((a ^^^ b ^^^ res) &&& 0x10) != 0 then ((1 : UInt64) <<< 4) else 0

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Updates RFLAGS arithmetic condition codes following a 64-bit comparison (a - b) while preserving system flags. -/
def X86_64MachineState.setFlagsCmp64 (s : X86_64MachineState) (a b : UInt64) : X86_64MachineState :=
  let diff := a - b
  let zf : UInt64 := if diff == 0 then ((1 : UInt64) <<< 6) else 0
  let sf : UInt64 := if (diff >>> 63) == 1 then ((1 : UInt64) <<< 7) else 0
  let cf : UInt64 := if a < b then ((1 : UInt64) <<< 0) else 0
  let of_val : UInt64 := if ((a ^^^ b) &&& (a ^^^ diff) &&& ((1 : UInt64) <<< 63)) != 0 then ((1 : UInt64) <<< 11) else 0
  let pf := computeParity8 diff
  let af := computeAuxCarry a b diff
  let preserved := s.flags &&& (~~~arithmeticStatusMask)
  { s with flags := preserved ||| zf ||| sf ||| cf ||| of_val ||| pf ||| af }

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Updates RFLAGS arithmetic condition codes following a 64-bit addition (a + b) while preserving system flags. -/
def X86_64MachineState.setFlagsAdd64 (s : X86_64MachineState) (a b : UInt64) : X86_64MachineState :=
  let sum := a + b
  let zf : UInt64 := if sum == 0 then ((1 : UInt64) <<< 6) else 0
  let sf : UInt64 := if (sum >>> 63) == 1 then ((1 : UInt64) <<< 7) else 0
  let cf : UInt64 := if sum < a then ((1 : UInt64) <<< 0) else 0
  let of_val : UInt64 := if ((~~~(a ^^^ b)) &&& (a ^^^ sum) &&& ((1 : UInt64) <<< 63)) != 0 then ((1 : UInt64) <<< 11) else 0
  let pf := computeParity8 sum
  let af := computeAuxCarry a b sum
  let preserved := s.flags &&& (~~~arithmeticStatusMask)
  { s with flags := preserved ||| zf ||| sf ||| cf ||| of_val ||| pf ||| af }

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Updates RFLAGS arithmetic condition codes following a 64-bit subtraction (a - b). -/
def X86_64MachineState.setFlagsSub64 (s : X86_64MachineState) (a b : UInt64) : X86_64MachineState :=
  s.setFlagsCmp64 a b

/- REF: docs/TARGETS/X86_64.md#11-general-purpose-registers-gprs-32-bit-zero-extension -/
/-- Updates RFLAGS condition codes for bitwise logical operations (AND, OR, XOR, TEST) at a
    given destination operand width (in bits): clears CF, OF, AF, sets ZF, SF, PF from the
    result, preserves system flags. SF must be read from the top bit of the *destination
    operand's* width, not from bit 63 of the register: a narrower-than-64-bit destination is
    always zero-extended into the 64-bit backing register, so bit 63 of that zero-extended
    value is never the correct sign bit for anything narrower than 64 bits (the class of bug
    this width parameter exists to prevent — see `setFlagsLogic64` below and its callers).
    `res` is masked to `width` bits before ZF/SF/PF are derived, so ZF is unconditionally
    correct per the SDM even if a caller passes a value with garbage above bit `width - 1`,
    rather than being correct only by caller discipline. `width = 64` is special-cased (rather
    than computed as `(1 <<< width) - 1`) since shifting a 64-bit value left by 64 wraps the
    shift amount instead of producing zero, which would otherwise yield a mask of 0. -/
def X86_64MachineState.setFlagsLogic (s : X86_64MachineState) (width : UInt64) (res : UInt64) : X86_64MachineState :=
  let widthMask : UInt64 := if width >= 64 then 0xFFFFFFFFFFFFFFFF else ((1 : UInt64) <<< width) - 1
  let res := res &&& widthMask
  let zf : UInt64 := if res == 0 then ((1 : UInt64) <<< 6) else 0
  let sf : UInt64 := if ((res >>> (width - 1)) &&& 1) == 1 then ((1 : UInt64) <<< 7) else 0
  let pf := computeParity8 res
  let preserved := s.flags &&& (~~~arithmeticStatusMask)
  { s with flags := preserved ||| zf ||| sf ||| pf }

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Updates RFLAGS condition codes for 64-bit-destination bitwise logical operations (AND, OR,
    XOR, TEST): the width=64 specialization of `setFlagsLogic`, kept so existing 64-bit call
    sites don't need to spell out the width. -/
def X86_64MachineState.setFlagsLogic64 (s : X86_64MachineState) (res : UInt64) : X86_64MachineState :=
  s.setFlagsLogic 64 res

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Updates RFLAGS condition codes for two's complement negation (NEG r64): 0 - val. -/
def X86_64MachineState.setFlagsNeg64 (s : X86_64MachineState) (val : UInt64) : X86_64MachineState :=
  let res := 0 - val
  let zf : UInt64 := if res == 0 then ((1 : UInt64) <<< 6) else 0
  let sf : UInt64 := if (res >>> 63) == 1 then ((1 : UInt64) <<< 7) else 0
  let cf : UInt64 := if val != 0 then ((1 : UInt64) <<< 0) else 0
  let of_val : UInt64 := if val == 0x8000000000000000 then ((1 : UInt64) <<< 11) else 0
  let pf := computeParity8 res
  let af := computeAuxCarry 0 val res
  let preserved := s.flags &&& (~~~arithmeticStatusMask)
  { s with flags := preserved ||| zf ||| sf ||| cf ||| of_val ||| pf ||| af }

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Updates RFLAGS condition codes for 64-bit shift operations (SHL, SHR, SAR) when count > 0, supporting 1-bit OF semantics. -/
def X86_64MachineState.setFlagsShift64 (s : X86_64MachineState) (res : UInt64) (cfBit : UInt64) (ofBit : UInt64) (count : UInt8) : X86_64MachineState :=
  if count == 0 then s
  else
    let zf : UInt64 := if res == 0 then ((1 : UInt64) <<< 6) else 0
    let sf : UInt64 := if (res >>> 63) == 1 then ((1 : UInt64) <<< 7) else 0
    let cf : UInt64 := if cfBit != 0 then ((1 : UInt64) <<< 0) else 0
    let of_val : UInt64 := if ofBit != 0 then ((1 : UInt64) <<< 11) else 0
    let pf := computeParity8 res
    let preserved := s.flags &&& (~~~arithmeticStatusMask)
    { s with flags := preserved ||| zf ||| sf ||| cf ||| of_val ||| pf }

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Updates RFLAGS condition codes for signed 64-bit multiplication (IMUL r64, r64): sets CF and OF on signed truncation, clears other status flags, preserves system flags. -/
def X86_64MachineState.setFlagsImul64 (s : X86_64MachineState) (a b : UInt64) : X86_64MachineState :=
  let aInt : Int := if (a >>> 63) == 1 then -(0x10000000000000000 - a.toNat : Int) else (a.toNat : Int)
  let bInt : Int := if (b >>> 63) == 1 then -(0x10000000000000000 - b.toNat : Int) else (b.toNat : Int)
  let prodInt := aInt * bInt
  let minInt : Int := -0x8000000000000000
  let maxInt : Int := 0x7FFFFFFFFFFFFFFF
  let overflow := prodInt < minInt || prodInt > maxInt
  let cf_of : UInt64 := if overflow then (((1 : UInt64) <<< 0) ||| ((1 : UInt64) <<< 11)) else 0
  let preserved := s.flags &&& (~~~arithmeticStatusMask)
  { s with flags := preserved ||| cf_of }

/- REF: docs/MEMORY_HOOK.md#31-types-and-api -/
/-- Reads a single byte from machine memory, through the sealed hook. -/
abbrev X86_64MachineState.read8 (s : X86_64MachineState) (a : Address) : UInt64 :=
  X86_64Mem.read .w8 a s.memory

/- REF: docs/MEMORY_HOOK.md#31-types-and-api -/
/-- Reads a 4-byte little-endian doubleword from machine memory, through the sealed hook. This is
    one of the "missing widths" `docs/MEMORY_HOOK.md` §1.1 names: before this hook,
    `MovReg32RspDisp32.step` re-implemented this ladder inline because no `read32` existed. -/
abbrev X86_64MachineState.read32 (s : X86_64MachineState) (a : Address) : UInt64 :=
  X86_64Mem.read .w32 a s.memory

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Reads an 8-byte little-endian quadword from machine memory. Definitionally the same byte
    ladder as before sealing (an `abbrev` into `X86_64Mem.read`), so every existing `rfl` step
    lemma that unfolds this keeps closing (`docs/MEMORY_HOOK.md` §7). -/
abbrev X86_64MachineState.read64 (s : X86_64MachineState) (a : Address) : UInt64 :=
  X86_64Mem.read .w64 a s.memory

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Writes a single byte into machine memory. Definitionally the same update as before sealing. -/
abbrev X86_64MachineState.write8 (s : X86_64MachineState) (a : Address) (v : UInt8) : X86_64MachineState :=
  { s with memory := X86_64Mem.write .w8 a v.toUInt64 s.memory }

/- REF: docs/MEMORY_HOOK.md#31-types-and-api -/
/-- Writes a 4-byte little-endian doubleword into machine memory. The other "missing width":
    before this hook, `MovRspDispImm32.step` re-implemented this ladder inline because no
    `write32` existed (`docs/MEMORY_HOOK.md` §1.1). -/
abbrev X86_64MachineState.write32 (s : X86_64MachineState) (a : Address) (v : UInt32) : X86_64MachineState :=
  { s with memory := X86_64Mem.write .w32 a v.toUInt64 s.memory }

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Writes an 8-byte little-endian quadword into machine memory. Definitionally the same update
    as before sealing. -/
abbrev X86_64MachineState.write64 (s : X86_64MachineState) (a : Address) (v : UInt64) : X86_64MachineState :=
  { s with memory := X86_64Mem.write .w64 a v s.memory }

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Hardware PUSH: decrements RSP by 8 and writes a 64-bit value to the stack. -/
abbrev X86_64MachineState.push64 (s : X86_64MachineState) (v : UInt64) : X86_64MachineState :=
  let s' := s.setGpr64 .rsp (s.rsp - 8)
  s'.write64 s'.rsp v

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Hardware POP: reads a 64-bit value from [RSP] and increments RSP by 8. -/
abbrev X86_64MachineState.pop64 (s : X86_64MachineState) : UInt64 × X86_64MachineState :=
  let v := s.read64 s.rsp
  (v, s.setGpr64 .rsp (s.rsp + 8))

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Reads a string or raw byte stream directly from machine memory. -/
def X86_64MachineState.readString (s : X86_64MachineState) (buf : Address) (len : Nat) : String :=
  let bytes := (List.range len).map (fun i => (X86_64Mem.read .w8 (buf + i.toUInt64) s.memory).toUInt8)
  let byteArr := ByteArray.mk bytes.toArray
  match String.fromUTF8? byteArr with
  | some str => str
  | none => String.ofList (bytes.map (fun b => Char.ofNat b.toNat))

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Returns the 3-bit register index and REX extension bit for 64-bit registers. -/
def reg64Code (r : Reg64) : UInt8 × Bool :=
  match r with
  | .rax => (0, false) | .rcx => (1, false) | .rdx => (2, false) | .rbx => (3, false)
  | .rsp => (4, false) | .rbp => (5, false) | .rsi => (6, false) | .rdi => (7, false)
  | .r8  => (0, true)  | .r9  => (1, true)  | .r10 => (2, true)  | .r11 => (3, true)
  | .r12 => (4, true)  | .r13 => (5, true)  | .r14 => (6, true)  | .r15 => (7, true)

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Returns the 3-bit register index and REX extension bit for 32-bit registers. -/
def reg32Code (r : Reg32) : UInt8 × Bool :=
  match r with
  | .eax => (0, false) | .ecx => (1, false) | .edx => (2, false) | .ebx => (3, false)
  | .esp => (4, false) | .ebp => (5, false) | .esi => (6, false) | .edi => (7, false)
  | .r8d => (0, true)  | .r9d => (1, true)  | .r10d => (2, true) | .r11d => (3, true)
  | .r12d => (4, true) | .r13d => (5, true) | .r14d => (6, true) | .r15d => (7, true)

/- REF: intel-sdm#vol=1;sec=3.4;part=34-basic-program-execution-registers -/
/-- Formats a 64-bit general-purpose register into lowercase NASM text. -/
def Reg64.toString : Reg64 → String
  | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx"
  | .rsp => "rsp" | .rbp => "rbp" | .rsi => "rsi" | .rdi => "rdi"
  | .r8  => "r8"  | .r9  => "r9"  | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

/- REF: intel-sdm#vol=1;sec=3.4;part=34-basic-program-execution-registers;pp=67-90;mp=Vol._1_3-1_to_3-24_Vol._1 -/
instance : ToString Reg64 where
  toString := Reg64.toString

/- REF: intel-sdm#vol=1;sec=3.4;part=34-basic-program-execution-registers -/
/-- Formats a 32-bit general-purpose register into lowercase NASM text. -/
def Reg32.toString : Reg32 → String
  | .eax => "eax" | .ecx => "ecx" | .edx => "edx" | .ebx => "ebx"
  | .esp => "esp" | .ebp => "ebp" | .esi => "esi" | .edi => "edi"
  | .r8d => "r8d" | .r9d => "r9d" | .r10d => "r10d" | .r11d => "r11d"
  | .r12d => "r12d" | .r13d => "r13d" | .r14d => "r14d" | .r15d => "r15d"

/- REF: intel-sdm#vol=1;sec=3.4;part=34-basic-program-execution-registers;pp=67-90;mp=Vol._1_3-1_to_3-24_Vol._1 -/
instance : ToString Reg32 where
  toString := Reg32.toString

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Decodes a 3-bit register index and REX extension bit into a 64-bit general-purpose register. -/
def codeToReg64 (code : UInt8) (ext : Bool) : Reg64 :=
  match (code &&& 7), ext with
  | 0, false => .rax | 1, false => .rcx | 2, false => .rdx | 3, false => .rbx
  | 4, false => .rsp | 5, false => .rbp | 6, false => .rsi | 7, false => .rdi
  | 0, true  => .r8  | 1, true  => .r9  | 2, true  => .r10 | 3, true  => .r11
  | 4, true  => .r12 | 5, true  => .r13 | 6, true  => .r14 | 7, true  => .r15
  | _, _ => .rax

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Decodes a 3-bit register index and REX extension bit into a 32-bit sub-register. -/
def codeToReg32 (code : UInt8) (ext : Bool) : Reg32 :=
  match (code &&& 7), ext with
  | 0, false => .eax  | 1, false => .ecx  | 2, false => .edx  | 3, false => .ebx
  | 4, false => .esp  | 5, false => .ebp  | 6, false => .esi  | 7, false => .edi
  | 0, true  => .r8d  | 1, true  => .r9d  | 2, true  => .r10d | 3, true  => .r11d
  | 4, true  => .r12d | 5, true  => .r13d | 6, true  => .r14d | 7, true  => .r15d
  | _, _ => .eax

/- REF: intel-sdm#vol=1;sec=3.4;part=34-basic-program-execution-registers -/
/-- Returns the standard 8-bit low byte register name in 64-bit mode. -/
def reg64To8BitString : Reg64 → String
  | .rax => "al"   | .rcx => "cl"   | .rdx => "dl"   | .rbx => "bl"
  | .rsp => "spl"  | .rbp => "bpl"  | .rsi => "sil"  | .rdi => "dil"
  | .r8  => "r8b"  | .r9  => "r9b"  | .r10 => "r10b" | .r11 => "r11b"
  | .r12 => "r12b" | .r13 => "r13b" | .r14 => "r14b" | .r15 => "r15b"

end Gasm.Targets.X86_64
