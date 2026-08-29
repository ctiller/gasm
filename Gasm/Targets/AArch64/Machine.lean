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
import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.MemoryCell
import Gasm.Targets.AArch64.Addressing

namespace Gasm.Targets.AArch64

open Gasm.Core

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Architecture-level exception and fault conditions for 64-bit ARM (AArch64).
    Unlike x86-64, integer division by zero does not trap in AArch64 hardware
    (UDIV/SDIV returns 0); faults represent true processor exception states. -/
inductive AArch64Fault where
  | alignmentFault
  | unmappedAccess
  | undefinedInstruction
  | permissionFault
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Native machine execution state for the 64-bit ARM architecture (AArch64).
    Maintains program counter, 31 general registers, dedicated stack pointer,
    NZCV condition flags, sealed memory cell, and termination status. -/
structure AArch64MachineState where
  pc               : UInt64 := 0
  gprs             : Fin 31 → UInt64 := fun _ => 0
  sp               : UInt64 := 0
  nzcv             : NZCV := default
  memory           : AArch64Memory := default
  fault            : Option AArch64Fault := none
  terminated       : Bool := false
  exitCode         : UInt32 := 0
  syscallReturnPc  : UInt64 := 0
  stdinBuffer      : ByteArray := ByteArray.empty
  incomingRequests : List ByteArray := []

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Default inhabited instance providing a clean zeroed machine state. -/
instance : Inhabited AArch64MachineState where
  default := {
    pc               := 0
    gprs             := fun _ => 0
    sp               := 0
    nzcv             := default
    memory           := default
    fault            := none
    terminated       := false
    exitCode         := 0
    syscallReturnPc  := 0
    stdinBuffer      := ByteArray.empty
    incomingRequests := []
  }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Resets machine state to initial clean state with PC=0, SP=0, all registers 0, and no faults. -/
def AArch64MachineState.reset : AArch64MachineState :=
  default

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Initializes machine state with specified entry PC and initial stack pointer SP. -/
def AArch64MachineState.init (entryPc : UInt64 := 0) (initialSp : UInt64 := 0) : AArch64MachineState :=
  { pc               := entryPc
    gprs             := fun _ => 0
    sp               := initialSp
    nzcv             := default
    memory           := default
    fault            := none
    terminated       := false
    exitCode         := 0
    syscallReturnPc  := 0
    stdinBuffer      := ByteArray.empty
    incomingRequests := [] }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Retrieves the 64-bit value of general-purpose register indexed by `Fin 31` (X0 through X30). -/
def AArch64MachineState.getGpr64 (s : AArch64MachineState) (idx : Fin 31) : UInt64 :=
  s.gprs idx

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Updates the 64-bit value of general-purpose register indexed by `Fin 31` (X0 through X30). -/
def AArch64MachineState.setGpr64 (s : AArch64MachineState) (idx : Fin 31) (val : UInt64) : AArch64MachineState :=
  { s with gprs := fun i => if i == idx then val else s.gprs i }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Retrieves the lower 32 bits of general-purpose register indexed by `Fin 31` (W0 through W30). -/
def AArch64MachineState.getGpr32 (s : AArch64MachineState) (idx : Fin 31) : UInt32 :=
  (s.gprs idx).toUInt32

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Updates 32-bit sub-register with mandatory AArch64 hardware zero-extension into upper 32 bits. -/
def AArch64MachineState.setGpr32 (s : AArch64MachineState) (idx : Fin 31) (val : UInt32) : AArch64MachineState :=
  s.setGpr64 idx val.toUInt64

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Retrieves 64-bit register in data-processing context using 5-bit register field (index 31 is XZR: returns 0). -/
def AArch64MachineState.getGpr64WithXzr (s : AArch64MachineState) (reg : Fin 32) : UInt64 :=
  if h : reg.val < 31 then
    s.getGpr64 ⟨reg.val, h⟩
  else
    0

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Updates 64-bit register in data-processing context using 5-bit register field (index 31 is XZR: write discarded). -/
def AArch64MachineState.setGpr64WithXzr (s : AArch64MachineState) (reg : Fin 32) (val : UInt64) : AArch64MachineState :=
  if h : reg.val < 31 then
    s.setGpr64 ⟨reg.val, h⟩ val
  else
    s

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Retrieves 32-bit register in data-processing context using 5-bit register field (index 31 is WZR: returns 0). -/
def AArch64MachineState.getGpr32WithWzr (s : AArch64MachineState) (reg : Fin 32) : UInt32 :=
  if h : reg.val < 31 then
    s.getGpr32 ⟨reg.val, h⟩
  else
    0

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Updates 32-bit register in data-processing context with zero-extension (index 31 is WZR: write discarded). -/
def AArch64MachineState.setGpr32WithWzr (s : AArch64MachineState) (reg : Fin 32) (val : UInt32) : AArch64MachineState :=
  if h : reg.val < 31 then
    s.setGpr32 ⟨reg.val, h⟩ val
  else
    s

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Retrieves 64-bit register in SP context using 5-bit register field (index 31 is SP). -/
def AArch64MachineState.getGpr64WithSp (s : AArch64MachineState) (reg : Fin 32) : UInt64 :=
  if h : reg.val < 31 then
    s.getGpr64 ⟨reg.val, h⟩
  else
    s.sp

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Updates 64-bit register in SP context using 5-bit register field (index 31 is SP). -/
def AArch64MachineState.setGpr64WithSp (s : AArch64MachineState) (reg : Fin 32) (val : UInt64) : AArch64MachineState :=
  if h : reg.val < 31 then
    s.setGpr64 ⟨reg.val, h⟩ val
  else
    { s with sp := val }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Retrieves 64-bit register using typed `Reg64` enum (xzr reads 0, sp reads stack pointer). -/
def AArch64MachineState.getReg64 (s : AArch64MachineState) (r : Reg64) : UInt64 :=
  match r with
  | .xzr => 0
  | .sp  => s.sp
  | other =>
    match regIndex other with
    | some idx => s.getGpr64 idx
    | none => 0

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Updates 64-bit register using typed `Reg64` enum (xzr write discarded, sp updates stack pointer). -/
def AArch64MachineState.setReg64 (s : AArch64MachineState) (r : Reg64) (val : UInt64) : AArch64MachineState :=
  match r with
  | .xzr => s
  | .sp  => { s with sp := val }
  | other =>
    match regIndex other with
    | some idx => s.setGpr64 idx val
    | none => s

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Retrieves 32-bit register using typed `Reg32` enum (wzr reads 0, wsp reads lower 32 bits of SP). -/
def AArch64MachineState.getReg32 (s : AArch64MachineState) (r : Reg32) : UInt32 :=
  match r with
  | .wzr => 0
  | .wsp => s.sp.toUInt32
  | other =>
    match reg32Index other with
    | some idx => s.getGpr32 idx
    | none => 0

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Updates 32-bit register with zero-extension using typed `Reg32` enum. -/
def AArch64MachineState.setReg32 (s : AArch64MachineState) (r : Reg32) (val : UInt32) : AArch64MachineState :=
  match r with
  | .wzr => s
  | .wsp => { s with sp := val.toUInt64 }
  | other =>
    match reg32Index other with
    | some idx => s.setGpr32 idx val
    | none => s

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Verifies whether the stack pointer (SP) satisfies mandatory AAPCS64 16-byte alignment (`sp % 16 == 0`). -/
def AArch64MachineState.isSpAligned (s : AArch64MachineState) : Bool :=
  s.sp % 16 == 0

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- SP alignment validation check predicate (`sp % 16 == 0`). -/
def AArch64MachineState.checkSpAlignment (s : AArch64MachineState) : Bool :=
  s.sp % 16 == 0

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Evaluates whether machine execution has encountered an architectural fault. -/
def AArch64MachineState.faulted (s : AArch64MachineState) : Bool :=
  s.fault.isSome

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Evaluates whether machine execution has halted (terminated cleanly or halted on fault). -/
def AArch64MachineState.isHalted (s : AArch64MachineState) : Bool :=
  s.terminated || s.fault.isSome

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Sets execution fault, halting further instruction stepping. -/
def AArch64MachineState.setFault (s : AArch64MachineState) (f : AArch64Fault) : AArch64MachineState :=
  { s with fault := some f }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Marks machine execution as cleanly terminated with the provided exit code. -/
def AArch64MachineState.terminate (s : AArch64MachineState) (code : UInt32) : AArch64MachineState :=
  { s with terminated := true, exitCode := code }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Advances program counter sequentially by 4 bytes (size of one AArch64 instruction word). -/
def AArch64MachineState.advancePc (s : AArch64MachineState) : AArch64MachineState :=
  { s with pc := s.pc + 4 }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Updates program counter to target address for control-flow branch instructions. -/
def AArch64MachineState.branch (s : AArch64MachineState) (target : UInt64) : AArch64MachineState :=
  { s with pc := target }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Evaluates condition code `c` against current machine condition flags `s.nzcv`. -/
def AArch64MachineState.testCond (s : AArch64MachineState) (c : Cond) : Bool :=
  evalCond c s.nzcv

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Computes NZCV flags following 64-bit integer addition `a + b`. -/
def computeAddFlags64 (a b : UInt64) : NZCV :=
  let sum := a + b
  let n := (sum >>> 63) == 1
  let z := sum == 0
  let c := sum < a
  let v := (((~~~(a ^^^ b)) &&& (a ^^^ sum) &&& 0x8000000000000000) != 0)
  { n := n, z := z, c := c, v := v }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Computes NZCV flags following 64-bit integer subtraction `a - b` (Inverted Carry: C=1 if a >= b). -/
def computeSubFlags64 (a b : UInt64) : NZCV :=
  let diff := a - b
  let n := (diff >>> 63) == 1
  let z := diff == 0
  let c := a >= b
  let v := (((a ^^^ b) &&& (a ^^^ diff) &&& 0x8000000000000000) != 0)
  { n := n, z := z, c := c, v := v }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Computes NZCV flags following 32-bit integer addition `a + b`. -/
def computeAddFlags32 (a b : UInt32) : NZCV :=
  let sum := a + b
  let n := (sum >>> 31) == 1
  let z := sum == 0
  let c := sum < a
  let v := (((~~~(a ^^^ b)) &&& (a ^^^ sum) &&& 0x80000000) != 0)
  { n := n, z := z, c := c, v := v }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Computes NZCV flags following 32-bit integer subtraction `a - b` (Inverted Carry: C=1 if a >= b). -/
def computeSubFlags32 (a b : UInt32) : NZCV :=
  let diff := a - b
  let n := (diff >>> 31) == 1
  let z := diff == 0
  let c := a >= b
  let v := (((a ^^^ b) &&& (a ^^^ diff) &&& 0x80000000) != 0)
  { n := n, z := z, c := c, v := v }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Computes NZCV flags following 64-bit bitwise logical operation (clears C and V to false). -/
def computeLogicFlags64 (res : UInt64) : NZCV :=
  { n := (res >>> 63) == 1,
    z := res == 0,
    c := false,
    v := false }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Computes NZCV flags following 32-bit bitwise logical operation (clears C and V to false). -/
def computeLogicFlags32 (res : UInt32) : NZCV :=
  { n := (res >>> 31) == 1,
    z := res == 0,
    c := false,
    v := false }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Updates NZCV condition flags following a 64-bit addition. -/
def AArch64MachineState.setFlagsAdd64 (s : AArch64MachineState) (a b : UInt64) : AArch64MachineState :=
  { s with nzcv := computeAddFlags64 a b }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Updates NZCV condition flags following a 64-bit subtraction. -/
def AArch64MachineState.setFlagsSub64 (s : AArch64MachineState) (a b : UInt64) : AArch64MachineState :=
  { s with nzcv := computeSubFlags64 a b }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Updates NZCV condition flags following a 32-bit addition. -/
def AArch64MachineState.setFlagsAdd32 (s : AArch64MachineState) (a b : UInt32) : AArch64MachineState :=
  { s with nzcv := computeAddFlags32 a b }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Updates NZCV condition flags following a 32-bit subtraction. -/
def AArch64MachineState.setFlagsSub32 (s : AArch64MachineState) (a b : UInt32) : AArch64MachineState :=
  { s with nzcv := computeSubFlags32 a b }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Updates NZCV condition flags following a 64-bit logical operation. -/
def AArch64MachineState.setFlagsLogic64 (s : AArch64MachineState) (res : UInt64) : AArch64MachineState :=
  { s with nzcv := computeLogicFlags64 res }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Updates NZCV condition flags following a 32-bit logical operation. -/
def AArch64MachineState.setFlagsLogic32 (s : AArch64MachineState) (res : UInt32) : AArch64MachineState :=
  { s with nzcv := computeLogicFlags32 res }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Reads value of specified width from machine memory via sealed cell interface. -/
def AArch64MachineState.readMem (s : AArch64MachineState) (w : MemWidth) (addr : Address) : UInt64 :=
  AArch64Mem.read w addr s.memory

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Writes value of specified width into machine memory via sealed cell interface. -/
def AArch64MachineState.writeMem (s : AArch64MachineState) (w : MemWidth) (addr : Address) (val : UInt64) : AArch64MachineState :=
  { s with memory := AArch64Mem.write w addr val s.memory }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Evaluates an addressing mode in the context of the current machine state. -/
def AArch64MachineState.evalAddrMode (s : AArch64MachineState) (mode : AArch64AddrMode) :
    Address × Option (Reg64 × Address) :=
  evalAddr mode s.getReg64 s.pc

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Invariant theorem: write to XZR is silently discarded. -/
theorem setReg64_xzr_eq (s : AArch64MachineState) (v : UInt64) :
    s.setReg64 .xzr v = s := rfl

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Invariant theorem: read from XZR always returns 0. -/
theorem getReg64_xzr_eq (s : AArch64MachineState) :
    s.getReg64 .xzr = 0 := rfl

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Invariant theorem: write to WZR is silently discarded. -/
theorem setReg32_wzr_eq (s : AArch64MachineState) (v : UInt32) :
    s.setReg32 .wzr v = s := rfl

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Invariant theorem: read from WZR always returns 0. -/
theorem getReg32_wzr_eq (s : AArch64MachineState) :
    s.getReg32 .wzr = 0 := rfl

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Invariant theorem: write to SP updates SP. -/
theorem setReg64_sp_eq (s : AArch64MachineState) (v : UInt64) :
    (s.setReg64 .sp v).sp = v := rfl

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Invariant theorem: read from SP returns current SP. -/
theorem getReg64_sp_eq (s : AArch64MachineState) :
    s.getReg64 .sp = s.sp := rfl

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Invariant theorem: sequential PC advance adds exactly 4 bytes. -/
theorem advancePc_eq (s : AArch64MachineState) :
    s.advancePc.pc = s.pc + 4 := rfl

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Invariant theorem: branch sets PC to target. -/
theorem branch_eq (s : AArch64MachineState) (t : UInt64) :
    (s.branch t).pc = t := rfl

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Invariant theorem: terminate sets terminated flag and exitCode. -/
theorem terminate_eq (s : AArch64MachineState) (c : UInt32) :
    (s.terminate c).terminated = true ∧ (s.terminate c).exitCode = c := ⟨rfl, rfl⟩

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Invariant theorem: setFault sets fault option to some. -/
theorem setFault_eq (s : AArch64MachineState) (f : AArch64Fault) :
    (s.setFault f).fault = some f := rfl

-- TargetArch instance for AArch64 is canonically provided in Gasm.Targets.AArch64.Semantics.
end Gasm.Targets.AArch64

