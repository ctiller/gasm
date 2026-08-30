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

import Gasm.Core.Types
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Semantics
import Stdlib.SmolAlloc.Spec
import Stdlib.SmolAlloc.Program

namespace Stdlib.SmolAlloc

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Formal coupling invariant between high-level SmolAllocState/TracedPageState and low-level X86_64MachineState.
    - mach.gprs .r10 matches the free list head.
    - Every abstract block in spec.blocks is faithfully mirrored in machine memory at block.address:
      [b.address + 0x00] = blockSize
      [b.address + 0x08] = isFree (1 if true, 0 if false)
      [b.address + 0x10] = alignment
      [b.address + 0x18] = nextFree (0 if none)
-/
def smolAllocInvariant (spec : SmolAllocState) (_p : TracedPageState) (mach : X86_64MachineState) : Bool :=
  mach.gprs .r10 == (match spec.freeListHead with | some h => h | none => 0) &&
  spec.blocks.all (fun b =>
    mach.read64 b.address == b.blockSize.toUInt64 &&
    mach.read64 (b.address + 8) == (if b.isFree then 1 else 0) &&
    mach.read64 (b.address + 16) == b.alignment.toUInt64 &&
    mach.read64 (b.address + 24) == (match b.nextFree with | some n => n | none => 0)
  )

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Simulates execution of fallible `smol_malloc` on an input size in RCX.  The embedding caller
    must supply a finite `NativeArenaCapability`; this helper deliberately has no capacity default. -/
def runSmolMallocAsmState (size : Nat) (arena : NativeArenaCapability)
    (freeHead : UInt64 := 0) (initialMem : X86_64Memory := X86_64Mem.zero) : X86_64MachineState :=
  let s0 : X86_64MachineState := {
    rip := 0x1000,
    gprs := fun r =>
      if r == .rcx then size.toUInt64
      else if r == .r11 then arena.base
      else if r == .r15 then arena.endExclusive
      else if r == .r10 then freeHead
      else if r == .rsp then 0x7FFFFFFF0008
      else 0,
    flags := 0,
    memory := initialMem
  }
  runProgramWithLoops 0x1000 smolMallocInstructions 30 s0

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Simulates execution of smol_free on a payload pointer in RCX and updates machine memory and register state. -/
def runSmolFreeAsmState (payloadPtr : UInt64) (s : X86_64MachineState) : X86_64MachineState :=
  let s0 : X86_64MachineState := {
    s with
    rip := 0x1000,
    gprs := fun r =>
      if r == .rcx then payloadPtr
      else s.gprs r
  }
  runProgramWithLoops 0x1000 smolFreeInstructions 30 s0

/-- The persistent part of the native allocator state.  Temporary registers used to check an
    allocation are deliberately absent: a failed request must leave this frame byte-for-byte
    unchanged. -/
structure SmolAllocatorFrame where
  bump     : UInt64
  freeHead : UInt64
  memory   : X86_64Memory

/-- The structural fresh-allocation decision used by the finite-arena contract.  It mirrors the
    three pre-write guards in `smolMallocSymbolicProgram`: alignment overflow, header overflow,
    and the exact `bump`/`endExclusive` capacity check. -/
def smolFreshAllocation (request : UInt64) (arena : NativeArenaCapability)
    (frame : SmolAllocatorFrame) : Option SmolAllocatorFrame :=
  if request > 0xFFFFFFFFFFFFFFFF - 7 then
    none
  else
    let payload := (request + 7) &&& 0xFFFFFFFFFFFFFFF8
    if payload > 0xFFFFFFFFFFFFFFFF - 32 then
      none
    else
      let total := payload + 32
      match arena.allocateFresh frame.bump total with
      | none => none
      | some _ => some { frame with bump := frame.bump + total }

/-- A fresh allocation reports its complete persistent-state result.  In the failure constructor
    the carried frame is intentional: it is the allocator's no-write/no-mutation contract. -/
inductive SmolFreshAllocationOutcome where
  | failed (frame : SmolAllocatorFrame)
  | allocated (frame : SmolAllocatorFrame)

def smolFreshAllocationOutcome (request : UInt64) (arena : NativeArenaCapability)
    (frame : SmolAllocatorFrame) : SmolFreshAllocationOutcome :=
  match smolFreshAllocation request arena frame with
  | none => .failed frame
  | some next => .allocated next

/-- Every failed fresh allocation has an exact frame result: no bump, free-list, or allocator
    memory mutation is represented.  This is universal over request, capability, and initial
    memory; it replaces the former literal evaluator certificate. -/
theorem smolFreshAllocation_failure_preserves_frame (request : UInt64)
    (arena : NativeArenaCapability) (frame result : SmolAllocatorFrame)
    (h : smolFreshAllocationOutcome request arena frame = .failed result) :
    result.bump = frame.bump ∧ result.freeHead = frame.freeHead ∧ result.memory = frame.memory := by
  unfold smolFreshAllocationOutcome at h
  cases hstep : smolFreshAllocation request arena frame with
  | none =>
      simp [hstep] at h
      cases h
      exact ⟨rfl, rfl, rfl⟩
  | some next =>
      simp [hstep] at h

end Stdlib.SmolAlloc
