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

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Verified Simulation Instance: smol_malloc initializes memory headers and preserves the formal coupling invariant. -/
theorem smol_malloc_refinement_soundness_inst :
    let s0 : SmolAllocState := {}
    let p0 : TracedPageState := {}
    (match (malloc (m := SmolTracedM) 64 8) s0 p0 with
     | some ((some specPtr, spec1), p1) =>
       let mach1 := runSmolMallocAsmState 64 { base := 0x20000000, endExclusive := 0x20010000 } 0
       mach1.gprs .rax == specPtr &&
       mach1.gprs .r11 == 0x20000060 &&
       smolAllocInvariant spec1 p1 mach1
     | _ => false) = true := by
  decide

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Verified Simulation Instance: smol_free marks the header free, updates freelist links, and preserves the formal coupling invariant. -/
theorem smol_free_refinement_soundness_inst :
    let s0 : SmolAllocState := {}
    let p0 : TracedPageState := {}
    (match (malloc (m := SmolTracedM) 64 8) s0 p0 with
     | some ((some specPtr, spec1), p1) =>
       match (free (m := SmolTracedM) specPtr) spec1 p1 with
       | some ((_, spec2), p2) =>
         let mach1 := runSmolMallocAsmState 64 { base := 0x20000000, endExclusive := 0x20010000 } 0
         let mach2 := runSmolFreeAsmState specPtr mach1
         mach2.gprs .rax == 1 &&
         smolAllocInvariant spec2 p2 mach2
       | _ => false
     | _ => false) = true := by
  decide

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Verified Simulation Instance: smol_malloc with an active freelist pops the free head and preserves the formal coupling invariant. -/
theorem smol_freelist_reuse_refinement_soundness_inst :
    let s0 : SmolAllocState := {}
    let p0 : TracedPageState := {}
    (match (malloc (m := SmolTracedM) 64 8) s0 p0 with
     | some ((some ptr1, spec1), p1) =>
       match (free (m := SmolTracedM) ptr1) spec1 p1 with
       | some ((_, spec2), p2) =>
         match (malloc (m := SmolTracedM) 48 8) spec2 p2 with
         | some ((some ptr2, spec3), p3) =>
           let mach1 := runSmolMallocAsmState 64 { base := 0x20000000, endExclusive := 0x20010000 } 0
           let mach2 := runSmolFreeAsmState ptr1 mach1
           let mach3 := runSmolMallocAsmState 48 { base := mach2.gprs .r11, endExclusive := mach2.gprs .r15 }
             (mach2.gprs .r10) mach2.memory
           ptr2 == ptr1 &&
           mach3.gprs .rax == ptr2 &&
           mach3.gprs .r11 == mach2.gprs .r11 &&
           mach3.gprs .r10 == 0 &&
           smolAllocInvariant spec3 p3 mach3
         | _ => false
       | _ => false
     | _ => false) = true := by
  decide

set_option maxRecDepth 10000 in
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- A fresh request exceeding a caller-provided finite arena returns the explicit null failure
    result without advancing the bump pointer or changing the free-list head.  This is the
    reusable native certificate consumed by clients that turn exhaustion into a recoverable
    outcome. -/
theorem smol_finite_arena_exhaustion_preserves_allocator_state :
    let arena : NativeArenaCapability := { base := 0x20000000, endExclusive := 0x2000005F }
    let mach := runSmolMallocAsmState 64 arena 0
    mach.gprs .rax == 0 &&
    mach.gprs .r11 == arena.base &&
    mach.gprs .r10 == 0 &&
    mach.gprs .r15 == arena.endExclusive := by
  decide

set_option maxRecDepth 10000 in
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Verified Simulation Instance: smol_malloc with insufficient freelist capacity falls back to fresh arena allocation. -/
theorem smol_freelist_insufficient_capacity_fallback_inst :
    let mach1 := runSmolMallocAsmState 64 { base := 0x20000000, endExclusive := 0x20010000 } 0
    let mach2 := runSmolFreeAsmState 0x20000020 mach1
    let mach3 := runSmolMallocAsmState 128 { base := mach2.gprs .r11, endExclusive := mach2.gprs .r15 }
      (mach2.gprs .r10) mach2.memory
    mach3.gprs .rax == 0x20000080 &&
    mach3.gprs .r11 == 0x20000100 &&
    mach3.gprs .r10 == 0x20000000 &&
    mach3.read64 0x20000060 == 128 &&
    mach3.read64 0x20000000 == 64 &&
    mach3.read64 0x20000008 == 1 := by
  decide

end Stdlib.SmolAlloc
