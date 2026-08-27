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
/-- Simulates execution of smol_malloc on an input size in RCX with initial bump pointer in R11 and freelist in R10. -/
def runSmolMallocAsmState (size : Nat) (arenaBase : UInt64 := 0x20000000) (freeHead : UInt64 := 0) (initialMem : Address → Byte := fun _ => 0) : X86_64MachineState :=
  let s0 : X86_64MachineState := {
    rip := 0x1000,
    gprs := fun r =>
      if r == .rcx then size.toUInt64
      else if r == .r11 then arenaBase
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
       let mach1 := runSmolMallocAsmState 64 0x20000000 0
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
         let mach1 := runSmolMallocAsmState 64 0x20000000 0
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
           let mach1 := runSmolMallocAsmState 64 0x20000000 0
           let mach2 := runSmolFreeAsmState ptr1 mach1
           let mach3 := runSmolMallocAsmState 48 (mach2.gprs .r11) (mach2.gprs .r10) mach2.memory
           ptr2 == ptr1 &&
           mach3.gprs .rax == ptr2 &&
           mach3.gprs .r11 == mach2.gprs .r11 &&
           mach3.gprs .r10 == 0 &&
           smolAllocInvariant spec3 p3 mach3
         | _ => false
       | _ => false
     | _ => false) = true := by
  decide

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Verified Simulation Instance: smol_malloc with insufficient freelist capacity falls back to fresh arena allocation. -/
theorem smol_freelist_insufficient_capacity_fallback_inst :
    let mach1 := runSmolMallocAsmState 64 0x20000000 0
    let mach2 := runSmolFreeAsmState 0x20000020 mach1
    let mach3 := runSmolMallocAsmState 128 (mach2.gprs .r11) (mach2.gprs .r10) mach2.memory
    mach3.gprs .rax == 0x20000080 &&
    mach3.gprs .r11 == 0x20000100 &&
    mach3.gprs .r10 == 0x20000000 &&
    mach3.read64 0x20000060 == 128 &&
    mach3.read64 0x20000000 == 64 &&
    mach3.read64 0x20000008 == 1 := by
  decide

end Stdlib.SmolAlloc
