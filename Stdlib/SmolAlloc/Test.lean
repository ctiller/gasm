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
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Semantics
import Stdlib.SmolAlloc.Spec
import Stdlib.SmolAlloc.Program
import Stdlib.SmolAlloc.Equivalence

namespace Stdlib.SmolAlloc

open Gasm.Core
open Gasm.Targets.X86_64

/- REF: docs/STDLIB_SMOLALLOC.md#1-overview-architectural-role -/
/-- Formats 64-bit integer as hex string. -/
def toHexString (v : UInt64) : String :=
  let rec loop (fuel : Nat) (n : Nat) (digits : List Char) : String :=
    match fuel with
    | 0 => if digits.isEmpty then "0" else String.ofList digits
    | fuel + 1 =>
      if n == 0 then (if digits.isEmpty then "0" else String.ofList digits)
      else
        let rem := n % 16
        let c := if rem < 10 then (Char.ofNat (48 + rem)) else (Char.ofNat (55 + rem))
        loop fuel (n / 16) (c :: digits)
  loop 16 v.toNat []

/- REF: docs/STDLIB_SMOLALLOC.md#1-overview-architectural-role -/
/-- Test runner for SmolAlloc specification and machine state simulation. -/
def runTests : IO UInt32 := do
  IO.println "================================================================================"
  IO.println "                    GASM STDLIB: SMOLALLOC TEST SUITE                           "
  IO.println "================================================================================"

  -- Test 1: Basic Malloc & Obligation Tracking
  IO.println "[Test 1/5] Testing basic malloc & linear free obligation tracking via PageSource..."
  let s0 : SmolAllocState := {}
  let p0 : TracedPageState := {}
  match (malloc (m := SmolTracedM) 64 8) s0 p0 with
  | none =>
    IO.println "[-] FAIL: malloc failed on initial state"
    return 1
  | some ((none, _), _) =>
    IO.println "[-] FAIL: malloc returned none"
    return 1
  | some ((some ptr1, s1), p1) =>
    if ptr1 != 0x20000020 then
      IO.println s!"[-] FAIL: unexpected ptr1 = {ptr1}"
      return 1
    if s1.activeBorrows != 1 || !s1.obligations.contains (mkFreeObligation ptr1) then
      IO.println s!"[-] FAIL: expected 1 active borrow and FreeObligation, found activeBorrows = {s1.activeBorrows}"
      return 1
    if p1.actionTrace.isEmpty then
      IO.println "[-] FAIL: PageSource was not called for initial allocation!"
      return 1
    IO.println s!"[+] PASS: malloc(64) -> 0x{toHexString ptr1}, 1 active borrow tracked, PageSource.fetchPages called."

    -- Test 2: Free & Obligation Discharge
    IO.println "[Test 2/5] Testing free & obligation discharge..."
    match (free (m := SmolTracedM) ptr1) s1 p1 with
    | none =>
      IO.println "[-] FAIL: free failed"
      return 1
    | some ((success, s2), p2) =>
      if !success then
        IO.println "[-] FAIL: free returned false"
        return 1
      if s2.activeBorrows != 0 || s2.obligations.contains (mkFreeObligation ptr1) then
        IO.println s!"[-] FAIL: expected 0 active borrows and FreeObligation discharged, found activeBorrows = {s2.activeBorrows}"
        return 1
      if s2.freeListHead != some 0x20000000 then
        IO.println s!"[-] FAIL: expected freeListHead = 0x20000000, found {s2.freeListHead}"
        return 1
      IO.println "[+] PASS: free(ptr1) succeeded, obligation discharged, block linked to freelist."

      -- Test 3: FreeList First-Fit Block Reuse (0 PageSource calls)
      IO.println "[Test 3/5] Testing FreeList first-fit reuse without allocating new pages..."
      match (malloc (m := SmolTracedM) 48 8) s2 p2 with
      | none =>
        IO.println "[-] FAIL: malloc after free failed"
        return 1
      | some ((none, _), _) =>
        IO.println "[-] FAIL: malloc returned none"
        return 1
      | some ((some ptr2, s3), p3) =>
        if ptr2 != ptr1 then
          IO.println s!"[-] FAIL: expected reused ptr2 ({ptr2}) == ptr1 ({ptr1})"
          return 1
        if s3.pageCount != s1.pageCount then
          IO.println s!"[-] FAIL: expected pageCount {s1.pageCount}, found {s3.pageCount} (new pages allocated!)"
          return 1
        if p3.actionTrace.length != p2.actionTrace.length then
          IO.println "[-] FAIL: PageSource.fetchPages was unexpectedly called during freelist reuse!"
          return 1
        IO.println s!"[+] PASS: malloc(48) successfully reused freed block at 0x{toHexString ptr2} with 0 new pages and 0 PageSource calls."

  -- Test 4: Custom Alignment Malloc
  IO.println "[Test 4/5] Testing malloc with 64-byte alignment..."
  match (malloc (m := SmolTracedM) 128 64) s0 p0 with
  | none =>
    IO.println "[-] FAIL: malloc_aligned failed"
    return 1
  | some ((none, _), _) =>
    IO.println "[-] FAIL: malloc returned none"
    return 1
  | some ((some ptr, s4), _) =>
    let block := s4.blocks.head!
    if block.alignment != 64 then
      IO.println s!"[-] FAIL: expected alignment 64, found {block.alignment}"
      return 1
    IO.println s!"[+] PASS: malloc(128, 64) created 64-byte aligned block at 0x{toHexString ptr}."

  -- Test 5: Symbolic x86-64 Machine Equivalence Simulation
  IO.println "[Test 5/5] Testing symbolic x86-64 assembly execution, memory header inspection, & freelist chaining..."
  let mach0 := runSmolMallocAsmState 64 { base := 0x20000000, endExclusive := 0x20010000 } 0
  let mach1 := runSmolFreeAsmState (mach0.gprs .rax) mach0
  let mach2 := runProgramWithLoops 0x1000 smolMallocInstructions 15 { mach1 with rip := 0x1000, gprs := fun r => if r == .rcx then 48 else mach1.gprs r }

  if mach0.gprs .rax != 0x20000020 then
    IO.println s!"[-] FAIL: expected machine malloc rax = 0x20000020, found {mach0.gprs .rax}"
    return 1
  if mach1.gprs .rax != 1 then
    IO.println s!"[-] FAIL: expected machine free rax = 1, found {mach1.gprs .rax}"
    return 1
  if mach1.gprs .r10 != 0x20000000 then
    IO.println s!"[-] FAIL: expected machine freelist head r10 = 0x20000000, found {mach1.gprs .r10}"
    return 1
  if mach2.gprs .rax != 0x20000020 then
    IO.println s!"[-] FAIL: expected machine reused malloc rax = 0x20000020, found {mach2.gprs .rax}"
    return 1
  if mach2.gprs .r10 != 0 then
    IO.println s!"[-] FAIL: expected machine freelist head after reuse r10 = 0, found {mach2.gprs .r10}"
    return 1

  IO.println "[+] PASS: x86-64 assembly smol_malloc and smol_free executed with real memory header manipulation and freelist chaining."
  IO.println "================================================================================"
  IO.println "[+] ALL SMOLALLOC SPECIFICATION & MACHINE TESTS PASSED CLEANLY!"
  IO.println "================================================================================"
  return 0

/- REF: docs/STDLIB_SMOLALLOC.md#1-overview-architectural-role -/
/-- SmolAlloc test runner binary entry point. -/
def _root_.main : IO UInt32 :=
  Stdlib.SmolAlloc.runTests
