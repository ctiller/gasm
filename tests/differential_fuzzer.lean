/-
Copyright 2026 Google LLC

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

import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.MemoryCell
import Gasm.Targets.AArch64.Addressing
import Gasm.Targets.AArch64.Machine

open Gasm.Targets.AArch64
open Gasm.Core

-- Xorshift64 PRNG
structure Rng where
  state : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := if r.state == 0 then 0x853c49e6748fea9b else r.state
  let x1 := s ^^^ (s <<< 13)
  let x2 := x1 ^^^ (x1 >>> 7)
  let x3 := x2 ^^^ (x2 <<< 17)
  (x3, { state := x3 })

def Rng.nextNat (r : Rng) (bound : Nat) : Nat × Rng :=
  let (u, r') := r.next
  ((u.toNat % bound), r')

-- Naive Sparse Association List Memory Oracle
def NaiveMem := List (Address × UInt8)

def naiveReadByte (a : Address) (m : NaiveMem) : UInt8 :=
  match m.find? (fun (addr, _) => addr == a) with
  | some (_, b) => b
  | none => 0

def naiveWriteByte (a : Address) (b : UInt8) (m : NaiveMem) : NaiveMem :=
  (a, b) :: m

def naiveRead16 (a : Address) (m : NaiveMem) : UInt64 :=
  (naiveReadByte a m).toUInt64 ||| ((naiveReadByte (a + 1) m).toUInt64 <<< 8)

def naiveRead32 (a : Address) (m : NaiveMem) : UInt64 :=
  (naiveReadByte a m).toUInt64 |||
  ((naiveReadByte (a + 1) m).toUInt64 <<< 8) |||
  ((naiveReadByte (a + 2) m).toUInt64 <<< 16) |||
  ((naiveReadByte (a + 3) m).toUInt64 <<< 24)

def naiveRead64 (a : Address) (m : NaiveMem) : UInt64 :=
  (naiveReadByte a m).toUInt64 |||
  ((naiveReadByte (a + 1) m).toUInt64 <<< 8) |||
  ((naiveReadByte (a + 2) m).toUInt64 <<< 16) |||
  ((naiveReadByte (a + 3) m).toUInt64 <<< 24) |||
  ((naiveReadByte (a + 4) m).toUInt64 <<< 32) |||
  ((naiveReadByte (a + 5) m).toUInt64 <<< 40) |||
  ((naiveReadByte (a + 6) m).toUInt64 <<< 48) |||
  ((naiveReadByte (a + 7) m).toUInt64 <<< 56)

def naiveWrite16 (a : Address) (v : UInt64) (m : NaiveMem) : NaiveMem :=
  let m1 := naiveWriteByte a v.toUInt8 m
  naiveWriteByte (a + 1) (v >>> 8).toUInt8 m1

def naiveWrite32 (a : Address) (v : UInt64) (m : NaiveMem) : NaiveMem :=
  let m1 := naiveWriteByte a v.toUInt8 m
  let m2 := naiveWriteByte (a + 1) (v >>> 8).toUInt8 m1
  let m3 := naiveWriteByte (a + 2) (v >>> 16).toUInt8 m2
  naiveWriteByte (a + 3) (v >>> 24).toUInt8 m3

def naiveWrite64 (a : Address) (v : UInt64) (m : NaiveMem) : NaiveMem :=
  let m1 := naiveWriteByte a v.toUInt8 m
  let m2 := naiveWriteByte (a + 1) (v >>> 8).toUInt8 m1
  let m3 := naiveWriteByte (a + 2) (v >>> 16).toUInt8 m2
  let m4 := naiveWriteByte (a + 3) (v >>> 24).toUInt8 m3
  let m5 := naiveWriteByte (a + 4) (v >>> 32).toUInt8 m4
  let m6 := naiveWriteByte (a + 5) (v >>> 40).toUInt8 m5
  let m7 := naiveWriteByte (a + 6) (v >>> 48).toUInt8 m6
  naiveWriteByte (a + 7) (v >>> 56).toUInt8 m7

def runMemoryDifferentialFuzz (iterations : Nat) : IO (Bool × Nat) := do
  let mut rng : Rng := { state := 0x123456789ABCDEF0 }
  let mut aarchMem := AArch64Mem.zero
  let mut naiveMem : NaiveMem := []
  let mut passedCount := 0

  -- Addresses pool to focus on overlaps and boundaries
  let baseAddresses : List Address := [
    0x1000, 0x1001, 0x1002, 0x1003, 0x1004, 0x1007, 0x1008, 0x100F,
    0, 1, 2, 7, 8,
    0xFFFFFFFFFFFFFFF8, 0xFFFFFFFFFFFFFFFC, 0xFFFFFFFFFFFFFFFF
  ]

  for iter in [0:iterations] do
    let (opKind, r1) := rng.nextNat 4  -- 0: write, 1: read, 2: write, 3: read
    let (addrIdx, r2) := r1.nextNat baseAddresses.length
    let (randOffset, r3) := r2.nextNat 16
    let addr := baseAddresses[addrIdx]! + randOffset.toUInt64
    let (widthCode, r4) := r3.nextNat 4
    let width := match widthCode with
      | 0 => MemWidth.w8
      | 1 => MemWidth.w16
      | 2 => MemWidth.w32
      | _ => MemWidth.w64
    let (val, r5) := r4.next
    rng := r5

    if opKind == 0 || opKind == 2 then
      -- Write
      aarchMem := AArch64Mem.write width addr val aarchMem
      naiveMem := match width with
        | .w8 => naiveWriteByte addr val.toUInt8 naiveMem
        | .w16 => naiveWrite16 addr val naiveMem
        | .w32 => naiveWrite32 addr val naiveMem
        | .w64 => naiveWrite64 addr val naiveMem
      passedCount := passedCount + 1
    else
      -- Read & Compare
      let actual := AArch64Mem.read width addr aarchMem
      let expected := match width with
        | .w8 => (naiveReadByte addr naiveMem).toUInt64
        | .w16 => naiveRead16 addr naiveMem
        | .w32 => naiveRead32 addr naiveMem
        | .w64 => naiveRead64 addr naiveMem
      if actual != expected then
        IO.println s!"MISMATCH at iter {iter}: width={repr width}, addr={addr}, actual={actual}, expected={expected}"
        return (false, passedCount)
      passedCount := passedCount + 1

  return (true, passedCount)

def runAlignmentPredicateFuzz (iterations : Nat) : IO (Bool × Nat) := do
  let mut rng : Rng := { state := 0xCAFEBABEDEADBEEF }
  let mut passedCount := 0

  for _ in [0:iterations] do
    let (addr, r1) := rng.next
    rng := r1

    -- Check w8 (always true)
    let a8 := isAligned addr .w8
    if !a8 then
      IO.println s!"w8 alignment error on {addr}"
      return (false, passedCount)
    passedCount := passedCount + 1

    -- Check w16 (addr % 2 == 0)
    let a16 := isAligned addr .w16
    let exp16 := (addr.toNat % 2 == 0)
    if a16 != exp16 then
      IO.println s!"w16 alignment error on {addr}"
      return (false, passedCount)
    passedCount := passedCount + 1

    -- Check w32 (addr % 4 == 0)
    let a32 := isAligned addr .w32
    let exp32 := (addr.toNat % 4 == 0)
    if a32 != exp32 then
      IO.println s!"w32 alignment error on {addr}"
      return (false, passedCount)
    passedCount := passedCount + 1

    -- Check w64 (addr % 8 == 0)
    let a64 := isAligned addr .w64
    let exp64 := (addr.toNat % 8 == 0)
    if a64 != exp64 then
      IO.println s!"w64 alignment error on {addr}"
      return (false, passedCount)
    passedCount := passedCount + 1

    -- Check isSpAligned (addr % 16 == 0)
    let spAlign := isSpAligned addr
    let expSp := (addr.toNat % 16 == 0)
    if spAlign != expSp then
      IO.println s!"sp alignment error on {addr}"
      return (false, passedCount)
    passedCount := passedCount + 1

  return (true, passedCount)

def runAddressingDifferentialFuzz (iterations : Nat) : IO (Bool × Nat) := do
  let mut rng : Rng := { state := 0xDEADBEEF01234567 }
  let mut passedCount := 0

  let regs : List Reg64 := [
    .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7,
    .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
    .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23,
    .x24, .x25, .x26, .x27, .x28, .x29, .x30,
    .xzr, .sp
  ]

  for _ in [0:iterations] do
    let (baseIdx, r1) := rng.nextNat regs.length
    let base := regs[baseIdx]!
    let (baseVal, r2) := r1.next
    let (immRaw, r3) := r2.next
    let (modeCode, r4) := r3.nextNat 3  -- 0: immOffset, 1: preIndex, 2: postIndex
    let (pc, r5) := r4.next
    rng := r5

    let getReg (r : Reg64) : UInt64 :=
      if r == .xzr then 0
      else if r == base then baseVal
      else 0

    let effectiveBase := if base == .xzr then 0 else baseVal
    let imm := int64OfUInt64 immRaw

    match modeCode with
    | 0 =>
      -- immOffset
      let (ea, wb) := evalAddr (.immOffset base imm) getReg pc
      let expEa := effectiveBase + immRaw
      if ea != expEa || wb != none then
        IO.println s!"immOffset error: ea={ea}, exp={expEa}, wb={wb.isSome}"
        return (false, passedCount)
      passedCount := passedCount + 1

    | 1 =>
      -- preIndex
      let (ea, wb) := evalAddr (.preIndex base imm) getReg pc
      let expEa := effectiveBase + immRaw
      let expWb := some (base, expEa)
      if ea != expEa || wb != expWb then
        IO.println s!"preIndex error: ea={ea}, exp={expEa}, wb={repr wb}"
        return (false, passedCount)
      passedCount := passedCount + 1

    | _ =>
      -- postIndex
      let (ea, wb) := evalAddr (.postIndex base imm) getReg pc
      let expEa := effectiveBase
      let expWb := some (base, effectiveBase + immRaw)
      if ea != expEa || wb != expWb then
        IO.println s!"postIndex error: ea={ea}, exp={expEa}, wb={repr wb}"
        return (false, passedCount)
      passedCount := passedCount + 1

  return (true, passedCount)

def main : IO Unit := do
  IO.println "================================================================================"
  IO.println "  AArch64 Differential Fuzzing: Addressing & Memory Model vs Naive Oracles"
  IO.println "================================================================================"

  IO.println "Running Memory Cell differential fuzzing (1000 operations)..."
  let (memOk, memOps) ← runMemoryDifferentialFuzz 1000
  if !memOk then
    IO.println "Memory Cell differential fuzzing FAILED!"
    IO.Process.exit 1
  IO.println s!"  Memory Cell differential fuzzing PASSED ({memOps} checks verified)."

  IO.println "Running Alignment Predicates fuzzing (2000 random addresses)..."
  let (alignOk, alignOps) ← runAlignmentPredicateFuzz 2000
  if !alignOk then
    IO.println "Alignment Predicates fuzzing FAILED!"
    IO.Process.exit 1
  IO.println s!"  Alignment Predicates fuzzing PASSED ({alignOps} checks verified)."

  IO.println "Running Addressing Modes differential fuzzing (2000 random cases)..."
  let (addrOk, addrOps) ← runAddressingDifferentialFuzz 2000
  if !addrOk then
    IO.println "Addressing Modes differential fuzzing FAILED!"
    IO.Process.exit 1
  IO.println s!"  Addressing Modes differential fuzzing PASSED ({addrOps} checks verified)."

  IO.println "--------------------------------------------------------------------------------"
  let totalOps := memOps + alignOps + addrOps
  IO.println s!"Total Differential Fuzz Checks: {totalOps}"
  IO.println "All differential tests against independent oracles PASSED!"
  IO.Process.exit 0
