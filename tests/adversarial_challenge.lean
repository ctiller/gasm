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

/-
Adversarial Stress Harness for AArch64 Registers and Machine State.
Implements differential oracles, boundary condition sweeps, invariant checkers.
-/

import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.MemoryCell
import Gasm.Targets.AArch64.Machine

open Gasm.Core
open Gasm.Targets.AArch64

def toFin31 (n : Nat) : Fin 31 :=
  if h : n < 31 then ⟨n, h⟩ else ⟨0, by decide⟩

def toFin32 (n : Nat) : Fin 32 :=
  if h : n < 32 then ⟨n, h⟩ else ⟨0, by decide⟩

def stateEquals (s1 s2 : AArch64MachineState) : Bool :=
  s1.pc == s2.pc &&
  s1.sp == s2.sp &&
  s1.nzcv == s2.nzcv &&
  s1.fault == s2.fault &&
  s1.terminated == s2.terminated &&
  s1.exitCode == s2.exitCode &&
  (List.range 31).all (fun i => s1.getGpr64 (toFin31 i) == s2.getGpr64 (toFin31 i))

def check (desc : String) (cond : Bool) : IO Unit := do
  if !cond then
    IO.println s!"[FAIL] {desc}"
    throw (IO.userError s!"Assertion failed: {desc}")
  else
    IO.println s!"[PASS] {desc}"

/-- Reference Oracle for ARMv8 condition evaluation (Armv8-A DDI 0487 Table C1-1) -/
def armReferenceEvalCond (c : Cond) (n z cv v : Bool) : Bool :=
  match c with
  | .EQ => z
  | .NE => !z
  | .CS => cv
  | .CC => !cv
  | .MI => n
  | .PL => !n
  | .VS => v
  | .VC => !v
  | .HI => cv && !z
  | .LS => !cv || z
  | .GE => n == v
  | .LT => n != v
  | .GT => !z && (n == v)
  | .LE => z || (n != v)
  | .AL => true
  | .NV => true

def stressTestConditionEvaluation : IO Unit := do
  IO.println "\n=== Section 1: Stress-Testing Condition Evaluation (evalCond) ==="
  let allConds : List Cond := [
    .EQ, .NE, .CS, .CC, .MI, .PL, .VS, .VC,
    .HI, .LS, .GE, .LT, .GT, .LE, .AL, .NV
  ]
  let bools := [false, true]
  let mut totalTested := 0

  -- Test all 16 condition codes against all 16 flag permutations (256 pairs)
  for c in allConds do
    for n in bools do
      for z in bools do
        for cv in bools do
          for v in bools do
            let flags : NZCV := { n := n, z := z, c := cv, v := v }
            let expected := armReferenceEvalCond c n z cv v
            let actual := evalCond c flags
            let actualU32 := evalCondUInt32 c flags.toUInt32
            totalTested := totalTested + 1
            if actual != expected then
              throw (IO.userError s!"evalCond mismatch for {c.toString} with N:{n} Z:{z} C:{cv} V:{v}: expected {expected}, got {actual}")
            if actualU32 != expected then
              throw (IO.userError s!"evalCondUInt32 mismatch for {c.toString} with N:{n} Z:{z} C:{cv} V:{v}: expected {expected}, got {actualU32}")

  check s!"Verified all {totalTested} (condition x NZCV) combinations against ARM reference oracle" (totalTested == 256)

  -- Test Cond inversion properties
  for c in allConds do
    let inv := c.invert
    check s!"Double inversion on {c.toString} is identity" (inv.invert == c)
    for n in bools do
      for z in bools do
        for cv in bools do
          for v in bools do
            let flags : NZCV := { n := n, z := z, c := cv, v := v }
            if c != .AL && c != .NV then
              let resC := evalCond c flags
              let resInv := evalCond inv flags
              if resInv != (!resC) then
                throw (IO.userError s!"Condition inversion failed for {c.toString} vs {inv.toString} on flags {flags.toString}")

  -- Verify AL and NV behavior specifically
  for n in bools do
    for z in bools do
      for cv in bools do
        for v in bools do
          let flags : NZCV := { n := n, z := z, c := cv, v := v }
          check "AL is always true" (evalCond .AL flags == true)
          check "NV is always true in ARMv8-A" (evalCond .NV flags == true)
          check "AL.invert is NV" (Cond.AL.invert == .NV)
          check "NV.invert is AL" (Cond.NV.invert == .AL)

  -- Test flag packing/unpacking with dirty lower 28 bits
  let dirtyBools : List UInt32 := [0x00000000, 0x0FFFFFFF, 0x05555555, 0x0AAAAAAA]
  for d in dirtyBools do
    for n in bools do
      for z in bools do
        for cv in bools do
          for v in bools do
            let flags : NZCV := { n := n, z := z, c := cv, v := v }
            let packed := flags.toUInt32 ||| d
            let unpacked := NZCV.ofUInt32 packed
            if unpacked != flags then
              throw (IO.userError s!"Dirty lower bits corrupted NZCV unpacking: dirty={d}, unpacked={unpacked.toString}")

  IO.println "[PASS] Condition Evaluation stress test completed successfully."

def stressTestRegistersAndZeroExtension : IO Unit := do
  IO.println "\n=== Section 2: Stress-Testing Register Aliasing and 32-bit Zero-Extension ==="
  -- 1. Initialize machine state with all GPRs and SP set to 0xFFFFFFFFFFFFFFFF (dirty high bits)
  let mut s : AArch64MachineState := default
  s := { s with sp := 0xFFFFFFFFFFFFFFFF }
  for i in [0:31] do
    s := s.setGpr64 (toFin31 i) 0xFFFFFFFFFFFFFFFF

  -- Verify all registers start dirty
  for i in [0:31] do
    check s!"Precondition: x{i} has dirty high bits" (s.getGpr64 (toFin31 i) == 0xFFFFFFFFFFFFFFFF)
  check "Precondition: sp has dirty high bits" (s.sp == 0xFFFFFFFFFFFFFFFF)

  -- Test values for 32-bit writes
  let testVals : List UInt32 := [
    0x00000000, 0x00000001, 0x00000002, 0x7FFFFFFF,
    0x80000000, 0x80000001, 0xAAAAAAAA, 0x55555555,
    0xFFFFFFFF, 0x12345678, 0xDEADBEEF, 0xCAFEBABE
  ]

  -- 2. Test setGpr32 for all 31 registers across all test values
  for idx in [0:31] do
    let finIdx := toFin31 idx
    for val in testVals do
      -- Setup state where this register is 0xFFFFFFFFFFFFFFFF
      s := s.setGpr64 finIdx 0xFFFFFFFFFFFFFFFF
      -- Perform 32-bit write
      s := s.setGpr32 finIdx val
      let val64 := s.getGpr64 finIdx
      let val32 := s.getGpr32 finIdx

      -- Invariant 1: value returned by getGpr32 matches val
      if val32 != val then
        throw (IO.userError s!"setGpr32/getGpr32 mismatch for index {idx}: expected {val}, got {val32}")
      -- Invariant 2: upper 32 bits are strictly 0
      if (val64 >>> 32) != 0 then
        throw (IO.userError s!"Zero-extension VIOLATION on x{idx} after writing w{idx}={val}: x{idx}={val64}")
      -- Invariant 3: full 64-bit value equals val.toUInt64
      if val64 != val.toUInt64 then
        throw (IO.userError s!"64-bit value mismatch on x{idx}: expected {val.toUInt64}, got {val64}")

  IO.println "[PASS] setGpr32 strictly clears upper 32 bits on all GPRs (0-30) for all test vectors."

  -- 3. Test register isolation: writing to w_i must NOT alter x_j for j != i
  for i in [0:31] do
    let finI := toFin31 i
    -- Reset all registers to known distinct pattern
    for j in [0:31] do
      let finJ := toFin31 j
      s := s.setGpr64 finJ (0x1000000000000000 + j.toUInt64)

    -- Write to w_i
    s := s.setGpr32 finI 0xA5A5A5A5

    -- Verify all j != i are untouched
    for j in [0:31] do
      let finJ := toFin31 j
      let actual := s.getGpr64 finJ
      if j == i then
        if actual != 0x00000000A5A5A5A5 then
          throw (IO.userError s!"Expected w{i} zero-extended value, got {actual}")
      else
        let expected := 0x1000000000000000 + j.toUInt64
        if actual != expected then
          throw (IO.userError s!"Register isolation failure! Writing w{i} corrupted x{j}: expected {expected}, got {actual}")

  IO.println "[PASS] Register isolation verified: modifying w_i preserves all other registers."

  -- 4. Test WSP / SP zero-extension
  s := { s with sp := 0xFFFFFFFFFFFFFFFF }
  for val in testVals do
    s := { s with sp := 0xFFFFFFFFFFFFFFFF }
    s := s.setReg32 .wsp val
    check s!"wsp write with {val} updates sp" (s.sp == val.toUInt64)
    check s!"wsp write with {val} clears sp upper 32 bits" ((s.sp >>> 32) == 0)
    check s!"getReg32 .wsp returns written value" (s.getReg32 .wsp == val)

  -- 5. Test XZR / WZR invariants
  let preXzrState := s
  -- Writes to xzr / wzr must be strictly no-ops
  s := s.setReg64 .xzr 0xDEADBEEFCAFE0000
  check "Write to xzr discarded" (stateEquals s preXzrState)
  s := s.setReg32 .wzr 0xFFFFFFFF
  check "Write to wzr discarded" (stateEquals s preXzrState)
  s := s.setGpr64WithXzr (toFin32 31) 0x1234567890ABCDEF
  check "setGpr64WithXzr(31) discarded" (stateEquals s preXzrState)
  s := s.setGpr32WithWzr (toFin32 31) 0x12345678
  check "setGpr32WithWzr(31) discarded" (stateEquals s preXzrState)

  -- Reads from xzr / wzr must strictly return 0
  check "getReg64 .xzr is 0" (s.getReg64 .xzr == 0)
  check "getReg32 .wzr is 0" (s.getReg32 .wzr == 0)
  check "getGpr64WithXzr(31) is 0" (s.getGpr64WithXzr (toFin32 31) == 0)
  check "getGpr32WithWzr(31) is 0" (s.getGpr32WithWzr (toFin32 31) == 0)

  -- 6. Test roundtrip mappings between Reg32 and Reg64
  let allReg32 : List Reg32 := [
    .w0, .w1, .w2, .w3, .w4, .w5, .w6, .w7,
    .w8, .w9, .w10, .w11, .w12, .w13, .w14, .w15,
    .w16, .w17, .w18, .w19, .w20, .w21, .w22, .w23,
    .w24, .w25, .w26, .w27, .w28, .w29, .w30,
    .wzr, .wsp
  ]
  for r32 in allReg32 do
    let r64 := reg32To64 r32
    check s!"reg64To32 (reg32To64 {r32.toString}) == {r32.toString}" (reg64To32 r64 == r32)

  IO.println "[PASS] Register aliasing and 32-bit zero-extension invariants strictly hold."

def stressTestStateResetSpAlignmentAndFaults : IO Unit := do
  IO.println "\n=== Section 3: Machine State Reset, SP Alignment, and Fault Transitions ==="
  -- 1. Machine state reset test
  let dirtyState : AArch64MachineState := {
    pc := 0x40001000,
    sp := 0x7FFFFFFF0008,
    gprs := fun _ => 0xCAFEBABEDEADBEEF,
    nzcv := { n := true, z := true, c := true, v := true },
    fault := some .alignmentFault,
    terminated := true,
    exitCode := 42
  }

  check "dirtyState is dirty" (dirtyState.pc != 0 && dirtyState.faulted && dirtyState.isHalted)
  let clean : AArch64MachineState := AArch64MachineState.reset
  check "reset: pc == 0" (clean.pc == 0)
  check "reset: sp == 0" (clean.sp == 0)
  for i in [0:31] do
    check s!"reset: gprs[{i}] == 0" (clean.getGpr64 (toFin31 i) == 0)
  check "reset: nzcv.n == false" (clean.nzcv.n == false)
  check "reset: nzcv.z == false" (clean.nzcv.z == false)
  check "reset: nzcv.c == false" (clean.nzcv.c == false)
  check "reset: nzcv.v == false" (clean.nzcv.v == false)
  check "reset: fault == none" (clean.fault == none)
  check "reset: faulted == false" (clean.faulted == false)
  check "reset: terminated == false" (clean.terminated == false)
  check "reset: exitCode == 0" (clean.exitCode == 0)
  check "reset: isHalted == false" (clean.isHalted == false)

  -- 2. SP 16-byte alignment predicate test
  let alignedSpValues : List UInt64 := [
    0x0, 0x10, 0x20, 0x100, 0x1000, 0x40000000,
    0x7FFFFFFF0000, 0x7FFFFFFF0010, 0x8000000000000000,
    0xFFFFFFFFFFFFFFF0, 0xFFFFFFFFFFFFFFE0
  ]
  for spVal in alignedSpValues do
    let sAligned : AArch64MachineState := { clean with sp := spVal }
    check s!"SP {spVal} is aligned (isSpAligned)" (sAligned.isSpAligned == true)
    check s!"SP {spVal} is aligned (checkSpAlignment)" (sAligned.checkSpAlignment == true)
    -- Verify equivalence with isSpAligned from MemoryCell.lean
    check s!"SP {spVal} isSpAligned match" (isSpAligned spVal == true)

  let unalignedSpValues : List UInt64 := [
    0x1, 0x2, 0x3, 0x4, 0x7, 0x8, 0x9, 0xF,
    0x11, 0x18, 0x1F, 0x7FFFFFFF0008, 0x7FFFFFFF0004,
    0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFF8, 0xFFFFFFFFFFFFFFF1
  ]
  for spVal in unalignedSpValues do
    let sUnaligned : AArch64MachineState := { clean with sp := spVal }
    check s!"SP {spVal} is unaligned (isSpAligned)" (sUnaligned.isSpAligned == false)
    check s!"SP {spVal} is unaligned (checkSpAlignment)" (sUnaligned.checkSpAlignment == false)
    -- Verify equivalence with isSpAligned from MemoryCell.lean
    check s!"SP {spVal} isSpAligned match" (isSpAligned spVal == false)

  -- Exhaustive check over small values [0..255]
  for offset in [0:256] do
    let spVal : UInt64 := offset.toUInt64
    let expected := (offset % 16 == 0)
    let sSp : AArch64MachineState := { clean with sp := spVal }
    if sSp.isSpAligned != expected then
      throw (IO.userError s!"SP alignment failure on offset {offset}: expected {expected}, got {sSp.isSpAligned}")
    if (isSpAligned spVal) != expected then
      throw (IO.userError s!"isSpAligned failure on offset {offset}")

  IO.println "[PASS] SP 16-byte alignment predicate verified on all edge cases and boundary sweeps."

  -- 3. Fault transitions and termination
  let allFaults : List AArch64Fault := [
    .alignmentFault, .unmappedAccess, .undefinedInstruction, .permissionFault
  ]
  for f in allFaults do
    let sFault := clean.setFault f
    check s!"setFault({repr f}) sets fault" (sFault.fault == some f)
    check s!"setFault({repr f}) sets faulted" (sFault.faulted == true)
    check s!"setFault({repr f}) sets isHalted" (sFault.isHalted == true)
    check s!"setFault({repr f}) leaves terminated false" (sFault.terminated == false)

  -- Termination tests
  let exitCodes : List UInt32 := [0, 1, 2, 42, 127, 255, 0xFFFFFFFF]
  for code in exitCodes do
    let sTerm := clean.terminate code
    check s!"terminate({code}) sets terminated" (sTerm.terminated == true)
    check s!"terminate({code}) sets exitCode" (sTerm.exitCode == code)
    check s!"terminate({code}) sets isHalted" (sTerm.isHalted == true)
    check s!"terminate({code}) leaves fault none" (sTerm.fault == none)
    check s!"terminate({code}) leaves faulted false" (sTerm.faulted == false)

  -- Advance PC and branch checks
  let sPc0 := clean
  check "advancePc advances by 4" (sPc0.advancePc.pc == 4)
  check "advancePc twice advances by 8" (sPc0.advancePc.advancePc.pc == 8)
  check "branch updates pc to target" ((sPc0.branch 0x40001000).pc == 0x40001000)

  IO.println "[PASS] Machine State reset, SP alignment, and fault transitions fully verified."

def stressTestFlagComputationAddSubLogic : IO Unit := do
  IO.println "\n=== Section 4: Stress-Testing Add/Sub/Logic Flag Computations ==="
  -- Test 64-bit addition flags
  let f0 := computeAddFlags64 0 0
  check "0+0: Z=1, N=0, C=0, V=0" (f0.z && !f0.n && !f0.c && !f0.v)

  let fMaxAdd1 := computeAddFlags64 0xFFFFFFFFFFFFFFFF 1
  check "MAX+1: Z=1, N=0, C=1, V=0" (fMaxAdd1.z && !fMaxAdd1.n && fMaxAdd1.c && !fMaxAdd1.v)

  let fPosOverflow := computeAddFlags64 0x7FFFFFFFFFFFFFFF 1
  check "INT64_MAX+1: N=1, V=1, C=0, Z=0" (fPosOverflow.n && fPosOverflow.v && !fPosOverflow.c && !fPosOverflow.z)

  let fNegOverflow := computeAddFlags64 0x8000000000000000 0x8000000000000000
  check "MIN+MIN: Z=1, C=1, V=1, N=0" (fNegOverflow.z && fNegOverflow.c && fNegOverflow.v && !fNegOverflow.n)

  -- Test 64-bit subtraction flags
  let fSubEq := computeSubFlags64 5 5
  check "5-5: Z=1, C=1, N=0, V=0" (fSubEq.z && fSubEq.c && !fSubEq.n && !fSubEq.v)

  let fSubBorrow := computeSubFlags64 4 5
  check "4-5: C=0 (borrow), N=1, Z=0, V=0" (!fSubBorrow.c && fSubBorrow.n && !fSubBorrow.z && !fSubBorrow.v)

  let fSubOverflow := computeSubFlags64 0x8000000000000000 1
  check "MIN-1: V=1, C=1, N=0, Z=0" (fSubOverflow.v && fSubOverflow.c && !fSubOverflow.n && !fSubOverflow.z)

  -- Test 32-bit addition flags
  let f32Add := computeAddFlags32 0xFFFFFFFF 1
  check "32-bit MAX+1: Z=1, C=1, N=0, V=0" (f32Add.z && f32Add.c && !f32Add.n && !f32Add.v)

  -- 32-bit subtraction flags
  let f32Sub := computeSubFlags32 10 20
  check "32-bit 10-20: C=0, N=1, Z=0, V=0" (!f32Sub.c && f32Sub.n && !f32Sub.z && !f32Sub.v)

  -- Test logic flags (must clear C and V)
  let fLog64 := computeLogicFlags64 0x8000000000000000
  check "Logic64 MSB: N=1, Z=0, C=0, V=0" (fLog64.n && !fLog64.z && !fLog64.c && !fLog64.v)

  let fLog32 := computeLogicFlags32 0
  check "Logic32 zero: Z=1, N=0, C=0, V=0" (fLog32.z && !fLog32.n && !fLog32.c && !fLog32.v)

  IO.println "[PASS] Flag computation stress tests passed."

def stressTestMemoryOperations : IO Unit := do
  IO.println "\n=== Section 5: Stress-Testing Memory Model Operations ==="
  let clean : AArch64MachineState := AArch64MachineState.reset
  let baseAddr : UInt64 := 0x40001000

  -- Write 64-bit value: 0x0102030405060708
  let val64 : UInt64 := 0x0102030405060708
  let sMem := clean.writeMem .w64 baseAddr val64

  -- Check little-endian byte ordering
  check "byte 0 is 0x08" (sMem.readMem .w8 baseAddr == 0x08)
  check "byte 1 is 0x07" (sMem.readMem .w8 (baseAddr + 1) == 0x07)
  check "byte 2 is 0x06" (sMem.readMem .w8 (baseAddr + 2) == 0x06)
  check "byte 3 is 0x05" (sMem.readMem .w8 (baseAddr + 3) == 0x05)
  check "byte 4 is 0x04" (sMem.readMem .w8 (baseAddr + 4) == 0x04)
  check "byte 5 is 0x03" (sMem.readMem .w8 (baseAddr + 5) == 0x03)
  check "byte 6 is 0x02" (sMem.readMem .w8 (baseAddr + 6) == 0x02)
  check "byte 7 is 0x01" (sMem.readMem .w8 (baseAddr + 7) == 0x01)

  -- Check multi-width reads
  check "readMem w16 is 0x0708" (sMem.readMem .w16 baseAddr == 0x0708)
  check "readMem w32 is 0x05060708" (sMem.readMem .w32 baseAddr == 0x05060708)
  check "readMem w64 is 0x0102030405060708" (sMem.readMem .w64 baseAddr == val64)

  -- Test memory isolation: memory at other addresses is zero
  check "unwritten memory is 0" (sMem.readMem .w64 (baseAddr + 8) == 0)
  check "unwritten memory before is 0" (sMem.readMem .w64 (baseAddr - 8) == 0)

  -- Test natural alignment predicate
  check "baseAddr is w8 aligned" (isAligned baseAddr .w8 == true)
  check "baseAddr is w16 aligned" (isAligned baseAddr .w16 == true)
  check "baseAddr is w32 aligned" (isAligned baseAddr .w32 == true)
  check "baseAddr is w64 aligned" (isAligned baseAddr .w64 == true)

  let unalign1 := baseAddr + 1
  check "unalign1 is w8 aligned" (isAligned unalign1 .w8 == true)
  check "unalign1 is not w16 aligned" (isAligned unalign1 .w16 == false)
  check "unalign1 is not w32 aligned" (isAligned unalign1 .w32 == false)
  check "unalign1 is not w64 aligned" (isAligned unalign1 .w64 == false)

  let unalign2 := baseAddr + 2
  check "unalign2 is w16 aligned" (isAligned unalign2 .w16 == true)
  check "unalign2 is not w32 aligned" (isAligned unalign2 .w32 == false)
  check "unalign2 is not w64 aligned" (isAligned unalign2 .w64 == false)

  let unalign4 := baseAddr + 4
  check "unalign4 is w32 aligned" (isAligned unalign4 .w32 == true)
  check "unalign4 is not w64 aligned" (isAligned unalign4 .w64 == false)

  IO.println "[PASS] Memory model operations and alignment checks passed."

def main : IO Unit := do
  IO.println "Starting Empirical Challenger Stress Harness for AArch64..."
  stressTestConditionEvaluation
  stressTestRegistersAndZeroExtension
  stressTestStateResetSpAlignmentAndFaults
  stressTestFlagComputationAddSubLogic
  stressTestMemoryOperations
  IO.println "\nALL ADVERSARIAL CHALLENGES PASSED EMPIRICALLY."
