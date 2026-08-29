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
Adversarial Stress Test Suite for Cortex-A53 Performance Model and Cycle Simulator.
Tests dual-issue pairing, RAW hazards, structural hazards, division stalls, and analytic bounds.
-/

import Lean
import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.Addressing
import Gasm.Targets.AArch64.Instructions
import Gasm.Targets.AArch64.Uop
import Gasm.Targets.AArch64.Performance

open Gasm.Core
open Gasm.Targets.AArch64

def check (desc : String) (cond : Bool) : IO Unit := do
  if !cond then
    IO.println s!"[FAIL] {desc}"
    throw (IO.userError s!"Assertion failed: {desc}")
  else
    IO.println s!"[PASS] {desc}"

def runSim (uops : List AArch64Uop) : CortexA53SimState × Nat × PerfCycleBounds :=
  let s := uops.foldl (fun st u => stepSimUop st u cortexA53Profile) {}
  let cyc := finalizeSimCycles s
  let bounds := computeCycleBounds uops cortexA53Profile
  (s, cyc, bounds)

-- Helper UOP constructors
def makeAlu (name : String) (src : List Reg64) (dst : List Reg64) : AArch64Uop :=
  { mnemonic := name, uopClass := .intALU, eligibleSlots := [.slot0, .slot1], latencyCycles := 1, reciprocalThroughput := 0.5, srcRegs := src, dstRegs := dst }

def makeShiftedAlu (name : String) (src : List Reg64) (dst : List Reg64) : AArch64Uop :=
  { mnemonic := name, uopClass := .intShift, eligibleSlots := [.slot1], latencyCycles := 2, reciprocalThroughput := 1.0, srcRegs := src, dstRegs := dst }

def makeLoad (name : String) (rt rn : Reg64) : AArch64Uop :=
  { mnemonic := name, uopClass := .load, eligibleSlots := [.slot1], latencyCycles := 3, reciprocalThroughput := 1.0, srcRegs := [rn], dstRegs := [rt], isLoad := true }

def makeStore (name : String) (rt rn : Reg64) : AArch64Uop :=
  { mnemonic := name, uopClass := .store, eligibleSlots := [.slot1], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [rn, rt], dstRegs := [], isStore := true }

def makeBranch (name : String) : AArch64Uop :=
  { mnemonic := name, uopClass := .branch, eligibleSlots := [.slot0], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [], dstRegs := [], isBranch := true }

def makeDiv (name : String) (rd rn rm : Reg64) (lat : Nat := 12) : AArch64Uop :=
  { mnemonic := name, uopClass := .intDiv, eligibleSlots := [.slot0], latencyCycles := lat, reciprocalThroughput := lat.toFloat, srcRegs := [rn, rm], dstRegs := [rd] }

-- LCG Pseudo-Random Number Generator
structure SimpleRng where
  state : UInt64

def SimpleRng.next (rng : SimpleRng) : UInt64 × SimpleRng :=
  let nextState := rng.state * 6364136223846793005 + 1442695040888963407
  (nextState, { state := nextState })

def SimpleRng.nextNat (rng : SimpleRng) (maxVal : Nat) : Nat × SimpleRng :=
  let (v, r) := rng.next
  ((v.toNat % maxVal), r)

def pickReg (regs : Array Reg64) (idx : Nat) : Reg64 :=
  regs[idx % regs.size]!

def main : IO Unit := do
  IO.println "================================================================================"
  IO.println "STARTING ADVERSARIAL STRESS TESTING: CORTEX-A53 PERFORMANCE MODEL"
  IO.println "================================================================================"

  -- ============================================================================
  -- Section 1: Dual-Issue Pairing of Independent ALU Instructions
  -- ============================================================================
  IO.println "\n=== Section 1: Dual-Issue Pairing ==="

  -- 1.1: Two independent ALUs should pair into cycle 1
  let alu1 := makeAlu "ADD1" [.x1, .x2] [.x0]
  let alu2 := makeAlu "ADD2" [.x3, .x4] [.x5]
  let (s1, cyc1, _) := runSim [alu1, alu2]
  check "Two independent ALUs issue in cycle 1" (s1.curCycle == 1)
  check "Two independent ALUs slot0 and slot1 occupied" (s1.slot0Occupied && s1.slot1Occupied)
  check "Two independent ALUs totalCycles == 2 (1 issue + 1 latency)" (cyc1 == 2)
  check "Two independent ALUs zero structural stalls" (s1.structuralStalls == 0)
  check "Two independent ALUs zero raw stalls" (s1.rawStalls == 0)

  -- 1.2: Four independent ALUs should pair into two cycles
  let alu3 := makeAlu "ADD3" [.x6, .x7] [.x8]
  let alu4 := makeAlu "ADD4" [.x9, .x10] [.x11]
  let (s2, cyc2, _) := runSim [alu1, alu2, alu3, alu4]
  check "Four independent ALUs finish issue at cycle 2" (s2.curCycle == 2)
  check "Four independent ALUs totalCycles == 3 (2 issue + 1 latency)" (cyc2 == 3)
  check "Four independent ALUs zero raw stalls" (s2.rawStalls == 0)

  -- 1.3: ALU (slot0, slot1) + Shifted ALU (slot1 only) can pair
  let alu_any := makeAlu "ADD" [.x1, .x2] [.x0]
  let alu_shift := makeShiftedAlu "ADD_LSL" [.x3, .x4] [.x5]
  let (s3, _, _) := runSim [alu_any, alu_shift]
  check "ALU and Shifted-ALU pair in cycle 1" (s3.curCycle == 1)
  check "ALU takes slot0, Shifted-ALU takes slot1" (s3.slot0Occupied && s3.slot1Occupied)

  -- 1.4: Shifted ALU (slot1 only) + Shifted ALU (slot1 only) CANNOT pair (structural slot conflict)
  let shift1 := makeShiftedAlu "SHIFT1" [.x1, .x2] [.x0]
  let shift2 := makeShiftedAlu "SHIFT2" [.x3, .x4] [.x5]
  let (s4, _, _) := runSim [shift1, shift2]
  check "Two Slot1-only instructions cannot dual issue" (s4.curCycle == 2)
  check "Structural stall charged for slot conflict" (s4.structuralStalls == 1)

  -- ============================================================================
  -- Section 2: RAW Hazard Stall Cycles
  -- ============================================================================
  IO.println "\n=== Section 2: RAW Hazard Stall Cycles ==="

  -- 2.1: Simple ALU-to-ALU dependency: ADD x0, x1, x2; ADD x3, x0, x4
  let dep_alu1 := makeAlu "PRODUCER" [.x1, .x2] [.x0]
  let dep_alu2 := makeAlu "CONSUMER" [.x0, .x4] [.x3]
  let (s_raw1, cyc_raw1, _) := runSim [dep_alu1, dep_alu2]
  check "Dependent ALU cannot dual issue in cycle 1" (s_raw1.curCycle == 2)
  check "Dependent ALU completes at cycle 3 (cyc 1 issue, cyc 2 issue, +1 lat)" (cyc_raw1 == 3)

  -- 2.2: Load-to-Use Hazard: LDR x0, [x1]; ADD x2, x0, x3
  let ldr_uop := makeLoad "LDR" .x0 .x1
  let use_uop := makeAlu "USE" [.x0, .x3] [.x2]
  let (s_load_use, cyc_load_use, _) := runSim [ldr_uop, use_uop]
  check "Load-to-use consumer issues at cycle 4" (s_load_use.curCycle == 4)
  check "Load-to-use charges exactly 2 rawStalls" (s_load_use.rawStalls == 2)
  check "Load-to-use total cycles == 5 (cyc 4 issue + 1 latency)" (cyc_load_use == 5)

  -- 2.3: Zero register (XZR) writes discard, reads are cycle 1 (no RAW hazard)
  let xzr_write := makeAlu "WR_XZR" [.x1, .x2] [.xzr]
  let xzr_read  := makeAlu "RD_XZR" [.xzr, .x3] [.x4]
  let (s_xzr, _, _) := runSim [xzr_write, xzr_read]
  check "XZR producer-consumer dual-issues in cycle 1 without RAW stall" (s_xzr.curCycle == 1)
  check "XZR hazard zero rawStalls" (s_xzr.rawStalls == 0)

  -- 2.4: Three-instruction dependent chain: x0 -> x1 -> x2
  let ch1 := makeAlu "CH1" [.x10] [.x0]
  let ch2 := makeAlu "CH2" [.x0] [.x1]
  let ch3 := makeAlu "CH3" [.x1] [.x2]
  let (s_chain, cyc_chain, _) := runSim [ch1, ch2, ch3]
  check "3-hop serial chain issues at cycle 3" (s_chain.curCycle == 3)
  check "3-hop serial chain completes at cycle 4" (cyc_chain == 4)

  -- ============================================================================
  -- Section 3: Structural Hazard Stalls on Dual Memory and Dual Branches
  -- ============================================================================
  IO.println "\n=== Section 3: Structural Hazard Stalls ==="

  -- 3.1: Dual Loads: LDR x0, [x1]; LDR x2, [x3] (independent registers)
  let ldr1 := makeLoad "LDR1" .x0 .x1
  let ldr2 := makeLoad "LDR2" .x2 .x3
  let (s_mem1, _, _) := runSim [ldr1, ldr2]
  check "Dual loads cannot dual issue (issuedMemInCycle)" (s_mem1.curCycle == 2)
  check "Dual loads structuralStalls == 1" (s_mem1.structuralStalls == 1)

  -- 3.2: Dual Stores: STR x0, [x1]; STR x2, [x3]
  let str1 := makeStore "STR1" .x0 .x1
  let str2 := makeStore "STR2" .x2 .x3
  let (s_mem2, _, _) := runSim [str1, str2]
  check "Dual stores cannot dual issue" (s_mem2.curCycle == 2)
  check "Dual stores structuralStalls == 1" (s_mem2.structuralStalls == 1)

  -- 3.3: Mixed Load then Store: LDR x0, [x1]; STR x2, [x3]
  let (s_mem3, _, _) := runSim [ldr1, str2]
  check "Load + Store cannot dual issue" (s_mem3.curCycle == 2)
  check "Load + Store structuralStalls == 1" (s_mem3.structuralStalls == 1)

  -- 3.4: Dual Branches: B #16; B #32
  let br1 := makeBranch "B1"
  let br2 := makeBranch "B2"
  let (s_br, _, _) := runSim [br1, br2]
  check "Dual branches cannot dual issue (issuedBranchInCycle)" (s_br.curCycle == 2)
  check "Dual branches structuralStalls == 1" (s_br.structuralStalls == 1)

  -- 3.5: Branch (slot0) + ALU (slot0, slot1) CAN dual-issue
  let br3 := makeBranch "B_COND"
  let alu_pair := makeAlu "ADD" [.x1, .x2] [.x0]
  let (s_br_alu, _, _) := runSim [br3, alu_pair]
  check "Branch + independent ALU can dual issue in cycle 1" (s_br_alu.curCycle == 1)
  check "Branch + ALU zero structural stalls" (s_br_alu.structuralStalls == 0)

  -- ============================================================================
  -- Section 4: Division Latency and Unpipelined Divider Stalls
  -- ============================================================================
  IO.println "\n=== Section 4: Division Latency & Divider Stalls ==="

  -- 4.1: Single division of latency 12
  let div1 := makeDiv "UDIV1" .x0 .x1 .x2 12
  let (s_div1, cyc_div1, _) := runSim [div1]
  check "Single division issues in cycle 1" (s_div1.curCycle == 1)
  check "Single division sets dividerFreeAt to 13" (s_div1.dividerFreeAt == 13)
  check "Single division finalizeSimCycles == 13" (cyc_div1 == 13)

  -- 4.2: Two consecutive independent divisions (unpipelined hardware divider)
  let div2 := makeDiv "UDIV2" .x3 .x4 .x5 12
  let (s_div2, cyc_div2, _) := runSim [div1, div2]
  check "Second division stalls until dividerFreeAt (cycle 13)" (s_div2.curCycle == 13)
  check "Unpipelined divider charges rawStalls == 11 (13 - 2)" (s_div2.rawStalls == 11)
  check "Two divisions total execution cycles == 25" (cyc_div2 == 25)

  -- 4.3: Division followed by independent ALU instruction
  let alu_free := makeAlu "ADD_FREE" [.x6, .x7] [.x8]
  let (s_div_alu, cyc_div_alu, _) := runSim [div1, alu_free]
  check "Independent ALU dual-issues with division in cycle 1" (s_div_alu.curCycle == 1)
  check "ALU does not suffer divider stall (rawStalls == 0)" (s_div_alu.rawStalls == 0)
  check "Final cycles bound by long division latency (13)" (cyc_div_alu == 13)

  -- 4.4: Division followed by dependent ALU instruction
  let alu_dep := makeAlu "ADD_DEP" [.x0, .x7] [.x8]
  let (s_div_dep, cyc_div_dep, _) := runSim [div1, alu_dep]
  check "Dependent ALU issues at cycle 13" (s_div_dep.curCycle == 13)
  check "Dependent ALU completion cycles == 14 (13 issue + 1 lat)" (cyc_div_dep == 14)
  check "RAW stall charged for division result dependence (11 cycles)" (s_div_dep.rawStalls == 11)

  -- ============================================================================
  -- Section 5: Analytic Cycle Bounds (minCycles <= nominalCycles <= maxCycles)
  -- ============================================================================
  IO.println "\n=== Section 5: Analytic Cycle Bounds Invariant Verification ==="

  -- 5.1: Empty stream
  let b_empty := computeCycleBounds []
  check "Empty stream: min=1, nom=1, max=1" (b_empty.minCycles == 1 && b_empty.nominalCycles == 1 && b_empty.maxCycles == 1)
  check "Empty stream bounds ordering: min <= nom <= max" (b_empty.minCycles <= b_empty.nominalCycles && b_empty.nominalCycles <= b_empty.maxCycles)

  -- 5.2: Boundary streams
  let testStreams : List (String × List AArch64Uop) := [
    ("Single ALU", [alu1]),
    ("Two independent ALUs", [alu1, alu2]),
    ("Four independent ALUs", [alu1, alu2, alu3, alu4]),
    ("Load-to-use chain", [ldr_uop, use_uop]),
    ("Dual branch stream", [br1, br2]),
    ("Dual load stream", [ldr1, ldr2]),
    ("Back-to-back div stream", [div1, div2]),
    ("Div + ALU stream", [div1, alu_free]),
    ("All-dependent chain 5", [ch1, ch2, ch3, makeAlu "C4" [.x2] [.x3], makeAlu "C5" [.x3] [.x4]])
  ]

  for (name, stm) in testStreams do
    let bounds := computeCycleBounds stm
    let ok := bounds.minCycles <= bounds.nominalCycles && bounds.nominalCycles <= bounds.maxCycles
    check s!"Bounds invariant for '{name}': min({bounds.minCycles}) <= nom({bounds.nominalCycles}) <= max({bounds.maxCycles})" ok

  -- 5.3: Stress Fuzzing 5,000 Randomized Micro-Op Streams
  IO.println "\n--- Stress Fuzzing 5,000 Randomized UOP Streams ---"
  let mut rng : SimpleRng := { state := 0xDEADBEEFCAFE1234 }
  let regs : Array Reg64 := #[.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .sp, .xzr]
  let numTrials := 5000
  let mut failedTrials := 0

  for trial in [0:numTrials] do
    let (streamLen, r1) := rng.nextNat 30  -- 0 to 29 uops
    rng := r1
    let mut uops : List AArch64Uop := []

    for _ in [0:streamLen] do
      let (kind, r2) := rng.nextNat 6
      let (rIdx1, r3) := r2.nextNat regs.size
      let (rIdx2, r4) := r3.nextNat regs.size
      let (rIdx3, r5) := r4.nextNat regs.size
      rng := r5
      let reg1 := pickReg regs rIdx1
      let reg2 := pickReg regs rIdx2
      let reg3 := pickReg regs rIdx3

      let uop := match kind with
      | 0 => makeAlu s!"ALU_{trial}" [reg2, reg3] [reg1]
      | 1 => makeShiftedAlu s!"SHIFT_{trial}" [reg2, reg3] [reg1]
      | 2 => makeLoad s!"LDR_{trial}" reg1 reg2
      | 3 => makeStore s!"STR_{trial}" reg1 reg2
      | 4 => makeBranch s!"BR_{trial}"
      | _ => makeDiv s!"DIV_{trial}" reg1 reg2 reg3 12
      uops := uops ++ [uop]

    let bounds := computeCycleBounds uops
    if !(bounds.minCycles <= bounds.nominalCycles && bounds.nominalCycles <= bounds.maxCycles) then
      failedTrials := failedTrials + 1
      IO.println s!"[FAIL INVARIANT] Trial {trial} failed: len={uops.length} min={bounds.minCycles} nom={bounds.nominalCycles} max={bounds.maxCycles}"

  check s!"All {numTrials} randomized adversarial micro-op streams satisfy minCycles <= nominalCycles <= maxCycles" (failedTrials == 0)

  -- ============================================================================
  -- Section 6: Instruction Level Simulation (toUops -> simulateExecution)
  -- ============================================================================
  IO.println "\n=== Section 6: Real AArch64 AST simulateInstructions ==="

  let realInstrs : List AArch64Instr := [
    .movz true .x0 100 0,
    .movz true .x1 200 0,
    .addReg true false .x2 .x0 .x1 .LSL 0,
    .strImm true .x2 .sp 16,
    .ldrImm true .x3 .sp 16,
    .bCond .EQ 8,
    .ret .x30
  ]

  let rep := analyzeInstructionPerformance realInstrs
  check "analyzeInstructionPerformance totalInstructions == 7" (rep.totalInstructions == 7)
  check "analyzeInstructionPerformance bounds invariant holds" (rep.bounds.minCycles <= rep.bounds.nominalCycles && rep.bounds.nominalCycles <= rep.bounds.maxCycles)
  check "analyzeInstructionPerformance simulatedCycles == nominalCycles" (rep.simulatedCycles == rep.bounds.nominalCycles)
  check "analyzeInstructionPerformance cpiNominal > 0.0" (rep.cpiNominal > 0.0)
  check "analyzeInstructionPerformance ipcNominal > 0.0" (rep.ipcNominal > 0.0)
  check "Waterfall timeline generated" (rep.waterfallTimeline.length > 50)

  IO.println "\n================================================================================"
  IO.println "ALL 34 PERFORMANCE MODEL CORE TESTS PASSED EMPIRICALLY."
  IO.println "================================================================================"

