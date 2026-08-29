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
import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.Addressing
import Gasm.Targets.AArch64.Instructions
import Gasm.Targets.AArch64.Uop

namespace Gasm.Targets.AArch64

open Gasm.Targets.AArch64.Instructions

/- REF: docs/TARGETS/ARM64.md#cortex-a53-performance-model-validation-obligations -/
/-- Minimum of two Float values. -/
def floatMin (a b : Float) : Float := if a < b then a else b

/- REF: docs/TARGETS/ARM64.md#cortex-a53-performance-model-validation-obligations -/
/-- Maximum of two Float values. -/
def floatMax (a b : Float) : Float := if a > b then a else b

/- REF: docs/TARGETS/ARM64.md#cortex-a53-performance-model-validation-obligations -/
/-- Clamps a Float percentage to [0.0, 100.0]. -/
def clampPct (v : Float) : Float := floatMin 100.0 (floatMax 0.0 v)

/- REF: docs/TARGETS/ARM64.md#1-pipeline-microarchitecture-dual-issue-rules -/
/-- Microarchitectural simulation tracking state for Cortex-A53 in-order dual-issue execution. -/
structure CortexA53SimState where
  curCycle             : Nat := 1
  slot0Occupied        : Bool := false
  slot1Occupied        : Bool := false
  issuedMemInCycle     : Bool := false
  issuedBranchInCycle  : Bool := false
  dividerFreeAt        : Nat := 1
  regReadyAt           : List (Reg64 × Nat) := []
  totalInstructions    : Nat := 0
  totalUops            : Nat := 0
  dualIssuedPairs      : Nat := 0
  rawStalls            : Nat := 0
  structuralStalls     : Nat := 0
  loadToUseStalls      : Nat := 0
  deriving Repr, Inhabited

/- REF: docs/TARGETS/ARM64.md#1-pipeline-microarchitecture-dual-issue-rules -/
/-- Look up when a register will become ready in the simulation state. -/
def getRegReadyAt (state : CortexA53SimState) (r : Reg64) : Nat :=
  if r == .xzr then 1
  else match state.regReadyAt.lookup r with
    | some cyc => cyc
    | none => 1

/- REF: docs/TARGETS/ARM64.md#1-pipeline-microarchitecture-dual-issue-rules -/
/-- Update when a destination register will become ready. -/
def setRegReadyAt (state : CortexA53SimState) (r : Reg64) (readyCyc : Nat) : CortexA53SimState :=
  if r == .xzr then state
  else
    let filtered := state.regReadyAt.filter (fun (reg, _) => reg != r)
    { state with regReadyAt := (r, readyCyc) :: filtered }

/- REF: docs/TARGETS/ARM64.md#1-pipeline-microarchitecture-dual-issue-rules -/
/-- Determines if an instruction uop can dual-issue in the current cycle without hazards. -/
def canDualIssue (uop : AArch64Uop) (state : CortexA53SimState) : Option CortexA53Slot :=
  if state.slot0Occupied && state.slot1Occupied then none
  else if (uop.isLoad || uop.isStore) && state.issuedMemInCycle then none
  else if uop.isBranch && state.issuedBranchInCycle then none
  else if !state.slot0Occupied && uop.eligibleSlots.contains .slot0 then some .slot0
  else if !state.slot1Occupied && uop.eligibleSlots.contains .slot1 then some .slot1
  else none

/- REF: docs/TARGETS/ARM64.md#1-pipeline-microarchitecture-dual-issue-rules -/
/-- Steps the Cortex-A53 simulation state by scheduling one micro-op. -/
def stepSimUop (state : CortexA53SimState) (uop : AArch64Uop) (profile : CortexA53Profile := cortexA53Profile) : CortexA53SimState :=
  let dataReadyCycle := uop.srcRegs.foldl (fun acc r =>
    Nat.max acc (getRegReadyAt state r)
  ) 1
  let earliestCycle :=
    if uop.uopClass == .intDiv then Nat.max dataReadyCycle state.dividerFreeAt
    else dataReadyCycle

  let canPairInCurCycle := earliestCycle <= state.curCycle
  let dualSlotOpt := if canPairInCurCycle then canDualIssue uop state else none

  match dualSlotOpt with
  | some slot =>
    let issueCyc := state.curCycle
    let completionCyc := issueCyc + uop.latencyCycles
    let effectiveResultCyc :=
      if uop.isLoad then issueCyc + profile.loadToUseStallCycles + 1
      else completionCyc

    let s1 := { state with
      slot0Occupied       := state.slot0Occupied || slot == .slot0
      slot1Occupied       := state.slot1Occupied || slot == .slot1
      issuedMemInCycle    := state.issuedMemInCycle || uop.isLoad || uop.isStore
      issuedBranchInCycle := state.issuedBranchInCycle || uop.isBranch
      totalInstructions   := state.totalInstructions + 1
      totalUops           := state.totalUops + 1
      dualIssuedPairs     := state.dualIssuedPairs + 1
      dividerFreeAt       := if uop.uopClass == .intDiv then issueCyc + uop.latencyCycles else state.dividerFreeAt
    }
    uop.dstRegs.foldl (fun s r => setRegReadyAt s r effectiveResultCyc) s1

  | none =>
    let nextCyc := Nat.max (state.curCycle + 1) earliestCycle
    let rawStallDelta := if earliestCycle > state.curCycle + 1 then earliestCycle - (state.curCycle + 1) else 0
    let structStallDelta := if earliestCycle <= state.curCycle && (state.slot0Occupied || state.slot1Occupied) then 1 else 0

    let bindSlot := if uop.eligibleSlots.contains .slot0 then CortexA53Slot.slot0 else CortexA53Slot.slot1
    let completionCyc := nextCyc + uop.latencyCycles
    let effectiveResultCyc :=
      if uop.isLoad then nextCyc + profile.loadToUseStallCycles + 1
      else completionCyc

    let s1 := { state with
      curCycle            := nextCyc
      slot0Occupied       := bindSlot == .slot0
      slot1Occupied       := bindSlot == .slot1
      issuedMemInCycle    := uop.isLoad || uop.isStore
      issuedBranchInCycle := uop.isBranch
      totalInstructions   := state.totalInstructions + 1
      totalUops           := state.totalUops + 1
      rawStalls           := state.rawStalls + rawStallDelta
      structuralStalls    := state.structuralStalls + structStallDelta
      dividerFreeAt       := if uop.uopClass == .intDiv then nextCyc + uop.latencyCycles else state.dividerFreeAt
    }
    uop.dstRegs.foldl (fun s r => setRegReadyAt s r effectiveResultCyc) s1

/- REF: docs/TARGETS/ARM64.md#1-pipeline-microarchitecture-dual-issue-rules -/
/-- Finalizes the total execution cycles for the simulation run. -/
def finalizeSimCycles (state : CortexA53SimState) : Nat :=
  let maxRegCyc := state.regReadyAt.foldl (fun acc (_, c) => Nat.max acc c) state.curCycle
  Nat.max (Nat.max state.curCycle maxRegCyc) state.dividerFreeAt

/- REF: docs/TARGETS/ARM64.md#1-pipeline-microarchitecture-dual-issue-rules -/
/-- Simulates execution of a micro-op stream on the Cortex-A53 dual-issue core, returning cycle count. -/
def simulateExecution (uops : List AArch64Uop) (profile : CortexA53Profile := cortexA53Profile) : Nat :=
  if uops.isEmpty then 1
  else
    let finalState := uops.foldl (fun s u => stepSimUop s u profile) {}
    finalizeSimCycles finalState

/- REF: docs/TARGETS/ARM64.md#2-execution-latencies-micro-op-classification -/
/-- Computes min, nominal, and max cycle bounds for a retired micro-op stream on Cortex-A53. -/
def computeCycleBounds (uops : List AArch64Uop) (profile : CortexA53Profile := cortexA53Profile) : PerfCycleBounds :=
  if uops.isEmpty then
    { minCycles := 1, nominalCycles := 1, maxCycles := 1 }
  else
    let totalUops := uops.length
    let minCycles := Nat.max 1 ((totalUops + profile.issueWidth - 1) / profile.issueWidth)
    let nominalCycles := simulateExecution uops profile
    let serialLatencySum := uops.foldl (fun acc u => acc + u.latencyCycles) 0
    let branchCount := (uops.filter fun u => u.isBranch).length
    let maxCycles := Nat.max nominalCycles (serialLatencySum + (branchCount * profile.branchMispredictPenalty))
    { minCycles := minCycles, nominalCycles := nominalCycles, maxCycles := maxCycles }

/- REF: docs/TARGETS/ARM64.md#cortex-a53-performance-model-validation-obligations -/
/-- Structured report summarizing Cortex-A53 microarchitectural cycle bounds and execution statistics. -/
structure AArch64PerformanceReport where
  profileName          : String
  totalInstructions    : Nat
  totalUops            : Nat
  bounds               : PerfCycleBounds
  simulatedCycles      : Nat
  ipcNominal           : Float
  cpiNominal           : Float
  dualIssueRatePct     : Float
  rawStallCycles       : Nat
  structuralStallCycles: Nat
  waterfallTimeline    : String
  deriving Repr, Inhabited

/- REF: docs/TARGETS/ARM64.md#1-pipeline-microarchitecture-dual-issue-rules -/
/-- Generates structured ASCII Waterfall Timeline visualization for Cortex-A53 8-stage pipeline:
    [F]etch -> [D]ecode -> [I]ssue -> [E]xecute -> [W]riteback. -/
def generateWaterfall (uops : List AArch64Uop) (profile : CortexA53Profile := cortexA53Profile) (maxDisplayUops : Nat := 16) (maxDisplayCycles : Nat := 24) : String := Id.run do
  let mut lines : List String := []
  lines := lines ++ ["--------------------------------------------------------------------------------"]
  lines := lines ++ ["                 GASM AARCH64 CORTEX-A53 PIPELINE WATERFALL                     "]
  lines := lines ++ ["--------------------------------------------------------------------------------"]
  lines := lines ++ ["Uop ID | Mnemonic        | Slots  | Pipeline Stage Timeline [F|D|I|E|W]         "]
  lines := lines ++ ["--------------------------------------------------------------------------------"]

  let displayedUops := uops.take maxDisplayUops
  let mut curCyc := 1
  let mut uopIdx := 0

  for u in displayedUops do
    let uidStr := s!"#{uopIdx}".pushn ' ' (7 - s!"#{uopIdx}".length)
    let mnemStr := u.mnemonic.pushn ' ' (16 - u.mnemonic.length)
    let slotStr := (if u.eligibleSlots.length > 1 then "Both  " else "Slot0 ").pushn ' ' 7

    let fetchCyc := (uopIdx / profile.decodeWidth) + 1
    let decodeCyc := fetchCyc + 1
    let issueCyc := decodeCyc + 1
    let execCyc := issueCyc + 1
    let retireCyc := execCyc + u.latencyCycles

    let mut timeline := ""
    for cyc in [1:maxDisplayCycles + 1] do
      let char :=
        if cyc == retireCyc then 'W'
        else if cyc >= execCyc && cyc < retireCyc then 'E'
        else if cyc == issueCyc then 'I'
        else if cyc == decodeCyc then 'D'
        else if cyc == fetchCyc then 'F'
        else '.'
      timeline := timeline.push char

    lines := lines ++ [s!"{uidStr}| {mnemStr}| {slotStr}| {timeline}"]
    uopIdx := uopIdx + 1
    curCyc := retireCyc

  lines := lines ++ ["--------------------------------------------------------------------------------"]
  return String.intercalate "\n" lines

/- REF: docs/TARGETS/ARM64.md#cortex-a53-performance-model-validation-obligations -/
/-- Comprehensive performance analyzer for AArch64 micro-op sequences on Cortex-A53. -/
def analyzePerformance (uops : List AArch64Uop) (profile : CortexA53Profile := cortexA53Profile) : AArch64PerformanceReport :=
  let bounds := computeCycleBounds uops profile
  let finalState := uops.foldl (fun s u => stepSimUop s u profile) {}
  let simCycles := finalizeSimCycles finalState
  let waterfall := generateWaterfall uops profile
  let totalUopsFloat := uops.length.toFloat
  let simCyclesFloat := simCycles.toFloat
  let ipc := if simCycles == 0 then 0.0 else totalUopsFloat / simCyclesFloat
  let cpi := if uops.isEmpty then 0.0 else simCyclesFloat / totalUopsFloat
  let dualIssuePct := if uops.isEmpty then 0.0 else clampPct ((finalState.dualIssuedPairs.toFloat * 2.0 / totalUopsFloat) * 100.0)

  {
    profileName           := profile.name
    totalInstructions     := uops.length
    totalUops             := uops.length
    bounds                := bounds
    simulatedCycles       := simCycles
    ipcNominal            := ipc
    cpiNominal            := cpi
    dualIssueRatePct      := dualIssuePct
    rawStallCycles        := finalState.rawStalls
    structuralStallCycles := finalState.structuralStalls
    waterfallTimeline     := waterfall
  }

/- REF: docs/TARGETS/ARM64.md#2-execution-latencies-micro-op-classification -/
/-- Decomposes an AArch64 instruction into Cortex-A53 micro-ops via typeclass dispatch. -/
def toUops (i : AnyAArch64Instruction) : List AArch64Uop :=
  AArch64Instruction.toUops i

/- REF: docs/TARGETS/ARM64.md#2-execution-latencies-micro-op-classification -/
/-- Simulates an instruction sequence directly by decomposing instructions into micro-ops. -/
def simulateInstructions (instrs : List AnyAArch64Instruction) (profile : CortexA53Profile := cortexA53Profile) : Nat :=
  simulateExecution (instrs.flatMap toUops) profile

/- REF: docs/TARGETS/ARM64.md#cortex-a53-performance-model-validation-obligations -/
/-- Analyzes an instruction sequence directly on the Cortex-A53 dual-issue core. -/
def analyzeInstructionPerformance (instrs : List AnyAArch64Instruction) (profile : CortexA53Profile := cortexA53Profile) : AArch64PerformanceReport :=
  analyzePerformance (instrs.flatMap toUops) profile

end Gasm.Targets.AArch64
