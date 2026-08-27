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
import Gasm.Targets.X86_64.Uop
import Gasm.Targets.X86_64.Instructions.Base

namespace Gasm.Targets.X86_64

open Gasm.Targets.X86_64.Instructions

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Minimum of two Float values. -/
def floatMin (a b : Float) : Float := if a < b then a else b

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Maximum of two Float values. -/
def floatMax (a b : Float) : Float := if a > b then a else b

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Clamps a Float percentage to [0.0, 100.0]. -/
def clampPct (v : Float) : Float :=
  floatMin 100.0 (floatMax 0.0 v)

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- TMAM Level-1 Performance Metric Breakdown (Normalized to 100.0% of total pipeline slots). -/
structure TMAMLevel1 where
  frontendBoundPct  : Float
  badSpeculationPct : Float
  backendBoundPct   : Float
  retiringPct       : Float
  deriving Repr, Inhabited

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- TMAM Level-2 Performance Metric Detailed Breakdown. -/
structure TMAMLevel2 where
  fetchLatencyPct          : Float
  fetchBandwidthPct        : Float
  memoryBoundL1DPct        : Float
  memoryBoundL2Pct         : Float
  memoryBoundLLCPct        : Float
  memoryBoundDRAMPct       : Float
  coreBoundPortPressurePct : Float
  coreBoundDividerPct      : Float
  deriving Repr, Inhabited

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Structured report summarizing microarchitectural cycle bounds, uop breakdown, and pipeline performance. -/
structure PerformanceReport where
  profileName       : String
  totalInstructions : Nat
  totalUops         : Nat
  bounds            : PerfCycleBounds
  ipcNominal        : Float
  cpiNominal        : Float
  portPressure      : List (PortId × Float)
  tmamL1            : TMAMLevel1
  tmamL2            : TMAMLevel2
  waterfallTimeline : String
  deriving Repr, Inhabited

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Computes execution port demand in fractional cycles distributed equally across valid active hardware ports for the microarchitecture profile. -/
def computePortPressure (uops : List X86_64Uop) (profile : MicroarchProfile := goldenCoveProfile) : List (PortId × Float) :=
  profile.activePorts.map fun p =>
    let pressure := uops.foldl (fun acc u =>
      let validPorts := u.eligiblePorts.filter (fun ep => profile.activePorts.contains ep)
      if validPorts.contains p then
        let portCount := validPorts.length.toFloat
        acc + (1.0 / floatMax 1.0 portCount)
      else
        acc
    ) 0.0
    (p, pressure)

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Computes min, nominal, and max cycle bounds for a retired micro-op stream. -/
def computeCycleBounds (uops : List X86_64Uop) (profile : MicroarchProfile := goldenCoveProfile) : PerfCycleBounds :=
  if uops.isEmpty then
    { minCycles := 1, nominalCycles := 1, maxCycles := 1 }
  else
    let totalUops := uops.length
    -- 1. Optimistic Minimum Cycles (Peak parallel dispatch width)
    let minCycles := Nat.max 1 ((totalUops + profile.dispatchWidthUops - 1) / profile.dispatchWidthUops)

    -- 2. Port Bottleneck Calculation for Nominal Cycles (Using profile-active distributed port pressure)
    let portPressures := computePortPressure uops profile
    let maxPortPressureFloat := portPressures.foldl (fun acc (_, f) => floatMax acc f) 0.0
    let maxPortCycles := (maxPortPressureFloat.ceil).toUInt64.toNat
    let divLatencyTotal := (uops.filter (fun u => u.uopClass == .intDiv)).foldl (fun acc u => acc + u.latencyCycles) 0
    let nominalCycles := Nat.max minCycles (Nat.max maxPortCycles divLatencyTotal)

    -- 3. Pessimistic Maximum Cycles (Bounded below by nominal dispatch time to account for zeroing idioms, plus serial latency and branch mispredict penalties)
    let serialLatencySum := uops.foldl (fun acc u => acc + u.latencyCycles) 0
    let branchCount := (uops.filter fun u => u.uopClass == .branch).length
    let maxCycles := Nat.max nominalCycles (serialLatencySum + (branchCount * profile.branchMispredictPenalty))

    { minCycles := minCycles, nominalCycles := nominalCycles, maxCycles := maxCycles }

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Computes TMAM Level 1 and Level 2 breakdown percentages from retired uops and cycle bounds. -/
def computeTMAM (uops : List X86_64Uop) (bounds : PerfCycleBounds) (profile : MicroarchProfile := goldenCoveProfile) : Prod TMAMLevel1 TMAMLevel2 :=
  if uops.isEmpty then
    (
      { frontendBoundPct := 0.0, badSpeculationPct := 0.0, backendBoundPct := 0.0, retiringPct := 100.0 },
      { fetchLatencyPct := 0.0, fetchBandwidthPct := 0.0, memoryBoundL1DPct := 0.0, memoryBoundL2Pct := 0.0,
        memoryBoundLLCPct := 0.0, memoryBoundDRAMPct := 0.0, coreBoundPortPressurePct := 0.0, coreBoundDividerPct := 0.0 }
    )
  else
    let totalSlotsNat := bounds.nominalCycles * profile.dispatchWidthUops
    let totalSlots := if totalSlotsNat == 0 then 1.0 else totalSlotsNat.toFloat
    let retiredUopsFloat := uops.length.toFloat

    let divUops := (uops.filter (fun u => u.uopClass == .intDiv)).length.toFloat
    let memUops := (uops.filter (fun u => u.uopClass == .load || u.uopClass == .storeAddr || u.uopClass == .storeData)).length.toFloat
    let branchUops := (uops.filter fun u => u.uopClass == .branch).length.toFloat

    let retiringSlots := floatMin totalSlots retiredUopsFloat
    let retiringPct := clampPct ((retiringSlots / totalSlots) * 100.0)

    let badSpecPct := clampPct (floatMin (100.0 - retiringPct) ((branchUops * 2.0 / totalSlots) * 100.0))
    let feBoundPct := clampPct (floatMin (100.0 - retiringPct - badSpecPct) 15.0)
    let beBoundPct := clampPct (floatMax 0.0 (100.0 - retiringPct - badSpecPct - feBoundPct))

    let tmam1 : TMAMLevel1 := {
      frontendBoundPct  := feBoundPct,
      badSpeculationPct := badSpecPct,
      backendBoundPct   := beBoundPct,
      retiringPct       := retiringPct
    }

    let tmam2 : TMAMLevel2 := {
      fetchLatencyPct          := clampPct (feBoundPct * 0.4),
      fetchBandwidthPct        := clampPct (feBoundPct * 0.6),
      memoryBoundL1DPct        := clampPct ((memUops * 0.5 / totalSlots) * 100.0),
      memoryBoundL2Pct         := clampPct ((memUops * 0.2 / totalSlots) * 100.0),
      memoryBoundLLCPct        := clampPct ((memUops * 0.1 / totalSlots) * 100.0),
      memoryBoundDRAMPct       := clampPct ((memUops * 0.05 / totalSlots) * 100.0),
      coreBoundPortPressurePct := clampPct (beBoundPct * 0.7),
      coreBoundDividerPct      := clampPct ((divUops * 14.0 / totalSlots) * 100.0)
    }

    (tmam1, tmam2)

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Generates structured ASCII Waterfall Timeline visualization of the pipeline stages:
    [F]etch -> [D]ecode -> [R]ename -> [S]chedule/RS -> [E]xecute -> [W]riteback/Retire. -/
def generateWaterfall (uops : List X86_64Uop) (profile : MicroarchProfile := goldenCoveProfile) (maxDisplayUops : Nat := 16) (maxDisplayCycles : Nat := 24) : String := Id.run do
  let mut lines : List String := []
  lines := lines ++ ["--------------------------------------------------------------------------------"]
  lines := lines ++ ["                    GASM X86-64 PIPELINE ASCII WATERFALL                        "]
  lines := lines ++ ["--------------------------------------------------------------------------------"]
  lines := lines ++ ["Uop ID | Mnemonic        | Port | Pipeline Stage Timeline [F|D|R|S|E|W]         "]
  lines := lines ++ ["--------------------------------------------------------------------------------"]

  let displayedUops := uops.take maxDisplayUops
  let decodeWidth := Nat.max 1 profile.decodeWidthUops
  let mut curCyc := 1
  let mut uopIdx := 0

  for u in displayedUops do
    let uidStr := s!"#{uopIdx}".pushn ' ' (7 - s!"#{uopIdx}".length)
    let mnemStr := u.mnemonic.pushn ' ' (16 - u.mnemonic.length)
    let portStr := (match u.eligiblePorts.head? with | some p => p.toString | none => "--").pushn ' ' 6

    let fetchCyc := (uopIdx / decodeWidth) + 1
    let decodeCyc := fetchCyc + 1
    let renameCyc := decodeCyc + 1
    let schedCyc := renameCyc + 1
    let execCyc := schedCyc + 1
    let retireCyc := execCyc + u.latencyCycles

    let mut timeline := ""
    for cyc in [1:maxDisplayCycles + 1] do
      let char :=
        if cyc == retireCyc then 'W'
        else if cyc >= execCyc && cyc < retireCyc then 'E'
        else if cyc == schedCyc then 'S'
        else if cyc == renameCyc then 'R'
        else if cyc == decodeCyc then 'D'
        else if cyc == fetchCyc then 'F'
        else '.'
      timeline := timeline.push char

    lines := lines ++ [s!"{uidStr}| {mnemStr}| {portStr}| {timeline}"]
    uopIdx := uopIdx + 1
    curCyc := retireCyc

  lines := lines ++ ["--------------------------------------------------------------------------------"]
  return String.intercalate "\n" lines

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Comprehensive performance analyzer for x86-64 instruction sequences. -/
def analyzePerformance (instrs : List AnyX86_64Instruction) (profile : MicroarchProfile := goldenCoveProfile) : PerformanceReport :=
  let uops : List X86_64Uop := instrs.flatMap (fun i => X86_64Instruction.toUops i)
  let bounds := computeCycleBounds uops profile
  let (tmam1, tmam2) := computeTMAM uops bounds profile
  let pressures := computePortPressure uops profile
  let waterfall := generateWaterfall uops profile
  let totalUopsFloat := uops.length.toFloat
  let nominalCyclesFloat := bounds.nominalCycles.toFloat
  let ipc := if bounds.nominalCycles == 0 then 0.0 else totalUopsFloat / nominalCyclesFloat
  let cpi := if uops.isEmpty then 0.0 else nominalCyclesFloat / totalUopsFloat

  {
    profileName       := profile.name,
    totalInstructions := instrs.length,
    totalUops         := uops.length,
    bounds            := bounds,
    ipcNominal        := ipc,
    cpiNominal        := cpi,
    portPressure      := pressures,
    tmamL1            := tmam1,
    tmamL2            := tmam2,
    waterfallTimeline := waterfall
  }

end Gasm.Targets.X86_64
