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

namespace Gasm.Targets.X86_64

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Hardware execution port identifiers for modern superscalar x86 cores. -/
inductive PortId where
  | p0 | p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11
  deriving Repr, DecidableEq, Inhabited

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Formats a PortId to standard string. -/
def PortId.toString : PortId -> String
  | .p0 => "P0" | .p1 => "P1" | .p2 => "P2" | .p3 => "P3"
  | .p4 => "P4" | .p5 => "P5" | .p6 => "P6" | .p7 => "P7"
  | .p8 => "P8" | .p9 => "P9" | .p10 => "P10" | .p11 => "P11"

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment;pp=67-90;mp=Vol._1_3-1_to_3-24_Vol._1 -/
instance : ToString PortId where
  toString := PortId.toString

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Micro-op functional classification for execution scheduling and port binding. -/
inductive UopClass where
  | intALU
  | intMul
  | intDiv
  | vecALU
  | vecMul
  | vecFMA
  | load
  | storeAddr
  | storeData
  | branch
  | serializing
  deriving Repr, DecidableEq, Inhabited

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Microarchitectural dynamic optimization mode (Optimistic peak vs Nominal vs Pessimistic bound). -/
inductive OptimizationMode where
  | optimistic   -- Move elimination, zeroing idioms, peak port dispatch
  | nominal      -- Typical superscalar Out-of-Order execution
  | pessimistic  -- Conservative decode/dispatch and non-eliminated moves
  deriving Repr, DecidableEq, Inhabited

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Individual retired micro-op descriptor representing low-level hardware execution. -/
structure X86_64Uop where
  mnemonic             : String := "NOP"
  uopClass             : UopClass := .intALU
  eligiblePorts        : List PortId := [.p0, .p1, .p5, .p6]
  latencyCycles        : Nat := 1
  reciprocalThroughput : Float := 0.25
  deriving Repr, Inhabited

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Microarchitectural hardware profile defining core execution capacities and pipeline widths. -/
structure MicroarchProfile where
  name                    : String := "Intel Golden Cove"
  optMode                 : OptimizationMode := .nominal
  fetchBandwidthBytes     : Nat := 32
  decodeWidthUops         : Nat := 6
  renameWidthUops         : Nat := 6
  dispatchWidthUops       : Nat := 6
  retireWidthUops         : Nat := 8
  robCapacityUops         : Nat := 512
  branchMispredictPenalty : Nat := 16
  activePorts             : List PortId := [.p0, .p1, .p2, .p3, .p4, .p5, .p6, .p7, .p8, .p9, .p10, .p11]
  deriving Repr, Inhabited

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Canonical Intel Golden Cove (Alder Lake / Raptor Lake P-Core) hardware profile. -/
def goldenCoveProfile : MicroarchProfile := {
  name                    := "Intel Golden Cove",
  optMode                 := .nominal,
  fetchBandwidthBytes     := 32,
  decodeWidthUops         := 6,
  renameWidthUops         := 6,
  dispatchWidthUops       := 6,
  retireWidthUops         := 8,
  robCapacityUops         := 512,
  branchMispredictPenalty := 16,
  activePorts             := [.p0, .p1, .p2, .p3, .p4, .p5, .p6, .p7, .p8, .p9, .p10, .p11]
}

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Canonical Intel Skylake hardware profile. -/
def skylakeProfile : MicroarchProfile := {
  name                    := "Intel Skylake",
  optMode                 := .nominal,
  fetchBandwidthBytes     := 16,
  decodeWidthUops         := 4,
  renameWidthUops         := 4,
  dispatchWidthUops       := 4,
  retireWidthUops         := 4,
  robCapacityUops         := 224,
  branchMispredictPenalty := 14,
  activePorts             := [.p0, .p1, .p2, .p3, .p4, .p5, .p6, .p7]
}

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Canonical AMD Zen 4 hardware profile. -/
def zen4Profile : MicroarchProfile := {
  name                    := "AMD Zen 4",
  optMode                 := .nominal,
  fetchBandwidthBytes     := 32,
  decodeWidthUops         := 6,
  renameWidthUops         := 6,
  dispatchWidthUops       := 6,
  retireWidthUops         := 8,
  robCapacityUops         := 320,
  branchMispredictPenalty := 14,
  activePorts             := [.p0, .p1, .p2, .p3, .p4, .p5]
}

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Ideal 1-cycle execution profile for formal deductive performance bounds. -/
def idealProfile : MicroarchProfile := {
  name                    := "Ideal 1-Cycle Profile",
  optMode                 := .optimistic,
  fetchBandwidthBytes     := 64,
  decodeWidthUops         := 64,
  renameWidthUops         := 64,
  dispatchWidthUops       := 64,
  retireWidthUops         := 64,
  robCapacityUops         := 4096,
  branchMispredictPenalty := 0,
  activePorts             := [.p0, .p1, .p2, .p3, .p4, .p5, .p6, .p7, .p8, .p9, .p10, .p11]
}

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Structured execution cycle bounds representing optimistic best-case, nominal, and pessimistic bounds. -/
structure PerfCycleBounds where
  minCycles     : Nat
  nominalCycles : Nat
  maxCycles     : Nat
  deriving Repr, DecidableEq, Inhabited

end Gasm.Targets.X86_64
