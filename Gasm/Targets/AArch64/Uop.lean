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

import Lean
import Gasm.Core.Types
import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.Addressing

namespace Gasm.Targets.AArch64

/- REF: docs/TARGETS/ARM64.md#1-pipeline-microarchitecture-dual-issue-rules -/
/-- Hardware execution pipeline slot identifiers for the ARM Cortex-A53 dual-issue core.
    Slot 0 (Pipe 0) executes integer ALU, branch, and memory operations.
    Slot 1 (Pipe 1) executes integer ALU, shifted operations, and FP/SIMD/crypto. -/
inductive CortexA53Slot where
  | slot0
  | slot1
  deriving Repr, DecidableEq, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#1-pipeline-microarchitecture-dual-issue-rules -/
/-- Formats a CortexA53Slot to string representation. -/
def CortexA53Slot.toString : CortexA53Slot → String
  | .slot0 => "Slot0"
  | .slot1 => "Slot1"

/- REF: docs/TARGETS/ARM64.md#1-pipeline-microarchitecture-dual-issue-rules -/
instance : ToString CortexA53Slot where
  toString := CortexA53Slot.toString

/- REF: docs/TARGETS/ARM64.md#2-execution-latencies-micro-op-classification -/
/-- Micro-op functional classification for Cortex-A53 execution scheduling and pipeline binding. -/
inductive AArch64UopClass where
  | intALU
  | intShift
  | intMul
  | intDiv
  | load
  | store
  | branch
  | system
  deriving Repr, DecidableEq, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#2-execution-latencies-micro-op-classification -/
/-- Formats an AArch64UopClass to string representation. -/
def AArch64UopClass.toString : AArch64UopClass → String
  | .intALU   => "intALU"
  | .intShift => "intShift"
  | .intMul   => "intMul"
  | .intDiv   => "intDiv"
  | .load     => "load"
  | .store    => "store"
  | .branch   => "branch"
  | .system   => "system"

/- REF: docs/TARGETS/ARM64.md#2-execution-latencies-micro-op-classification -/
instance : ToString AArch64UopClass where
  toString := AArch64UopClass.toString

/- REF: docs/TARGETS/ARM64.md#2-execution-latencies-micro-op-classification -/
/-- Individual retired micro-op descriptor representing low-level Cortex-A53 hardware execution. -/
structure AArch64Uop where
  mnemonic             : String := "NOP"
  uopClass             : AArch64UopClass := .intALU
  eligibleSlots        : List CortexA53Slot := [.slot0, .slot1]
  latencyCycles        : Nat := 1
  reciprocalThroughput : Float := 0.5
  srcRegs              : List Reg64 := []
  dstRegs              : List Reg64 := []
  isLoad               : Bool := false
  isStore              : Bool := false
  isBranch             : Bool := false
  deriving Repr, Inhabited

/- REF: docs/TARGETS/ARM64.md#3-mandatory-validation-obligations-cost-provenance-laws-13-14 -/
/-- Which named validation oracle has verified this instruction instance. -/
inductive AArch64ValidationOracle where
  | silicon
  | llvmMcEncoding (reason : String)
  | optedOut       (reason : String)
  deriving Repr, DecidableEq, Inhabited

/- REF: docs/TARGETS/ARM64.md#3-mandatory-validation-obligations-cost-provenance-laws-13-14 -/
/-- Origin and calibration provenance of micro-op cost coefficients. -/
inductive CoefficientProvenance where
  | cited (artifact : String)
  | modelInternalUnvalidated (reason : String)
  deriving Repr, DecidableEq, Inhabited

/- REF: docs/TARGETS/ARM64.md#1-pipeline-microarchitecture-dual-issue-rules -/
/-- Microarchitectural hardware profile defining core execution capacities and pipeline parameters. -/
structure CortexA53Profile where
  name                    : String := "ARM Cortex-A53"
  pipelineStages          : Nat := 8
  fetchWidth              : Nat := 2
  decodeWidth             : Nat := 2
  issueWidth              : Nat := 2
  retireWidth             : Nat := 2
  branchMispredictPenalty : Nat := 8
  loadToUseStallCycles    : Nat := 2
  deriving Repr, Inhabited

/- REF: docs/TARGETS/ARM64.md#1-pipeline-microarchitecture-dual-issue-rules -/
/-- Canonical ARM Cortex-A53 hardware profile. -/
def cortexA53Profile : CortexA53Profile := {}

/- REF: docs/TARGETS/ARM64.md#cortex-a53-performance-model-validation-obligations -/
/-- Structured execution cycle bounds representing optimistic best-case, nominal, and pessimistic bounds. -/
structure PerfCycleBounds where
  minCycles     : Nat
  nominalCycles : Nat
  maxCycles     : Nat
  deriving Repr, DecidableEq, Inhabited

end Gasm.Targets.AArch64
