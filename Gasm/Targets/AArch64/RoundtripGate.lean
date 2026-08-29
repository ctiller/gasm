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
import Gasm.Targets.AArch64.Decoder
import Gasm.Targets.AArch64.Roundtrip

namespace Gasm.Targets.AArch64

open Gasm.Core
open Gasm.Targets.AArch64.Instructions

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Verification predicate: decoding the encoded instruction recovers the original instruction,
    and re-encoding the decoded instruction matches the original encoding bit-for-bit. -/
def decodesOk (tryDecode : UInt32 → Option AnyAArch64Instruction) (i : AnyAArch64Instruction) : Bool :=
  let encoded := encodeWord i
  match tryDecode encoded with
  | none => false
  | some decoded =>
    (encodeWord decoded == encoded) &&
    (AArch64Instruction.toAssembly decoded == AArch64Instruction.toAssembly i)

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- In-bucket exclusivity: no two instruction cases in a verified round-trip gate collide ambiguously in encoding. -/
theorem inBucketExclusiveOf {cases : List AnyAArch64Instruction}
    (h : cases.all (decodesOk decodeWord) = true) :
    ∀ i ∈ cases, ∀ j ∈ cases,
      encodeWord i = encodeWord j →
      AArch64Instruction.toAssembly i = AArch64Instruction.toAssembly j := by
  intro i hi j hj heq
  have hi' : decodesOk decodeWord i = true := (List.all_eq_true.mp h) i hi
  have hj' : decodesOk decodeWord j = true := (List.all_eq_true.mp h) j hj
  simp only [decodesOk, heq] at hi' hj'
  cases hcase : decodeWord (encodeWord j) with
  | none =>
    rw [hcase] at hi'
    contradiction
  | some decoded =>
    rw [hcase] at hi' hj'
    simp only [Bool.and_eq_true, beq_iff_eq] at hi' hj'
    rw [← hi'.2, hj'.2]

-- ============================================================================
-- Representative Test Witness Collections per Family
-- ============================================================================

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
def addFamilyCases : List AnyAArch64Instruction :=
  Gasm.Targets.AArch64.Instructions.addFamilyCases

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
def subFamilyCases : List AnyAArch64Instruction :=
  Gasm.Targets.AArch64.Instructions.subFamilyCases

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
def logicalFamilyCases : List AnyAArch64Instruction :=
  Gasm.Targets.AArch64.Instructions.logicalFamilyCases ++
  (AArch64Instruction.roundtripCases (ι := MovReg)).map AnyAArch64Instruction.mk

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
def moveWideFamilyCases : List AnyAArch64Instruction :=
  Gasm.Targets.AArch64.Instructions.moveWideFamilyCases

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
def loadStoreImmFamilyCases : List AnyAArch64Instruction :=
  Gasm.Targets.AArch64.Instructions.loadStoreImmFamilyCases

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
def loadStorePairFamilyCases : List AnyAArch64Instruction :=
  Gasm.Targets.AArch64.Instructions.loadStorePairFamilyCases

/- REF: docs/TARGETS/ARM64.md#11-branchimm-family -/
def branchFamilyCases : List AnyAArch64Instruction :=
  Gasm.Targets.AArch64.Instructions.branchFamilyCases

/- REF: docs/TARGETS/ARM64.md#15-system-family -/
def systemFamilyCases : List AnyAArch64Instruction :=
  Gasm.Targets.AArch64.Instructions.systemFamilyCases

/- REF: docs/TARGETS/ARM64.md#14-adr-family -/
def adrFamilyCases : List AnyAArch64Instruction :=
  Gasm.Targets.AArch64.Instructions.adrFamilyCases

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Exhaustive collection of representative AArch64 instruction test cases covering all 15 families. -/
def allAArch64Cases : List AnyAArch64Instruction :=
  addFamilyCases ++ subFamilyCases ++ logicalFamilyCases ++ moveWideFamilyCases ++
  loadStoreImmFamilyCases ++ loadStorePairFamilyCases ++ branchFamilyCases ++
  systemFamilyCases ++ adrFamilyCases

-- ============================================================================
-- Gate Verification Theorems (Pure Constructive Kernel Axioms)
-- ============================================================================

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
theorem addFamily_roundtripGate : addFamilyCases.all (decodesOk decodeWord) = true := by decide

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
theorem subFamily_roundtripGate : subFamilyCases.all (decodesOk decodeWord) = true := by decide

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
theorem logicalFamily_roundtripGate : logicalFamilyCases.all (decodesOk decodeWord) = true := by decide

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
theorem moveWideFamily_roundtripGate : moveWideFamilyCases.all (decodesOk decodeWord) = true := by decide

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
theorem loadStoreImmFamily_roundtripGate : loadStoreImmFamilyCases.all (decodesOk decodeWord) = true := by decide

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
theorem loadStorePairFamily_roundtripGate : loadStorePairFamilyCases.all (decodesOk decodeWord) = true := by decide

/- REF: docs/TARGETS/ARM64.md#11-branchimm-family -/
theorem branchFamily_roundtripGate : branchFamilyCases.all (decodesOk decodeWord) = true := by decide

/- REF: docs/TARGETS/ARM64.md#15-system-family -/
theorem systemFamily_roundtripGate : systemFamilyCases.all (decodesOk decodeWord) = true := by decide

/- REF: docs/TARGETS/ARM64.md#14-adr-family -/
theorem adrFamily_roundtripGate : adrFamilyCases.all (decodesOk decodeWord) = true := by decide

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Universal round-trip gate theorem: 100% of registered instruction cases decode back to themselves. -/
theorem aarch64_roundtripGate : allAArch64Cases.all (decodesOk decodeWord) = true := by decide

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Derived in-bucket exclusivity: no two instruction test cases collide into identical 32-bit encodings. -/
theorem aarch64_inBucketExclusive :
    ∀ i ∈ allAArch64Cases, ∀ j ∈ allAArch64Cases,
      encodeWord i = encodeWord j →
      AArch64Instruction.toAssembly i = AArch64Instruction.toAssembly j :=
  inBucketExclusiveOf aarch64_roundtripGate

end Gasm.Targets.AArch64
