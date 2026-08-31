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

import Gasm.Targets.X86_64.Decoder

namespace Gasm.Targets.X86_64.HardwareMemoryPlan

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Bytes captured on each side of the scratch payload.  These are real writable canaries in the
    emitted image, not a claim inferred from the declared access footprint. -/
def guardBytes : Nat := 16

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Scratch bytes whose complete preimage and postimage are compared. -/
def payloadBytes : Nat := 64

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Complete captured region: leading canary, payload, and trailing canary. -/
def regionBytes : Nat := guardBytes + payloadBytes + guardBytes

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- The first admitted memory operation is placed away from both payload boundaries. -/
def accessOffset : Nat := 24

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Closed initial admission list for scratch-memory differential validation.  This is deliberately
    not inferred from descriptor count: adding another instruction family requires adding a
    constructor and reviewing its straight-line/non-stack/non-atomic operational semantics. -/
inductive ScratchMov where
  | mem8Reg8 (instr : MovMem8Reg8)
  | mem64DispReg64 (instr : MovMem64DispReg64)
  | mem64DispImm32 (instr : MovMem64DispImm32)
  | reg64Mem64Disp (instr : MovReg64Mem64Disp)
  deriving Inhabited

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Coverage identity for every constructor in the closed initial memory-form admission list. -/
inductive ScratchClass where
  | mem8Reg8 | mem64DispReg64 | mem64DispImm32 | reg64Mem64Disp
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Complete finite inventory of the initial admitted classes. -/
def ScratchClass.all : List ScratchClass :=
  [.mem8Reg8, .mem64DispReg64, .mem64DispImm32, .reg64Mem64Disp]

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Classifies a closed request for nonvacuous coverage accounting. -/
def ScratchMov.scratchClass : ScratchMov → ScratchClass
  | .mem8Reg8 _ => .mem8Reg8
  | .mem64DispReg64 _ => .mem64DispReg64
  | .mem64DispImm32 _ => .mem64DispImm32
  | .reg64Mem64Disp _ => .reg64Mem64Disp

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- The exact production instruction whose encoder and step function are authoritative for a
    scratch test. -/
def ScratchMov.pack : ScratchMov → AnyX86_64Instruction
  | .mem8Reg8 i => ⟨i⟩
  | .mem64DispReg64 i => ⟨i⟩
  | .mem64DispImm32 i => ⟨i⟩
  | .reg64Mem64Disp i => ⟨i⟩

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Base register admitted by the closed MOV form. -/
def ScratchMov.baseReg : ScratchMov → Reg64
  | .mem8Reg8 i => i.dstPtr
  | .mem64DispReg64 i => i.basePtr
  | .mem64DispImm32 i => i.basePtr
  | .reg64Mem64Disp i => i.basePtr

private def ScratchMov.hostRegistersSafe : ScratchMov → Bool
  | .mem8Reg8 i => i.dstPtr != .rsp && i.srcReg != .rsp
  | .mem64DispReg64 i => i.basePtr != .rsp && i.srcReg != .rsp
  | .mem64DispImm32 i => i.basePtr != .rsp
  | .reg64Mem64Disp i => i.basePtr != .rsp && i.dstReg != .rsp

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Expected access class of the closed MOV form, independently checked against `memAccesses`. -/
def ScratchMov.expectedKind : ScratchMov → MemAccessKind
  | .mem8Reg8 _ | .mem64DispReg64 _ | .mem64DispImm32 _ => .store
  | .reg64Mem64Disp _ => .load

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Expected width of the closed MOV form, independently checked against `memAccesses`. -/
def ScratchMov.expectedWidth : ScratchMov → MemWidth
  | .mem8Reg8 _ => .w8
  | .mem64DispReg64 _ | .mem64DispImm32 _ | .reg64Mem64Disp _ => .w64

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- True exactly for canonical 48-bit x86-64 virtual addresses.  The first hardware-memory slice
    admits no address-size or segment override and therefore checks the computed 64-bit EA. -/
def isCanonical48 (addr : UInt64) : Bool :=
  let high := addr >>> 48
  if ((addr >>> 47) &&& 1) == 0 then high == 0 else high == 0xffff

private def maxAddress : UInt64 := 0xffffffffffffffff

private def checkedAdd (base : UInt64) (delta : Nat) : Except String UInt64 :=
  let d := delta.toUInt64
  if base > maxAddress - d then
    .error s!"address addition wraps: {base} + {delta}"
  else
    .ok (base + d)

private def checkedBaseFor (target disp : UInt64) : Except String UInt64 :=
  if ((disp >>> 63) &&& 1) == 0 then
    if target < disp then
      .error s!"positive displacement underflows rebased address: target={target}, disp={disp}"
    else
      .ok (target - disp)
  else
    let magnitude := 0 - disp
    if target > maxAddress - magnitude then
      .error s!"negative displacement overflows rebased address: target={target}, disp={disp}"
    else
      .ok (target + magnitude)

private def patternedRegion (caseId : UInt64) : ByteArray :=
  ByteArray.mk <| ((List.range regionBytes).map (fun i =>
    ((caseId + (i * 37).toUInt64 + 0x5b) &&& 0xff).toUInt8)).toArray

private structure DecodedSummary where
  accesses : List MemAccessSpec
  leanSource : String

private def decodeSummary (bytes : ByteArray) : Except String DecodedSummary :=
  match decodeX86_64Instr bytes 0 with
  | .error msg => .error s!"production bytes failed to decode: {msg}"
  | .ok (decoded, consumed) =>
      if consumed != bytes.size then
        .error s!"production decoder consumed {consumed}/{bytes.size} instruction bytes"
      else if X86_64Instruction.encode decoded != bytes then
        .error "decoded production instruction did not re-encode to the exact native bytes"
      else
        .ok { accesses := X86_64Instruction.memAccesses decoded,
              leanSource := X86_64Instruction.toLean decoded }

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- One fully checked scratch execution plan.  `initialState`, `instructionBytes`, and
    `form.pack` are a single authority bundle: native execution consumes the stored bytes and
    model execution consumes the same production package.  The effective address was evaluated
    from this exact pre-state and is never reconstructed from a post-state register value. -/
structure Plan where
  caseId : UInt64
  form : ScratchMov
  instructionBytes : ByteArray
  initialState : X86_64MachineState
  regionBase : UInt64
  payloadBase : UInt64
  accessAddress : UInt64
  accessKind : MemAccessKind
  accessWidth : MemWidth
  regionBefore : ByteArray
  deriving Inhabited

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Exact result of decoding and stepping the bytes the native runner executes. -/
structure DecodedStep where
  state : X86_64MachineState
  undefinedFlagsMask : UInt64
  accesses : List MemAccessSpec

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Decodes and steps the exact stored production bytes.  This is the model authority used by the
    differential comparator; it never reconstructs an instruction independently of those bytes. -/
def Plan.decodeAndStep (plan : Plan) : Except String DecodedStep :=
  match decodeX86_64Instr plan.instructionBytes 0 with
  | .error msg => .error s!"case {plan.caseId}: production bytes failed to decode: {msg}"
  | .ok (decoded, consumed) =>
      if consumed != plan.instructionBytes.size then
        .error s!"case {plan.caseId}: decoder consumed {consumed}/{plan.instructionBytes.size} bytes"
      else if X86_64Instruction.encode decoded != plan.instructionBytes then
        .error s!"case {plan.caseId}: decoded instruction did not re-encode exactly"
      else
        .ok {
          state := X86_64Instruction.step decoded plan.initialState
          undefinedFlagsMask := X86_64Instruction.undefinedFlagsMask decoded
          accesses := X86_64Instruction.memAccesses decoded
        }

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Reads the entire guarded scratch region from model memory. -/
def readRegion (regionBase : UInt64) (memory : X86_64Memory) : ByteArray :=
  ByteArray.mk <| ((List.range regionBytes).map (fun i =>
    X86_64Mem.readByte memory (regionBase + i.toUInt64))).toArray

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Model postimage corresponding to the exact decoded bytes of a checked plan. -/
def Plan.modelRegionAfter (plan : Plan) : Except String ByteArray := do
  let decoded ← plan.decodeAndStep
  pure <| readRegion plan.regionBase decoded.state.memory

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Builds a checked address-identity plan for one closed MOV form.

    Rejection is fail-closed.  The production descriptor must be exactly one base-only access and
    must agree with the constructor's independently stated kind/width/base.  RSP, indexed,
    RIP-relative, implicit-memory, multi-access, address-size/segment-override and atomic forms
    have no constructor here.  The guarded region and target access must be nonwrapping and
    canonical, and the descriptor must evaluate to the chosen payload address in the exact
    pre-state installed in model memory. -/
def prepare (caseId : UInt64) (form : ScratchMov) (seed : X86_64MachineState)
    (regionBase : UInt64) : Except String Plan := do
  if !form.hostRegistersSafe then
    throw "RSP base/source/destination operands are excluded from the initial scratch-memory validator"
  let regionEnd ← checkedAdd regionBase regionBytes
  if !isCanonical48 regionBase || !isCanonical48 (regionEnd - 1) then
    throw "guarded scratch region is not wholly canonical"
  let payloadBase ← checkedAdd regionBase guardBytes
  let accessAddress ← checkedAdd payloadBase accessOffset
  let instruction := form.pack
  let instructionBytes := X86_64Instruction.encode instruction
  let decoded ← decodeSummary instructionBytes
  if decoded.leanSource != X86_64Instruction.toLean instruction then
    throw "decoded production instruction disagrees with the closed MOV constructor"
  let specE : Except String MemAccessSpec := match decoded.accesses with
    | [spec] => .ok spec
    | specs => throw s!"closed scratch MOV must expose exactly one production access descriptor, got {specs.length}"
  let spec : MemAccessSpec ← specE
  if spec.kind != form.expectedKind then
    throw "production descriptor kind disagrees with the closed MOV form"
  if spec.width != form.expectedWidth then
    throw "production descriptor width disagrees with the closed MOV form"
  if spec.ref.base != some form.baseReg then
    throw "production descriptor base disagrees with the closed MOV form"
  if spec.ref.index.isSome then
    throw "indexed memory operands are excluded from the initial scratch-memory validator"
  if accessOffset + spec.width.bytes > payloadBytes then
    throw "declared access does not fit wholly inside the scratch payload"
  let baseValue ← checkedBaseFor accessAddress spec.ref.disp
  let regionBefore := patternedRegion caseId
  if regionBefore.size != regionBytes then
    throw "internal scratch preimage length mismatch"
  let memory := X86_64Mem.writeBytes regionBase regionBefore.data.toList seed.memory
  let initialState := (seed.setGpr64 form.baseReg baseValue)
  let initialState := { initialState with memory := memory }
  if spec.ref.effectiveAddress initialState != accessAddress then
    throw "production descriptor does not evaluate to the checked native scratch address"
  if !isCanonical48 accessAddress then
    throw "computed memory access is not canonical"
  pure {
    caseId := caseId
    form := form
    instructionBytes := instructionBytes
    initialState := initialState
    regionBase := regionBase
    payloadBase := payloadBase
    accessAddress := accessAddress
    accessKind := spec.kind
    accessWidth := spec.width
    regionBefore := regionBefore
  }

end Gasm.Targets.X86_64.HardwareMemoryPlan
