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
import Gasm.Targets.X86_64.MemoryRange

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
/-- Fixed exact-identity frame carried unchanged through the native result record.  The frame
    stores a length-delimited canonical plan/pre-state payload followed by checked zero padding;
    it is not a digest and therefore introduces no collision assumption. -/
def planIdentityBytes : Nat := 512

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- The first admitted memory operation is placed away from both payload boundaries. -/
def accessOffset : Nat := 24

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Closed initial family inventory for supplemental scratch-memory differential evidence. This is
    not `ValidationOracle.silicon` and grants no registry, capability, or execution admission. -/
inductive ScratchClass where
  | mem8Reg8 | mem64DispReg64 | mem64DispImm32 | reg64Mem64Disp | movzxR64Mem8
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Complete finite inventory of the initial admitted classes. -/
def ScratchClass.all : List ScratchClass :=
  [.mem8Reg8, .mem64DispReg64, .mem64DispImm32, .reg64Mem64Disp, .movzxR64Mem8]

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- The inventory is exhaustive over the actual closed class type. -/
theorem ScratchClass.mem_all (cls : ScratchClass) : cls ∈ ScratchClass.all := by
  cases cls <;> simp [ScratchClass.all]

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Each admitted class selects exactly one production instruction family. Adding support requires
    a new class and therefore breaks every exhaustive match and the native coverage control. -/
def ScratchClass.Instruction : ScratchClass → Type
  | .mem8Reg8 => MovMem8Reg8
  | .mem64DispReg64 => MovMem64DispReg64
  | .mem64DispImm32 => MovMem64DispImm32
  | .reg64Mem64Disp => MovReg64Mem64Disp
  | .movzxR64Mem8 => MovzxR64Mem8

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- One family-indexed supplemental request. The class is stored, not reconstructed by a
    many-to-one classifier, so a distinct admitted family cannot hide under an existing class. -/
structure ScratchMov where
  scratchClass : ScratchClass
  instr : scratchClass.Instruction

namespace ScratchMov

def mem8Reg8 (instr : MovMem8Reg8) : ScratchMov := ⟨.mem8Reg8, instr⟩
def mem64DispReg64 (instr : MovMem64DispReg64) : ScratchMov := ⟨.mem64DispReg64, instr⟩
def mem64DispImm32 (instr : MovMem64DispImm32) : ScratchMov := ⟨.mem64DispImm32, instr⟩
def reg64Mem64Disp (instr : MovReg64Mem64Disp) : ScratchMov := ⟨.reg64Mem64Disp, instr⟩
def movzxR64Mem8 (instr : MovzxR64Mem8) : ScratchMov := ⟨.movzxR64Mem8, instr⟩

instance : Inhabited ScratchMov := ⟨mem8Reg8 default⟩

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- The exact production instruction whose encoder and step function are authoritative for a
    scratch test. -/
private def packFor : (cls : ScratchClass) → cls.Instruction → AnyX86_64Instruction
  | .mem8Reg8, i => ⟨(show MovMem8Reg8 from i)⟩
  | .mem64DispReg64, i => ⟨(show MovMem64DispReg64 from i)⟩
  | .mem64DispImm32, i => ⟨(show MovMem64DispImm32 from i)⟩
  | .reg64Mem64Disp, i => ⟨(show MovReg64Mem64Disp from i)⟩
  | .movzxR64Mem8, i => ⟨(show MovzxR64Mem8 from i)⟩

def pack (form : ScratchMov) : AnyX86_64Instruction :=
  packFor form.scratchClass form.instr

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Base register admitted by the closed MOV form. -/
private def baseRegFor : (cls : ScratchClass) → cls.Instruction → Reg64
  | .mem8Reg8, i => i.dstPtr
  | .mem64DispReg64, i => i.basePtr
  | .mem64DispImm32, i => i.basePtr
  | .reg64Mem64Disp, i => i.basePtr
  | .movzxR64Mem8, i => i.basePtr

def baseReg (form : ScratchMov) : Reg64 :=
  baseRegFor form.scratchClass form.instr

private def hostRegistersSafeFor : (cls : ScratchClass) → cls.Instruction → Bool
  | .mem8Reg8, i => i.dstPtr != .rsp && i.srcReg != .rsp
  | .mem64DispReg64, i => i.basePtr != .rsp && i.srcReg != .rsp
  | .mem64DispImm32, i => i.basePtr != .rsp
  | .reg64Mem64Disp, i => i.basePtr != .rsp && i.dstReg != .rsp
  | .movzxR64Mem8, i => i.basePtr != .rsp && i.dstReg != .rsp

private def hostRegistersSafe (form : ScratchMov) : Bool :=
  hostRegistersSafeFor form.scratchClass form.instr

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Expected access class of the closed MOV form, independently checked against `memAccesses`. -/
private def expectedKindFor : (cls : ScratchClass) → cls.Instruction → MemAccessKind
  | .mem8Reg8, _ | .mem64DispReg64, _ | .mem64DispImm32, _ => .store
  | .reg64Mem64Disp, _ | .movzxR64Mem8, _ => .load

def expectedKind (form : ScratchMov) : MemAccessKind :=
  expectedKindFor form.scratchClass form.instr

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Expected width of the closed MOV form, independently checked against `memAccesses`. -/
private def expectedWidthFor : (cls : ScratchClass) → cls.Instruction → MemWidth
  | .mem8Reg8, _ => .w8
  | .mem64DispReg64, _ | .mem64DispImm32, _ | .reg64Mem64Disp, _ => .w64
  | .movzxR64Mem8, _ => .w8

def expectedWidth (form : ScratchMov) : MemWidth :=
  expectedWidthFor form.scratchClass form.instr

end ScratchMov

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
  ByteArray.mk <| ((List.range regionBytes).map (fun (i : Nat) =>
    let caseByte := (caseId >>> ((i % 8) * 8).toUInt64).toUInt8
    let positionByte := (((i * 37).toUInt64 + 0x5b) &&& 0xff).toUInt8
    caseByte ^^^ positionByte)).toArray

private def everyCaseIdBitAffectsPattern : Bool :=
  (List.range 64).all fun bit =>
    patternedRegion 0 != patternedRegion ((1 : UInt64) <<< bit.toUInt64)

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Every bit of the public 64-bit case identity changes its independently generated preimage.
#guard everyCaseIdBitAffectsPattern

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
  planIdentity : ByteArray
  deriving Inhabited

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Exact result of decoding and stepping the bytes the native runner executes. -/
structure DecodedStep where
  state : X86_64MachineState
  undefinedFlagsMask : UInt64
  accesses : List MemAccessSpec

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Reads the entire guarded scratch region from model memory. -/
def readRegion (regionBase : UInt64) (memory : X86_64Memory) : ByteArray :=
  ByteArray.mk <| ((List.range regionBytes).map (fun i =>
    X86_64Mem.readByte memory (regionBase + i.toUInt64))).toArray

private def encodeSizedBytes (bytes : ByteArray) : ByteArray :=
  uint64ToLittleEndian bytes.size.toUInt64 ++ bytes

private def identityRegs : List Reg64 :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
   .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

private def accessKindTag : MemAccessKind → UInt8
  | .load => 0
  | .store => 1

private def accessWidthTag : MemWidth → UInt8
  | .w8 => 0
  | .w16 => 1
  | .w32 => 2
  | .w64 => 3

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Canonical, collision-free serialization of every owner-selected input that can distinguish
    one guarded execution plan: closed form, production bytes, all initial registers/RIP/flags,
    external byte inputs, guarded memory preimage and geometry, descriptor kind, and width.

    Memory outside the guarded region is deliberately absent: the admitted production descriptor
    has exactly one wholly-contained access, and `validateDecodedAccess` independently checks that
    the exact model preimage in that region agrees. -/
private def Plan.identityPayload (plan : Plan) : ByteArray := Id.run do
  let mut bytes := uint64ToLittleEndian plan.caseId
  bytes := bytes ++ encodeSizedBytes plan.instructionBytes
  bytes := bytes ++ encodeSizedBytes (X86_64Instruction.toLean plan.form.pack).toUTF8
  bytes := bytes ++ uint64ToLittleEndian plan.initialState.rip
  for reg in identityRegs do
    bytes := bytes ++ uint64ToLittleEndian (plan.initialState.gprs reg)
  bytes := bytes ++ uint64ToLittleEndian plan.initialState.flags
  bytes := bytes ++ encodeSizedBytes plan.initialState.stdinBuffer
  bytes := bytes ++ uint64ToLittleEndian plan.initialState.incomingRequests.length.toUInt64
  for request in plan.initialState.incomingRequests do
    bytes := bytes ++ encodeSizedBytes request
  bytes := bytes ++ uint64ToLittleEndian plan.regionBase
  bytes := bytes ++ uint64ToLittleEndian plan.payloadBase
  bytes := bytes ++ uint64ToLittleEndian plan.accessAddress
  bytes := bytes.push (accessKindTag plan.accessKind)
  bytes := bytes.push (accessWidthTag plan.accessWidth)
  bytes ++ encodeSizedBytes plan.regionBefore

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Recomputes the exact fixed-width identity frame from a plan's owner-selected fields. -/
private def Plan.expectedIdentity (plan : Plan) : Except String ByteArray := do
  let payload := plan.identityPayload
  let encoded := encodeSizedBytes payload
  if encoded.size > planIdentityBytes then
    throw s!"case {plan.caseId}: exact plan identity requires {encoded.size}/{planIdentityBytes} bytes"
  let padding := ByteArray.mk (Array.replicate (planIdentityBytes - encoded.size) (0 : UInt8))
  pure (encoded ++ padding)

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Revalidates the decoded production descriptor against the stored plan and its exact pre-state.
    This check is intentionally owner-local: it hardens the supplemental hardware consumer but
    proves no memory authority, mapping, target fidelity beyond this plan, or execution admission. -/
private def Plan.validateDecodedAccess (plan : Plan) (accesses : List MemAccessSpec) :
    Except String Unit := do
  let expectedIdentity ← plan.expectedIdentity
  if plan.planIdentity != expectedIdentity then
    throw s!"case {plan.caseId}: stored plan identity disagrees with the exact form/bytes/pre-state"
  if !plan.form.hostRegistersSafe then
    throw s!"case {plan.caseId}: decoded closed form uses RSP, which the native harness owns"
  let spec ← match accesses with
    | [spec] => pure spec
    | specs => throw s!"case {plan.caseId}: decoded plan must expose exactly one access, got {specs.length}"
  if spec.kind != plan.accessKind then
    throw s!"case {plan.caseId}: decoded access kind disagrees with the stored plan"
  if spec.width != plan.accessWidth then
    throw s!"case {plan.caseId}: decoded access width disagrees with the stored plan"
  if spec.kind != plan.form.expectedKind then
    throw s!"case {plan.caseId}: decoded access kind disagrees with the independent closed family"
  if spec.width != plan.form.expectedWidth then
    throw s!"case {plan.caseId}: decoded access width disagrees with the independent closed family"
  let actual := spec.addressRange plan.initialState
  let expected : Gasm.MemoryModel.AddressRange :=
    { start := plan.accessAddress, length := plan.accessWidth.bytes }
  if actual != expected then
    throw s!"case {plan.caseId}: decoded access range disagrees with the stored exact pre-state range"
  let regionEnd ← checkedAdd plan.regionBase regionBytes
  let payloadBase ← checkedAdd plan.regionBase guardBytes
  if payloadBase != plan.payloadBase then
    throw s!"case {plan.caseId}: stored payload base disagrees with the guarded region layout"
  let payloadEnd ← checkedAdd payloadBase payloadBytes
  let accessEnd ← checkedAdd actual.start actual.length
  if actual.start < payloadBase || accessEnd > payloadEnd then
    throw s!"case {plan.caseId}: decoded access range is not wholly inside the scratch payload"
  if !isCanonical48 plan.regionBase || !isCanonical48 (regionEnd - 1) ||
      !isCanonical48 actual.start || !isCanonical48 (accessEnd - 1) then
    throw s!"case {plan.caseId}: decoded plan contains a noncanonical guarded or access address"
  if plan.regionBefore.size != regionBytes then
    throw s!"case {plan.caseId}: stored guarded preimage length is not exact"
  if plan.regionBefore != patternedRegion plan.caseId then
    throw s!"case {plan.caseId}: stored guarded preimage disagrees with its independent case pattern"
  if readRegion plan.regionBase plan.initialState.memory != plan.regionBefore then
    throw s!"case {plan.caseId}: exact guarded preimage disagrees with the stored initial memory"

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
      else if X86_64Instruction.encode plan.form.pack != plan.instructionBytes then
        .error s!"case {plan.caseId}: closed MOV form disagrees with the stored production bytes"
      else if X86_64Instruction.toLean decoded != X86_64Instruction.toLean plan.form.pack then
        .error s!"case {plan.caseId}: decoded instruction disagrees with the stored closed MOV form"
      else do
        let accesses := X86_64Instruction.memAccesses decoded
        plan.validateDecodedAccess accesses
        .ok {
          state := X86_64Instruction.step decoded plan.initialState
          undefinedFlagsMask := X86_64Instruction.undefinedFlagsMask decoded
          accesses := accesses
        }

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Model postimage corresponding to the exact decoded bytes of a checked plan. -/
def Plan.modelRegionAfter (plan : Plan) : Except String ByteArray := do
  let decoded ← plan.decodeAndStep
  pure <| readRegion plan.regionBase decoded.state.memory

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Builds a checked address-identity plan for one closed MOV form at a selected payload offset.

    Rejection is fail-closed.  The production descriptor must be exactly one base-only access and
    must agree with the constructor's independently stated kind/width/base.  RSP, indexed,
    RIP-relative, implicit-memory, multi-access, address-size/segment-override and atomic forms
    have no constructor here.  The guarded region and target access must be nonwrapping and
    canonical, and the descriptor must evaluate to the chosen payload address in the exact
    pre-state installed in model memory. The offset parameter exists so the rejection boundary is
    directly testable; ordinary harness requests use `prepare`'s fixed interior offset. -/
def prepareAtOffset (selectedOffset : Nat) (caseId : UInt64) (form : ScratchMov)
    (seed : X86_64MachineState)
    (regionBase : UInt64) : Except String Plan := do
  if !form.hostRegistersSafe then
    throw "RSP base/source/destination operands are excluded from the initial scratch-memory validator"
  if seed.fault.isSome then
    throw "scratch-memory validator requires a nonfaulted initial machine state"
  let regionEnd ← checkedAdd regionBase regionBytes
  if !isCanonical48 regionBase || !isCanonical48 (regionEnd - 1) then
    throw "guarded scratch region is not wholly canonical"
  let payloadBase ← checkedAdd regionBase guardBytes
  let accessAddress ← checkedAdd payloadBase selectedOffset
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
  if selectedOffset + spec.width.bytes > payloadBytes then
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
  let plan : Plan := {
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
    planIdentity := ByteArray.empty
  }
  let planIdentity ← plan.expectedIdentity
  pure { plan with planIdentity := planIdentity }

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Ordinary harness entry: place the access at the single reviewed interior payload offset. -/
def prepare (caseId : UInt64) (form : ScratchMov) (seed : X86_64MachineState)
    (regionBase : UInt64) : Except String Plan :=
  prepareAtOffset accessOffset caseId form seed regionBase

end Gasm.Targets.X86_64.HardwareMemoryPlan
