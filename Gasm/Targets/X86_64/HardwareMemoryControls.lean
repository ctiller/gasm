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

import Gasm.Targets.X86_64.HardwareMemoryProtocol

namespace Gasm.Targets.X86_64.HardwareMemoryControls

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.HardwareMemoryPlan
open Gasm.Targets.X86_64.HardwareMemoryProtocol

private def putU8 (bytes : ByteArray) (offset : Nat) (value : UInt8) : ByteArray :=
  bytes.set! offset value

private def putU32 (bytes : ByteArray) (offset : Nat) (value : UInt32) : ByteArray :=
  let bytes := putU8 bytes offset value.toUInt8
  let bytes := putU8 bytes (offset + 1) (value >>> 8).toUInt8
  let bytes := putU8 bytes (offset + 2) (value >>> 16).toUInt8
  putU8 bytes (offset + 3) (value >>> 24).toUInt8

private def putU64 (bytes : ByteArray) (offset : Nat) (value : UInt64) : ByteArray :=
  let bytes := putU32 bytes offset value.toUInt32
  putU32 bytes (offset + 4) (value >>> 32).toUInt32

private def controlFrame (caseId : UInt64) : ByteArray := Id.run do
  let mut bytes := ByteArray.mk (Array.replicate recordBytes (0 : UInt8))
  bytes := putU64 bytes 0 wireMagic
  bytes := putU32 bytes 8 wireVersion
  bytes := putU32 bytes 12 recordBytes.toUInt32
  bytes := putU64 bytes 16 caseId
  bytes := putU32 bytes 24 regionBytes.toUInt32
  for i in [0:regionBytes] do
    bytes := putU8 bytes (168 + i) ((i * 13 + 7) % 256).toUInt8
  bytes

private def decodedExactly (caseId : UInt64) (bytes : ByteArray) : Bool :=
  match decodeBatch bytes [caseId] with
  | .ok [result] => result.caseId == caseId && result.regionAfter.size == regionBytes
  | _ => false

private def rejected (caseId : UInt64) (bytes : ByteArray) : Bool :=
  match decodeBatch bytes [caseId] with
  | .error _ => true
  | .ok _ => false

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Positive framing control: an exactly sized, correctly identified record is accepted.
#guard decodedExactly 17 (controlFrame 17)

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Negative framing control: a short record is rejected rather than default-filled.
#guard rejected 17 ((controlFrame 17).extract 0 (recordBytes - 1))

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Negative framing control: trailing bytes are rejected rather than ignored.
#guard rejected 17 ((controlFrame 17).push 0)

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Negative framing control: positional case identity prevents swapped/replayed records.
#guard rejected 18 (controlFrame 17)

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Negative framing control: unknown reserved framing data is rejected.
#guard rejected 17 (putU8 (controlFrame 17) 29 1)

private def planAccepted : Bool :=
  let seed := (default : X86_64MachineState).setGpr64 .rbx 0xfeedface
  match prepare 3 (.reg64Mem64Disp ⟨.rax, .rax, 0⟩) seed 0x140004000 with
  | .ok plan =>
      plan.accessAddress == 0x140004028 &&
      plan.initialState.gprs .rax == 0x140004028 &&
      plan.regionBefore.size == regionBytes &&
      plan.instructionBytes == X86_64Instruction.encode plan.form.pack
  | .error _ => false

private def rspRejected : Bool :=
  match prepare 4 (.mem8Reg8 ⟨.rsp, .rax⟩) default 0x140004000 with
  | .error _ => true
  | .ok _ => false

private def noncanonicalRejected : Bool :=
  match prepare 5 (.mem8Reg8 ⟨.rax, .rbx⟩) default 0x0000800000000000 with
  | .error _ => true
  | .ok _ => false

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Positive address-identity control, including the alias-sensitive load where destination and
-- base are the same register: the checked address is fixed from the pre-state.
#guard planAccepted

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Negative eligibility control: stack-addressed forms cannot enter the initial validator.
#guard rspRejected

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Negative address control: a noncanonical scratch mapping is rejected.
#guard noncanonicalRejected

end Gasm.Targets.X86_64.HardwareMemoryControls
