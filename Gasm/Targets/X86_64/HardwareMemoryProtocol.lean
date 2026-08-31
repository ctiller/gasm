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

import Gasm.Targets.X86_64.HardwareHarness
import Gasm.Targets.X86_64.HardwareMemoryPlan

namespace Gasm.Targets.X86_64.HardwareMemoryProtocol

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.HardwareHarness
open Gasm.Targets.X86_64.HardwareMemoryPlan

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Little-endian wire magic for scratch-memory hardware result records (`GASMHMM1`). -/
def wireMagic : UInt64 := 0x314d4d484d534147

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Version of the scratch-memory result framing contract. -/
def wireVersion : UInt32 := 2

def planIdentityOffset : Nat := 32

def registerResultOffset : Reg64 → Nat
  | .rax => planIdentityOffset + planIdentityBytes
  | .rcx => planIdentityOffset + planIdentityBytes + 8
  | .rdx => planIdentityOffset + planIdentityBytes + 16
  | .rbx => planIdentityOffset + planIdentityBytes + 24
  | .rsp => planIdentityOffset + planIdentityBytes + 32
  | .rbp => planIdentityOffset + planIdentityBytes + 40
  | .rsi => planIdentityOffset + planIdentityBytes + 48
  | .rdi => planIdentityOffset + planIdentityBytes + 56
  | .r8 => planIdentityOffset + planIdentityBytes + 64
  | .r9 => planIdentityOffset + planIdentityBytes + 72
  | .r10 => planIdentityOffset + planIdentityBytes + 80
  | .r11 => planIdentityOffset + planIdentityBytes + 88
  | .r12 => planIdentityOffset + planIdentityBytes + 96
  | .r13 => planIdentityOffset + planIdentityBytes + 104
  | .r14 => planIdentityOffset + planIdentityBytes + 112
  | .r15 => planIdentityOffset + planIdentityBytes + 120

def flagsResultOffset : Nat := planIdentityOffset + planIdentityBytes + 128
def regionResultOffset : Nat := flagsResultOffset + 8

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Fixed record size: framing header, exact plan identity, sixteen GPRs, flags, and the complete
    guarded region. -/
def recordBytes : Nat := regionResultOffset + regionBytes

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- One decoded, case-bound native observation. -/
structure Result where
  caseId : UInt64
  planIdentity : ByteArray
  machine : HardwareExecutionResult
  regionAfter : ByteArray

private def getU8 (bytes : ByteArray) (offset : Nat) : Except String UInt8 :=
  if offset < bytes.size then .ok (bytes.get! offset)
  else .error s!"result record truncated at byte {offset}"

private def getU32 (bytes : ByteArray) (offset : Nat) : Except String UInt32 := do
  let b0 ← getU8 bytes offset
  let b1 ← getU8 bytes (offset + 1)
  let b2 ← getU8 bytes (offset + 2)
  let b3 ← getU8 bytes (offset + 3)
  pure (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24))

private def getU64 (bytes : ByteArray) (offset : Nat) : Except String UInt64 := do
  let lo ← getU32 bytes offset
  let hi ← getU32 bytes (offset + 4)
  pure (lo.toUInt64 ||| (hi.toUInt64 <<< 32))

private def copyBytes (bytes : ByteArray) (offset count : Nat) : Except String ByteArray := do
  if offset + count > bytes.size then
    throw s!"result record truncated while copying [{offset}, {offset + count})"
  pure <| ByteArray.mk <| ((List.range count).map (fun i => bytes.get! (offset + i))).toArray

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Decodes exactly one record and binds it to the expected case identity.  Every framing field is
    checked; reserved bytes must be zero so future protocol extensions cannot be silently ignored. -/
def decodeRecord (bytes : ByteArray) (offset : Nat) (expectedCaseId : UInt64) : Except String Result := do
  let magic ← getU64 bytes offset
  if magic != wireMagic then throw s!"scratch result magic mismatch for case {expectedCaseId}"
  let version ← getU32 bytes (offset + 8)
  if version != wireVersion then throw s!"scratch result version mismatch for case {expectedCaseId}"
  let encodedRecordBytes ← getU32 bytes (offset + 12)
  if encodedRecordBytes.toNat != recordBytes then throw s!"scratch result record length mismatch for case {expectedCaseId}"
  let caseId ← getU64 bytes (offset + 16)
  if caseId != expectedCaseId then throw s!"scratch result case identity mismatch: expected {expectedCaseId}, got {caseId}"
  let encodedRegionBytes ← getU32 bytes (offset + 24)
  if encodedRegionBytes.toNat != regionBytes then throw s!"scratch result region length mismatch for case {expectedCaseId}"
  let faultByte ← getU8 bytes (offset + 28)
  if faultByte > 1 then throw s!"scratch result fault marker is not boolean for case {expectedCaseId}"
  let reserved0 ← getU8 bytes (offset + 29)
  let reserved1 ← getU8 bytes (offset + 30)
  let reserved2 ← getU8 bytes (offset + 31)
  if reserved0 != 0 || reserved1 != 0 || reserved2 != 0 then
    throw s!"scratch result reserved framing bytes are nonzero for case {expectedCaseId}"
  let planIdentity ← copyBytes bytes (offset + planIdentityOffset) planIdentityBytes
  let rax ← getU64 bytes (offset + registerResultOffset .rax)
  let rcx ← getU64 bytes (offset + registerResultOffset .rcx)
  let rdx ← getU64 bytes (offset + registerResultOffset .rdx)
  let rbx ← getU64 bytes (offset + registerResultOffset .rbx)
  let rsp ← getU64 bytes (offset + registerResultOffset .rsp)
  let rbp ← getU64 bytes (offset + registerResultOffset .rbp)
  let rsi ← getU64 bytes (offset + registerResultOffset .rsi)
  let rdi ← getU64 bytes (offset + registerResultOffset .rdi)
  let r8 ← getU64 bytes (offset + registerResultOffset .r8)
  let r9 ← getU64 bytes (offset + registerResultOffset .r9)
  let r10 ← getU64 bytes (offset + registerResultOffset .r10)
  let r11 ← getU64 bytes (offset + registerResultOffset .r11)
  let r12 ← getU64 bytes (offset + registerResultOffset .r12)
  let r13 ← getU64 bytes (offset + registerResultOffset .r13)
  let r14 ← getU64 bytes (offset + registerResultOffset .r14)
  let r15 ← getU64 bytes (offset + registerResultOffset .r15)
  let flags ← getU64 bytes (offset + flagsResultOffset)
  let regionAfter ← copyBytes bytes (offset + regionResultOffset) regionBytes
  let gprs : Reg64 → UInt64
    | .rax => rax | .rcx => rcx | .rdx => rdx | .rbx => rbx
    | .rsp => rsp | .rbp => rbp | .rsi => rsi | .rdi => rdi
    | .r8 => r8 | .r9 => r9 | .r10 => r10 | .r11 => r11
    | .r12 => r12 | .r13 => r13 | .r14 => r14 | .r15 => r15
  pure {
    caseId := caseId
    planIdentity := planIdentity
    machine := { gprs := gprs, flags := flags, faulted := faultByte == 1 }
    regionAfter := regionAfter
  }

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Decodes a batch with exact length and order.  Short, extra, duplicate, omitted, or reordered
    records cannot be accepted: the byte count and each positional case identity must match. -/
def decodeBatch (bytes : ByteArray) (expectedCaseIds : List UInt64) : Except String (List Result) := do
  let expectedBytes := expectedCaseIds.length * recordBytes
  if bytes.size != expectedBytes then
    throw s!"scratch result batch length mismatch: expected exactly {expectedBytes} bytes, got {bytes.size}"
  let mut results : List Result := []
  for i in [0:expectedCaseIds.length] do
    let result ← decodeRecord bytes (i * recordBytes) expectedCaseIds[i]!
    results := results ++ [result]
  pure results

end Gasm.Targets.X86_64.HardwareMemoryProtocol
