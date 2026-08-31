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
import Gasm.Targets.X86_64.StackStorePrefix
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.X86_64.Roundtrip

/-!
# Linked production evidence for the selected stack-store prefix

This module connects `StackStorePrefix`'s operational facts to the production instruction list,
serializer, decoder, and instruction index.  It is the static-text/fetch portion of the future
checked-store demonstration's dynamic-origin proof.

It remains deliberately below authority and admission: a successful lookup proves which ordinary
instruction production execution fetches at the selected RIP, not that the access owns a view,
is mapped or writable, corresponds to a binding/use occurrence, or belongs to a
`VerifiedProgram`.
-/

namespace Gasm.Targets.X86_64.StackStorePrefixLink

open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Roundtrip
open Gasm.Targets.X86_64.StackStorePrefix

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The exact ordinary production instruction sequence selected by the checked-store
demonstration. -/
def instructions (value : UInt8) : List X86_64Instr :=
  [sub_rsp frameSize, mov_rsp_byte byteOffset value]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Production instruction index for the exact selected prefix. -/
def indexed (base : UInt64) (value : UInt8) : List (UInt64 × X86_64Instr) :=
  indexInstructions base (instructions value)

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The production serializer emits the exact nine bytes of the selected prefix. -/
theorem serialized_eq (value : UInt8) :
    serializeInstructions (instructions value) =
      ByteArray.mk #[0x48, 0x83, 0xEC, 0x28, 0xC6, 0x44, 0x24, 0x20, value] := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The production decoder recovers the exact selected allocation instruction. -/
theorem allocate_roundtrip : DecodesTo (sub_rsp frameSize) := by
  dsimp [DecodesTo, frameSize]
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The production decoder recovers the exact selected store for every authored byte. -/
theorem store_roundtrip (value : UInt8) : DecodesTo (mov_rsp_byte byteOffset value) :=
  roundtrip_mov_rsp_disp_byte byteOffset value

private theorem base_ne_storeRip (base : UInt64)
    (_textNoWrap : base.toNat + 9 ≤ 2 ^ 64) : base ≠ base + 4 := by
  intro same
  have sameNat := congrArg UInt64.toNat same
  rw [UInt64.toNat_add] at sameNat
  change base.toNat = (base.toNat + 4) % 2 ^ 64 at sameNat
  have addLt : base.toNat + 4 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt addLt] at sameNat
  omega

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The first production fetch resolves to the exact stack-allocation instruction. -/
@[simp] theorem lookup_allocate (base : UInt64) (value : UInt8) :
    instructionAtRipIndexed (indexed base value) base = some (sub_rsp frameSize) := by
  simp [indexed, instructions, indexInstructions, indexInstructions.loop,
    instructionAtRipIndexed]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Under the artifact's explicit text nonwrap premise, the second production fetch resolves to
the exact selected byte-store instruction. -/
theorem lookup_store (base : UInt64) (value : UInt8)
    (textNoWrap : base.toNat + 9 ≤ 2 ^ 64) :
    instructionAtRipIndexed (indexed base value) (base + 4) =
      some (mov_rsp_byte byteOffset value) := by
  have subSize :
      (X86_64Instruction.encode (sub_rsp frameSize)).size.toUInt64 = 4 := by
    rfl
  unfold indexed instructions indexInstructions
  simp only [indexInstructions.loop, subSize]
  simp [instructionAtRipIndexed, base_ne_storeRip base textNoWrap]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Executing the exact first instruction reaches the RIP at which the production index fetches
the selected store.  This connects actual operational succession to static text membership, but
does not yet construct a binding-history `UseOccurrence` or execution event. -/
theorem lookup_store_after_allocate (state : X86_64MachineState) (value : UInt8)
    (textNoWrap : state.rip.toNat + 9 ≤ 2 ^ 64) :
    instructionAtRipIndexed (indexed state.rip value) (afterAllocate state).rip =
      some (mov_rsp_byte byteOffset value) := by
  rw [afterAllocate_rip]
  exact lookup_store state.rip value textNoWrap

end Gasm.Targets.X86_64.StackStorePrefixLink
