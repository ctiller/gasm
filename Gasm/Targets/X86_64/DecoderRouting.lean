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

namespace Gasm.Targets.X86_64.DecoderRouting

open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- A decoder rejects one exact byte position.  The error text is deliberately existential:
routing depends only on rejection versus success, while each family remains free to improve its
diagnostic. -/
def RejectsAt
    (decoder : ByteArray → Nat → Except String (AnyX86_64Instruction × Nat))
    (bytes : ByteArray) (offset : Nat) : Prop :=
  ∃ error, decoder bytes offset = .error error

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- A rejecting decoder prefix is observationally absent from `tryDecoders`.  This is the shared
proof step needed by universal family codec theorems: they can establish local decode success and
one non-shadowing certificate for the registered prefix without unfolding every later family. -/
theorem tryDecoders_append_of_rejects
    (before after : List (ByteArray → Nat → Except String (AnyX86_64Instruction × Nat)))
    (bytes : ByteArray) (offset : Nat)
    (rejects : ∀ decoder ∈ before, RejectsAt decoder bytes offset) :
    tryDecoders (before ++ after) bytes offset = tryDecoders after bytes offset := by
  induction before with
  | nil => rfl
  | cons decoder rest ih =>
      have headRejects := rejects decoder (by simp)
      rcases headRejects with ⟨error, headRejects⟩
      rw [List.cons_append, tryDecoders, headRejects]
      apply ih
      intro candidate member
      exact rejects candidate (by simp [member])

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Lifts one local family decode result through the production dispatcher.  The caller supplies
the exact registry split and proves that every earlier decoder rejects this byte position; no
claim about later decoders is needed because `tryDecoders` returns the first success.

This is routing evidence only.  It does not prove that the instruction's encoder produced
`bytes`, that the local decoder is semantically correct, or that executing the decoded
instruction is authorized or admitted. -/
theorem decode_of_registered_success
    (before after : List (ByteArray → Nat → Except String (AnyX86_64Instruction × Nat)))
    (decoder : ByteArray → Nat → Except String (AnyX86_64Instruction × Nat))
    (bytes : ByteArray) (offset : Nat) (result : AnyX86_64Instruction × Nat)
    (registered : allTryDecoders = before ++ decoder :: after)
    (prefixRejects : ∀ prior ∈ before, RejectsAt prior bytes offset)
    (localSuccess : decoder bytes offset = .ok result) :
    decodeX86_64Instr bytes offset = .ok result := by
  unfold decodeX86_64Instr
  rw [registered, tryDecoders_append_of_rejects before (decoder :: after) bytes offset
    prefixRejects]
  simp only [tryDecoders, localSuccess]

private def rejectingControlDecoder :
    ByteArray → Nat → Except String (AnyX86_64Instruction × Nat) :=
  fun _ _ => .error "routing rejection control"

private def successfulControlDecoder (result : AnyX86_64Instruction × Nat) :
    ByteArray → Nat → Except String (AnyX86_64Instruction × Nat) :=
  fun _ _ => .ok result

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Private positive control: the routing premise is inhabitable and a rejecting prefix exposes
the later successful decoder.  This is fixture evidence only, not an instruction codec claim. -/
private theorem rejecting_prefix_exposes_later_control
    (bytes : ByteArray) (offset : Nat) (result : AnyX86_64Instruction × Nat) :
    tryDecoders [rejectingControlDecoder, successfulControlDecoder result] bytes offset =
      .ok result := by
  rfl

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Private negative boundary: a successful prefix is not a rejecting prefix.  Consequently the
shared lifting theorem cannot be used to skip an earlier decoder that already claimed the bytes. -/
private theorem successful_prefix_not_rejecting_control
    (bytes : ByteArray) (offset : Nat) (result : AnyX86_64Instruction × Nat) :
    ¬ RejectsAt (successfulControlDecoder result) bytes offset := by
  rintro ⟨error, impossible⟩
  cases impossible

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Private shadowing control: if the first decoder succeeds, `tryDecoders` returns that result
and never consults the later success. -/
private theorem successful_prefix_shadows_later_control
    (bytes : ByteArray) (offset : Nat)
    (first second : AnyX86_64Instruction × Nat) :
    tryDecoders [successfulControlDecoder first, successfulControlDecoder second] bytes offset =
      .ok first := by
  rfl

end Gasm.Targets.X86_64.DecoderRouting
