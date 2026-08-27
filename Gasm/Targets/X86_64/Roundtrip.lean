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
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Push
import Gasm.Targets.X86_64.Instructions.Pop
import Gasm.Targets.X86_64.Instructions.Div
import Gasm.Targets.X86_64.Instructions.Imul
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Instructions.Or
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Targets.X86_64.Instructions.Not
import Gasm.Targets.X86_64.Instructions.Neg
import Gasm.Targets.X86_64.Instructions.Shift
import Gasm.Targets.X86_64.Instructions.Test
import Gasm.Targets.X86_64.Instructions.Xchg
import Gasm.Targets.X86_64.Instructions.Cmov
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.Decoder
import Gasm.Targets.X86_64.Assembler

namespace Gasm.Targets.X86_64.Roundtrip

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Universal round-trip equivalence predicate: decoding the encoded bytes of an instruction yields the exact original instruction and byte size. -/
def DecodesTo (i : X86_64Instr) : Prop :=
  decodeX86_64Instr (X86_64Instruction.encode i) 0 = Except.ok (i, (X86_64Instruction.encode i).size)

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Stream round-trip equivalence predicate: disassembling the serialized bytes of an instruction sequence reproduces the identical sequence. -/
def StreamRoundtrips (instrs : List X86_64Instr) : Prop :=
  disassembleX86_64 (serializeInstructions instrs) = Except.ok instrs

-- ============================================================================
-- 1. Universal (∀-quantified) per-instruction roundtrip theorems.
--
-- NOTE ON SCOPE (docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate): this file
-- used to also carry one ground `DecodesTo` instance per instruction (`roundtrip_add_r64`,
-- `roundtrip_mov_r32`, etc.). Every one of those is now subsumed — with strictly more coverage —
-- by the exhaustive `RoundtripGate/*.lean` per-family gate theorems, which check every instruction
-- family's full `roundtripCases` list, not one hand-picked witness. They were deleted rather than
-- kept as redundant, narrower duplicates. Only the theorems below survive here: the ones that are
-- genuinely UNIVERSAL (∀-quantified over an infinite or law-8-honest domain), which the registry
-- gate — being a check over a finite enumerated list — cannot state.
-- ============================================================================

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Universal: JA rel8 (0x77) decodes back for every displacement byte. Sound because encode/decode
    for this instruction perform a direct positional byte read with no value-dependent branching,
    so the roundtrip is definitionally transparent for an arbitrary `d`. -/
theorem roundtrip_ja_rel8 : ∀ d : UInt8, DecodesTo (ja_rel8 d) := by intro d; rfl
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Universal: JBE rel8 (0x76) decodes back for every displacement byte (same rationale as JA rel8). -/
theorem roundtrip_jbe_rel8 : ∀ d : UInt8, DecodesTo (jbe_rel8 d) := by intro d; rfl
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Universal: SHL r64, CL (0xD3 /4) decodes back for every destination register. `encode` has no
    value-dependent branching (unlike the disp8-omitting MOV/LEA forms), so once `dst` is fixed by
    case analysis the remaining computation is fully transparent to `rfl`. -/
theorem roundtrip_shl_r64_cl : ∀ dst : Reg64, DecodesTo (shl_r64_cl dst) := by
  intro dst; cases dst <;> rfl
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Universal: SHR r64, CL (0xD3 /5) decodes back for every destination register (same rationale
    as `roundtrip_shl_r64_cl`). -/
theorem roundtrip_shr_r64_cl : ∀ dst : Reg64, DecodesTo (shr_r64_cl dst) := by
  intro dst; cases dst <;> rfl

-- ============================================================================
-- 2. Multi-instruction Program Stream Roundtrip Theorems
-- ============================================================================

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Formal theorem: Spike 1 instruction sequence exact stream roundtrip. -/
theorem roundtrip_spike1_stream :
    StreamRoundtrips [
      sub_rsp 56,
      mov_r32 .ecx 0xFFFFFFF5,
      mov_r64 .rcx .rax,
      mov_r32 .r8d 15,
      lea_rsp .r9 0x28,
      mov_rsp64 0x20 0,
      xor_r32 .ecx .ecx
    ] := by
  dsimp [StreamRoundtrips]; rfl

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Formal theorem: Spike 2 (Fibonacci) core instruction sequence exact stream roundtrip. -/
theorem roundtrip_spike2_stream :
    StreamRoundtrips [
      push_r64 .rbx,
      push_r64 .r12,
      sub_rsp 40,
      mov_r32 .eax 1,
      cmp_r64_imm8 .rcx 2,
      jl_rel8 16,
      mov_r64 .r12 .rcx,
      mov_r64 .rbx .rax,
      add_r64 .rax .rbx,
      sub_r64_imm8 .r12 1,
      cmp_r64_imm8 .r12 1,
      jg_rel8 (-15 : Int8).toUInt8,
      add_rsp 40,
      pop_r64 .r12,
      pop_r64 .rbx,
      ret_op
    ] := by
  dsimp [StreamRoundtrips]; rfl

end Gasm.Targets.X86_64.Roundtrip
