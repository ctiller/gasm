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

namespace Gasm.Targets.AArch64

open Gasm.Core
open Gasm.Targets.AArch64.Instructions

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Proposition asserting that an instruction decodes back to itself when serialized to a 32-bit word. -/
def DecodesTo (i : AnyAArch64Instruction) : Prop :=
  decodeWord (encodeWord i) = some i

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Deserializes a sequential stream of 32-bit AArch64 instructions from a byte array. -/
def disassembleAArch64 (bytes : ByteArray) : Option (List AnyAArch64Instruction) :=
  let rec loop (fuel : Nat) (idx : Nat) (acc : List AnyAArch64Instruction) : Option (List AnyAArch64Instruction) :=
    match fuel with
    | 0 => if idx >= bytes.size then some acc.reverse else none
    | fuel + 1 =>
      if idx >= bytes.size then some acc.reverse
      else
        match decode bytes idx with
        | some (instr, len) => loop fuel (idx + len) (instr :: acc)
        | none => none
  loop (bytes.size + 1) 0 []

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Serializes an instruction list into a contiguous little-endian byte array. -/
def serializeAArch64 (instrs : List AnyAArch64Instruction) : ByteArray :=
  let rec loop (rem : List AnyAArch64Instruction) (acc : ByteArray) : ByteArray :=
    match rem with
    | [] => acc
    | i :: rest => loop rest (acc ++ encode i)
  loop instrs ByteArray.empty

/- REF: docs/TARGETS/ARM64.md#encodable-instruction-registry-codec-roundtrip-gate -/
/-- Proposition asserting that a list of instructions roundtrips identically through binary streaming. -/
def StreamRoundtrips (instrs : List AnyAArch64Instruction) : Prop :=
  disassembleAArch64 (serializeAArch64 instrs) = some instrs

-- ============================================================================
-- Ground Roundtrip Theorems for Representative Instructions across 15 Families
-- All proven definitionally by `rfl` with standard kernel purity [propext, Quot.sound]
-- ============================================================================

/- REF: docs/TARGETS/ARM64.md#15-system-family -/
theorem roundtrip_nop : decodeWord (encodeWord ⟨Nop.mk⟩) = some ⟨Nop.mk⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#13-branchreg-family -/
theorem roundtrip_ret_x30 : decodeWord (encodeWord ⟨Ret.mk .x30⟩) = some ⟨Ret.mk .x30⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#13-branchreg-family -/
theorem roundtrip_ret_x0 : decodeWord (encodeWord ⟨Ret.mk .x0⟩) = some ⟨Ret.mk .x0⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#15-system-family -/
theorem roundtrip_svc : decodeWord (encodeWord ⟨Svc.mk 0⟩) = some ⟨Svc.mk 0⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#15-system-family -/
theorem roundtrip_hlt : decodeWord (encodeWord ⟨Hlt.mk 0xF000⟩) = some ⟨Hlt.mk 0xF000⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#11-branchimm-family -/
theorem roundtrip_b : decodeWord (encodeWord ⟨B.mk 16⟩) = some ⟨B.mk 16⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#11-branchimm-family -/
theorem roundtrip_bl : decodeWord (encodeWord ⟨Bl.mk 32⟩) = some ⟨Bl.mk 32⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#12-branchcond-family -/
theorem roundtrip_b_cond_ne : decodeWord (encodeWord ⟨BCond.mk .NE 16⟩) = some ⟨BCond.mk .NE 16⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#12-branchcond-family -/
theorem roundtrip_b_cond_eq : decodeWord (encodeWord ⟨BCond.mk .EQ 0⟩) = some ⟨BCond.mk .EQ 0⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
theorem roundtrip_movz64 : decodeWord (encodeWord ⟨Movz.mk true .x0 42 0⟩) = some ⟨Movz.mk true .x0 42 0⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
theorem roundtrip_movz32 : decodeWord (encodeWord ⟨Movz.mk false .x1 100 0⟩) = some ⟨Movz.mk false .x1 100 0⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
theorem roundtrip_movn : decodeWord (encodeWord ⟨Movn.mk true .x2 1 0⟩) = some ⟨Movn.mk true .x2 1 0⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
theorem roundtrip_movk : decodeWord (encodeWord ⟨Movk.mk true .x3 0x1234 1⟩) = some ⟨Movk.mk true .x3 0x1234 1⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
theorem roundtrip_movReg64 : decodeWord (encodeWord ⟨MovReg.mk true .x0 .x1⟩) = some ⟨MovReg.mk true .x0 .x1⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
theorem roundtrip_movReg32 : decodeWord (encodeWord ⟨MovReg.mk false .x2 .x3⟩) = some ⟨MovReg.mk false .x2 .x3⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
theorem roundtrip_addImm64 : decodeWord (encodeWord ⟨AddImm.mk true false .x0 .x1 16 false⟩) = some ⟨AddImm.mk true false .x0 .x1 16 false⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
theorem roundtrip_addImm32 : decodeWord (encodeWord ⟨AddImm.mk false true .x2 .x3 100 false⟩) = some ⟨AddImm.mk false true .x2 .x3 100 false⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
theorem roundtrip_subImm64 : decodeWord (encodeWord ⟨SubImm.mk true false .x4 .x5 32 false⟩) = some ⟨SubImm.mk true false .x4 .x5 32 false⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
theorem roundtrip_subImm_cmp : decodeWord (encodeWord ⟨SubImm.mk false true .xzr .x6 8 false⟩) = some ⟨SubImm.mk false true .xzr .x6 8 false⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
theorem roundtrip_addReg : decodeWord (encodeWord ⟨AddReg.mk true false .x0 .x1 .x2 .LSL 0⟩) = some ⟨AddReg.mk true false .x0 .x1 .x2 .LSL 0⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
theorem roundtrip_subReg_cmp : decodeWord (encodeWord ⟨SubReg.mk true true .xzr .x1 .x2 .LSL 0⟩) = some ⟨SubReg.mk true true .xzr .x1 .x2 .LSL 0⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
theorem roundtrip_andReg : decodeWord (encodeWord ⟨AndReg.mk true false .x0 .x1 .x2 .LSL 0 false⟩) = some ⟨AndReg.mk true false .x0 .x1 .x2 .LSL 0 false⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
theorem roundtrip_orrReg : decodeWord (encodeWord ⟨OrrReg.mk true .x0 .x1 .x2 .LSL 0 false⟩) = some ⟨OrrReg.mk true .x0 .x1 .x2 .LSL 0 false⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
theorem roundtrip_eorReg : decodeWord (encodeWord ⟨EorReg.mk true .x0 .x1 .x2 .LSL 0 false⟩) = some ⟨EorReg.mk true .x0 .x1 .x2 .LSL 0 false⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
theorem roundtrip_strbImm : decodeWord (encodeWord ⟨StrbImm.mk .x1 .x0 0⟩) = some ⟨StrbImm.mk .x1 .x0 0⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
theorem roundtrip_ldrbImm : decodeWord (encodeWord ⟨LdrbImm.mk .x1 .x0 0⟩) = some ⟨LdrbImm.mk .x1 .x0 0⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
theorem roundtrip_strImm64 : decodeWord (encodeWord ⟨StrImm.mk true .x0 .sp 0⟩) = some ⟨StrImm.mk true .x0 .sp 0⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
theorem roundtrip_ldrImm64 : decodeWord (encodeWord ⟨LdrImm.mk true .x0 .sp 0⟩) = some ⟨LdrImm.mk true .x0 .sp 0⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
theorem roundtrip_strImm32 : decodeWord (encodeWord ⟨StrImm.mk false .x0 .sp 0⟩) = some ⟨StrImm.mk false .x0 .sp 0⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
theorem roundtrip_ldrImm32 : decodeWord (encodeWord ⟨LdrImm.mk false .x0 .sp 0⟩) = some ⟨LdrImm.mk false .x0 .sp 0⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
theorem roundtrip_stpPre : decodeWord (encodeWord ⟨StpPre.mk true .x29 .x30 .sp (-16)⟩) = some ⟨StpPre.mk true .x29 .x30 .sp (-16)⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
theorem roundtrip_ldpPost : decodeWord (encodeWord ⟨LdpPost.mk true .x29 .x30 .sp 16⟩) = some ⟨LdpPost.mk true .x29 .x30 .sp 16⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#14-adr-family -/
theorem roundtrip_adr : decodeWord (encodeWord ⟨Adr.mk .x0 16⟩) = some ⟨Adr.mk .x0 16⟩ := by rfl

/- REF: docs/TARGETS/ARM64.md#14-adr-family -/
theorem roundtrip_adrp : decodeWord (encodeWord ⟨Adrp.mk .x0 4096⟩) = some ⟨Adrp.mk .x0 4096⟩ := by rfl

-- ============================================================================
-- Multi-Instruction Stream Roundtrip Theorems (Spikes 1 & 2)
-- ============================================================================

/- REF: docs/TARGETS/ARM64.md#1-probe-1-direct-serial-output-over-pl011-uart -/
/-- Multi-instruction sequence for Spike 1 Bare Metal PL011 UART output probe. -/
def spike1BareMetalStream : List AnyAArch64Instruction := [
  ⟨Movz.mk true .x0 0x0900 1⟩,  -- movz x0, #0x0900, lsl #16 (PL011 UART base 0x09000000)
  ⟨Movz.mk false .x1 0x48 0⟩,   -- movz w1, #'H'
  ⟨StrbImm.mk .x1 .x0 0⟩,       -- strb w1, [x0]
  ⟨Movz.mk false .x1 0x69 0⟩,   -- movz w1, #'i'
  ⟨StrbImm.mk .x1 .x0 0⟩,       -- strb w1, [x0]
  ⟨Movz.mk false .x1 0x0A 0⟩,   -- movz w1, #'\n'
  ⟨StrbImm.mk .x1 .x0 0⟩,       -- strb w1, [x0]
  ⟨B.mk 0⟩                      -- b . (spin halt)
]

/- REF: docs/TARGETS/ARM64.md#1-probe-1-direct-serial-output-over-pl011-uart -/
/-- Proves that the Spike 1 Bare Metal PL011 instruction stream roundtrips identically through binary streaming. -/
theorem roundtrip_spike1_baremetal_stream :
    disassembleAArch64 (serializeAArch64 spike1BareMetalStream) = some spike1BareMetalStream := by
  rfl

/- REF: docs/TARGETS/ARM64.md#2-probe-2-pl011-uart-output-semihosting-programmatic-exit -/
/-- Multi-instruction sequence for Spike 2 Fibonacci recursive prologue and epilogue. -/
def spike2FibonacciStream : List AnyAArch64Instruction := [
  ⟨StpPre.mk true .x29 .x30 .sp (-16)⟩,    -- stp x29, x30, [sp, #-16]!
  ⟨AddImm.mk true false .x29 .sp 0 false⟩, -- add x29, sp, #0 (architectural mov x29, sp)
  ⟨SubImm.mk false true .xzr .x0 2 false⟩, -- cmp w0, #2
  ⟨BCond.mk .GE 16⟩,                       -- b.ge recurse
  ⟨LdpPost.mk true .x29 .x30 .sp 16⟩,      -- ldp x29, x30, [sp], #16
  ⟨Ret.mk .x30⟩                            -- ret
]

/- REF: docs/TARGETS/ARM64.md#2-probe-2-pl011-uart-output-semihosting-programmatic-exit -/
/-- Proves that the Spike 2 Fibonacci instruction stream roundtrips identically through binary streaming. -/
theorem roundtrip_spike2_fibonacci_stream :
    disassembleAArch64 (serializeAArch64 spike2FibonacciStream) = some spike2FibonacciStream := by
  rfl

end Gasm.Targets.AArch64
