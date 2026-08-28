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
import Gasm.Core.Rng
import Gasm.Core.Arch
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Uop
import Gasm.Targets.X86_64.Instructions.Obligations

namespace Gasm.Targets.X86_64.Instructions

open Gasm.Core
open Gasm.Targets.X86_64

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Pure universe-polymorphic typeclass interface for x86-64 machine instruction semantics, binary encoding, micro-op decomposition, NASM formatting, and Lean source code emission.
    `roundtripCases` has no default: every instance MUST enumerate a finite, representative
    sample of its constructor's argument domain (registers, boundary immediates/displacements).
    This is the forcing function that makes `decodeX86_64Instr` gaps and misdecodes a build
    failure — see the Encodable Instruction Registry & Roundtrip Gate design section for the
    full rationale, the enumeration convention, and how these lists are consumed by
    `Gasm/Targets/X86_64/Registry.lean` and the sharded `RoundtripGate/*.lean` gate theorems. -/
class X86_64Instruction (ι : Type u) where
  encode          : ι → ByteArray
  step            : ι → X86_64MachineState → X86_64MachineState
  toUops          : ι → List X86_64Uop
  toNASM          : ι → String
  toLean          : ι → String
  canFuzzHardware : ι → Bool := fun _ => true
  undefinedFlagsMask : ι → UInt64 := fun _ => 0
  generateFuzzStates : ι → FuzzerRng → List X86_64MachineState × FuzzerRng
  roundtripCases  : List ι
  -- P4/P5 unification (docs/X86_ISA_EXPANSION_PREREQUISITES.md, Obligations.lean): deliberately
  -- NO default, exactly like `roundtripCases` above -- an instance cannot compile without
  -- declaring both. This is what makes "an instruction with identity semantics, an empty uop
  -- list, and zero fuzz states compiles cleanly" (the prerequisites document's mutation probe)
  -- impossible going forward: the author must say, in DATA `Tools/CheckX86Obligations.lean` and
  -- `scripts/check_x86_obligations.py` can both read, which oracle validated this instance and
  -- where its cost coefficients came from.
  validationOracle : ι → ValidationOracle
  costProvenance   : ι → CoefficientProvenance

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Open existential instruction container packing any type implementing X86_64Instruction. -/
structure AnyX86_64Instruction where
  {α : Type}
  [inst : X86_64Instruction α]
  instr : α

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
instance : X86_64Instruction AnyX86_64Instruction where
  encode pkg := @X86_64Instruction.encode pkg.α pkg.inst pkg.instr
  step pkg s := @X86_64Instruction.step pkg.α pkg.inst pkg.instr s
  toUops pkg := @X86_64Instruction.toUops pkg.α pkg.inst pkg.instr
  toNASM pkg := @X86_64Instruction.toNASM pkg.α pkg.inst pkg.instr
  toLean pkg := @X86_64Instruction.toLean pkg.α pkg.inst pkg.instr
  canFuzzHardware pkg := @X86_64Instruction.canFuzzHardware pkg.α pkg.inst pkg.instr
  undefinedFlagsMask pkg := @X86_64Instruction.undefinedFlagsMask pkg.α pkg.inst pkg.instr
  generateFuzzStates pkg rng := @X86_64Instruction.generateFuzzStates pkg.α pkg.inst pkg.instr rng
  -- The open existential wrapper has no intrinsic argument domain of its own to enumerate (it
  -- erases which concrete instruction it holds); the aggregate case list lives in
  -- `Gasm/Targets/X86_64/Registry.lean` as `allEncodableInstructions`, built by lifting every
  -- concrete instruction type's `roundtripCases` through `⟨_⟩`.
  roundtripCases := []
  validationOracle pkg := @X86_64Instruction.validationOracle pkg.α pkg.inst pkg.instr
  costProvenance pkg := @X86_64Instruction.costProvenance pkg.α pkg.inst pkg.instr

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
instance : ToString AnyX86_64Instruction where
  toString pkg := X86_64Instruction.toNASM pkg

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Total retired micro-ops for an instruction. -/
def uopsRetired (pkg : AnyX86_64Instruction) : Nat :=
  (X86_64Instruction.toUops pkg).length

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Constructs an 8-bit REX prefix byte from its 1-bit fields. -/
def makeRex (w : Bool) (r : Bool) (x : Bool) (b : Bool) : UInt8 :=
  0x40 ||| (if w then 8 else 0) ||| (if r then 4 else 0) ||| (if x then 2 else 0) ||| (if b then 1 else 0)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Returns true if the byte is an x86-64 REX prefix (0x40-0x4F). -/
def isRex (b : UInt8) : Bool :=
  b >= 0x40 && b <= 0x4F

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Parses a REX prefix byte into its (W, R, X, B) flag bits. -/
def parseRex (b : UInt8) : Bool × Bool × Bool × Bool :=
  ((b &&& 8) != 0, (b &&& 4) != 0, (b &&& 2) != 0, (b &&& 1) != 0)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Constructs an 8-bit ModR/M byte from mod, reg, and rm fields. -/
def makeModRM (mod : UInt8) (reg : UInt8) (rm : UInt8) : UInt8 :=
  ((mod &&& 3) <<< 6) ||| ((reg &&& 7) <<< 3) ||| (rm &&& 7)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Unpacks an 8-bit ModR/M byte into (mod, reg, rm) fields. -/
def extractModRM (b : UInt8) : UInt8 × UInt8 × UInt8 :=
  ((b >>> 6) &&& 3, (b >>> 3) &&& 7, b &&& 7)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Constructs an 8-bit SIB byte from scale, index, and base fields. -/
def makeSIB (scale : UInt8) (index : UInt8) (base : UInt8) : UInt8 :=
  ((scale &&& 3) <<< 6) ||| ((index &&& 7) <<< 3) ||| (base &&& 7)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Unpacks an 8-bit SIB byte into (scale, index, base) fields. -/
def extractSIB (b : UInt8) : UInt8 × UInt8 × UInt8 :=
  ((b >>> 6) &&& 3, (b >>> 3) &&& 7, b &&& 7)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Reads an 8-bit unsigned byte from the ByteArray at the given offset. -/
def readUInt8 (bytes : ByteArray) (offset : Nat) : Except String UInt8 :=
  if offset < bytes.size then
    Except.ok (bytes.get! offset)
  else
    Except.error s!"Unexpected end of byte stream at offset {offset}"

/- REF: docs/TARGETS/X86_64.md#5-stage-b-design-only-not-implemented-by-this-change -/
/-- Reads an 8-bit ModR/M byte at `offset` and unpacks it into (mod, reg, rm, nextOffset), where
    `nextOffset` points just past the ModR/M byte. Shared boilerplate for every per-family
    `tryDecode` that reads a ModR/M byte (Stage B: `Instructions/*.lean` own their decode logic
    directly instead of `Decoder.lean`'s monolithic `decodeX86_64Instr`). -/
def readModRM (bytes : ByteArray) (offset : Nat) : Except String (UInt8 × UInt8 × UInt8 × Nat) := do
  let b ← readUInt8 bytes offset
  let (mod, reg, rm) := extractModRM b
  pure (mod, reg, rm, offset + 1)

/- REF: docs/TARGETS/X86_64.md#5-stage-b-design-only-not-implemented-by-this-change -/
/-- Parses an optional REX prefix at `offset`, then reads the opcode byte that follows it.
    Returns `(hasRex, rexW, rexR, rexX, rexB, opcode, nextOffset)` where `nextOffset` points just
    past the opcode byte (the position of any ModR/M/immediate bytes). Every x86-64 instruction
    this decoder supports shares this REX-then-opcode preamble; under Stage B each per-family
    `tryDecode` calls this directly instead of relying on `decodeX86_64Instr`'s monolithic
    preamble, so this helper (not the preamble itself) is the single place that logic lives. -/
def parseRexAndOpcode (bytes : ByteArray) (offset : Nat) :
    Except String (Bool × Bool × Bool × Bool × Bool × UInt8 × Nat) := do
  let b0 ← readUInt8 bytes offset
  let (hasRex, rexW, rexR, rexX, rexB, curOffset) :=
    if isRex b0 then
      let (w, r, x, b) := parseRex b0
      (true, w, r, x, b, offset + 1)
    else
      (false, false, false, false, false, offset)
  let opcode ← readUInt8 bytes curOffset
  pure (hasRex, rexW, rexR, rexX, rexB, opcode, curOffset + 1)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Reads a 16-bit little-endian integer from the ByteArray at the given offset. -/
def readUInt16LE (bytes : ByteArray) (offset : Nat) : Except String UInt16 := do
  let b0 ← readUInt8 bytes offset
  let b1 ← readUInt8 bytes (offset + 1)
  Except.ok (b0.toUInt16 ||| (b1.toUInt16 <<< 8))

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Reads a 32-bit little-endian integer from the ByteArray at the given offset. -/
def readUInt32LE (bytes : ByteArray) (offset : Nat) : Except String UInt32 := do
  let b0 ← readUInt8 bytes offset
  let b1 ← readUInt8 bytes (offset + 1)
  let b2 ← readUInt8 bytes (offset + 2)
  let b3 ← readUInt8 bytes (offset + 3)
  Except.ok (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24))

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Reads a 32-bit little-endian signed integer from the ByteArray at the given offset. -/
def readInt32LE (bytes : ByteArray) (offset : Nat) : Except String Int32 := do
  let u ← readUInt32LE bytes offset
  Except.ok (Int32.ofUInt32 u)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Reads a 64-bit little-endian integer from the ByteArray at the given offset. -/
def readUInt64LE (bytes : ByteArray) (offset : Nat) : Except String UInt64 := do
  let lo ← readUInt32LE bytes offset
  let hi ← readUInt32LE bytes (offset + 4)
  Except.ok (lo.toUInt64 ||| (hi.toUInt64 <<< 32))

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Serializes a UInt32 into 4 bytes in little-endian order. -/
def uint32ToLittleEndian (v : UInt32) : ByteArray :=
  ByteArray.mk #[
    v.toUInt8,
    (v >>> 8).toUInt8,
    (v >>> 16).toUInt8,
    (v >>> 24).toUInt8
  ]

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Serializes an Int32 into 4 bytes in little-endian order. -/
def int32ToLittleEndian (v : Int32) : ByteArray :=
  uint32ToLittleEndian v.toUInt32

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Serializes a UInt64 into 8 bytes in little-endian order. -/
def uint64ToLittleEndian (v : UInt64) : ByteArray :=
  ByteArray.mk #[
    v.toUInt8,
    (v >>> 8).toUInt8,
    (v >>> 16).toUInt8,
    (v >>> 24).toUInt8,
    (v >>> 32).toUInt8,
    (v >>> 40).toUInt8,
    (v >>> 48).toUInt8,
    (v >>> 56).toUInt8
  ]

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Sign-extends an 8-bit immediate byte to 64-bit unsigned integer. -/
def signExtend8To64 (v : UInt8) : UInt64 :=
  if (v &&& 0x80) != 0 then
    0xFFFFFFFFFFFFFF00 ||| v.toUInt64
  else
    v.toUInt64

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Sign-extends a 32-bit immediate signed integer to 64-bit unsigned integer. -/
def signExtend32To64 (v : Int32) : UInt64 :=
  v.toUInt32.toUInt64 ||| (if v < 0 then 0xFFFFFFFF00000000 else 0)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Sign-extends a 32-bit unsigned immediate to 64-bit unsigned integer based on bit 31. -/
def signExtendUInt32To64 (v : UInt32) : UInt64 :=
  if (v &&& 0x80000000) != 0 then
    0xFFFFFFFF00000000 ||| v.toUInt64
  else
    v.toUInt64

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Formats a signed 8-bit displacement as a relative offset string for NASM (+ 0xN or - 0xN). -/
def formatDisp8 (disp : UInt8) : String :=
  let n := disp.toNat
  if n <= 127 then
    s!"+ 0x{String.ofList (Nat.toDigits 16 n)}"
  else
    let neg := 256 - n
    s!"- 0x{String.ofList (Nat.toDigits 16 neg)}"

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Formats a signed 32-bit displacement as a relative offset string for NASM (+ 0xN or - 0xN). -/
def formatDisp32 (disp : Int32) : String :=
  if disp >= 0 then
    s!"+ 0x{String.ofList (Nat.toDigits 16 disp.toNatClampNeg)}"
  else
    -- Negating `Int32.min` (-2147483648, a `curatedInt32Cases` boundary witness) overflows back
    -- to itself in two's-complement `Int32` arithmetic, which made the old `(-disp).toNatClampNeg`
    -- silently collapse to 0 for exactly that boundary value: "- 0x0" instead of the correct
    -- "- 0x80000000" -- found via P4(a)'s registry-derived encoding fuzzer
    -- (`docs/X86_ISA_EXPANSION_PREREQUISITES.md`), which was the first thing to ever exercise
    -- `JmpRel32`/`JeRel32`/etc.'s NASM cross-check with this witness. Computing the magnitude via
    -- `UInt32` (`0 - disp.toUInt32`, unsigned wraparound) instead of `Int32` negation sidesteps
    -- the overflow entirely: `0x80000000`'s own two's-complement negation IS `0x80000000` when
    -- read as an unsigned magnitude, which is exactly the correct hex digits to print after "- ".
    let mag : UInt32 := 0 - disp.toUInt32
    s!"- 0x{String.ofList (Nat.toDigits 16 mag.toNat)}"

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Formats a UInt8 as a hexadecimal string literal for Lean source code. -/
def formatHex8 (v : UInt8) : String :=
  let s := String.ofList (Nat.toDigits 16 v.toNat)
  s!"0x{s}"

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Formats a UInt32 as a hexadecimal string literal for Lean source code. -/
def formatHex32 (v : UInt32) : String :=
  let s := String.ofList (Nat.toDigits 16 v.toNat)
  s!"0x{s}"

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Formats a UInt64 as a hexadecimal string literal for Lean source code. -/
def formatHex64 (v : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 v.toNat)
  s!"0x{s}"

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Curated 64-bit edge case boundary values (zero, signs, min/max, powers of 2, bit patterns).
    The 32-bit and 64-bit sign boundaries (0x7FFFFFFF/0x80000000, 0x7FFFFFFFFFFFFFFF/
    0x8000000000000000) are deliberately placed within the first 6 entries: 2-register fuzz
    state generation (`generateStandardFuzzStatesFor2Regs`) only takes the first 6 values for
    each operand to bound the combinatorial grid, and a prior sign-boundary bug (a 32-bit XOR's
    SF flag) was only ever caught by chance via the random-state tail, never by the curated
    grid, precisely because these values previously sat past index 5. 0xFFFFFFFF00000000 (all
    of the high dword set, none of the low dword) is included for the same reason: it exercises
    a value whose 32-bit truncation is zero while the full 64-bit value is not. -/
def curated64BitValues : List UInt64 := [
  0, 1, 0x7FFFFFFF, 0x80000000, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000,
  2, 0x7F, 0x80, 0xFF, 0x100, 0x7FFF, 0x8000, 0xFFFFFFFF, 0xFFFFFFFFFFFFFFFF,
  0xFFFFFFFF00000000, 0xAAAAAAAAAAAAAAAA, 0x5555555555555555
]

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Curated flag test states (CF, PF, AF, ZF, SF, OF permutations with bit 1 reserved). -/
def curatedFlagValues : List UInt64 := [
  0x2,        -- No flags set
  0x3,        -- CF
  0x43,       -- CF, ZF
  0x843,      -- CF, ZF, OF
  0x802,      -- OF
  0x47,       -- CF, PF, AF, ZF
  0x8C7       -- CF, PF, AF, ZF, SF, OF
]

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- All 16 general-purpose 64-bit registers, in encoding order. Shared anchor list for every
    instruction's `roundtripCases` (Law-8-adjacent forcing function): using one canonical list
    keeps register coverage consistent and REX.R/REX.B extension bits exercised everywhere. -/
def allReg64List : List Reg64 := [
  .rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
  .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15
]

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- All 16 registers except RSP. For instruction families where a register-immediate form and a
    dedicated RSP-specific helper (e.g. `AddR64Imm8` vs `AddRspImm8`) are byte-identical when the
    register is RSP, the decoder canonicalizes to the RSP-specific structure on decode (an
    intentional, pre-existing disambiguation choice, exercised by that structure's own
    `roundtripCases`) — so `roundtripCases` for the general register-immediate form uses this list
    to avoid asserting a `toLean` match the decoder deliberately does not preserve. -/
def allReg64ListNoRsp : List Reg64 := [
  .rax, .rcx, .rdx, .rbx, .rbp, .rsi, .rdi,
  .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15
]

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- All 16 general-purpose 32-bit sub-registers, in encoding order. -/
def allReg32List : List Reg32 := [
  .eax, .ecx, .edx, .ebx, .esp, .ebp, .esi, .edi,
  .r8d, .r9d, .r10d, .r11d, .r12d, .r13d, .r14d, .r15d
]

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Both-extended (dst, src) register pairs for two-register `roundtripCases`. The "vary one slot
    against a `.rax` anchor" convention above never sets REX.R and REX.B simultaneously (the
    anchor slot is always the non-extended `.rax`), so it cannot catch a REX bit swapped or
    conditioned on the OTHER operand's extension (e.g. `makeRex true srcExt false (dstExt &&
    !srcExt)` — correct-looking when only one operand is extended, wrong when both are). These
    three pairs (confirmed to decode correctly against the pristine encoders) close that gap;
    `(.r15, .r8)` is the reverse of `(.r8, .r15)` so both REX.R=srcExt-first and
    REX.B=dstExt-first orderings get an extended/extended witness. -/
def extendedReg64Pairs : List (Reg64 × Reg64) := [(.r8, .r15), (.r12, .r13), (.r15, .r8)]

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- 32-bit-register counterpart of `extendedReg64Pairs`, for two-`Reg32`-argument families
    (currently only XOR). -/
def extendedReg32Pairs : List (Reg32 × Reg32) := [(.r8d, .r15d), (.r12d, .r13d), (.r15d, .r8d)]

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Curated UInt8 boundary values for `roundtripCases`: zero, one, the rel8/imm8 signed
    boundary (0x7F max positive, 0x80 min negative), and 0xFF (-1). -/
def curatedUInt8Cases : List UInt8 := [0x00, 0x01, 0x7F, 0x80, 0xFF]

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Curated UInt32/imm32 boundary values for `roundtripCases`: zero, a representative small
    value, the INT32_MAX/sign-flip boundary, and UINT32_MAX. -/
def curatedUInt32Cases : List UInt32 := [0x00000000, 0x00001000, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Curated Int32/rel32 boundary values for `roundtripCases`: zero, a representative small
    positive/negative pair, and the INT32_MAX/INT32_MIN signed boundaries. -/
def curatedInt32Cases : List Int32 := [0, 0x1000, -0x1000, 0x7FFFFFFF, -0x80000000]

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- `canFuzzHardware`'s instance-level RSP safety check for `Reg64` register fields, shared by
    every ALU/data-movement family that defaults `canFuzzHardware := true` and whose
    `roundtripCases` can put RSP in *any* register field (dst, src, or a read-only source like
    DIV's divisor).

    **Why this must be instance-level, not type-level** (the bug this closes): `canFuzzHardware`
    lives on the typeclass and was previously only ever overridden per-*type* (e.g. every
    `AddR64R64` was `true`). But `AddR64R64.roundtripCases` — correctly, for decode coverage —
    includes RSP as both dst and src (`allReg64List` has no reason to special-case RSP for
    decoding). Deriving the hardware-fuzz suite as `allEncodableInstructions.filter
    canFuzzHardware` then fed `add rsp, rax`-shaped instances straight to real silicon: the
    harness died with `STATUS_ACCESS_VIOLATION` (0xC0000005) and the whole batch aborted having
    produced zero results, because a *type*-level flag cannot see that this specific *instance*
    writes RSP. This helper — and per-family `canFuzzHardware i := hwSafeReg64 i.dst && ...`
    definitions using it — make the check instance-level: `false` whenever RSP appears in any
    register field of the instance actually being asked about, `true` otherwise.

    **Why both dst (write) and src/divisor (read) are excluded, per
    `Gasm/Targets/X86_64/HardwareHarness.lean`'s actual state handling**:
    - `buildTestText`'s per-test block loads every GPR from the fuzz test vector *except* RSP
      ("Load all GPRs (except rsp which remains stack-backed)") — RSP is never set from
      `state.gprs .rsp`, and both the post-instruction result-capture sequence (`pushfq`,
      `pop qword [rsp-8]`, `mov [rsp-16], rax`, ...) and the VEH's own recovery path address
      memory *relative to the current RSP*. **Writing RSP** (e.g. `add rsp, rax` with a fuzzed
      `rax`) can move RSP to an address so far outside the mapped stack that even the OS's
      exception-dispatch machinery cannot use it to invoke the VEH handler — the observed failure
      mode is not a recovered per-vector fault but the whole harness process dying (exit code
      3221225477 = 0xC0000005), which is why this is a hazard class, not merely "the model and
      hardware would disagree."
    - **Reading RSP** as a source does not crash the harness (RSP always holds a valid,
      harness-controlled stack address at that point), but it is still excluded: the model
      (`step`) computes using whatever `UInt64` the fuzz generator put in `state.gprs .rsp`
      (a boundary value like `0x8000000000000000`), while the hardware instance actually
      consumes the harness's real, harness-pinned stack pointer — a different input to the same
      computation. Any result register that mixes in RSP's value (e.g. `div rsp`, `add rax, rsp`)
      is then compared against the model's answer for a *different* input and is guaranteed to
      mismatch, even though nothing crashed. `SemanticsFuzzer.allRegs64` already excludes RSP
      from the *compared output* registers, which hides a mismatch in RSP's own final value, but
      it does nothing for a *different*, compared register whose value was computed from RSP —
      so RSP-as-source is excluded here too, on comparison-soundness grounds rather than
      crash-safety grounds. -/
def hwSafeReg64 (r : Reg64) : Bool := r != .rsp

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- 32-bit-register counterpart of `hwSafeReg64` (ESP is RSP's low 32 bits and is subject to the
    exact same write-crash / read-mismatch hazards described there — e.g. `XorR32R32`). -/
def hwSafeReg32 (r : Reg32) : Bool := r != .esp

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Curated UInt64/imm64 boundary values for `roundtripCases` (deliberately smaller than
    `curated64BitValues`, which is sized for fuzz-state generation, not the decode gate): zero,
    the INT64_MAX/MIN signed boundaries, UINT64_MAX, and one alternating bit pattern. Kept short
    to bound `MovR64Imm64.roundtripCases` (the single largest contributor to the MOV family's
    gate elaboration cost) without dropping any boundary class. -/
def curatedUInt64Cases : List UInt64 := [
  0, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF, 0xAAAAAAAAAAAAAAAA
]

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Generates a pseudo-random machine state across all general-purpose registers and flags. -/
def generateRandomMachineState (rng : FuzzerRng) : X86_64MachineState × FuzzerRng := Id.run do
  let mut curRng := rng
  let mut state : X86_64MachineState := default
  let allRegs : List Reg64 := [
    .rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
    .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15
  ]
  for r in allRegs do
    let (v, nextRng) := curRng.next
    state := state.setGpr64 r v
    curRng := nextRng
  let (flagsVal, nextRng2) := curRng.next
  let validFlags := (flagsVal &&& arithmeticStatusMask) ||| 2
  state := { state with flags := validFlags }
  (state, nextRng2)

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Standard fuzz state generator for 2-register binary operations (e.g. ADD r1, r2). -/
def generateStandardFuzzStatesFor2Regs (r1 r2 : Reg64) (rng : FuzzerRng) (randCount : Nat := 8) : List X86_64MachineState × FuzzerRng := Id.run do
  let mut states : List X86_64MachineState := []
  for v1 in curated64BitValues.take 6 do
    for v2 in curated64BitValues.take 6 do
      for flg in curatedFlagValues.take 3 do
        let s : X86_64MachineState := default
        let s := s.setGpr64 r1 v1
        let s := s.setGpr64 r2 v2
        let s := { s with flags := flg }
        states := states ++ [s]
  let mut curRng := rng
  for _ in [0:randCount] do
    let (s, nextRng) := generateRandomMachineState curRng
    states := states ++ [s]
    curRng := nextRng
  (states, curRng)

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Standard fuzz state generator for 1-register unary operations (e.g. NOT r1, NEG r1). -/
def generateStandardFuzzStatesFor1Reg (r : Reg64) (rng : FuzzerRng) (randCount : Nat := 8) : List X86_64MachineState × FuzzerRng := Id.run do
  let mut states : List X86_64MachineState := []
  for v in curated64BitValues do
    for flg in curatedFlagValues.take 3 do
      let s : X86_64MachineState := default
      let s := s.setGpr64 r v
      let s := { s with flags := flg }
      states := states ++ [s]
  let mut curRng := rng
  for _ in [0:randCount] do
    let (s, nextRng) := generateRandomMachineState curRng
    states := states ++ [s]
    curRng := nextRng
  (states, curRng)

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Standard fuzz state generator for immediate operations (e.g. ADD r1, imm). -/
def generateStandardFuzzStatesForImm (r : Reg64) (rng : FuzzerRng) (randCount : Nat := 8) : List X86_64MachineState × FuzzerRng :=
  generateStandardFuzzStatesFor1Reg r rng randCount

end Gasm.Targets.X86_64.Instructions

-- B1 iteration 2 (build-perf: Instructions.lean aggregator sharding): `X86_64Instr`, the
-- `TargetArch X86_64` instance, and `X86_64Instr.toBinary` used to live in the
-- `Instructions.lean` umbrella (moved here with their REF citations unchanged; the code itself
-- is unchanged too, modulo the `open` this file already provides making the unqualified
-- `AnyX86_64Instruction` resolve the same way it did at the old site). Every Instructions/*.lean
-- submodule already imports this file, so relocating them here adds no new dependency edge, but
-- it means a consumer that only needs "an x86-64 instruction" (not whole-registry visibility)
-- can import `Instructions.Base` directly instead of the umbrella, which otherwise drags in all
-- 21 instruction submodules transitively (a 22-module forward-closure reduction per such
-- consumer — 33 modules via the umbrella vs. 11 via this file directly; see
-- `scripts/build_baseline.md` §7 for the measured cascade-size delta). See `Instructions.lean`'s
-- own header comment for the audit-completeness property this split preserves.
namespace Gasm.Targets.X86_64

open Gasm.Core
open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Standard x86-64 open existential instruction container alias. -/
abbrev X86_64Instr := AnyX86_64Instruction

/- REF: docs/TARGETS/TARGET_MODEL.md#1-vertical-slice-target-structure -/
instance : TargetArch X86_64 where
  wordWidth    := 8
  MachineState := X86_64MachineState
  Instruction  := X86_64Instr
  stepPure     := X86_64Instruction.step

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
def X86_64Instr.toBinary (instr : X86_64Instr) : ByteArray :=
  X86_64Instruction.encode instr

end Gasm.Targets.X86_64
