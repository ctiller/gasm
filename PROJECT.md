# Project: Gasm x86-64 User-Space GPR Instruction Implementation

## Architecture
- Target Architecture: x86-64 (AMD64 / Intel 64)
- Domain Restriction: User-space general-purpose registers (64-bit, 32-bit, 16-bit, 8-bit) and immediates (imm64, imm32, imm16, imm8) exclusively.
- Strict Exclusions: Memory operands (`[reg + disp]`, SIB, etc.), specialist registers (XMM/YMM/ZMM, MMX, x87 FPU, CR*, DR*, MSRs), and privileged/system/kernel instructions.
- Modular Design:
  - AST & Typeclass: `Gasm/Targets/X86_64/Instructions/<Family>.lean` implementing `X86_64Instruction`.
  - Machine State & Registers: `Gasm/Targets/X86_64/Registers.lean` (`X86_64MachineState`, `Reg64`, `Reg32`, `Reg16`, `Reg8`).
  - Binary Encoding: Per-instruction `X86_64Instruction.encode` with REX, 0x66 prefix, ModR/M, and immediate serialization.
  - Binary Decoding: Decentralized `<family>TryDecode` dispatched sequentially in `Gasm/Targets/X86_64/Decoder.lean`.
  - Memory Isolation: `Gasm/Targets/X86_64/MemoryFrame/<Family>.lean` proving `WritesWithin` and `ReadsWithin` with `memAccesses _ := []`.
  - Compile-Time Roundtrip Gates: `Gasm/Targets/X86_64/RoundtripGate/<Family>.lean` verifying `decodesOk` via `by decide`.
  - Registry & Global Audit: `Gasm/Targets/X86_64/Registry.lean` compiling all encodable instructions and auditing live instances against `expectedInstructionTypes`.
  - Verification Obligations: Enforced by `Tools/CheckX86Obligations.lean` (`.silicon`/`.nasmEncoding`, `.modelInternalUnvalidated`, non-empty `toUops`, fuzz state count >= 3).

## Feature Inventory
| # | Feature | Description | Milestone | Source |
|---|---------|-------------|-----------|--------|
| 1 | Reg16 & Reg8 Sub-Registers | Add `Reg16` and `Reg8` inductive types, mappings to `Reg64`, and register code encoders | M1 | Survey |
| 2 | Partial Register Write Semantics | Add `setGpr16` and `setGpr8` preserving upper bits of 64-bit GPRs | M1 | Survey |
| 3 | RFLAGS Parity, AuxCarry, Direction | Add `.pf`, `.af`, `.df` accessors and arithmetic flag calculation helpers for 32/16/8-bit | M1 | Survey |
| 4 | Codec 0x66 Prefix Scanning | Update `Base.lean` `parseRexAndOpcode` to recognize and scan `0x66` operand-size override | M1 | Survey |
| 5 | ADD Width Variants | Add `AddR32R32`, `AddR32Imm8`, `AddR32Imm32`, `AddR16R16`, `AddR16Imm8`, `AddR16Imm16`, `AddR8R8`, `AddR8Imm8` | M2 | Survey / R1 |
| 6 | SUB Width Variants | Add `SubR32R32`, `SubR32Imm8`, `SubR32Imm32`, `SubR16R16`, `SubR16Imm8`, `SubR16Imm16`, `SubR8R8`, `SubR8Imm8` | M2 | Survey / R1 |
| 7 | AND Width Variants | Add `AndR64Imm32`, `AndR32R32`, `AndR32Imm8`, `AndR32Imm32`, `AndR16R16`, `AndR16Imm8`, `AndR16Imm16`, `AndR8R8`, `AndR8Imm8` | M2 | Survey / R1 |
| 8 | OR Width Variants | Add `OrR32R32`, `OrR32Imm8`, `OrR32Imm32`, `OrR16R16`, `OrR16Imm8`, `OrR16Imm16`, `OrR8R8`, `OrR8Imm8` | M2 | Survey / R1 |
| 9 | XOR Width Variants | Add `XorR64R64`, `XorR64Imm8`, `XorR64Imm32`, `XorR32Imm8`, `XorR32Imm32`, `XorR16R16`, `XorR16Imm8`, `XorR16Imm16`, `XorR8R8`, `XorR8Imm8` | M2 | Survey / R1 |
| 10 | CMP Width Variants | Add `CmpR32R32`, `CmpR32Imm8`, `CmpR32Imm32`, `CmpR16R16`, `CmpR16Imm8`, `CmpR16Imm16`, `CmpR8R8`, `CmpR8Imm8` | M2 | Survey / R1 |
| 11 | TEST Width Variants | Add `TestR32R32`, `TestR32Imm32`, `TestR16R16`, `TestR16Imm16`, `TestR8R8`, `TestR8Imm8` | M2 | Survey / R1 |
| 12 | NOT & NEG Width Variants | Add `NotR32`, `NotR16`, `NotR8`, `NegR32`, `NegR16`, `NegR8` | M2 | Survey / R1 |
| 13 | SHIFT Width Variants | Add 32/16/8-bit SHL, SHR, SAR immediate and CL forms + `SarR64Cl` | M3 | Survey / R1 |
| 14 | MOV Width & Imm32 Variants | Add `MovR64Imm32` (sign-extended), `MovR32R32`, `MovR16R16`, `MovR16Imm16`, `MovR8R8`, `MovR8Imm8` | M3 | Survey / R1 |
| 15 | XCHG Width Variants & NOP | Add `XchgR32R32` (including NOP `0x90`), `XchgR16R16`, `XchgR8R8` | M3 | Survey / R1 |
| 16 | IMUL & DIV/MUL Width Variants | Add 2-op/3-op IMUL variants, 1-op IMUL/MUL, unsigned DIV, signed IDIV | M3 | Survey / R1 |
| 17 | ADC Family | Implement `Adc.lean`: 64/32/16/8-bit reg-reg and imm variants | M4 | Survey / R1 |
| 18 | SBB Family | Implement `Sbb.lean`: 64/32/16/8-bit reg-reg and imm variants | M4 | Survey / R1 |
| 19 | Flag Manipulation Family | Implement `Flags.lean`: CLC, STC, CMC, CLD, STD, LAHF, SAHF | M4 | Survey / R1 |
| 20 | Sign/Zero Extension & Conversion | Implement `Convert.lean` / `Extend.lean`: CBW, CWDE, CDQE, CWD, CDQ, CQO, MOVSX, MOVZX, MOVSXD | M4 | Survey / R1 |
| 21 | Bit Test Family | Implement `BitOps.lean`: BT, BTC, BTR, BTS (64/32/16-bit reg-reg and imm8) | M5 | Survey / R1 |
| 22 | Bit Scan & Counting Family | Implement `BitScan.lean` / `Popcnt.lean`: BSF, BSR, POPCNT, LZCNT, TZCNT (64/32/16-bit) | M5 | Survey / R1 |
| 23 | Byte Swap & Exchange Families | Implement `Bswap.lean` (BSWAP 64/32), `Xadd.lean` (XADD 64/32/16/8), `Cmpxchg.lean` (CMPXCHG 64/32/16/8) | M5 | Survey / R1 |
| 24 | SETcc Family | Implement `Setcc.lean`: All 16 condition codes targeting `Reg8` | M6 | Survey / R1 |
| 25 | CMOVcc Expansion | Expand `Cmov.lean`: remaining 8 condition codes for 64-bit, plus 32-bit and 16-bit forms | M6 | Survey / R1 |
| 26 | E2E Test Suite Pass (Tiers 1-4) | Comprehensive opaque-box test runner validating all inventoried features against spec | M7 | Survey / Dual Track |
| 27 | Adversarial Hardening (Tier 5) | White-box adversarial edge case fuzzing and coverage verification | M7 | Survey / Dual Track |

## Milestones
| # | Name | Scope | Dependencies | Status |
|---|------|-------|-------------|--------|
| M1 | Sub-Register & Flag Foundation | `Reg16`, `Reg8`, `setGpr16`, `setGpr8`, flag accessors (`pf`, `af`, `df`), flag calculation helpers, 0x66 prefix decoder support | none | DONE |
| M2 | ALU, Logic, & Test Width Expansion | 32/16/8-bit forms for ADD, SUB, AND, OR, XOR, CMP, TEST, NOT, NEG | M1 | PLANNED |
| M3 | Shift, Mov, Xchg, Imul, Div Expansion | 32/16/8-bit SHIFT (SHL, SHR, SAR), MOV (including sign-extended Imm32), XCHG, IMUL, DIV/MUL | M1 | PLANNED |
| M4 | New ALU, Flags, & Conversion Families | ADC, SBB, Flags (CLC, STC, CMC, CLD, STD, LAHF, SAHF), Extensions/Conversions (CBW, CWDE, CDQE, CWD, CDQ, CQO, MOVSX, MOVZX, MOVSXD) | M1, M2 | PLANNED |
| M5 | Bit Operations, Scans, & Byte Swaps | BT, BTC, BTR, BTS, BSF, BSR, POPCNT, LZCNT, TZCNT, BSWAP, XADD, CMPXCHG | M1 | PLANNED |
| M6 | Condition Codes: SETcc & CMOVcc | SETcc (16 conditions on Reg8) and CMOVcc complete 16 conditions across 64/32/16-bit | M1, M2 | PLANNED |
| M7 | E2E Integration & Verification Hardening | Phase 1: 100% pass of E2E test suite (Tiers 1-4); Phase 2: Adversarial coverage hardening (Tier 5); final git sync | M1, M2, M3, M4, M5, M6 | PLANNED |

## Interface Contracts
### `Registers.lean` ↔ Instruction Families
- `Reg16`: `ax`, `cx`, `dx`, `bx`, `sp`, `bp`, `si`, `di`, `r8w`..`r15w`
- `Reg8`: `al`, `cl`, `dl`, `bl`, `spl`, `bpl`, `sil`, `dil`, `r8b`..`r15b`
- `setGpr16 (s : X86_64MachineState) (r : Reg16) (val : UInt16) : X86_64MachineState`
  - Formula: `s.setGpr64 (reg16To64 r) ((s.gprs (reg16To64 r) &&& 0xFFFFFFFFFFFF0000) ||| val.toUInt64)`
- `setGpr8 (s : X86_64MachineState) (r : Reg8) (val : UInt8) : X86_64MachineState`
  - Formula: `s.setGpr64 (reg8To64 r) ((s.gprs (reg8To64 r) &&& 0xFFFFFFFFFFFFFF00) ||| val.toUInt64)`
- Status flags:
  - `s.pf : Bool`: `(s.flags &&& (1 <<< 2)) != 0`
  - `s.af : Bool`: `(s.flags &&& (1 <<< 4)) != 0`
  - `s.df : Bool`: `(s.flags &&& (1 <<< 10)) != 0`
- Status flag mutators:
  - `setFlagsAdd32`, `setFlagsAdd16`, `setFlagsAdd8`
  - `setFlagsSub32`, `setFlagsSub16`, `setFlagsSub8`
  - `setFlagsCmp32`, `setFlagsCmp16`, `setFlagsCmp8`
  - `setFlagsNeg32`, `setFlagsNeg16`, `setFlagsNeg8`

### `Base.lean` ↔ Decoder & Codec
- Prefix decoding: `parsePrefixesAndOpcode bytes offset` returns `(has0x66, hasRex, rexW, rexR, rexX, rexB, opcode, opOffset)`
- Register encoding:
  - `reg16Code : Reg16 → UInt8 × Bool`
  - `reg8Code : Reg8 → UInt8 × Bool × Bool` (where second bool indicates if REX byte is mandatory)

### Instruction Family ↔ Integration Framework
Every instruction `<Form>` must provide:
1. `instance : X86_64Instruction <Form>` with:
   - `encode`: REX / 0x66 / opcode / ModRM / immediate
   - `step`: Semantic machine state transition
   - `toUops`: Explicit uop breakdown
   - `toNASM`: Explicit size-qualified string
   - `toLean`: DSL representation
   - `canFuzzHardware`: RSP/ESP safety check
   - `validationOracle`: `.silicon` if safe, `.nasmEncoding` otherwise
   - `costProvenance`: `.modelInternalUnvalidated` with reason >= 8 chars
   - `roundtripCases`: Curated non-empty witness list
   - `memAccesses`: `[]`
   - `generateFuzzStates`: count >= 3
   - `undefinedFlagsMask`: Match Intel SDM
2. `/- REF: intel-sdm#vol=2;instr=<Mnemonic>;part=description -/` and `part=operation`
3. In `MemoryFrame/<Family>.lean`: `<Form>.writesWithin` and `<Form>.readsWithin` using batch lemmas
4. In `RoundtripGate/<Family>.lean`: Entry in `<family>FamilyCases` with `by decide`
5. In `Registry.lean`: Name in `expectedInstructionTypes`
6. In `Instructions.lean`: Umbrella import (if new family file)

## Code Layout
- Foundation: `Gasm/Targets/X86_64/Registers.lean`, `Gasm/Targets/X86_64/Instructions/Base.lean`
- Instructions: `Gasm/Targets/X86_64/Instructions/<Family>.lean`
- Umbrella: `Gasm/Targets/X86_64/Instructions.lean`
- Decoder: `Gasm/Targets/X86_64/Decoder.lean`
- Registry: `Gasm/Targets/X86_64/Registry.lean`
- Memory Frames: `Gasm/Targets/X86_64/MemoryFrame/<Family>.lean`
- Roundtrip Gates: `Gasm/Targets/X86_64/RoundtripGate/<Family>.lean`, `DispatchExhaustive.lean`
- Verification Gates: `scripts/check_instructions_umbrella.py`, `Tools/CheckX86Obligations.lean`, `lakefile.toml`
- E2E Tests: `tests/e2e/` (runner and test cases)
