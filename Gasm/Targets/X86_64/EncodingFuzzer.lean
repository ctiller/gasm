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
import Gasm.Targets.X86_64.Instructions.Hlt
import Gasm.Targets.X86_64.Registry
import Gasm.Targets.X86_64.NASM
import Gasm.Targets.X86_64.Fuzzer

namespace Gasm.Targets.X86_64.EncodingFuzzer

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Fuzzer

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Result structure for differential encoding verification against NASM oracle. -/
structure EncodingDiffResult where
  passed        : Bool
  totalInstrs   : Nat
  gasmBytes     : ByteArray
  nasmBytes     : ByteArray
  nasmAssembly  : String
  errorMsg      : Option String := none
  deriving Inhabited

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Formats a ByteArray as hex pairs for mismatch inspection. -/
def formatHexBytes (b : ByteArray) : String :=
  let hexList := (List.range b.size).map fun idx =>
    let byte := b.get! idx
    let s := String.ofList (Nat.toDigits 16 byte.toNat)
    if s.length == 1 then "0" ++ s else s
  String.intercalate " " hexList

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- ALU-with-imm32 family `toLean` prefixes that have a dedicated, shorter x86-64 "accumulator
    immediate" opcode (`04/05/0C/0D/24/25/2C/2D/34/35/3C/3D/A8/A9 id`, no ModRM byte) whenever the
    destination is RAX specifically. NASM always prefers that shorter form for `<mnemonic> rax,
    <imm32>` text over the general ModRM form (`81 /n id`) gasm's `encode` always emits for these
    types -- see `encodingFuzzerCandidates`'s doc comment for why this is filtered rather than
    matched in `encode`. Only the imm32-carrying member of each family is listed: the imm8
    sign-extended forms (`add_r64_imm8` etc., opcode `83 /n ib`) are already the shortest possible
    encoding for a small immediate on a 64-bit register regardless of which register, so they
    carry no such hazard and are not excluded. -/
def accumulatorImm32HazardPrefixes : List String :=
  ["add_r64_imm32", "sub_r64_imm32", "cmp_r64_imm32", "test_r64_imm32", "or_r64_imm32"]

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- Shift-by-immediate `toLean` prefixes that have a dedicated, shorter "shift by 1" opcode
    (`D0/D1 /n`, no immediate byte) specifically when the immediate is exactly 1. NASM always
    prefers that shorter form for `<mnemonic> <reg>, 1` text over the general immediate form
    (`C1 /n ib`) gasm's `encode` always emits -- see `encodingFuzzerCandidates`'s doc comment. -/
def shiftByOneHazardPrefixes : List String :=
  ["shl_r64_imm8", "shr_r64_imm8", "sar_r64_imm8"]

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- `Registry.allEncodableInstructions`, filtered to exclude the classes of FALSE POSITIVE this
    registry-derived generator surfaced while it was being wired up (P4(a)). All four are the
    same underlying phenomenon: NASM's assembler prefers the shortest available encoding for
    semantically-identical assembly text, while gasm's `encode` deterministically emits one fixed
    encoding per instruction TYPE regardless of operand values. Every excluded case is a valid,
    standard x86-64 encoding choice on gasm's side too -- not a correctness defect -- but adopting
    NASM's shorter choice would require `Decoder.lean` to reciprocally recognize the alternate
    opcode and would perturb the `decide`-checked `RoundtripGate/*.lean` shards' witness sets,
    which is out of scope for this obligation-gate change:
      1. `xchg r64, r64` (the WHOLE family, not just an RAX-anchored subset -- widened after
         empirically finding a second, independent divergence): `xchg r64, rax` (either operand
         order) hits the 1-byte accumulator-XCHG short form (`90+r`) NASM prefers over the general
         two-operand ModRM form (`87 /r`); separately, and unrelated to RAX at all, NASM's ModRM
         reg/rm ROLE ASSIGNMENT for the general form is the mirror image of `XchgR64R64.encode`'s
         own (confirmed empirically: `xchg r15, r8` assembles to `reg=r15,rm=r8` under NASM, while
         gasm's `encode dst src` always emits `reg=srcCode,rm=dstCode` -- `reg=r8,rm=r15` for the
         same instance) -- both are valid encodings of a semantically commutative instruction, but
         essentially every non-self-paired `XchgR64R64` witness hits ONE of these two divergences,
         so the family is excluded outright rather than carrying a narrower, RAX-only predicate
         that would still fail on most witnesses.
      2. ALU instructions (`accumulatorImm32HazardPrefixes`) with RAX as the destination and an
         imm32 operand: NASM emits the accumulator-immediate short form instead of the general
         ModRM form.
      3. Shift instructions (`shiftByOneHazardPrefixes`) with immediate exactly 1: NASM emits the
         dedicated shift-by-1 short form instead of the general immediate form.
      4. `MovReg32Mem32Disp` (`mov_reg32_mem32_disp`) and `LeaRspDisp32` (`lea_rsp32`) with
         `disp = 0`: both `encode` implementations unconditionally emit a full displacement
         (`mod=01` exact-disp8 for the former, `mod=10` forced-disp32 for the latter, even when the value
         is exactly `0`) -- unlike every sibling RSP/memory form in this file, which special-cases
         `disp == 0` to the shorter `mod=00` (no displacement byte) form both in `encode` and in
         `toNASM`. NASM optimizes `[rsp + 0x0]`-shaped text down to the shorter `mod=00` form
         regardless, so the two diverge whenever the curated `0` witness is picked. Narrower than
         classes 1-3 (excludes one specific immediate value per family, not the whole family)
         because every nonzero-disp witness of both types genuinely byte-matches NASM.
    Filtering here (not from `allEncodableInstructions` itself) keeps roundtrip and
    hardware-semantics fuzzing covering every witness unchanged; only the NASM encoding
    differential -- the one oracle these divergences actually affect -- skips them. `toLean`'s
    rendering is used as the filter key rather than a type-level match (which the erased
    `AnyX86_64Instruction` existential cannot express) -- see `Instructions/Base.lean`'s
    `allReg64ListNoRsp` doc comment for the precedent of a decoder-canonicalization mismatch being
    handled by excluding specific witnesses from one consumer's list rather than by changing
    `encode` itself. All four classes were found BY running this generator for the first time
    across the full registry (P4's own point: "an instruction can exist today whose... encoding...
    nothing has ever checked" -- closing that gap surfaces exactly this kind of previously-blind
    corner). -/
def encodingFuzzerCandidates : List AnyX86_64Instruction :=
  Gasm.Targets.X86_64.Registry.allEncodableInstructions.filter fun instr =>
    let s := X86_64Instruction.toLean instr
    let xchgHazard := s.startsWith "xchg_r64"
    let accumHazard := accumulatorImm32HazardPrefixes.any fun p => s.startsWith (p ++ " .rax ")
    let shiftOneHazard := shiftByOneHazardPrefixes.any fun p => s.startsWith p && s.endsWith " 0x1"
    let movR32MemZeroDispHazard := s.startsWith "mov_reg32_mem32_disp" && s.endsWith " 0x0"
    let leaRsp32ZeroDispHazard := s.startsWith "lea_rsp32" && s.endsWith "(0)"
    !(xchgHazard || accumHazard || shiftOneHazard || movR32MemZeroDispHazard || leaRsp32ZeroDispHazard)

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- Generates a pseudo-random instruction by picking uniformly from
    `encodingFuzzerCandidates` (registry-derived, see that definition for the one filtered
    class) -- the SAME registry-derived witness list the roundtrip gate and (via
    `canFuzzHardware`) the semantics fuzzer already derive their own suites from
    (`SemanticsFuzzer.lean`'s `hardwareFuzzableInstructions`) -- instead of the 22-way hand-written
    `match` this replaces (P4(a), `docs/X86_ISA_EXPANSION_PREREQUISITES.md`: that match covered
    only ≈21 of 88 registered forms and was left behind when the semantics-fuzzer suite was
    re-derived from the registry, "the exact drift class the registry was built to kill"). Every
    currently-registered instruction is now exercised here automatically, and a future family
    only needs its mandatory `roundtripCases` entry (already forced by
    `Gasm/Targets/X86_64/Registry.lean`'s build-time audit) to be picked up -- no second hand list
    to remember. The `getD`/pattern-match fallback below is unreachable in practice:
    `Registry.lean`'s own `run_cmd` audit fails the build if `allEncodableInstructions` is ever
    empty (and the XCHG filter above cannot empty a 88-form registry down to nothing), so
    `rng.nextNat candidates.length` always has `candidates.length > 0`; the fallback exists only
    so this function has no partial-match obligation of its own. -/
def generateComprehensiveRandomInstruction (rng : FuzzerRng) : Prod AnyX86_64Instruction FuzzerRng :=
  let candidates := encodingFuzzerCandidates
  let (idx, rng') := rng.nextNat candidates.length
  match candidates[idx]? with
  | some instr => (instr, rng')
  | none =>
    match candidates with
    | i :: _ => (i, rng')
    | [] => (⟨HltOp.mk⟩, rng')

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Generates a comprehensive random program of the specified length. -/
def generateComprehensiveProgram (length : Nat) (rng : FuzzerRng) : Prod (List AnyX86_64Instruction) FuzzerRng := Id.run do
  let mut curRng := rng
  let mut res : List AnyX86_64Instruction := []
  for _ in [0:length] do
    let (instr, nextRng) := generateComprehensiveRandomInstruction curRng
    res := res ++ [instr]
    curRng := nextRng
  (res, curRng)

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Byte-exact comparison predicate used to judge every differential result. Extracted as its
    own definition so the Law 13(4) control vectors below exercise the exact same comparison
    mechanism the real fuzzer uses, rather than an unrelated equality check. -/
def bytesMatch (gasmBytes nasmBytes : ByteArray) : Bool := gasmBytes == nasmBytes

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Verifies byte-exact equality between Gasm binary serialization and NASM assembled output.
    `overrideNasmSource`, when given, is assembled by NASM INSTEAD of `toNasmAssembly instrs` --
    gasm's own encoding of `instrs` is unaffected. This exists purely so a Law 13(4) negative
    control vector can force a genuine, guaranteed divergence (gasm encodes one instruction,
    NASM assembles a different one) through this exact function -- the one the real fuzzer
    suite calls -- rather than through a standalone re-implementation of the comparison that a
    bug here could bypass entirely. -/
def verifyDifferential (instrs : List AnyX86_64Instruction) (nasmPath : String) (tmpPrefix : String := ".tmp_gasm_nasm") (overrideNasmSource : Option String := none) : IO EncodingDiffResult := do
  let gasmBytes := instrs.foldl (fun acc i => acc ++ X86_64Instruction.encode i) ByteArray.empty
  let nasmAsm := overrideNasmSource.getD (toNasmAssembly instrs)
  let res ← assembleWithNasm nasmPath nasmAsm tmpPrefix
  match res with
  | .error err =>
    let msg := "NASM Assembly Failed:\n" ++ err ++ "\n\nAssembly Source:\n" ++ nasmAsm
    pure ⟨false, instrs.length, gasmBytes, ByteArray.empty, nasmAsm, some msg⟩
  | .ok nasmBytes =>
    if bytesMatch gasmBytes nasmBytes then
      pure ⟨true, instrs.length, gasmBytes, nasmBytes, nasmAsm, none⟩
    else
      let msg := "Binary Mismatch between Gasm and NASM!\n" ++
                 "  Gasm bytes (" ++ toString gasmBytes.size ++ " bytes): " ++ formatHexBytes gasmBytes ++ "\n" ++
                 "  NASM bytes (" ++ toString nasmBytes.size ++ " bytes): " ++ formatHexBytes nasmBytes ++ "\n\nDisassembly:\n" ++ nasmAsm
      pure ⟨false, instrs.length, gasmBytes, nasmBytes, nasmAsm, some msg⟩

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
/-- Independently-known-correct byte encoding for `mov rax, rbx`: REX.W (0x48) + opcode 0x89
    (MOV r/m64, r64) + ModRM 0xD8 (mod=11, reg=rbx=011, rm=rax=000). Taken directly from the
    Intel SDM's documented encoding — NOT derived from gasm's own `X86_64Instruction.encode` —
    so it can serve as ground truth for validating the NASM oracle itself. -/
def knownGoodMovRaxRbxEncoding : ByteArray := ByteArray.mk #[0x48, 0x89, 0xD8]

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
/-- A deliberately WRONG "expected" encoding for `mov rax, rbx` (this is actually the real
    encoding of `mov rax, rcx`). Used purely as the Law 13(4) negative control: NASM's real
    output for `mov rax, rbx` must NOT equal this, proving the comparison mechanism can
    actually discriminate rather than being a tautology that always reports a match. -/
def knownBadMovRaxRbxEncoding : ByteArray := ByteArray.mk #[0x48, 0x89, 0xC8]

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Mandatory Law 13(4) control vectors for the NASM oracle, run BEFORE any fuzzed
    differential result is allowed to count. Both controls route through `verifyDifferential`
    itself — the exact function `runEncodingFuzzerSuite` below calls — rather than a
    standalone re-implementation of the comparison, so a bug in `verifyDifferential`'s own
    control flow (e.g. a hardcoded `passed := true`) is caught here, not just a bug in
    `bytesMatch` in isolation:
    (1) POSITIVE — a known instruction must be reported as a match by `verifyDifferential`,
        AND the NASM bytes it captured must equal an independently-known-correct Intel SDM
        encoding (so gasm and NASM agreeing with each other, but both wrong, cannot pass).
    (2) NEGATIVE — `verifyDifferential` is fed gasm's real encoding of one instruction
        (`mov rax, rbx`) but NASM is made to assemble a genuinely different instruction
        (`ret`) via `overrideNasmSource` — a guaranteed, real divergence. `verifyDifferential`
        MUST report this as a mismatch; if it reports a pass, the function itself is fail-open.
    A control failure aborts the run: an oracle path that cannot demonstrate correctness on
    known vectors must never be trusted to validate unknown ones. -/
def runNasmControlVectors (nasmPath : String) : IO (Except String Unit) := do
  let controlInstrs : List AnyX86_64Instruction := [mov_r64 .rax .rbx]

  let posRes ← verifyDifferential controlInstrs nasmPath ".tmp_gasm_nasm_control_pos"
  if !posRes.passed then
    return .error s!"NASM POSITIVE control vector FAILED: verifyDifferential reported a mismatch for 'mov rax, rbx' ({posRes.errorMsg.getD "no detail"}). The NASM oracle cannot be trusted — aborting before any fuzzed vector is tested."
  if !bytesMatch posRes.nasmBytes knownGoodMovRaxRbxEncoding then
    return .error s!"NASM POSITIVE control vector FAILED: NASM's real output for 'mov rax, rbx' was {formatHexBytes posRes.nasmBytes}, but the independently-known-correct Intel SDM encoding is {formatHexBytes knownGoodMovRaxRbxEncoding}. gasm and NASM agree with each other but not with ground truth — aborting before any fuzzed vector is tested."

  let divergentNasmSource := toNasmAssembly [ret_op]
  let negRes ← verifyDifferential controlInstrs nasmPath ".tmp_gasm_nasm_control_neg" (some divergentNasmSource)
  if negRes.passed then
    return .error "NASM NEGATIVE control vector FAILED: verifyDifferential reported a MATCH when gasm's encoding of 'mov rax, rbx' was deliberately compared against NASM's assembly of a different instruction ('ret'). verifyDifferential itself is fail-open and cannot be trusted to detect real mismatches."

  return .ok ()

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Runs differential encoding verification across N randomized programs. -/
def runEncodingFuzzerSuite (numPrograms : Nat) (progLength : Nat) (initialSeed : UInt64 := 88172645463325252) (overrideNasm : Option String := none) : IO (Nat × Nat × Option String) := do
  let nasmPath ← findNasmPath overrideNasm
  IO.println s!"[NASM Oracle] Using assembler executable: {nasmPath}"
  let mut currentRng : FuzzerRng := ⟨initialSeed⟩
  let mut passedCount := 0
  let mut failedCount := 0
  let mut firstFailure : Option String := none

  for progIdx in [0:numPrograms] do
    let (program, nextRng) := generateComprehensiveProgram progLength currentRng
    currentRng := nextRng
    let tmpFilePrefix := ".tmp_fuzz_" ++ toString (progIdx + 1)
    let result ← verifyDifferential program nasmPath tmpFilePrefix
    let pNum := progIdx + 1
    if result.passed then
      passedCount := passedCount + 1
      if pNum % 10 == 0 || pNum == 1 || pNum == numPrograms then
        IO.println ("  [PASS] Program " ++ toString pNum ++ ": " ++ toString progLength ++ " instrs, " ++ toString result.gasmBytes.size ++ " bytes exact match with NASM")
    else
      failedCount := failedCount + 1
      if firstFailure.isNone then
        firstFailure := result.errorMsg
      IO.println ("  [FAIL] Program " ++ toString pNum ++ " Mismatch:\n" ++ result.errorMsg.getD "Unknown error")

  pure (passedCount, failedCount, firstFailure)

end Gasm.Targets.X86_64.EncodingFuzzer
