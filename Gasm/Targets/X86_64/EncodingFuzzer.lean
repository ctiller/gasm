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
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Push
import Gasm.Targets.X86_64.Instructions.Pop
import Gasm.Targets.X86_64.Instructions.Div
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.NASM
import Gasm.Targets.X86_64.Fuzzer

namespace Gasm.Targets.X86_64.EncodingFuzzer

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Fuzzer

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- All 16 64-bit general-purpose registers for comprehensive encoding coverage. -/
def allGprs64 : List Reg64 := [
  .rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
  .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15
]

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- All 16 32-bit sub-registers. -/
def allGprs32 : List Reg32 := [
  .eax, .ecx, .edx, .ebx, .esp, .ebp, .esi, .edi,
  .r8d, .r9d, .r10d, .r11d, .r12d, .r13d, .r14d, .r15d
]

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

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Generates a pseudo-random instruction covering all supported opcode families and register combinations. -/
def generateComprehensiveRandomInstruction (rng : FuzzerRng) : Prod AnyX86_64Instruction FuzzerRng :=
  let (catChoice, rng1) := rng.nextNat 22
  let (r1Idx, rng2) := rng1.nextNat allGprs64.length
  let (r2Idx, rng3) := rng2.nextNat allGprs64.length
  let (r32_1Idx, rng4) := rng3.nextNat allGprs32.length
  let (r32_2Idx, rng5) := rng4.nextNat allGprs32.length
  let (imm8Val, rng6) := rng5.nextNat 128
  let (imm32Val, rng7) := rng6.nextNat 65536
  let (disp8Val, rng8) := rng7.nextNat 120

  let r1 := allGprs64.getD r1Idx .rax
  let r2 := allGprs64.getD r2Idx .rdx
  let r32_1 := allGprs32.getD r32_1Idx .eax
  let r32_2 := allGprs32.getD r32_2Idx .edx

  match catChoice with
  | 0  => (add_r64 r1 r2, rng8)
  | 1  => (add_r64_imm8 r1 (UInt8.ofNat imm8Val), rng8)
  | 2  => (add_rsp (UInt8.ofNat (imm8Val % 64)), rng8)
  | 3  => (sub_r64 r1 r2, rng8)
  | 4  => (sub_r64_imm8 r1 (UInt8.ofNat imm8Val), rng8)
  | 5  => (sub_rsp (UInt8.ofNat (imm8Val % 64)), rng8)
  | 6  => (mov_r64 r1 r2, rng8)
  | 7  => (mov_r32 r32_1 (UInt32.ofNat imm32Val), rng8)
  | 8  => (mov_rsp_byte (UInt8.ofNat (disp8Val % 32)) (UInt8.ofNat imm8Val), rng8)
  | 9  => (mov_rsp32 (UInt8.ofNat (disp8Val % 32)) (UInt32.ofNat imm32Val), rng8)
  | 10 => (mov_rsp64 (UInt8.ofNat (disp8Val % 32)) (UInt32.ofNat imm32Val), rng8)
  | 11 => (mov_mem8 r1 r2, rng8)
  | 12 => (lea_rsp r1 (UInt8.ofNat (disp8Val % 64)), rng8)
  | 13 => (xor_r32 r32_1 r32_2, rng8)
  | 14 => (cmp_r64 r1 r2, rng8)
  | 15 => (cmp_r64_imm8 r1 (UInt8.ofNat imm8Val), rng8)
  | 16 => (push_r64 r1, rng8)
  | 17 => (pop_r64 r1, rng8)
  | 18 => (div_r64 r1, rng8)
  | 19 => (ret_op, rng8)
  | 20 => (mov_r64_imm64 r1 (UInt64.ofNat imm32Val * 65536 + UInt64.ofNat imm8Val), rng8)
  | _  => (xor_r32 r32_1 r32_1, rng8)

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
