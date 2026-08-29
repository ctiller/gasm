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
import Gasm.Targets.X86_64.Decoder
import Gasm.Targets.X86_64.Encoding
import Gasm.Targets.X86_64.Fuzzer

namespace Gasm.Targets.X86_64.StabilityFuzzer

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Fuzzer

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- The parser stability property (no external oracle required): for any bytestream `b`,
    if `decodeX86_64Instr b 0 = .ok (r₁, len₁)` then `decodeX86_64Instr (encodeX86_64Instr r₁) 0
    = .ok (r₂, len₂) → r₁ = r₂` (and `len₂` must equal the full re-encoded length -- the
    encoder's canonical bytes for `r₁` must decode back to exactly `r₁`, consuming exactly all
    of them). This is the internal counterpart to `encoding_fuzzer` (oracle: NASM, `Gasm/Targets
    /X86_64/EncodingFuzzer.lean`) and the `RoundtripGate/*.lean` per-instruction-type
    `native_decide` shards: those check that hand-constructed `roundtripCases` values decode
    correctly and match NASM byte-for-byte, but only over a curated, finite enumeration this
    codebase itself chose. This fuzzer instead feeds `decodeX86_64Instr` bytes derived from
    mutation of a valid encoding (flip/truncate/extend/reorder), so it can reach decode
    branches -- unusual REX/ModRM/SIB bit combinations -- the curated `roundtripCases` lists
    were never built to hit, closing part of the gap the owner flagged: only some encodable
    forms get silicon-oracle coverage (`x86_fuzzer`/`HardwareHarness.lean`); this property needs
    no silicon, no NASM, and no oracle of any kind.

    `X86_64Instr` (`AnyX86_64Instruction`) is an open existential (a `Type` + typeclass instance
    + payload) and does not derive `DecidableEq`, so `r₁ = r₂` is checked via three independent
    observable projections every concrete instruction type already provides:
    `X86_64Instruction.encode` (bytes), `X86_64Instruction.toNASM` (assembly text), and
    `X86_64Instruction.toLean` (exact constructor + argument source text) -- agreement on all
    three is the fuzzer's operational stand-in for structural equality. -/
def hexByte (b : UInt8) : String :=
  let s := String.ofList (Nat.toDigits 16 b.toNat)
  if s.length < 2 then "0" ++ s else s

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Renders a bounded hex preview of a `ByteArray` for fuzzer failure diagnostics. -/
def hexPreview (bytes : ByteArray) (maxLen : Nat := 64) : String := Id.run do
  let n := Nat.min bytes.size maxLen
  let mut s := ""
  for i in [0:n] do
    s := s ++ hexByte (bytes.get! i) ++ " "
  if bytes.size > maxLen then s ++ s!"... ({bytes.size} bytes total)" else s

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Generates `n` pseudo-random bytes using the existing `Fuzzer.FuzzerRng`. -/
def genRandomBytes (rng : FuzzerRng) (n : Nat) : ByteArray × FuzzerRng := Id.run do
  let mut cur := rng
  let mut out := ByteArray.empty
  for _ in [0:n] do
    let (v, nxt) := cur.next
    cur := nxt
    out := out.push (v &&& 0xFF).toUInt8
  (out, cur)

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- A single valid, encoder-produced instruction's bytes -- the "valid artifact" baseline every
    mutator below perturbs, per the vacuity-floor concern that uniform noise almost never
    decodes. -/
def genValidInstrBytes (rng : FuzzerRng) : ByteArray × FuzzerRng × String :=
  let (instr, r1) := generateRandomInstruction rng
  (X86_64Instruction.encode instr, r1, "valid-instr")

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Appends 1-8 pseudo-random trailing bytes after a valid instruction's encoding.
    `decodeX86_64Instr` returns the number of bytes it consumed rather than requiring the whole
    buffer to be exhausted, so this should always still decode the leading instruction
    correctly -- it exercises "decode ignores what follows" directly. -/
def mutAppendTrailingGarbage (rng : FuzzerRng) (bytes : ByteArray) : ByteArray × FuzzerRng × String := Id.run do
  let (n, r1) := rng.nextNat 8
  let (garbage, r2) := genRandomBytes r1 (n + 1)
  let mut out := bytes
  for b in garbage do out := out.push b
  (out, r2, s!"append-trailing-garbage+{n + 1}")

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Appends a second, independently generated valid instruction's encoding after the first.
    Like `mutAppendTrailingGarbage` but the trailing bytes are themselves a legitimate
    instruction encoding rather than noise -- a more realistic "decoding the first instruction
    out of a program stream" scenario. -/
def mutAppendSecondInstr (rng : FuzzerRng) (bytes : ByteArray) : ByteArray × FuzzerRng × String :=
  let (instr2, r1) := generateRandomInstruction rng
  let b2 := X86_64Instruction.encode instr2
  let out := bytes ++ b2
  (out, r1, "append-second-instruction")

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Prepends a pseudo-random REX prefix byte (0x40-0x4F) ahead of a valid instruction's
    encoding that does not already start with one. `decodeX86_64Instr` parses at most one REX
    prefix generically before opcode dispatch, so this exercises that shared prefix-parsing
    path across every instruction family, not just whichever ones already had roundtripCases
    with REX set. -/
def mutPrependRex (rng : FuzzerRng) (bytes : ByteArray) : ByteArray × FuzzerRng × String := Id.run do
  if bytes.size > 0 && isRex (bytes.get! 0) then
    (bytes, rng, "prepend-rex (skipped: already REX-prefixed)")
  else
    let (nibble, r1) := rng.nextNat 16
    let rexByte : UInt8 := 0x40 ||| nibble.toUInt8
    let mut out := ByteArray.mk #[rexByte]
    for b in bytes do out := out.push b
    (out, r1, s!"prepend-rex-0x{hexByte rexByte}")

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Flips a single pseudo-random bit within a single pseudo-random byte of a valid encoding.
    Most flips land on an opcode/ModRM/immediate byte and either produce a different, still
    legitimately-decodable instruction, or an unrecognized opcode that `decodeX86_64Instr`
    cleanly rejects -- this is the fuzzer's negative-coverage arm, expected to have a lower
    (but nonzero) success rate than the other categories. -/
def mutFlipByte (rng : FuzzerRng) (bytes : ByteArray) : ByteArray × FuzzerRng × String := Id.run do
  if bytes.size == 0 then (bytes, rng, "flip-byte (skipped: empty)")
  else
    let (idx, r1) := rng.nextNat bytes.size
    let (bits, r2) := r1.nextNat 256
    let old := bytes.get! idx
    (bytes.set! idx (old ^^^ bits.toUInt8), r2, s!"flip-byte@{idx}")

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Truncates a valid encoding by 1..size-1 bytes from the end. Almost every instruction family
    reads a fixed number of trailing operand/immediate bytes after its opcode, so this should
    almost always produce a clean "unexpected end of stream" rejection -- kept as a
    negative-coverage arm, like `mutFlipByte`. -/
def mutTruncate (rng : FuzzerRng) (bytes : ByteArray) : ByteArray × FuzzerRng × String := Id.run do
  if bytes.size <= 1 then (bytes, rng, "truncate (skipped: too short)")
  else
    let (dropRaw, r1) := rng.nextNat (bytes.size - 1)
    let dropN := dropRaw + 1
    let keepLen := bytes.size - dropN
    (bytes.extract 0 keepLen, r1, s!"truncate-to-{keepLen}-of-{bytes.size}")

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- A fully pseudo-random byte buffer of length 1-16, with no relation to any valid encoding.
    Kept as a small minority category: most opcode bytes are unassigned in this decoder's
    (partial) coverage, so this has the lowest expected success rate of any category, but a
    nonzero one -- e.g. a lone 0x50-0x5F byte alone already decodes as a valid PUSH/POP. -/
def genFullyRandomBytes (rng : FuzzerRng) : ByteArray × FuzzerRng × String := Id.run do
  let (nRaw, r1) := rng.nextNat 16
  let (bytes, r2) := genRandomBytes r1 (nRaw + 1)
  (bytes, r2, s!"fully-random-{nRaw + 1}-bytes")

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Dispatches to one of 7 generator/mutator categories. Categories 0-3 are expected to
    (almost) always still decode successfully -- each is checked against a per-category
    non-zero vacuity floor by the caller; categories 4-6 (flip/truncate/fully-random) are not,
    since their whole purpose is negative coverage. -/
def genMutatedCase (rng : FuzzerRng) : ByteArray × FuzzerRng × Nat × String := Id.run do
  let (cat, r1) := rng.nextNat 7
  let (bytes, r2, label) := match cat with
    | 0 => genValidInstrBytes r1
    | 1 => Id.run do
        let (base, r2, _) := genValidInstrBytes r1
        mutAppendTrailingGarbage r2 base
    | 2 => Id.run do
        let (base, r2, _) := genValidInstrBytes r1
        mutAppendSecondInstr r2 base
    | 3 => Id.run do
        let (base, r2, _) := genValidInstrBytes r1
        mutPrependRex r2 base
    | 4 => Id.run do
        let (base, r2, _) := genValidInstrBytes r1
        mutFlipByte r2 base
    | 5 => Id.run do
        let (base, r2, _) := genValidInstrBytes r1
        mutTruncate r2 base
    | _ => genFullyRandomBytes r1
  (bytes, r2, cat, label)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Core stability check: `decodeX86_64Instr b 0 = .ok (r₁, len₁) → decodeX86_64Instr
    (encodeX86_64Instr r₁) 0 = .ok (r₂, len₂) → r₁ = r₂ ∧ len₂ = (encodeX86_64Instr r₁).size`.
    Returns `true` iff `bytes` decoded at all (the vacuity-floor signal the caller
    accumulates), `false` if `decodeX86_64Instr` rejected it outright (expected for most
    mutated bytes), and returns `.error` with full diagnostic detail (both decodes'
    NASM/Lean-source fingerprints, both byte streams) when the property is violated. Returning
    `Except` rather than throwing lets the caller collect every finding in a run instead of
    aborting at the first one. -/
def checkStability (label : String) (bytes : ByteArray) : Except String Bool :=
  match decodeX86_64Instr bytes 0 with
  | .error _ => .ok false
  | .ok (instr1, len1) =>
    let written := X86_64Instruction.encode instr1
    match decodeX86_64Instr written 0 with
    | .error err =>
      .error s!"[FAIL] {label}: decode succeeded ({X86_64Instruction.toNASM instr1}, consumed {len1}/{bytes.size} bytes) but its own re-encoding failed to re-decode: {err}\n  original bytes: {hexPreview bytes}\n  written bytes ({written.size}): {hexPreview written}"
    | .ok (instr2, len2) =>
      let written2 := X86_64Instruction.encode instr2
      let nasm1 := X86_64Instruction.toNASM instr1
      let nasm2 := X86_64Instruction.toNASM instr2
      let lean1 := X86_64Instruction.toLean instr1
      let lean2 := X86_64Instruction.toLean instr2
      if len2 != written.size || written != written2 || nasm1 != nasm2 || lean1 != lean2 then
        .error s!"[FAIL] {label}: PARSER STABILITY VIOLATED -- decode b = r1, decode (encode r1) = r2, r1 ≠ r2\n  r1: {lean1}   (NASM: {nasm1})\n  r2: {lean2}   (NASM: {nasm2})\n  len2={len2} vs write-size={written.size} (full-consumption check)\n  original bytes: {hexPreview bytes}\n  r1's written bytes ({written.size}): {hexPreview written}\n  r2's written bytes ({written2.size}): {hexPreview written2}"
      else
        .ok true

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
/-- Runs the x86-64 decoder/encoder parser-stability fuzzer: deterministic edge cases first,
    then `iterations` randomized structured-mutation cases across the 7 categories in
    `genMutatedCase`. Enforces a vacuity floor: the overall decode-success rate must clear a
    minimum threshold, and each of the 4 "should usually succeed" categories must have
    contributed at least one successful decode. -/
def runStabilityFuzzer (iterations : Nat) (seed : UInt64) : IO Unit := do
  IO.println s!"[+] Starting x86-64 Decoder/Encoder Parser-Stability Fuzzer ({iterations} iterations, seed={seed})..."
  IO.println "    Property: decode b = r1 -> decode (encode r1) = r2 -> r1 = r2 (no external oracle)"

  IO.println "  [*] Stage 1: Testing deterministic edge cases..."
  let edgeCaseBytes : List (String × ByteArray) := [
    ("Empty buffer", ByteArray.empty),
    ("Single RET (0xC3)", ByteArray.mk #[0xC3]),
    ("Single PUSH RAX (0x50)", ByteArray.mk #[0x50]),
    ("Lone REX.W, no opcode", ByteArray.mk #[0x48]),
    ("REX.W + RET", ByteArray.mk #[0x48, 0xC3]),
    ("Unassigned opcode 0x0F alone", ByteArray.mk #[0x0F]),
    ("All-0xFF x4", ByteArray.mk #[0xFF, 0xFF, 0xFF, 0xFF]),
    ("HLT (0xF4)", ByteArray.mk #[0xF4])
  ]
  let mut edgeAttempts := 0
  let mut edgeSuccesses := 0
  let mut violations : Array String := #[]
  for (name, bytes) in edgeCaseBytes do
    edgeAttempts := edgeAttempts + 1
    match checkStability s!"Edge case '{name}'" bytes with
    | .error msg => violations := violations.push msg
    | .ok true => edgeSuccesses := edgeSuccesses + 1
    | .ok false => pure ()
  IO.println s!"      {edgeSuccesses}/{edgeAttempts} edge cases decoded successfully (rest were clean rejections); {violations.size} stability violation(s) so far."

  if iterations == 0 then
    throw (IO.userError "[VACUITY FLOOR TRIPPED] --count 0 requests 0 randomized structured-mutation vectors -- this is a hard FAIL, not a clean PASS (docs/REVIEW.md Law 13 class). Pass --count N with N >= 1.")

  IO.println s!"  [*] Stage 2: Running {iterations} randomized structured-mutation iterations..."
  let mut rng : FuzzerRng := { seed := seed }
  let mut totalAttempts := 0
  let mut totalSuccesses := 0
  let mut catAttempts : Array Nat := Array.replicate 7 0
  let mut catSuccesses : Array Nat := Array.replicate 7 0
  for iter in [0:iterations] do
    let (bytes, nextRng, cat, label) := genMutatedCase rng
    rng := nextRng
    totalAttempts := totalAttempts + 1
    catAttempts := catAttempts.set! cat (catAttempts[cat]! + 1)
    match checkStability s!"Iter {iter} [{label}]" bytes with
    | .error msg => violations := violations.push msg
    | .ok true =>
      totalSuccesses := totalSuccesses + 1
      catSuccesses := catSuccesses.set! cat (catSuccesses[cat]! + 1)
    | .ok false => pure ()
    if (iter + 1) % 200 == 0 then
      IO.println s!"      [Progress] {iter + 1}/{iterations} iterations, {totalSuccesses} successful decodes so far, {violations.size} violation(s)..."

  let catNames : Array String := #["valid-instr", "append-trailing-garbage", "append-second-instruction",
    "prepend-rex", "flip-byte", "truncate", "fully-random"]
  IO.println "  [*] Per-category results:"
  for i in [0:7] do
    let a := catAttempts[i]!
    let s := catSuccesses[i]!
    let pct := if a == 0 then 0.0 else (s.toFloat / a.toFloat) * 100.0
    IO.println s!"      {catNames[i]!}: {s}/{a} decoded ({pct}%)"

  -- Report every finding (STEP 3): print every violation in full before doing anything else.
  if !violations.isEmpty then
    IO.println s!"\n[!!!] {violations.size} PARSER STABILITY VIOLATION(S) FOUND:\n"
    for idx in [0:violations.size] do
      IO.println s!"--- Violation {idx + 1}/{violations.size} ---"
      IO.println violations[idx]!
      IO.println ""
    throw (IO.userError s!"{violations.size} parser stability violation(s) found (see above).")

  let overallPct := (totalSuccesses.toFloat / totalAttempts.toFloat) * 100.0
  IO.println s!"\n[Vacuity] Overall: {totalSuccesses}/{totalAttempts} attempts produced a successful decode ({overallPct}%) that was then checked for stability."
  if totalSuccesses * 5 < totalAttempts then
    throw (IO.userError s!"[VACUITY FLOOR TRIPPED] Only {totalSuccesses}/{totalAttempts} ({overallPct}%) attempts produced a successful decode -- below the 20% floor. Hard FAIL, not a clean PASS.")

  for i in [0:4] do
    if catSuccesses[i]! == 0 then
      throw (IO.userError s!"[VACUITY FLOOR TRIPPED] Category '{catNames[i]!}' (expected to almost always decode successfully) produced 0 successful decodes across {catAttempts[i]!} attempts. Hard FAIL.")

  IO.println s!"\n[+] X86-64 PARSER-STABILITY FUZZER COMPLETE: {totalAttempts + edgeAttempts} total attempts, {totalSuccesses + edgeSuccesses} successful decodes checked, 0 stability violations."
  IO.println "[Evidentiary Scope] Internal property only -- no external oracle needed or used. Complements encoding_fuzzer (NASM) and x86_fuzzer (silicon), neither of which cover every encodable form."

end Gasm.Targets.X86_64.StabilityFuzzer

open Gasm.Targets.X86_64.StabilityFuzzer

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
def main (args : List String) : IO UInt32 := do
  let mut iters := 1000
  let mut seed : UInt64 := 20260828
  let mut i := 0
  while i < args.length do
    match args[i]! with
    | "--count" =>
      if i + 1 < args.length then
        iters := args[i + 1]!.toNat?.getD 1000
        i := i + 2
      else i := i + 1
    | "--seed" =>
      if i + 1 < args.length then
        seed := args[i + 1]!.toNat?.getD 20260828 |>.toUInt64
        i := i + 2
      else i := i + 1
    | _ => i := i + 1

  IO.println "================================================================================"
  IO.println "            GASM X86-64 DECODER/ENCODER PARSER-STABILITY FUZZER                 "
  IO.println "        (No external oracle -- self-referential decode/encode/decode property)   "
  IO.println "================================================================================"

  try
    runStabilityFuzzer iters seed
    return 0
  catch e =>
    IO.eprintln (toString e)
    return 1
