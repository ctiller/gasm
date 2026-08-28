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
import Gasm.Targets.ELF.Parser
import Gasm.Targets.Linux.Emitter
import Gasm.Targets.Linux.Linker
import Spikes.Spike1Hello.Linux.Program
import Spikes.Spike2Fibonacci.Linux.Program
import Spikes.Spike3SortLines.Linux.Program
import Spikes.Spike4HttpServer.Linux.Program
import Spikes.Spike5Gzip.Linux.Program

/-
Spikes/Common/ElfStabilityFuzzer.lean - Parser-stability fuzzer for `Gasm.Targets.ELF.Parser`

WHY THIS LIVES UNDER `Spikes/Common/`, NOT `Gasm/Targets/ELF/`: this fuzzer's whole point is
to check the parser against the REAL bytes the five Linux Spikes emit (`LinuxExecutable.emit`
on each Spike's own `spikeNExecutable`), so it must import every `Spikes.SpikeN*.Linux.Program`
module. `Gasm/` never depends downward on `Spikes/` anywhere else in this tree (confirmed by
inspection of every other `Gasm.Targets.*.StabilityFuzzer`, none of which import `Spikes`);
`Spikes/Common/` is this tree's own established location for cross-spike shared tooling (see
`Spikes/Common/WasmHostRunner.lean`), so this file follows that precedent rather than inventing
a new layering.

THE PROPERTY CHECKED, and why it is phrased as `parse (write p) = .ok p` rather than the
"parse b, write, parse again, compare" phrasing `Stdlib/Png/StabilityFuzzer.lean` uses: the two
are equivalent whenever the FIRST parse of `b` already succeeded (which is exactly when the
PNG-style property is non-vacuous) -- if `parse b = .ok p` and `parse (write p) = .ok p` (this
file's `checkWriteParseFixpoint`), then in particular `parse (write p) = .ok p`, satisfying
`parse b = .ok r1 -> parse (write r1) = .ok r2 -> r1 = r2` with `r1 = r2 = p` directly. Phrasing
it as a direct fixpoint against the ALREADY-KNOWN value `p` (rather than an independently
obtained second parse `r2`) is what lets `checkWriteParseFixpoint` be reused verbatim against
STRUCTURED values this file constructs directly (the `field-mutation` category below), not only
against values obtained by parsing some `b` in the first place.

CONVENTIONS FOLLOWED FROM `Stdlib/Png/StabilityFuzzer.lean` (the freshest example this task
was pointed at): a per-fuzzer, non-shared Xorshift64 RNG (`ElfFuzzRng`, same shape as
`PngFuzzRng`/`Stdlib.Zlib.GzipFuzzer.FuzzRng`); structured mutation rather than uniform noise
(every category either calls the REAL writer, `Gasm.Targets.Linux.emitELF64Executable`, or
mutates a genuinely-parsed structured value -- never raw noise alone, except the two
deliberately-adversarial byte-level categories, which are exempted from the vacuity floor for
the same reason `Stdlib/Png/StabilityFuzzer.lean`'s `flip-byte` category is); a non-zero vacuity
floor (`--count 0` is a hard FAIL, not a vacuous PASS) both overall and per "should usually
succeed" category; every finding reported, not just the first.
-/

namespace Spikes.Common.ElfStabilityFuzzer

open Gasm.Core
open Gasm.Targets.ELF
open Gasm.Targets.Linux

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Deterministic Xorshift64 PRNG state, mirroring `Stdlib.Png.PngFuzzRng`'s shape. Kept local
    rather than shared, per this codebase's per-fuzzer-RNG convention. -/
structure ElfFuzzRng where
  state : UInt64
  deriving Inhabited

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Advances the RNG and produces the next `UInt64`. -/
def ElfFuzzRng.next (rng : ElfFuzzRng) : UInt64 × ElfFuzzRng :=
  let x := rng.state
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  (x, { state := if x == 0 then 88172645463325252 else x })

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Selects a pseudo-random natural number in `[0, bound)`; `bound = 0` always yields `0`. -/
def ElfFuzzRng.nextNat (bound : Nat) (rng : ElfFuzzRng) : Nat × ElfFuzzRng :=
  if bound == 0 then (0, rng)
  else
    let (v, nxt) := rng.next
    (v.toNat % bound, nxt)

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Generates `n` pseudo-random bytes. -/
def genRandomBytes (rng : ElfFuzzRng) (n : Nat) : ByteArray × ElfFuzzRng := Id.run do
  let mut cur := rng
  let mut out := ByteArray.empty
  for _ in [0:n] do
    let (v, nxt) := cur.next
    cur := nxt
    out := out.push (v &&& 0xFF).toUInt8
  (out, cur)

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Formats a single byte as a 2-digit lowercase hex string. Small, self-contained diagnostic
    utility -- kept local rather than imported from `Stdlib.Png.StabilityFuzzer` (which has an
    identically-shaped one) to avoid an otherwise-unjustified `Spikes -> Stdlib.Png` dependency
    for ten lines of hex formatting. -/
def byteHex (b : UInt8) : String :=
  let s := String.ofList (Nat.toDigits 16 b.toNat)
  if s.length < 2 then "0" ++ s else s

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Renders a bounded hex preview of a `ByteArray` for fuzzer failure diagnostics. -/
def hexPreview (bytes : ByteArray) (maxLen : Nat := 96) : String := Id.run do
  let n := Nat.min bytes.size maxLen
  let mut s := ""
  for i in [0:n] do
    s := s ++ byteHex (bytes.get! i) ++ " "
  if bytes.size > maxLen then s ++ s!"... ({bytes.size} bytes total)" else s

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Generates a fresh, real ELF64 executable via the actual writer
    (`Gasm.Targets.Linux.emitELF64Executable`) for a pseudo-random small `.text`/`.rodata`
    payload and a pseudo-random page-aligned base address -- this fuzzer's "valid artifact"
    baseline, exactly as `Stdlib.Png.StabilityFuzzer.genValidImageBytes` is for PNG. -/
def genValidRandomBytes (rng : ElfFuzzRng) : ByteArray × ElfFuzzRng × String := Id.run do
  let (baseIdx, r1) := rng.nextNat 16
  let base : Address := (0x400000 : UInt64) + baseIdx.toUInt64 * 0x1000
  let (textSize, r2) := r1.nextNat 64
  let (rodataSize, r3) := r2.nextNat 64
  let (textBytes, r4) := genRandomBytes r3 (textSize + 1)
  let (rodataBytes, r5) := genRandomBytes r4 rodataSize
  let bytes := emitELF64Executable base textBytes rodataBytes
  (bytes, r5, s!"valid-random base=0x{String.ofList (Nat.toDigits 16 base.toNat)} textSize={textBytes.size} rodataSize={rodataBytes.size}")

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Threads `rng` through `f` across a list, mutating each element with a fresh RNG draw.
    Structural recursion on the list: total. -/
def mapWithRng {α : Type} (f : ElfFuzzRng → α → α × ElfFuzzRng) (rng : ElfFuzzRng) :
    List α → List α × ElfFuzzRng
  | [] => ([], rng)
  | x :: rest =>
    let (x', r1) := f rng x
    let (restMapped, r2) := mapWithRng f r1 rest
    (x' :: restMapped, r2)

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Mutates a program header's `p_align` field to a pseudo-random value. `p_align` is not
    consulted by `Gasm.Targets.ELF.Parser`'s validation or extraction logic (only `p_offset`/
    `p_filesz` are), so this is a safe, layout-preserving structured mutation. -/
def mutatePhdr (rng : ElfFuzzRng) (ph : Gasm.Targets.ELF.Elf64_Phdr) : Gasm.Targets.ELF.Elf64_Phdr × ElfFuzzRng :=
  let (v, r1) := rng.next
  ({ ph with p_align := v }, r1)

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Mutates a section header's `sh_addralign` field to a pseudo-random value. Not consulted by
    `Gasm.Targets.ELF.Parser`'s validation or extraction logic (only `sh_type`/`sh_offset`/
    `sh_size`/`sh_name` are), so this is a safe, layout-preserving structured mutation. -/
def mutateShdr (rng : ElfFuzzRng) (sh : Gasm.Targets.ELF.Elf64_Shdr) : Gasm.Targets.ELF.Elf64_Shdr × ElfFuzzRng :=
  let (v, r1) := rng.next
  ({ sh with sh_addralign := v }, r1)

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Structured mutation category: given an already-parsed `Elf64Parsed` (from a real writer
    call), perturbs `e_flags` plus every program/section header's non-layout-affecting field.
    This exercises `serializeElf64Parsed`/`parseElf64` on values this codebase's own writer
    never directly produces (it never varies these fields), the same "attacker/independent-
    construction-chosen values explore paths the writer's own constructors never do" rationale
    `Stdlib/Png/StabilityFuzzer.lean`'s `genCustomHeaderBytes` documents for PNG. -/
def mutateFieldsStructured (rng : ElfFuzzRng) (p : Elf64Parsed) : Elf64Parsed × ElfFuzzRng :=
  let (flagsVal, r1) := rng.next
  let (phdrs', r2) := mapWithRng mutatePhdr r1 p.phdrs
  let (shdrs', r3) := mapWithRng mutateShdr r2 p.shdrs
  ({ p with ehdr := { p.ehdr with e_flags := flagsVal.toUInt32 }, phdrs := phdrs', shdrs := shdrs' }, r3)

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Core stability check: `parse (write p) = .ok p`, for an already-parsed `p` -- see this
    module's header comment for why this phrasing is equivalent to, and strictly more reusable
    than, the "parse b, write, parse again, compare the two parses" phrasing. Returns
    `.ok true` if the fixpoint holds, and `.error` with full diagnostic detail (both byte
    streams, plus which field disagrees) when it is violated. Never throws -- callers collect
    every finding across a run instead of aborting at the first one. -/
def checkWriteParseFixpoint (label : String) (p : Elf64Parsed) : Except String Bool :=
  let bytes2 := serializeElf64Parsed p
  match parseElf64 bytes2 with
  | .error err =>
    .error s!"[FAIL] {label}: PARSER STABILITY VIOLATED -- serializing a successfully-parsed \
value and re-parsing it FAILED: {repr err}\n  rewritten bytes ({bytes2.size}): {hexPreview bytes2}"
  | .ok p2 =>
    if _h : p = p2 then
      .ok true
    else
      let diffDesc :=
        if p.ehdr != p2.ehdr then "ELF header differs after a write/parse cycle"
        else if p.phdrs.length != p2.phdrs.length then
          s!"program header count differs: {p.phdrs.length} vs {p2.phdrs.length}"
        else if p.phdrs != p2.phdrs then "a program header entry differs"
        else if p.shdrs.length != p2.shdrs.length then
          s!"section header count differs: {p.shdrs.length} vs {p2.shdrs.length}"
        else if p.shdrs != p2.shdrs then "a section header entry differs"
        else "section payload bytes differ (headers and counts all agree)"
      .error s!"[FAIL] {label}: PARSER STABILITY VIOLATED -- parse (write p) != p\n  {diffDesc}\n\
  rewritten bytes ({bytes2.size}): {hexPreview bytes2}"

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Parses `bytes`; a clean rejection is `.ok false` (not a violation -- most mutated bytes in
    the adversarial categories are expected to be rejected), and a successful parse is checked
    against `checkWriteParseFixpoint`. -/
def checkBytesRoundtrip (label : String) (bytes : ByteArray) : Except String Bool :=
  match parseElf64 bytes with
  | .error _ => .ok false
  | .ok p => checkWriteParseFixpoint label p

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Dispatches to one of 5 generator/mutator categories, returning the resulting bytes to feed
    `checkBytesRoundtrip`. Categories 0-2 are expected to (almost) always still parse
    successfully -- checked against a per-category non-zero vacuity floor by the caller;
    categories 3-4 (truncation, single-byte flip) are the deliberately-adversarial arm and are
    exempt, mirroring `Stdlib/Png/StabilityFuzzer.lean`'s `flip-byte` category. -/
def genMutatedCase (rng : ElfFuzzRng) : ByteArray × ElfFuzzRng × Nat × String :=
  let (cat, r1) := rng.nextNat 5
  match cat with
  | 0 =>
    let (bytes, r2, desc) := genValidRandomBytes r1
    (bytes, r2, cat, desc)
  | 1 =>
    let (baseBytes, r2, _) := genValidRandomBytes r1
    match parseElf64 baseBytes with
    | .error _ => (baseBytes, r2, cat, "field-mutation (skipped: base parse failed)")
    | .ok p =>
      let (p', r3) := mutateFieldsStructured r2 p
      (serializeElf64Parsed p', r3, cat, "field-mutation")
  | 2 =>
    let (baseBytes, r2, _) := genValidRandomBytes r1
    let (n, r3) := r2.nextNat 32
    let (garbage, r4) := genRandomBytes r3 (n + 1)
    (baseBytes ++ garbage, r4, cat, s!"append-trailing-garbage+{n + 1}")
  | 3 =>
    let (baseBytes, r2, _) := genValidRandomBytes r1
    let (kRaw, r3) := r2.nextNat (Nat.max 1 baseBytes.size)
    let cut := Nat.max 1 kRaw
    let newSize := if baseBytes.size > cut then baseBytes.size - cut else 0
    (baseBytes.extract 0 newSize, r3, cat, s!"truncate-suffix-{cut}")
  | _ =>
    let (baseBytes, r2, _) := genValidRandomBytes r1
    if baseBytes.size == 0 then
      (baseBytes, r2, cat, "flip-byte (skipped: empty)")
    else
      let (idx, r3) := r2.nextNat baseBytes.size
      let (bits, r4) := r3.nextNat 256
      let old := baseBytes.get! idx
      (baseBytes.set! idx (old ^^^ bits.toUInt8), r4, cat, s!"flip-byte@{idx}")

/- REF: docs/SPIKES.md#4-continuous-spike-testing-verification-protocol -/
/-- The real ELF64 bytes every Linux Spike emits, paired with a human label and the exact
    `.text`/`.rodata` payload the writer was built from (for the direct emitter-defect check
    below) -- the deliverable this task's brief specifically asks for: parsing this project's
    OWN emitted binaries, not just synthetic writer output. -/
def realSpikeExecutables : List (String × LinuxExecutable) :=
  [ ("spike1_hello", Spikes.Spike1Hello.Linux.spike1Executable)
  , ("spike2_fibonacci", Spikes.Spike2Fibonacci.Linux.spike2Executable)
  , ("spike3_sort_lines", Spikes.Spike3SortLines.Linux.spike3Executable)
  , ("spike4_http_server", Spikes.Spike4HttpServer.Linux.spike4Executable)
  , ("spike5_gzip", Spikes.Spike5Gzip.Linux.spike5Executable)
  , ("spike5_gunzip", Spikes.Spike5Gzip.Linux.spike5GunzipExecutable)
  ]

/- REF: docs/SPIKES.md#4-continuous-spike-testing-verification-protocol -/
/-- Checks one real Spike's emitted ELF64 bytes against three independent things: (1) it parses
    at all, (2) the parser-stability fixpoint holds, and (3) the parsed `.text`/`.rodata`
    section payloads and entry point are byte-for-byte/value-for-value identical to what
    `Gasm.Targets.Linux.emitELF64Executable` was actually handed -- a mismatch here is a direct,
    precise emitter-vs-parser divergence report, exactly what this task asks to surface as the
    highest-value possible finding. Returns every finding (never stops at the first). -/
def checkRealSpike (name : String) (exe : LinuxExecutable) : List String := Id.run do
  let bytes := exe.emit
  let mut findings : List String := []
  match parseElf64 bytes with
  | .error err =>
    findings := findings ++
      [s!"[CRITICAL] {name}: this project's OWN emitted ELF64 binary FAILED TO PARSE: \
{repr err}\n  bytes ({bytes.size}): {hexPreview bytes}"]
  | .ok p =>
    match checkWriteParseFixpoint name p with
    | .error msg => findings := findings ++ [msg]
    | .ok _ => pure ()
    match p.sectionNamed ".text" with
    | none => findings := findings ++ [s!"[DEFECT] {name}: no '.text' section resolved by name in the parsed binary"]
    | some textData =>
      if textData != exe.textBytes then
        findings := findings ++
          [s!"[DEFECT] {name}: parsed '.text' section payload ({textData.size} bytes) does not \
match the exact textBytes ({exe.textBytes.size} bytes) emitELF64Executable was called with -- \
EMITTER DEFECT\n  parsed:   {hexPreview textData}\n  expected: {hexPreview exe.textBytes}"]
    match p.sectionNamed ".rodata" with
    | none => findings := findings ++ [s!"[DEFECT] {name}: no '.rodata' section resolved by name in the parsed binary"]
    | some rodataData =>
      if rodataData != exe.rodataBytes then
        findings := findings ++
          [s!"[DEFECT] {name}: parsed '.rodata' section payload ({rodataData.size} bytes) does \
not match the exact rodataBytes ({exe.rodataBytes.size} bytes) emitELF64Executable was called \
with -- EMITTER DEFECT\n  parsed:   {hexPreview rodataData}\n  expected: {hexPreview exe.rodataBytes}"]
    let shstrtabSize := (buildShStrTab [".text", ".rodata", ".shstrtab"]).1.size
    let layout := computeElf64Layout exe.imageBase exe.textBytes.size exe.rodataBytes.size shstrtabSize
    if p.ehdr.e_entry != layout.textVma then
      findings := findings ++
        [s!"[DEFECT] {name}: parsed entry point (e_entry=0x{String.ofList (Nat.toDigits 16 p.ehdr.e_entry.toNat)}) \
does not match the layout's computed .text VMA (0x{String.ofList (Nat.toDigits 16 layout.textVma.toNat)}) -- EMITTER DEFECT"]
  findings

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Runs the ELF64 parser-stability fuzzer: deterministic malformed-input edge cases, every
    real Spike's emitted binary, then `iterations` randomized structured-mutation cases across
    the 5 categories in `genMutatedCase`. Enforces a vacuity floor (TC17/T11-b class): `--count
    0` is a hard FAIL, not a vacuous PASS; overall parse-success rate must clear a minimum
    threshold; each "should usually succeed" category (0-2) must have contributed at least one
    successful parse. -/
def runElfStabilityFuzzer (iterations : Nat) (seed : UInt64) : IO Unit := do
  IO.println s!"[+] Starting ELF64 Parser-Stability Fuzzer ({iterations} iterations, seed={seed})..."
  IO.println "    Property: parse b = .ok r1 -> parse (write r1) = .ok r2 -> r1 = r2 (no external oracle)"

  let mut violations : Array String := #[]

  -- Stage 1a: malformed-input edge cases -- must be a CLEAN, typed rejection, never a panic.
  IO.println "  [*] Stage 1a: Testing malformed-input edge cases (clean rejection expected)..."
  let malformedCases : List (String × ByteArray) := [
    ("Empty buffer", ByteArray.empty),
    ("Single zero byte", ByteArray.mk #[0]),
    ("64 zero bytes (structurally sized, all-zero -- bad magic)", ByteArray.mk (Array.replicate 64 (0 : UInt8))),
    ("10-byte truncated buffer", ByteArray.mk (Array.replicate 10 (0xFF : UInt8)))
  ]
  let mut cleanRejections := 0
  for (name, bytes) in malformedCases do
    match parseElf64 bytes with
    | .error _ => cleanRejections := cleanRejections + 1
    | .ok _ =>
      violations := violations.push
        s!"[FAIL] Edge case '{name}': expected a clean rejection, but parseElf64 SUCCEEDED on malformed input."
  IO.println s!"      {cleanRejections}/{malformedCases.length} malformed inputs cleanly rejected."

  -- Stage 1b: every real Spike's actual emitted binary -- the direct "read our own output" check.
  IO.println "  [*] Stage 1b: Testing every real Linux Spike's emitted ELF64 binary..."
  let mut spikeChecked := 0
  for (name, exe) in realSpikeExecutables do
    let findings := checkRealSpike name exe
    spikeChecked := spikeChecked + 1
    violations := violations ++ findings.toArray
  IO.println s!"      {spikeChecked}/{realSpikeExecutables.length} real Spike binaries checked ({violations.size} finding(s) so far)."

  -- Vacuity floor (Law 13(4) class): 0 randomized iterations must not print a blanket pass.
  if iterations == 0 then
    throw (IO.userError "[VACUITY FLOOR TRIPPED] --count 0 requests 0 randomized structured-mutation vectors -- this is a hard FAIL, not a clean PASS (TCB.md T11-b class). Pass --count N with N >= 1.")

  IO.println s!"  [*] Stage 2: Running {iterations} randomized structured-mutation iterations..."
  let mut rng : ElfFuzzRng := { state := seed }
  let mut totalAttempts := 0
  let mut totalSuccesses := 0
  let mut catAttempts : Array Nat := Array.replicate 5 0
  let mut catSuccesses : Array Nat := Array.replicate 5 0
  for iter in [0:iterations] do
    let (bytes, nextRng, cat, label) := genMutatedCase rng
    rng := nextRng
    totalAttempts := totalAttempts + 1
    catAttempts := catAttempts.set! cat (catAttempts[cat]! + 1)
    match checkBytesRoundtrip s!"Iter {iter} [{label}]" bytes with
    | .error msg => violations := violations.push msg
    | .ok true =>
      totalSuccesses := totalSuccesses + 1
      catSuccesses := catSuccesses.set! cat (catSuccesses[cat]! + 1)
    | .ok false => pure ()
    if (iter + 1) % 100 == 0 then
      IO.println s!"      [Progress] {iter + 1}/{iterations} iterations, {totalSuccesses} successful parses so far, {violations.size} violation(s)..."

  let catNames : Array String := #["valid-random", "field-mutation", "append-trailing-garbage",
    "truncate-suffix", "flip-byte"]
  IO.println "  [*] Per-category results:"
  for i in [0:5] do
    let a := catAttempts[i]!
    let s := catSuccesses[i]!
    let pct := if a == 0 then 0.0 else (s.toFloat / a.toFloat) * 100.0
    IO.println s!"      {catNames[i]!}: {s}/{a} parsed ({pct}%)"

  -- Report every finding: if the property was violated anywhere (including Stage 1's edge
  -- cases and real-spike checks), print every occurrence in full before doing anything else.
  if !violations.isEmpty then
    IO.println s!"\n[!!!] {violations.size} FINDING(S):\n"
    for idx in [0:violations.size] do
      IO.println s!"--- Finding {idx + 1}/{violations.size} ---"
      IO.println violations[idx]!
      IO.println ""
    throw (IO.userError s!"{violations.size} finding(s) found (see above) -- see docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer for the format this parser is supposed to implement.")

  -- Vacuity floor: overall parse-success rate.
  let overallPct := (totalSuccesses.toFloat / totalAttempts.toFloat) * 100.0
  IO.println s!"\n[Vacuity] Overall: {totalSuccesses}/{totalAttempts} attempts produced a successful parse ({overallPct}%) that was then checked for stability."
  if totalSuccesses * 5 < totalAttempts then
    throw (IO.userError s!"[VACUITY FLOOR TRIPPED] Only {totalSuccesses}/{totalAttempts} ({overallPct}%) attempts produced a successful parse -- below the 20% floor. A run in which almost nothing parses tests almost nothing, even though it reports 0 violations. This is a hard FAIL, not a clean PASS.")

  -- Vacuity floor: each "should usually succeed" category (0-2) must have contributed at
  -- least one successful parse -- mirroring GzipFuzzer's/PngStabilityFuzzer's both-paths-
  -- exercised check.
  for i in [0:3] do
    if catSuccesses[i]! == 0 then
      throw (IO.userError s!"[VACUITY FLOOR TRIPPED] Category '{catNames[i]!}' (expected to almost always parse successfully) produced 0 successful parses across {catAttempts[i]!} attempts -- this category's coverage is vacuous. Hard FAIL.")

  IO.println s!"\n[+] ELF64 PARSER-STABILITY FUZZER COMPLETE: {totalAttempts + malformedCases.length + realSpikeExecutables.length} total attempts, {totalSuccesses + spikeChecked} successful parses checked, 0 violations."
  IO.println "[Evidentiary Scope] Internal property + this project's own 6 real emitted Linux Spike binaries -- no external oracle needed or used."

end Spikes.Common.ElfStabilityFuzzer

open Spikes.Common.ElfStabilityFuzzer

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
def main (args : List String) : IO UInt32 := do
  let mut iters := 300
  let mut seed : UInt64 := 20260828
  let mut i := 0
  while i < args.length do
    match args[i]! with
    | "--count" =>
      if i + 1 < args.length then
        iters := args[i + 1]!.toNat?.getD 300
        i := i + 2
      else i := i + 1
    | "--seed" =>
      if i + 1 < args.length then
        seed := args[i + 1]!.toNat?.getD 20260828 |>.toUInt64
        i := i + 2
      else i := i + 1
    | _ => i := i + 1

  IO.println "================================================================================"
  IO.println "               GASM ELF64 PARSER-STABILITY FUZZER                               "
  IO.println "        (No external oracle -- self-referential parse/write/parse property)      "
  IO.println "================================================================================"

  try
    runElfStabilityFuzzer iters seed
    return 0
  catch e =>
    IO.eprintln (toString e)
    return 1
