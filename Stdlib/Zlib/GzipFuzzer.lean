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
import Stdlib.Gzip
import Stdlib.Zlib.Spec

namespace Stdlib.Zlib

open Stdlib.Gzip

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Simple deterministic Pseudo-Random Number Generator (Xorshift64). -/
structure FuzzRng where
  state : UInt64
  deriving Inhabited

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Advances RNG and produces next UInt64. -/
def FuzzRng.next (rng : FuzzRng) : (UInt64 × FuzzRng) :=
  let x := rng.state
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  (x, { state := if x == 0 then 88172645463325252 else x })

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Generates a deterministic byte array of length `len` based on test pattern type. -/
def generateTestVector (rng : FuzzRng) (patternType : Nat) (len : Nat) : (ByteArray × FuzzRng) :=
  Id.run do
    let mut curRng := rng
    let mut bytes := ByteArray.empty
    match patternType % 5 with
    | 0 =>
      -- Pattern 0: Repeated single byte
      let (val, nextRng) := curRng.next
      curRng := nextRng
      let b := (val &&& 0xFF).toUInt8
      for _ in [0:len] do bytes := bytes.push b
    | 1 =>
      -- Pattern 1: Repeated short phrase (2 to 16 bytes)
      let (phraseLenRaw, r1) := curRng.next
      let phraseLen := (phraseLenRaw.toNat % 15) + 2
      let mut phrase := ByteArray.empty
      curRng := r1
      for _ in [0:phraseLen] do
        let (pb, r2) := curRng.next
        curRng := r2
        phrase := phrase.push (pb &&& 0xFF).toUInt8
      for i in [0:len] do
        bytes := bytes.push (phrase.get! (i % phrase.size))
    | 2 =>
      -- Pattern 2: Sequential ramp
      let (startVal, nextRng) := curRng.next
      curRng := nextRng
      for i in [0:len] do
        bytes := bytes.push (((startVal.toNat + i) &&& 0xFF).toUInt8)
    | 3 =>
      -- Pattern 3: High-entropy pseudo-random bytes
      for _ in [0:len] do
        let (rb, nextRng) := curRng.next
        curRng := nextRng
        bytes := bytes.push (rb &&& 0xFF).toUInt8
    | _ =>
      -- Pattern 4: Mixed text-like printable ASCII
      for _ in [0:len] do
        let (rb, nextRng) := curRng.next
        curRng := nextRng
        let ascii := 32 + (rb.toNat % 95)
        bytes := bytes.push ascii.toUInt8
    (bytes, curRng)

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Resolves a usable Python 3 interpreter on the host system by probing candidate command
    names. Per Law 13(4) ("an oracle that cannot run must fail the run; it must never no-op,
    skip, or synthesize results"), this returns `Except.error` — never a blind best-effort
    guess — when no candidate responds, so callers are forced to abort rather than proceed
    into a subprocess spawn that would otherwise throw an unlabeled, undiagnosable IO
    exception deep inside the fuzzer. -/
def findPythonPath (overridePath : Option String := none) : IO (Except String String) := do
  if let some p := overridePath then
    return .ok p
  let candidates := ["python3", "python", "py"]
  for p in candidates do
    let isAvail ← try
      let proc ← IO.Process.spawn {
        cmd := p
        args := #["--version"]
        stdout := .piped
        stderr := .piped
      }
      let code ← proc.wait
      pure (code == 0)
    catch _ =>
      pure false
    if isAvail then
      return .ok p
  return .error s!"No usable Python interpreter found on PATH (tried: {String.intercalate ", " candidates}). The GZIP differential fuzzer's oracle is the CPython standard-library `gzip` module; without a working interpreter it cannot validate anything and must not report success. Install Python 3 and ensure it is on PATH."

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Best-effort removal of a temporary file; failures to remove (e.g. already absent) are
    not oracle failures and must not mask the real result. -/
def removeTmpFile (path : String) : IO Unit :=
  try IO.FS.removeFile path catch _ => pure ()

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Invokes public Python standard library gunzip oracle on a gasm-compressed gzip stream.
    Fails loudly (`Except.error` with the subprocess's actual captured stderr, never the
    compressed binary misread as text) on any oracle malfunction, and always cleans up its
    own temporary files regardless of outcome. -/
def runOracleGunzip (pythonPath : String) (gasmGzBytes : ByteArray) (tmpPrefix : String := ".tmp_gasm_gunzip") : IO (Except String ByteArray) := do
  let tmpGz := s!"{tmpPrefix}.gz"
  let tmpOut := s!"{tmpPrefix}.bin"
  IO.FS.writeBinFile tmpGz gasmGzBytes
  let pyScript := s!"import gzip; open('{tmpOut}', 'wb').write(gzip.decompress(open('{tmpGz}', 'rb').read()))"
  let result ← try
    let proc ← IO.Process.spawn {
      cmd := pythonPath
      args := #["-c", pyScript]
      stdout := .piped
      stderr := .piped
    }
    let exitCode ← proc.wait
    if exitCode != 0 then
      let stderrOut ← proc.stderr.readToEnd
      pure (Except.error s!"Python gunzip oracle failed with exit code {exitCode}:\n{stderrOut}")
    else
      let decompBytes ← IO.FS.readBinFile tmpOut
      pure (Except.ok decompBytes)
  catch e =>
    pure (Except.error s!"Python gunzip oracle subprocess could not be executed (interpreter '{pythonPath}'): {e}")
  removeTmpFile tmpGz
  removeTmpFile tmpOut
  return result

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Invokes public Python standard library gzip oracle to produce a gzip stream for gasm
    decompression. Fails loudly with the subprocess's actual captured stderr on any oracle
    malfunction, and always cleans up its own temporary files regardless of outcome. -/
def runOracleGzip (pythonPath : String) (rawBytes : ByteArray) (tmpPrefix : String := ".tmp_gasm_gzip") : IO (Except String ByteArray) := do
  let tmpRaw := s!"{tmpPrefix}.raw"
  let tmpGz := s!"{tmpPrefix}.gz"
  IO.FS.writeBinFile tmpRaw rawBytes
  let pyScript := s!"import gzip; open('{tmpGz}', 'wb').write(gzip.compress(open('{tmpRaw}', 'rb').read()))"
  let result ← try
    let proc ← IO.Process.spawn {
      cmd := pythonPath
      args := #["-c", pyScript]
      stdout := .piped
      stderr := .piped
    }
    let exitCode ← proc.wait
    if exitCode != 0 then
      let stderrOut ← proc.stderr.readToEnd
      pure (Except.error s!"Python gzip oracle failed with exit code {exitCode}:\n{stderrOut}")
    else
      let gzBytes ← IO.FS.readBinFile tmpGz
      pure (Except.ok gzBytes)
  catch e =>
    pure (Except.error s!"Python gzip oracle subprocess could not be executed (interpreter '{pythonPath}'): {e}")
  removeTmpFile tmpRaw
  removeTmpFile tmpGz
  return result

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Invokes the public Python standard library zlib oracle to inflate a gasm-produced
    DEFLATE bitstream: `wbitsRaw = true` decodes a raw RFC 1951 stream (`wbits = -15`),
    `false` decodes an RFC 1950 zlib container (`wbits = 15`). This is the direct
    conformance oracle for `Stdlib.Zlib.compress`'s fixed- AND dynamic-Huffman block
    emission — CPython's `zlib` is real-world inflate, so acceptance here is evidence the
    encoder emits conformant DEFLATE, not merely streams our own decoder tolerates.
    Fails loudly with the subprocess's captured stderr on any oracle malfunction and always
    cleans up its temporary files. -/
def runOracleInflate (pythonPath : String) (compBytes : ByteArray) (wbitsRaw : Bool)
    (tmpPrefix : String := ".tmp_gasm_inflate") : IO (Except String ByteArray) := do
  let tmpIn := s!"{tmpPrefix}.bin"
  let tmpOut := s!"{tmpPrefix}.out"
  IO.FS.writeBinFile tmpIn compBytes
  let wbits := if wbitsRaw then "-15" else "15"
  let pyScript := s!"import zlib; d = zlib.decompressobj(wbits={wbits}); out = d.decompress(open('{tmpIn}', 'rb').read()) + d.flush(); assert d.eof, 'stream not terminated'; open('{tmpOut}', 'wb').write(out)"
  let result ← try
    let proc ← IO.Process.spawn {
      cmd := pythonPath
      args := #["-c", pyScript]
      stdout := .piped
      stderr := .piped
    }
    let exitCode ← proc.wait
    if exitCode != 0 then
      let stderrOut ← proc.stderr.readToEnd
      pure (Except.error s!"Python zlib inflate oracle failed with exit code {exitCode}:\n{stderrOut}")
    else
      let outBytes ← IO.FS.readBinFile tmpOut
      pure (Except.ok outBytes)
  catch e =>
    pure (Except.error s!"Python zlib inflate oracle subprocess could not be executed (interpreter '{pythonPath}'): {e}")
  removeTmpFile tmpIn
  removeTmpFile tmpOut
  return result

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Cross-checks one vector through `Stdlib.Zlib.compress` (raw RFC 1951, fixed-or-dynamic
    block selected by exact bit cost) and `zlibCompress` (RFC 1950 container) against the
    Python zlib oracle, plus the in-Lean `decompress` roundtrip — which exercises
    `decodeDynamicTables` whenever the dynamic block was chosen. Returns whether the
    dynamic-Huffman (BTYPE=10) block type was chosen for this vector so the caller can
    enforce a both-paths-exercised vacuity floor. -/
def crossCheckDeflate (pythonPath : String) (label : String) (raw : ByteArray) : IO Bool := do
  let (usedDynamic, deflated) := compressPlan raw
  let blockKind := if usedDynamic then "dynamic" else "fixed"
  match ← runOracleInflate pythonPath deflated true with
  | .error err => throw (IO.userError s!"[FAIL] {label}: gasm DEFLATE ({blockKind} block) -> Python zlib raw inflate failed: {err}")
  | .ok out =>
    if out != raw then
      throw (IO.userError s!"[FAIL] {label}: gasm DEFLATE ({blockKind} block) -> Python zlib raw inflate content mismatch (expected {raw.size} bytes, got {out.size})")
  let zc := zlibCompress raw
  match ← runOracleInflate pythonPath zc false with
  | .error err => throw (IO.userError s!"[FAIL] {label}: gasm zlibCompress ({blockKind} block) -> Python zlib inflate failed: {err}")
  | .ok out =>
    if out != raw then
      throw (IO.userError s!"[FAIL] {label}: gasm zlibCompress ({blockKind} block) -> Python zlib inflate content mismatch")
  match decompress deflated with
  | .error e => throw (IO.userError s!"[FAIL] {label}: gasm decompress rejected gasm compress {blockKind}-block output: {repr e}")
  | .ok out =>
    if out != raw then
      throw (IO.userError s!"[FAIL] {label}: gasm decompress(compress) {blockKind}-block content mismatch")
  return usedDynamic

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Runs cross-differential fuzzing iterations in both directions against the Python
    `pythonPath` interpreter oracle. -/
def runGzipDifferentialFuzzer (pythonPath : String) (iterations : Nat := 100) (seed : UInt64 := 42424242) : IO Unit := do
  IO.println s!"[+] Starting GZIP Dual-Direction Cross-Differential Fuzzer ({iterations} iterations, seed={seed})..."
  let mut rng : FuzzRng := { state := seed }

  -- Deterministic Edge Cases
  let edgeCases : List (String × ByteArray) := [
    ("Empty Buffer", ByteArray.empty),
    ("Single Zero Byte", ByteArray.mk #[0]),
    ("Single 0xFF Byte", ByteArray.mk #[0xFF]),
    ("Two Identical Bytes", ByteArray.mk #[0x42, 0x42]),
    ("Small ASCII String", "The quick brown fox jumps over the lazy dog.".toUTF8),
    ("Repeated 1000 'A's", (String.pushn "" 'A' 1000).toUTF8),
    ("256-byte Byte Ramp", Id.run do
      let mut a := ByteArray.empty
      for i in [0:256] do a := a.push i.toUInt8
      a),
    ("4096-byte Repeating Block", Id.run do
      let mut a := ByteArray.empty
      for i in [0:4096] do a := a.push ((i % 17).toUInt8)
      a)
  ]

  let mut totalTested := 0
  let mut dynChosen := 0
  let mut fixChosen := 0

  -- 1. Test Fixed Edge Cases
  IO.println "  [*] Stage 1: Testing deterministic edge cases..."
  for (name, raw) in edgeCases do
    -- Direction 1: gasm Gzip.compress -> python gunzip
    let gasmCompressed := Gzip.compress raw
    let oracleDecompRes ← runOracleGunzip pythonPath gasmCompressed
    match oracleDecompRes with
    | .error err => throw (IO.userError s!"[FAIL] Edge Case '{name}' gasm Gzip -> oracle Gunzip failed: {err}")
    | .ok decomp =>
      if decomp != raw then
        throw (IO.userError s!"[FAIL] Edge Case '{name}' gasm Gzip -> oracle Gunzip content mismatch! (expected {raw.size} bytes, got {decomp.size})")

    -- Direction 2: python gzip -> gasm Gzip.decompress
    let oracleGzRes ← runOracleGzip pythonPath raw
    match oracleGzRes with
    | .error err => throw (IO.userError s!"[FAIL] Edge Case '{name}' python gzip failed: {err}")
    | .ok oracleGz =>
      match Gzip.decompress oracleGz with
      | .error err => throw (IO.userError s!"[FAIL] Edge Case '{name}' oracle Gzip -> gasm Gunzip failed: {err}")
      | .ok gasmDecomp =>
        if gasmDecomp != raw then
          throw (IO.userError s!"[FAIL] Edge Case '{name}' oracle Gzip -> gasm Gunzip content mismatch!")

    -- Direction 3: gasm DEFLATE/zlib (fixed-or-dynamic block) -> python zlib inflate
    let usedDyn ← crossCheckDeflate pythonPath s!"Edge Case '{name}'" raw
    if usedDyn then dynChosen := dynChosen + 1 else fixChosen := fixChosen + 1
    totalTested := totalTested + 1

  IO.println s!"      ✓ All {edgeCases.length} edge cases passed all directions."

  -- 2. Randomized Differential Fuzzing
  -- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law
  -- TC17 vacuity floor (TCB.md T11-b): `--count 0` must not silently skip the randomized
  -- differential stage and still report "100% SUCCESS" below — 0 randomized vectors verifies
  -- nothing beyond the fixed edge cases, and must hard-fail rather than fall through.
  if iterations == 0 then
    throw (IO.userError "[VACUITY FLOOR TRIPPED] --count 0 requests 0 randomized cross-differential vectors for Stage 2 — this is a hard FAIL, not a clean PASS (TCB.md T11-b). Pass --count N with N >= 1.")
  IO.println s!"  [*] Stage 2: Running {iterations} randomized cross-differential fuzzing iterations..."
  for iter in [0:iterations] do
    let (patRaw, r1) := rng.next
    let (lenRaw, r2) := r1.next
    rng := r2
    let pattern := patRaw.toNat % 5
    let len := match iter % 6 with
      | 0 => (lenRaw.toNat % 32)        -- Tiny: 0..31 bytes
      | 1 => (lenRaw.toNat % 256) + 32  -- Small: 32..287 bytes
      | 2 => (lenRaw.toNat % 1024) + 256 -- Medium: 256..1279 bytes
      | 3 => (lenRaw.toNat % 4096) + 1024 -- Large: 1K..5K bytes
      | 4 => (lenRaw.toNat % 16384) + 4096 -- Extra Large: 4K..20K bytes
      | _ => (lenRaw.toNat % 65536) + 1000 -- Stress: up to 66KB

    let (raw, nextRng) := generateTestVector rng pattern len
    rng := nextRng

    -- Direction 1: Gasm Gzip -> Oracle Gunzip
    let gasmGz := Gzip.compress raw
    let oracleDecompRes ← runOracleGunzip pythonPath gasmGz
    match oracleDecompRes with
    | .error err => throw (IO.userError s!"[FAIL Iter {iter}] Gasm Gzip -> Oracle Gunzip failed: {err}")
    | .ok oracleDecomp =>
      if oracleDecomp != raw then
        throw (IO.userError s!"[FAIL Iter {iter}] Gasm Gzip -> Oracle Gunzip content mismatch on len {len} (pattern {pattern})")

    -- Direction 2: Oracle Gzip -> Gasm Gunzip
    let oracleGzRes ← runOracleGzip pythonPath raw
    match oracleGzRes with
    | .error err => throw (IO.userError s!"[FAIL Iter {iter}] Oracle Gzip failed: {err}")
    | .ok oracleGz =>
      match Gzip.decompress oracleGz with
      | .error err => throw (IO.userError s!"[FAIL Iter {iter}] Oracle Gzip -> Gasm Gunzip failed: {err}")
      | .ok gasmDecomp =>
        if gasmDecomp != raw then
          throw (IO.userError s!"[FAIL Iter {iter}] Oracle Gzip -> Gasm Gunzip content mismatch on len {len} (pattern {pattern})")

    -- Direction 3: gasm DEFLATE/zlib (fixed-or-dynamic block) -> python zlib inflate
    let usedDyn ← crossCheckDeflate pythonPath s!"Iter {iter} (len {len}, pattern {pattern})" raw
    if usedDyn then dynChosen := dynChosen + 1 else fixChosen := fixChosen + 1

    totalTested := totalTested + 1
    if (iter + 1) % 20 == 0 then
      IO.println s!"      [Progress] {iter + 1}/{iterations} iterations verified (100% bidirectional match)..."

  -- Vacuity floor (Law 13(4) class): the corpus must actually exercise BOTH encoder block
  -- types — a run in which compress never chose the dynamic-Huffman (or never chose the
  -- fixed-Huffman) block would leave that path's conformance claims untested while still
  -- printing a blanket success message below. The deterministic edge cases alone contain
  -- vectors on both sides of the cost heuristic, so this floor is seed-independent.
  if dynChosen == 0 then
    throw (IO.userError "[VACUITY FLOOR TRIPPED] No test vector caused compress to choose a dynamic-Huffman (BTYPE=10) block; the dynamic encode path was never exercised — hard FAIL, not a clean PASS.")
  if fixChosen == 0 then
    throw (IO.userError "[VACUITY FLOOR TRIPPED] No test vector caused compress to choose a fixed-Huffman (BTYPE=01) block; the fixed encode path was never exercised — hard FAIL, not a clean PASS.")

  IO.println s!"\n[+] GZIP DUAL-DIRECTION CROSS-DIFFERENTIAL FUZZER COMPLETE: {totalTested} TESTS PASSED (100% SUCCESS)."
  IO.println s!"[Block Types] compress chose dynamic-Huffman (BTYPE=10) on {dynChosen} vectors, fixed-Huffman (BTYPE=01) on {fixChosen} vectors (both paths exercised)."
  IO.println "[Evidentiary Scope] Validated against exactly 1 oracle (Python standard library gzip/zlib)."

end Stdlib.Zlib

open Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
def main (args : List String) : IO UInt32 := do
  let mut iters := 100
  let mut seed : UInt64 := 13374242
  let mut pythonOverride : Option String := none
  let mut i := 0
  while i < args.length do
    match args[i]! with
    | "--count" =>
      if i + 1 < args.length then
        iters := args[i + 1]!.toNat?.getD 100
        i := i + 2
      else i := i + 1
    | "--seed" =>
      if i + 1 < args.length then
        seed := args[i + 1]!.toNat?.getD 13374242 |>.toUInt64
        i := i + 2
      else i := i + 1
    | "--python" =>
      if i + 1 < args.length then
        pythonOverride := some args[i + 1]!
        i := i + 2
      else i := i + 1
    | _ => i := i + 1

  IO.println "================================================================================"
  IO.println "          GASM GZIP DUAL-DIRECTION CROSS-DIFFERENTIAL FUZZER                   "
  IO.println "              (Oracle: Python Standard Library gzip / zlib)                     "
  IO.println "================================================================================"

  -- Vacuity floor (Law 13(4)/T11-b class): a zero-iteration randomized stage must not be
  -- allowed to print a blanket success message. Refuse to run rather than report a vacuous
  -- "100% SUCCESS".
  if iters == 0 then
    IO.eprintln "[FATAL] --count must be >= 1: refusing to run the randomized differential stage with zero iterations and report success. This is a vacuity floor (Law 13(4)) — a fuzzer that tests nothing must not claim a pass."
    return 2

  -- Oracle presence check (Law 13(4)): the Python interpreter IS the oracle for this fuzzer.
  -- If it cannot be resolved, fail the run loudly and distinguishably rather than letting an
  -- uncaught subprocess-spawn exception (or, worse, a silently-skipped stage) stand in for a
  -- diagnosed failure.
  match ← findPythonPath pythonOverride with
  | .error err =>
    IO.eprintln s!"[FATAL] Python oracle unavailable: {err}"
    return 2
  | .ok pythonPath =>
    IO.println s!"[Oracle] Using Python interpreter: {pythonPath}"
    runGzipDifferentialFuzzer pythonPath iters seed
    return 0
