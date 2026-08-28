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
import Stdlib.Png.Streaming

namespace Stdlib.Png

open Stdlib.Zlib

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
/-- The parser stability property (no external oracle required): for any bytestream `b`,
    if `decodeImageRGBA8 b = .ok r₁` then `decodeImageRGBA8 (encodeImageRGBA8 r₁) = .ok r₂ → r₁ = r₂`.
    Unlike every other fuzzer in this tree (which differs against NASM, node, or CPython
    gzip/zlib), this property needs nothing external: it only requires that this codebase's
    own writer can reproduce whatever its own parser accepted. It catches a lossy parser --
    one that silently discards information the writer cannot put back -- which a
    roundtrip-from-structured-values test can never find, because such a test only ever
    ranges over values this codebase constructed, never over bytes an attacker chose. Simple
    deterministic Pseudo-Random Number Generator (Xorshift64), mirroring
    `Stdlib.Zlib.GzipFuzzer.FuzzRng`'s shape (kept local rather than shared, per this
    codebase's per-fuzzer-RNG convention). -/
structure PngFuzzRng where
  state : UInt64
  deriving Inhabited

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
/-- Advances the RNG and produces the next UInt64. -/
def PngFuzzRng.next (rng : PngFuzzRng) : UInt64 × PngFuzzRng :=
  let x := rng.state
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  (x, { state := if x == 0 then 88172645463325252 else x })

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
/-- Selects a pseudo-random natural number in `[0, bound)`; `bound = 0` always yields `0`. -/
def PngFuzzRng.nextNat (bound : Nat) (rng : PngFuzzRng) : Nat × PngFuzzRng :=
  if bound == 0 then (0, rng)
  else
    let (v, nxt) := rng.next
    (v.toNat % bound, nxt)

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
/-- Generates `n` pseudo-random bytes. -/
def genRandomBytes (rng : PngFuzzRng) (n : Nat) : ByteArray × PngFuzzRng := Id.run do
  let mut cur := rng
  let mut out := ByteArray.empty
  for _ in [0:n] do
    let (v, nxt) := cur.next
    cur := nxt
    out := out.push (v &&& 0xFF).toUInt8
  (out, cur)

/- REF: docs/STDLIB_PNG.md#41-the-five-standard-filter-types -/
/-- Cycle of filter choices exercised by the baseline generator: `none` selects
    `encodeImageRGBA8`'s adaptive heuristic (`chooseBestFilter`), the rest pin one of the 5
    standard filter types so every filter/unfilter code path in `Stdlib.Png.Filter` gets
    exercised by this fuzzer, not just whichever one the heuristic happens to prefer. -/
def filterCycle : List (Option FilterType) :=
  [none, some .none, some .sub, some .up, some .average, some .paeth]

/- REF: docs/STDLIB_PNG.md#41-the-five-standard-filter-types -/
/-- Human-readable label for a filter choice, for fuzzer diagnostics. -/
def filterLabel : Option FilterType → String
  | none => "auto"
  | some .none => "none"
  | some .sub => "sub"
  | some .up => "up"
  | some .average => "average"
  | some .paeth => "paeth"

/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- Generates a valid PNG byte stream for a pseudo-random small RGBA8 image, cycling through
    every filter choice. This is the "valid artifact" baseline the structured mutators below
    perturb -- per TC's vacuity-floor requirement, uniform noise almost never parses, so every
    mutation in this file starts from a genuine, decoder-accepted PNG rather than raw garbage. -/
def genValidImageBytes (rng : PngFuzzRng) (iter : Nat) : ByteArray × PngFuzzRng × String := Id.run do
  let (wRaw, r1) := rng.nextNat 12
  let (hRaw, r2) := r1.nextNat 12
  let w := wRaw + 1
  let h := hRaw + 1
  let (pixels, r3) := genRandomBytes r2 (w * h * 4)
  let img : ImageRGBA8 := { width := w, height := h, pixels := pixels }
  let ft := filterCycle.getD (iter % filterCycle.length) none
  let bytes := encodeImageRGBA8 img ft
  (bytes, r3, s!"valid-image {w}x{h} filter={filterLabel ft}")

/- REF: docs/STDLIB_PNG.md#32-color-types-bit-depth-matrix -/
/-- Bit depths outside PNG's 5 legal values (1, 2, 4, 8, 16). `parseIhdr` (`Stdlib/Png/Spec.lean`)
    rejects both this class (a `bitDepth` not in the standard 5-value set, for any `colorType`)
    and the narrower class of a `bitDepth` that is individually legal but not for the paired
    `colorType` (e.g. `bitDepth = 16` with `colorType = indexed`) -- see `allProbedBitDepths`,
    which covers the latter. Before that validation existed, a CRC-valid IHDR carrying one of
    these reached `unpackScanlinesToRGBA8`'s depth dispatch (`Stdlib/Png/Streaming.lean`), whose
    arms only covered 1, 2, 4, 8, and 16, silently dropping all pixel data instead of being
    rejected -- this list exists to keep driving that class of input at the (now-fixed) boundary. -/
def weirdBitDepths : List Nat := [0, 3, 5, 6, 7, 9, 12, 15, 17, 32, 200, 255]

/- REF: docs/STDLIB_PNG.md#32-color-types-bit-depth-matrix -/
/-- The 5 legal PNG color-type codes (RFC 2083 §4.3), used to build a custom IHDR whose
    `bitDepth` is independently varied via `weirdBitDepths` / `allProbedBitDepths`. -/
def standardColorCodes : List Nat := [0, 2, 3, 4, 6]

/- REF: png-rfc2083#section-4.1.1 -/
/-- The 5 standard PNG bit depths, one of which (paired with the wrong `colorType`) can be
    individually legal yet still illegal for that pairing per RFC 2083 §4.1.1's IHDR table --
    e.g. `bitDepth = 16` is legal for `truecolorRgba` but illegal for `indexed`. `weirdBitDepths`
    alone (all illegal for every `colorType`) never reaches that narrower case; combining the two
    (`allProbedBitDepths`) lets the deterministic sweep in `runPngStabilityFuzzer` hit every cell
    of the legality table, not just the row/column that is illegal everywhere. -/
def standardBitDepths : List Nat := [1, 2, 4, 8, 16]

/- REF: png-rfc2083#section-4.1.1 -/
/-- Every bit depth this fuzzer probes per-colorType: the 5 legal values (some of which are
    illegal for a *particular* colorType) plus `weirdBitDepths` (illegal for every colorType). -/
def allProbedBitDepths : List Nat := standardBitDepths ++ weirdBitDepths

/- REF: docs/STDLIB_PNG.md#22-pngwriter-push-state-machine -/
/-- Assembles a CRC-valid PNG stream from an arbitrary (including spec-illegal) `PngHeader` by
    driving `beginPng`/`writeScanline`/`endPng` directly -- the same writer machinery
    `encodeImageRGBA8` uses, but with a hand-chosen header so `bitDepth`/`colorType` combinations
    `encodeImageRGBA8` itself never produces (it always emits 8-bit truecolor-RGBA) can still be
    exercised. Row bytes are random and sized to `scanlineByteLength header`, which is
    arithmetically well-defined for any `bitDepth`/`colorType` pair even when PNG itself
    forbids the combination -- exactly the "attacker-chosen bytes explore paths this codebase's
    own constructors never do" scenario this fuzzer exists to cover. Splits roughly evenly between
    a `bitDepth` drawn from `colorType.legalBitDepths` (expected to parse and round-trip
    successfully -- this is what keeps this category clear of the per-category vacuity floor now
    that `parseIhdr` rejects every `weirdBitDepths` value) and one drawn from `weirdBitDepths`
    (expected to be rejected, continuing to exercise that boundary). -/
def genCustomHeaderBytes (rng : PngFuzzRng) : ByteArray × PngFuzzRng × String := Id.run do
  let (wRaw, r1) := rng.nextNat 8
  let (hRaw, r2) := r1.nextNat 8
  let w := wRaw + 1
  let h := hRaw + 1
  let (ctIdx, r3) := r2.nextNat standardColorCodes.length
  let colorCode := standardColorCodes.getD ctIdx 2
  let colorType := (PngColorType.fromNat? colorCode).getD .truecolorRgba
  let (useLegal, r4) := r3.nextNat 2
  let (bitDepth, r5) :=
    if useLegal == 0 then
      let legal := colorType.legalBitDepths
      let (idx, r5') := r4.nextNat legal.length
      (legal.getD idx 8, r5')
    else
      let (idx, r5') := r4.nextNat weirdBitDepths.length
      (weirdBitDepths.getD idx 8, r5')
  let header : PngHeader := { width := w, height := h, bitDepth := bitDepth, colorType := colorType }
  let scanlineLen := scanlineByteLength header
  let mut writer := beginPng header
  let mut curRng := r5
  for _ in [0:h] do
    let (rowBytes, nxt) := genRandomBytes curRng scanlineLen
    curRng := nxt
    match writeScanline writer rowBytes .none with
    | .ok w2 => writer := w2
    | .error _ => pure ()
  let bytes := match endPng writer with
    | .ok b => b
    | .error _ => ByteArray.empty
  (bytes, curRng, s!"custom-header {w}x{h} bitDepth={bitDepth} colorType={colorCode} legal={useLegal == 0}")

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Re-scans a PNG byte stream into its `(chunkType, data)` chunk list using `parseChunk`,
    stopping at `IEND` or the first parse failure. Reassembling via `mkChunk` (see
    `assembleChunks`) always recomputes a correct CRC, so every chunk-list-level mutator below
    (insert/split/drop/reorder) produces CRC-valid output by construction -- unlike a raw byte
    flip, which the per-chunk CRC almost always rejects outright and so cannot exercise the
    decoder past its first rejection (the vacuity-floor concern `checkSignature`/`parseChunk`'s
    own CRC check would otherwise trip on nearly every mutated byte). -/
def scanChunksAux (bytes : ByteArray) : Nat → Nat → List (String × ByteArray) → List (String × ByteArray)
  | 0, _, acc => acc.reverse
  | fuel + 1, pos, acc =>
    if pos >= bytes.size then acc.reverse
    else match parseChunk bytes pos with
      | .error _ => acc.reverse
      | .ok (chunk, nextPos) =>
        let acc' := (chunk.chunkType, chunk.data) :: acc
        if chunk.chunkType == "IEND" then acc'.reverse
        else scanChunksAux bytes fuel nextPos acc'

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Entry point for `scanChunksAux`: returns `[]` for a stream not beginning with the PNG
    signature (the mutators below are only ever applied to this fuzzer's own well-formed
    generator output, so this is a defensive default, not a load-bearing validation path). -/
def scanChunks (bytes : ByteArray) : List (String × ByteArray) :=
  if !checkSignature bytes then []
  else scanChunksAux bytes (bytes.size + 1) 8 []

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Reassembles a chunk list into a PNG byte stream, recomputing every chunk's CRC via
    `mkChunk`. -/
def assembleChunks (chunks : List (String × ByteArray)) : ByteArray := Id.run do
  let mut out := pngSignature
  for (t, d) in chunks do
    let c := mkChunk t d
    for b in c do out := out.push b
  out

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Splices a well-formed, CRC-valid ancillary chunk of an unrecognized type ("zzXt", which
    `parsePngChunks` neither special-cases nor rejects -- it falls into the wildcard "ignore
    unknown chunk" arm) at a pseudo-random position in the chunk list. Because
    `parsePngChunks` does not enforce chunk ordering beyond IHDR/IDAT/IEND's own presence
    checks, this should always still decode successfully: it directly exercises the "silently
    skip an unrecognized ancillary chunk" path that a pure roundtrip-from-structured-values
    test never reaches (nothing in `ImageRGBA8` can represent an extra ancillary chunk). -/
def mutInsertAncillary (rng : PngFuzzRng) (bytes : ByteArray) : ByteArray × PngFuzzRng × String := Id.run do
  let chunks := scanChunks bytes
  if chunks.isEmpty then (bytes, rng, "insert-ancillary (skipped: no chunks)")
  else
    let (payload, r1) := genRandomBytes rng 6
    let (posIdx, r2) := r1.nextNat (chunks.length + 1)
    let newChunk := ("zzXt", payload)
    let before := chunks.take posIdx
    let after := chunks.drop posIdx
    (assembleChunks (before ++ [newChunk] ++ after), r2, s!"insert-ancillary@{posIdx}")

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Splits a `ByteArray` into `pieces` roughly-equal, order-preserving, contiguous slices
    (fewer if `data` is too short to split further). -/
def splitBytesInto (data : ByteArray) (pieces : Nat) : List ByteArray :=
  if pieces <= 1 || data.size == 0 then [data]
  else Id.run do
    let chunkSz := Nat.max 1 ((data.size + pieces - 1) / pieces)
    let mut out : List ByteArray := []
    let mut pos := 0
    while pos < data.size do
      let e := Nat.min (pos + chunkSz) data.size
      out := out ++ [data.extract pos e]
      pos := e
    out

/- REF: docs/STDLIB_PNG.md#21-pngscanlinesink-typeclass -/
/-- Splits the (single) `IDAT` chunk `parsePngChunks` produced into 2-4 smaller `IDAT` chunks
    covering the exact same compressed payload, in order. PNG (and this decoder's
    `parsePngChunks`, which concatenates every `IDAT` chunk's `data` before decompressing)
    treats consecutive `IDAT` chunks as one logical stream, so this should always still decode
    to the same image -- it directly exercises the multi-`IDAT` concatenation path a
    single-chunk roundtrip test never reaches. -/
def mutSplitIdat (rng : PngFuzzRng) (bytes : ByteArray) : ByteArray × PngFuzzRng × String := Id.run do
  let chunks := scanChunks bytes
  let (piecesRaw, r1) := rng.nextNat 3
  let n := piecesRaw + 2
  let newChunks := chunks.foldl (fun acc (t, d) =>
    if t == "IDAT" then acc ++ (splitBytesInto d n).map (fun piece => ("IDAT", piece))
    else acc ++ [(t, d)]) []
  (assembleChunks newChunks, r1, s!"split-idat-into-{n}")

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Drops the `IEND` chunk entirely. `parsePngChunks`'s scan loop condition is
    `pos < stream.size && !seenIend`, so it terminates cleanly (using whatever it accumulated)
    the moment the stream runs out, with no separate "was IEND seen" check anywhere in
    `readPngStream` -- so a stream that ends immediately after a complete `IDAT` should decode
    identically to one that additionally has an `IEND` chunk. This mutator exists to confirm
    that; a mismatch (or a spurious "missingIhdr"/`prematureEof`) would mean `IEND`'s presence
    is silently load-bearing in a way the code does not document. -/
def mutDropIend (rng : PngFuzzRng) (bytes : ByteArray) : ByteArray × PngFuzzRng × String :=
  let chunks := scanChunks bytes
  let kept := chunks.filter (fun (t, _) => t != "IEND")
  (assembleChunks kept, rng, "drop-iend")

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Inserts an ancillary chunk (as `mutInsertAncillary`) and then moves it to the very front of
    the chunk list, ahead of `IHDR` itself. `parsePngChunks` accumulates `headerOpt` by chunk
    *type*, not position, so this should still decode successfully -- exercising whether chunk
    order is truly irrelevant to this decoder (a real PNG decoder is permitted to require IHDR
    first; this one does not enforce that, which is itself worth knowing regardless of whether
    the stability property holds across it). -/
def mutReorderAncillaryFirst (rng : PngFuzzRng) (bytes : ByteArray) : ByteArray × PngFuzzRng × String := Id.run do
  let (withAncillary, r1, _) := mutInsertAncillary rng bytes
  let chunks := scanChunks withAncillary
  match chunks.findIdx? (fun (t, _) => t == "zzXt") with
  | none => (withAncillary, r1, "reorder-ancillary-first (skipped: insert failed)")
  | some idx =>
    let target := chunks[idx]!
    let rest := chunks.eraseIdx idx
    (assembleChunks (target :: rest), r1, "reorder-ancillary-first")

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Appends 1-32 pseudo-random bytes after the complete PNG stream. `readPngStream` never reads
    past the `IEND` chunk it detects, so this should always still decode successfully. -/
def mutAppendTrailingGarbage (rng : PngFuzzRng) (bytes : ByteArray) : ByteArray × PngFuzzRng × String := Id.run do
  let (n, r1) := rng.nextNat 32
  let (garbage, r2) := genRandomBytes r1 (n + 1)
  let mut out := bytes
  for b in garbage do out := out.push b
  (out, r2, s!"append-trailing-garbage+{n + 1}")

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Flips a single pseudo-random bit within a single pseudo-random byte, anywhere in the
    stream. Every real chunk's CRC-32 covers its type+data, so this almost always lands the
    mutation somewhere that turns into a clean `.crcMismatch` (or `.truncatedStream`/decode
    error) rejection rather than a successful-but-different parse -- this category is
    deliberately the fuzzer's "mostly rejected, occasionally not" negative-coverage arm, kept
    a minority of iterations so it does not starve the vacuity floor by itself. -/
def mutFlipRandomByte (rng : PngFuzzRng) (bytes : ByteArray) : ByteArray × PngFuzzRng × String := Id.run do
  if bytes.size == 0 then (bytes, rng, "flip-byte (skipped: empty)")
  else
    let (idx, r1) := rng.nextNat bytes.size
    let (bits, r2) := r1.nextNat 256
    let old := bytes.get! idx
    (bytes.set! idx (old ^^^ bits.toUInt8), r2, s!"flip-byte@{idx}")

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
/-- Dispatches to one of 8 generator/mutator categories. Categories 0-6 are expected to
    (almost) always still decode successfully -- each is checked against a per-category
    non-zero vacuity floor by the caller; category 7 (raw byte flip) is not, since CRC
    protection makes success there incidental rather than structural. -/
def genMutatedCase (rng : PngFuzzRng) (iter : Nat) : ByteArray × PngFuzzRng × Nat × String := Id.run do
  let (cat, r1) := rng.nextNat 8
  let (bytes, r2, label) := match cat with
    | 0 => genValidImageBytes r1 iter
    | 1 => genCustomHeaderBytes r1
    | 2 => Id.run do
        let (base, r2, _) := genValidImageBytes r1 iter
        mutInsertAncillary r2 base
    | 3 => Id.run do
        let (base, r2, _) := genValidImageBytes r1 iter
        mutSplitIdat r2 base
    | 4 => Id.run do
        let (base, r2, _) := genValidImageBytes r1 iter
        mutDropIend r2 base
    | 5 => Id.run do
        let (base, r2, _) := genValidImageBytes r1 iter
        mutReorderAncillaryFirst r2 base
    | 6 => Id.run do
        let (base, r2, _) := genValidImageBytes r1 iter
        mutAppendTrailingGarbage r2 base
    | _ => Id.run do
        let (base, r2, _) := genValidImageBytes r1 iter
        mutFlipRandomByte r2 base
  (bytes, r2, cat, label)

/- REF: docs/STDLIB_PNG.md#33-pngerror-inductive-taxonomy -/
/-- Formats a single byte as a 2-digit lowercase hex string. -/
def byteHex (b : UInt8) : String :=
  let s := String.ofList (Nat.toDigits 16 b.toNat)
  if s.length < 2 then "0" ++ s else s

/- REF: docs/STDLIB_PNG.md#33-pngerror-inductive-taxonomy -/
/-- Renders a bounded hex preview of a `ByteArray` for fuzzer failure diagnostics. -/
def hexPreview (bytes : ByteArray) (maxLen : Nat := 96) : String := Id.run do
  let n := Nat.min bytes.size maxLen
  let mut s := ""
  for i in [0:n] do
    s := s ++ byteHex (bytes.get! i) ++ " "
  if bytes.size > maxLen then s ++ s!"... ({bytes.size} bytes total)" else s

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
/-- Core stability check: `parse b = .ok r₁ → parse (write r₁) = .ok r₂ → r₁ = r₂`, instantiated
    with `decodeImageRGBA8` as `parse` and `encodeImageRGBA8 · none` as `write` (the adaptive
    filter heuristic; the property is about the decoded *value*, not which filter re-encoding
    happens to choose). Returns `true` iff `bytes` parsed at all (the vacuity-floor signal the
    caller accumulates), `.ok false` if `decodeImageRGBA8` rejected it outright (not a
    violation -- most mutated bytes are expected to be rejected), and `.error` with full
    diagnostic detail (both parses' results, both byte streams) when the property itself is
    violated. Returning `Except` rather than throwing lets the caller collect *every* finding
    in a run instead of aborting at the first one, per this task's "report every finding"
    requirement. -/
def checkStability (label : String) (bytes : ByteArray) : Except String Bool :=
  match decodeImageRGBA8 bytes with
  | .error _ => .ok false
  | .ok r1 =>
    let bytes2 := encodeImageRGBA8 r1 none
    match decodeImageRGBA8 bytes2 with
    | .error err =>
      .error s!"[FAIL] {label}: parse succeeded (image {r1.width}x{r1.height}, {r1.pixels.size} pixel bytes) but re-encoding it and re-parsing that failed: {repr err}\n  original bytes ({bytes.size}): {hexPreview bytes}\n  rewritten bytes ({bytes2.size}): {hexPreview bytes2}"
    | .ok r2 =>
      if _h : r1 = r2 then
        .ok true
      else
        let diffDesc :=
          if r1.width != r2.width || r1.height != r2.height then
            s!"dimensions differ: {r1.width}x{r1.height} (r1) vs {r2.width}x{r2.height} (r2)"
          else if r1.pixels.size != r2.pixels.size then
            s!"pixel-buffer size differs: {r1.pixels.size} (r1) vs {r2.pixels.size} (r2) bytes -- classic lossy-decode signature (decoder produced fewer/more pixel bytes than width*height*4 implies)"
          else
            let firstDiffIdx : Option Nat := Id.run do
              let n := r1.pixels.size
              let mut idx : Option Nat := none
              for i in [0:n] do
                if idx.isNone && r1.pixels.get! i != r2.pixels.get! i then
                  idx := some i
              idx
            match firstDiffIdx with
            | some i => s!"pixel byte {i} differs: 0x{byteHex (r1.pixels.get! i)} (r1) vs 0x{byteHex (r2.pixels.get! i)} (r2)"
            | none => "r1 ≠ r2 per DecidableEq but no pixel byte differs (width/height/pixel-size all equal) -- inspect PngHeader-adjacent fields"
        .error s!"[FAIL] {label}: PARSER STABILITY VIOLATED -- parse b = r1, parse (write r1) = r2, r1 ≠ r2\n  {diffDesc}\n  original bytes ({bytes.size}): {hexPreview bytes}\n  rewritten (write r1) bytes ({bytes2.size}): {hexPreview bytes2}"

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
/-- Runs the PNG parser-stability fuzzer: deterministic edge cases first, then `iterations`
    randomized structured-mutation cases across the 8 categories in `genMutatedCase`. Enforces
    a vacuity floor (TC17/T11-b class): the overall parse-success rate must clear a minimum
    threshold, and each of the 7 "should usually succeed" categories must have contributed at
    least one successful parse, or the run is a hard FAIL even with zero stability violations --
    a run in which nothing parsed tests nothing while reporting a clean pass. -/
def runPngStabilityFuzzer (iterations : Nat) (seed : UInt64) : IO Unit := do
  IO.println s!"[+] Starting PNG Parser-Stability Fuzzer ({iterations} iterations, seed={seed})..."
  IO.println "    Property: parse b = .ok r1 -> parse (write r1) = .ok r2 -> r1 = r2 (no external oracle)"

  -- Deterministic edge cases.
  IO.println "  [*] Stage 1: Testing deterministic edge cases..."
  let edgeCaseBytes : List (String × ByteArray) := [
    ("Empty buffer", ByteArray.empty),
    ("Single zero byte", ByteArray.mk #[0]),
    ("Signature only, no chunks", pngSignature),
    ("Signature + garbage", pngSignature ++ ByteArray.mk #[1,2,3,4,5,6,7,8]),
    -- REGRESSION CASE for a `parseChunk` panic this fuzzer found: `String.fromUTF8!`
    -- (`Stdlib/Png/Spec.lean:173`) is called unconditionally on a chunk's raw 4-byte type
    -- field, *before* the CRC check that would otherwise reject a corrupted chunk -- so any
    -- chunk whose type bytes are not valid UTF-8 (e.g. a single flipped high bit) reaches
    -- `String.fromUTF8!` and panics, regardless of what its CRC says. Lean's panic recovers
    -- (logs to stderr, returns the `Inhabited` default `""`) rather than aborting, so this is
    -- not a crash in this build, but it is not a properly-typed `Except`-returning rejection
    -- either -- a byte flip anywhere in a chunk's type field can hit it.
    ("IHDR type field with invalid UTF-8 first byte (0xC9)",
      pngSignature ++ ByteArray.mk #[0,0,0,0x0d, 0xC9,0x48,0x44,0x52,
        0,0,0,1, 0,0,0,1, 8,6,0,0,0, 0x1f,0x15,0xc4,0x89]),
    -- REGRESSION CASE: the exact 1x1 bitDepth=0/colorType=0 byte stream this fuzzer's own
    -- report cites as the reproducing input for the bitDepth/colorType validation gap fixed in
    -- `parseIhdr` (`Stdlib/Png/Spec.lean`). Kept verbatim (rather than only re-derived via the
    -- `allProbedBitDepths` sweep below) so this exact reported byte sequence stays pinned as a
    -- regression case independent of any future change to how that sweep constructs its inputs.
    ("Literal reported bitDepth=0/colorType=0 case",
      ByteArray.mk #[
        0x89,0x50,0x4e,0x47,0x0d,0x0a,0x1a,0x0a, 0x00,0x00,0x00,0x0d, 0x49,0x48,0x44,0x52,
        0x00,0x00,0x00,0x01, 0x00,0x00,0x00,0x01,
        0x00,0x00,0x00,0x00,0x00, 0x0a,0x0e,0xd0,0x94, 0x00,0x00,0x00,0x09, 0x49,0x44,0x41,0x54,
        0x78,0x01,0x63,0x00,0x00,0x00,0x01,0x00,0x01, 0xea,0x7a,0xdc,0xd9,
        0x00,0x00,0x00,0x00, 0x49,0x45,0x4e,0x44, 0xae,0x42,0x60,0x82])
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
  -- 1x1 image through every filter, plus every probed-bitDepth x standard-colorType combination
  -- at 1x1 (`allProbedBitDepths` = the 5 legal depths, some illegal for a given colorType, plus
  -- `weirdBitDepths`, illegal for every colorType): deterministic, reproducible coverage of every
  -- cell of RFC 2083 §4.1.1's legality table, including bitDepth=16 x colorType=indexed --
  -- independent of RNG luck, and of `genCustomHeaderBytes`'s randomized draw.
  for ft in filterCycle do
    edgeAttempts := edgeAttempts + 1
    let img : ImageRGBA8 := { width := 1, height := 1, pixels := ByteArray.mk #[10, 20, 30, 255] }
    let bytes := encodeImageRGBA8 img ft
    match checkStability s!"Edge case '1x1 image filter={filterLabel ft}'" bytes with
    | .error msg => violations := violations.push msg
    | .ok true => edgeSuccesses := edgeSuccesses + 1
    | .ok false => pure ()
  for bitDepth in allProbedBitDepths do
    for colorCode in standardColorCodes do
      edgeAttempts := edgeAttempts + 1
      let colorType := (PngColorType.fromNat? colorCode).getD .truecolorRgba
      let header : PngHeader := { width := 1, height := 1, bitDepth := bitDepth, colorType := colorType }
      let scanlineLen := scanlineByteLength header
      let writer := beginPng header
      let bytes := match writeScanline writer (ByteArray.mk (Array.replicate scanlineLen 0x42)) .none with
        | .error _ => ByteArray.empty
        | .ok w2 => match endPng w2 with
          | .ok b => b
          | .error _ => ByteArray.empty
      match checkStability s!"Edge case '1x1 bitDepth={bitDepth} colorType={colorCode}'" bytes with
      | .error msg => violations := violations.push msg
      | .ok true => edgeSuccesses := edgeSuccesses + 1
      | .ok false => pure ()
  IO.println s!"      {edgeSuccesses}/{edgeAttempts} edge cases parsed successfully (rest were clean rejections); {violations.size} stability violation(s) so far."

  -- Vacuity floor (Law 13(4) class): 0 randomized iterations must not print a blanket pass.
  if iterations == 0 then
    throw (IO.userError "[VACUITY FLOOR TRIPPED] --count 0 requests 0 randomized structured-mutation vectors -- this is a hard FAIL, not a clean PASS (TCB.md T11-b class). Pass --count N with N >= 1.")

  IO.println s!"  [*] Stage 2: Running {iterations} randomized structured-mutation iterations..."
  let mut rng : PngFuzzRng := { state := seed }
  let mut totalAttempts := 0
  let mut totalSuccesses := 0
  let mut catAttempts : Array Nat := Array.replicate 8 0
  let mut catSuccesses : Array Nat := Array.replicate 8 0
  for iter in [0:iterations] do
    let (bytes, nextRng, cat, label) := genMutatedCase rng iter
    rng := nextRng
    totalAttempts := totalAttempts + 1
    catAttempts := catAttempts.set! cat (catAttempts[cat]! + 1)
    match checkStability s!"Iter {iter} [{label}]" bytes with
    | .error msg => violations := violations.push msg
    | .ok true =>
      totalSuccesses := totalSuccesses + 1
      catSuccesses := catSuccesses.set! cat (catSuccesses[cat]! + 1)
    | .ok false => pure ()
    if (iter + 1) % 50 == 0 then
      IO.println s!"      [Progress] {iter + 1}/{iterations} iterations, {totalSuccesses} successful parses so far, {violations.size} violation(s)..."

  let catNames : Array String := #["valid-image", "custom-header(weird-bitDepth)", "insert-ancillary",
    "split-idat", "drop-iend", "reorder-ancillary-first", "append-trailing-garbage", "flip-byte"]
  IO.println "  [*] Per-category results:"
  for i in [0:8] do
    let a := catAttempts[i]!
    let s := catSuccesses[i]!
    let pct := if a == 0 then 0.0 else (s.toFloat / a.toFloat) * 100.0
    IO.println s!"      {catNames[i]!}: {s}/{a} parsed ({pct}%)"

  -- Report every finding (STEP 3): if the property was violated anywhere, print every
  -- occurrence in full before doing anything else -- a fuzzer that reports only the first
  -- finding hides the rest of the evidence.
  if !violations.isEmpty then
    IO.println s!"\n[!!!] {violations.size} PARSER STABILITY VIOLATION(S) FOUND:\n"
    for idx in [0:violations.size] do
      IO.println s!"--- Violation {idx + 1}/{violations.size} ---"
      IO.println violations[idx]!
      IO.println ""
    throw (IO.userError s!"{violations.size} parser stability violation(s) found (see above) -- see docs/STDLIB_PNG.md for the format this decoder is supposed to implement.")

  -- Vacuity floor: overall parse-success rate.
  let overallPct := (totalSuccesses.toFloat / totalAttempts.toFloat) * 100.0
  IO.println s!"\n[Vacuity] Overall: {totalSuccesses}/{totalAttempts} attempts produced a successful parse ({overallPct}%) that was then checked for stability."
  if totalSuccesses * 5 < totalAttempts then
    throw (IO.userError s!"[VACUITY FLOOR TRIPPED] Only {totalSuccesses}/{totalAttempts} ({overallPct}%) attempts produced a successful parse -- below the 20% floor. A run in which almost nothing parses tests almost nothing, even though it reports 0 violations. This is a hard FAIL, not a clean PASS.")

  -- Vacuity floor: each "should usually succeed" category (0-6) must have contributed at
  -- least one successful parse, mirroring GzipFuzzer's dynChosen/fixChosen both-paths-exercised
  -- check -- a category whose mutator is broken (e.g. always producing malformed output) would
  -- silently contribute zero coverage while the overall floor above might still pass.
  for i in [0:7] do
    if catSuccesses[i]! == 0 then
      throw (IO.userError s!"[VACUITY FLOOR TRIPPED] Category '{catNames[i]!}' (expected to almost always parse successfully) produced 0 successful parses across {catAttempts[i]!} attempts -- this category's coverage is vacuous. Hard FAIL.")

  IO.println s!"\n[+] PNG PARSER-STABILITY FUZZER COMPLETE: {totalAttempts + edgeAttempts} total attempts, {totalSuccesses + edgeSuccesses} successful parses checked, 0 stability violations."
  IO.println "[Evidentiary Scope] Internal property only -- no external oracle needed or used."

end Stdlib.Png

open Stdlib.Png

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
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
  IO.println "               GASM PNG PARSER-STABILITY FUZZER                                 "
  IO.println "        (No external oracle -- self-referential parse/write/parse property)      "
  IO.println "================================================================================"

  try
    runPngStabilityFuzzer iters seed
    return 0
  catch e =>
    IO.eprintln (toString e)
    return 1
