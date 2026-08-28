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
import Stdlib.Zlib.Spec
import Stdlib.Png.Spec
import Stdlib.Png.Filter

namespace Stdlib.Png

open Stdlib.Zlib

/- REF: docs/STDLIB_PNG.md#21-pngscanlinesink-typeclass -/
/-- Monadic sink consumer for streaming PNG scanlines and metadata chunks. -/
class PngScanlineSink (m : Type → Type) (SinkState : Type) [Monad m] where
  onHeader       : PngHeader → SinkState → m (Except PngError SinkState)
  onPalette      : Array (UInt8 × UInt8 × UInt8) → SinkState → m (Except PngError SinkState) := fun _ s => pure (.ok s)
  onTransparency : ByteArray → SinkState → m (Except PngError SinkState) := fun _ s => pure (.ok s)
  onScanline     : (rowIdx : Nat) → (rowBytes : ByteArray) → SinkState → m (Except PngError SinkState)
  onEnd          : SinkState → m (Except PngError SinkState)

/- REF: docs/STDLIB_PNG.md#21-pngscanlinesink-typeclass -/
/-- In-memory accumulation sink collecting headers, raw scanlines, palette, and transparency. -/
structure MemoryImageSink where
  header       : Option PngHeader := none
  pixels       : ByteArray        := ByteArray.empty
  palette      : Array (UInt8 × UInt8 × UInt8) := #[]
  transparency : Option ByteArray := none
  deriving Inhabited

/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- Monad instance for MemoryImageSink in Except PngError monad. -/
instance : PngScanlineSink (Except PngError) MemoryImageSink where
  onHeader h s := .ok (.ok { s with header := some h })
  onPalette pal s := .ok (.ok { s with palette := pal })
  onTransparency trns s := .ok (.ok { s with transparency := some trns })
  onScanline _ row s :=
    let newPixels := s.pixels ++ row
    .ok (.ok { s with pixels := newPixels })
  onEnd s := .ok (.ok s)

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- A successful `parseChunk` always advances past the 12-byte length/type/CRC framing
    plus the chunk's declared data length, so `nextPos` is always strictly greater than
    `pos`. This is the progress fact that justifies well-founded recursion over the
    chunk-scanning loop below (mirrors `readBits_remainingBits`'s role for the
    bitstream loops in `Stdlib.Zlib.Deflate`). -/
theorem parseChunk_progress (bytes : ByteArray) (pos : Nat) (chunk : PngChunk) (nextPos : Nat)
    (hok : parseChunk bytes pos = .ok (chunk, nextPos)) : pos + 12 ≤ nextPos := by
  unfold parseChunk at hok
  simp only [bind, Except.bind] at hok
  repeat' (split at hok)
  all_goals simp_all
  all_goals omega

/- REF: docs/STDLIB_PNG.md#21-pngscanlinesink-typeclass -/
/-- Pure chunk-scanning pass over a PNG stream, accumulating the IHDR header, palette,
    transparency chunk, and concatenated IDAT payload, stopping at IEND or end-of-stream.
    Extracted from `readPngStream`'s original `while` loop, which is otherwise identical
    but threads no monadic effects during the scan itself (all sink callbacks happen only
    after this pass completes), so this helper stays in the pure `Except PngError` monad
    and can be given an explicit termination measure independent of `readPngStream`'s
    generic sink monad `m`. -/
def parsePngChunks (stream : ByteArray) (pos : Nat) (headerOpt : Option PngHeader)
    (palette : Array (UInt8 × UInt8 × UInt8)) (transparencyOpt : Option ByteArray)
    (idatAcc : ByteArray) (seenIend : Bool) :
    Except PngError (Option PngHeader × Array (UInt8 × UInt8 × UInt8) × Option ByteArray × ByteArray) :=
  if pos < stream.size && !seenIend then
    match hParse : parseChunk stream pos with
    | .error err => .error err
    | .ok (chunk, nextPos) =>
      if chunk.chunkType == "IHDR" then
        match parseIhdr chunk.data with
        | .error err => .error err
        | .ok hdr => parsePngChunks stream nextPos (some hdr) palette transparencyOpt idatAcc seenIend
      else if chunk.chunkType == "PLTE" then
        let numEntries := chunk.data.size / 3
        let pal := Id.run do
          let mut p := #[]
          for i in [0:numEntries] do
            let r := chunk.data.get! (i * 3)
            let g := chunk.data.get! (i * 3 + 1)
            let b := chunk.data.get! (i * 3 + 2)
            p := p.push (r, g, b)
          pure p
        parsePngChunks stream nextPos headerOpt pal transparencyOpt idatAcc seenIend
      else if chunk.chunkType == "tRNS" then
        parsePngChunks stream nextPos headerOpt palette (some chunk.data) idatAcc seenIend
      else if chunk.chunkType == "IDAT" then
        let newIdat := Id.run do
          let mut acc := idatAcc
          for b in chunk.data do acc := acc.push b
          pure acc
        parsePngChunks stream nextPos headerOpt palette transparencyOpt newIdat seenIend
      else if chunk.chunkType == "IEND" then
        parsePngChunks stream nextPos headerOpt palette transparencyOpt idatAcc true
      else
        parsePngChunks stream nextPos headerOpt palette transparencyOpt idatAcc seenIend
  else
    .ok (headerOpt, palette, transparencyOpt, idatAcc)
termination_by stream.size - pos
decreasing_by
  all_goals (
    have hprog := parseChunk_progress stream pos chunk nextPos hParse
    simp only [Bool.and_eq_true, decide_eq_true_eq] at *
    omega)

/- REF: docs/STDLIB_PNG.md#21-pngscanlinesink-typeclass -/
/-- Streaming PNG reader feeding decompressed and defiltered scanlines into a PngScanlineSink. -/
def readPngStream {m : Type → Type} {SinkState : Type} [Monad m] [PngScanlineSink m SinkState]
    (stream : ByteArray) (initialSink : SinkState) : m (Except PngError SinkState) := do
  if !checkSignature stream then return .error .invalidSignature

  let (headerOpt, palette, transparencyOpt, idatAcc) ←
    match parsePngChunks stream 8 none #[] none ByteArray.empty false with
    | .error err => return .error err
    | .ok st => pure st

  let header ← match headerOpt with
    | some h => pure h
    | none => return .error .missingIhdr

  let resHeader ← PngScanlineSink.onHeader header initialSink
  let mut curSink ← match resHeader with
    | Except.ok s => pure s
    | Except.error e => return .error e

  if !palette.isEmpty then
    let resPal ← PngScanlineSink.onPalette palette curSink
    match resPal with
    | Except.ok s => curSink := s
    | Except.error e => return .error e

  if let some trns := transparencyOpt then
    let resTrns ← PngScanlineSink.onTransparency trns curSink
    match resTrns with
    | Except.ok s => curSink := s
    | Except.error e => return .error e

  let decompressedRaw ← match zlibDecompress idatAcc with
    | .ok raw => pure raw
    | .error err => return .error (.zlibError err)

  let bpp := bytesPerPixel header
  let scanlineLen := scanlineByteLength header
  let expectedTotalSize := (scanlineLen + 1) * header.height
  if decompressedRaw.size < expectedTotalSize then
    return .error .prematureEof

  let mut priorRow := ByteArray.empty
  let mut rawPos := 0

  for rowIdx in [0:header.height] do
    if rawPos >= decompressedRaw.size then return .error .prematureEof
    let filterByte := (decompressedRaw.get! rawPos).toNat
    rawPos := rawPos + 1
    let filterType ← match FilterType.fromNat? filterByte with
      | some ft => pure ft
      | none => return .error (.invalidFilterType filterByte)

    let filteredSlice := decompressedRaw.extract rawPos (rawPos + scanlineLen)
    rawPos := rawPos + scanlineLen
    let reconstructedRow := unfilterScanline filterType filteredSlice priorRow bpp
    priorRow := reconstructedRow

    let resRow ← PngScanlineSink.onScanline rowIdx reconstructedRow curSink
    match resRow with
    | Except.ok nextSink => curSink := nextSink
    | Except.error e => return .error e

  let resEnd ← PngScanlineSink.onEnd curSink
  match resEnd with
  | Except.ok finalSink => return .ok finalSink
  | Except.error e => return .error e

/- REF: docs/STDLIB_PNG.md#22-pngwriter-push-state-machine -/
/-- Push-based progressive PNG writer state machine. -/
structure PngWriter where
  header     : PngHeader
  currentRow : Nat := 0
  prevRow    : ByteArray := ByteArray.empty
  rawStream  : ByteArray := ByteArray.empty
  isFinished : Bool := false
  deriving Inhabited

/- REF: docs/STDLIB_PNG.md#22-pngwriter-push-state-machine -/
/-- Initializes a PngWriter with given image header. -/
def beginPng (header : PngHeader) : PngWriter := {
  header     := header
  currentRow := 0
  prevRow    := ByteArray.empty
  rawStream  := ByteArray.empty
  isFinished := false
}

/- REF: docs/STDLIB_PNG.md#22-pngwriter-push-state-machine -/
/-- Writes a single raw scanline to the PngWriter with FilterType.none. -/
def writeScanline (w : PngWriter) (rowBytes : ByteArray) (ft : FilterType := .none) : Except PngError PngWriter := do
  if w.isFinished then throw (.custom "PngWriter is already finished")
  if w.currentRow >= w.header.height then throw (.custom "PngWriter exceeded specified height")
  let bpp := bytesPerPixel w.header
  let filtered := filterScanline ft rowBytes w.prevRow bpp
  let mut newRaw := w.rawStream
  newRaw := newRaw.push ft.toNat.toUInt8
  for b in filtered do newRaw := newRaw.push b
  .ok { w with
    currentRow := w.currentRow + 1
    prevRow    := rowBytes
    rawStream  := newRaw
  }

/- REF: docs/STDLIB_PNG.md#22-pngwriter-push-state-machine -/
/-- Finalizes the PNG stream, emitting signature, IHDR, compressed IDAT, and IEND chunks. -/
def endPng (w : PngWriter) : Except PngError ByteArray := do
  if w.currentRow != w.header.height then
    throw (.custom s!"PngWriter expected {w.header.height} rows, got {w.currentRow}")

  let mut out := ByteArray.empty
  -- 1. PNG Signature
  for b in pngSignature do out := out.push b

  -- 2. IHDR Chunk
  let mut ihdrData := ByteArray.empty
  let wVal := w.header.width.toUInt32
  ihdrData := ihdrData.push ((wVal >>> 24) &&& 0xFF).toUInt8
  ihdrData := ihdrData.push ((wVal >>> 16) &&& 0xFF).toUInt8
  ihdrData := ihdrData.push ((wVal >>> 8) &&& 0xFF).toUInt8
  ihdrData := ihdrData.push (wVal &&& 0xFF).toUInt8
  let hVal := w.header.height.toUInt32
  ihdrData := ihdrData.push ((hVal >>> 24) &&& 0xFF).toUInt8
  ihdrData := ihdrData.push ((hVal >>> 16) &&& 0xFF).toUInt8
  ihdrData := ihdrData.push ((hVal >>> 8) &&& 0xFF).toUInt8
  ihdrData := ihdrData.push (hVal &&& 0xFF).toUInt8
  ihdrData := ihdrData.push w.header.bitDepth.toUInt8
  ihdrData := ihdrData.push w.header.colorType.toNat.toUInt8
  ihdrData := ihdrData.push w.header.compressionMethod.toUInt8
  ihdrData := ihdrData.push w.header.filterMethod.toUInt8
  ihdrData := ihdrData.push w.header.interlaceMethod.toUInt8
  let ihdrChunk := mkChunk "IHDR" ihdrData
  for b in ihdrChunk do out := out.push b

  -- 3. IDAT Chunk (ZLIB compressed payload)
  let compressedIdat := zlibCompress w.rawStream
  let idatChunk := mkChunk "IDAT" compressedIdat
  for b in idatChunk do out := out.push b

  -- 4. IEND Chunk
  let iendChunk := mkChunk "IEND" ByteArray.empty
  for b in iendChunk do out := out.push b

  .ok out

/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- Encodes an ImageRGBA8 structure into a complete, valid PNG byte stream using optional filter or adaptive filter heuristic. -/
def encodeImageRGBA8 (img : ImageRGBA8) (ft : Option FilterType := none) : ByteArray :=
  Id.run do
    let header : PngHeader := {
      width     := img.width
      height    := img.height
      bitDepth  := 8
      colorType := .truecolorRgba
    }
    let mut writer := beginPng header
    let rowStride := img.width * 4
    for y in [0:img.height] do
      let rowSlice := img.pixels.extract (y * rowStride) ((y + 1) * rowStride)
      let chosenFt := match ft with
        | some filter => filter
        | none => chooseBestFilter rowSlice writer.prevRow 4
      match writeScanline writer rowSlice chosenFt with
      | .ok nextWriter => writer := nextWriter
      | .error _ => ()
    match endPng writer with
    | .ok bytes => bytes
    | .error _ => ByteArray.empty

/- REF: docs/STDLIB_PNG.md#32-color-types-bit-depth-matrix -/
/-- Unpacks raw scanlines from 1, 2, 4, 8, or 16-bit PNG color formats into standard 32-bit RGBA8
    pixels with tRNS transparency. Total by construction: `parseIhdr` (`Stdlib/Png/Spec.lean`)
    already rejects any `bitDepth`/`colorType` pair not in RFC 2083 §4.1.1's legal set before a
    header can reach here, but this function does not rely on that upstream guarantee -- every
    depth/colorType combination its `if`/`match` dispatch does not otherwise handle (an illegal
    `bitDepth`, or the `bitDepth = 16` + `colorType = .indexed` combination RFC 2083 also
    forbids) falls through to an explicit `.unsupportedBitDepth` error instead of silently
    producing a truncated or empty pixel buffer -- the defect the parser-stability fuzzer
    (`Stdlib/Png/StabilityFuzzer.lean`) found. An unhandled combination is a real possibility a
    caller must plan for (any future direct caller of this function, not routed through
    `parseIhdr`, could still pass one), not a can't-happen case, so this is `Except PngError
    ByteArray` rather than a refinement-typed `PngHeader` that made illegal pairs unrepresentable
    -- the latter would also have broken `StabilityFuzzer.genCustomHeaderBytes`, which
    deliberately constructs spec-illegal headers via the same `PngHeader` type to drive this
    exact gap. -/
def unpackScanlinesToRGBA8 (header : PngHeader) (rawScanlines : ByteArray) (palette : Array (UInt8 × UInt8 × UInt8)) (transparency : Option ByteArray := none) : Except PngError ByteArray := do
    let mut out := ByteArray.empty
    let depth := header.bitDepth
    let w := header.width
    let h := header.height
    let scanlineLen := scanlineByteLength header

    for y in [0:h] do
      let scanline := rawScanlines.extract (y * scanlineLen) ((y + 1) * scanlineLen)
      if depth == 8 then
        match header.colorType with
        | .truecolorRgba =>
          for b in scanline do out := out.push b
        | .truecolorRgb =>
          for i in [0:w] do
            let r := scanline.get! (i * 3)
            let g := scanline.get! (i * 3 + 1)
            let b := scanline.get! (i * 3 + 2)
            let a : UInt8 := match transparency with
              | some trns => if trns.size >= 6 && r == trns.get! 1 && g == trns.get! 3 && b == trns.get! 5 then 0 else 255
              | none => 255
            out := out.push r; out := out.push g; out := out.push b; out := out.push a
        | .grayscale =>
          for i in [0:w] do
            let yVal := scanline.get! i
            let a : UInt8 := match transparency with
              | some trns => if trns.size >= 2 && yVal == trns.get! 1 then 0 else 255
              | none => 255
            out := out.push yVal; out := out.push yVal; out := out.push yVal; out := out.push a
        | .grayscaleAlpha =>
          for i in [0:w] do
            let yVal := scanline.get! (i * 2)
            let a := scanline.get! (i * 2 + 1)
            out := out.push yVal; out := out.push yVal; out := out.push yVal; out := out.push a
        | .indexed =>
          for i in [0:w] do
            let idx := (scanline.get! i).toNat
            let (r, g, b) := if idx < palette.size then palette[idx]! else (0, 0, 0)
            let a : UInt8 := match transparency with
              | some trns => if idx < trns.size then trns.get! idx else 255
              | none => 255
            out := out.push r; out := out.push g; out := out.push b; out := out.push a

      else if depth == 16 then
        match header.colorType with
        | .truecolorRgba =>
          for i in [0:w] do
            let r := scanline.get! (i * 8)
            let g := scanline.get! (i * 8 + 2)
            let b := scanline.get! (i * 8 + 4)
            let a := scanline.get! (i * 8 + 6)
            out := out.push r; out := out.push g; out := out.push b; out := out.push a
        | .truecolorRgb =>
          for i in [0:w] do
            let rHi := scanline.get! (i * 6)
            let rLo := scanline.get! (i * 6 + 1)
            let gHi := scanline.get! (i * 6 + 2)
            let gLo := scanline.get! (i * 6 + 3)
            let bHi := scanline.get! (i * 6 + 4)
            let bLo := scanline.get! (i * 6 + 5)
            let r16 := (rHi.toNat <<< 8) ||| rLo.toNat
            let g16 := (gHi.toNat <<< 8) ||| gLo.toNat
            let b16 := (bHi.toNat <<< 8) ||| bLo.toNat
            let a : UInt8 := match transparency with
              | some trns =>
                if trns.size >= 6 then
                  let keyR := ((trns.get! 0).toNat <<< 8) ||| (trns.get! 1).toNat
                  let keyG := ((trns.get! 2).toNat <<< 8) ||| (trns.get! 3).toNat
                  let keyB := ((trns.get! 4).toNat <<< 8) ||| (trns.get! 5).toNat
                  if r16 == keyR && g16 == keyG && b16 == keyB then 0 else 255
                else 255
              | none => 255
            out := out.push rHi; out := out.push gHi; out := out.push bHi; out := out.push a
        | .grayscale =>
          for i in [0:w] do
            let yHi := scanline.get! (i * 2)
            let yLo := scanline.get! (i * 2 + 1)
            let y16 := (yHi.toNat <<< 8) ||| yLo.toNat
            let a : UInt8 := match transparency with
              | some trns =>
                if trns.size >= 2 then
                  let keyY := ((trns.get! 0).toNat <<< 8) ||| (trns.get! 1).toNat
                  if y16 == keyY then 0 else 255
                else 255
              | none => 255
            out := out.push yHi; out := out.push yHi; out := out.push yHi; out := out.push a
        | .grayscaleAlpha =>
          for i in [0:w] do
            let yVal := scanline.get! (i * 4)
            let a := scanline.get! (i * 4 + 2)
            out := out.push yVal; out := out.push yVal; out := out.push yVal; out := out.push a
        | .indexed =>
          -- RFC 2083 §4.1.1 does not list bitDepth=16 as legal for colorType=indexed (only
          -- 1/2/4/8 are); `parseIhdr` now rejects this combination before it can reach here
          -- (REF: png-rfc2083#section-4.1.1), but this dispatch stays total on its own: a
          -- silent no-op here would drop this row's pixel data instead of surfacing an error,
          -- which is exactly the class of defect the parser-stability fuzzer found for the
          -- unhandled-depth case below.
          throw (.unsupportedBitDepth depth)

      else if depth == 1 then
        for i in [0:w] do
          let byteIdx := i / 8
          let bitOffset := 7 - (i % 8)
          let b := scanline.get! byteIdx
          let val := (b.toNat >>> bitOffset) &&& 1
          if header.colorType == .indexed then
            let (r, g, b) := if val < palette.size then palette[val]! else (0, 0, 0)
            let a : UInt8 := match transparency with
              | some trns => if val < trns.size then trns.get! val else 255
              | none => 255
            out := out.push r; out := out.push g; out := out.push b; out := out.push a
          else
            let lum : UInt8 := if val == 1 then 255 else 0
            let a : UInt8 := match transparency with
              | some trns =>
                if trns.size >= 2 then
                  let keyY := ((trns.get! 0).toNat <<< 8) ||| (trns.get! 1).toNat
                  if val == keyY then 0 else 255
                else 255
              | none => 255
            out := out.push lum; out := out.push lum; out := out.push lum; out := out.push a

      else if depth == 2 then
        for i in [0:w] do
          let byteIdx := i / 4
          let bitOffset := (3 - (i % 4)) * 2
          let b := scanline.get! byteIdx
          let val := (b.toNat >>> bitOffset) &&& 3
          if header.colorType == .indexed then
            let (r, g, b) := if val < palette.size then palette[val]! else (0, 0, 0)
            let a : UInt8 := match transparency with
              | some trns => if val < trns.size then trns.get! val else 255
              | none => 255
            out := out.push r; out := out.push g; out := out.push b; out := out.push a
          else
            let lum := (val * 85).toUInt8
            let a : UInt8 := match transparency with
              | some trns =>
                if trns.size >= 2 then
                  let keyY := ((trns.get! 0).toNat <<< 8) ||| (trns.get! 1).toNat
                  if val == keyY then 0 else 255
                else 255
              | none => 255
            out := out.push lum; out := out.push lum; out := out.push lum; out := out.push a

      else if depth == 4 then
        for i in [0:w] do
          let byteIdx := i / 2
          let bitOffset := (1 - (i % 2)) * 4
          let b := scanline.get! byteIdx
          let val := (b.toNat >>> bitOffset) &&& 15
          if header.colorType == .indexed then
            let (r, g, b) := if val < palette.size then palette[val]! else (0, 0, 0)
            let a : UInt8 := match transparency with
              | some trns => if val < trns.size then trns.get! val else 255
              | none => 255
            out := out.push r; out := out.push g; out := out.push b; out := out.push a
          else
            let lum := (val * 17).toUInt8
            let a : UInt8 := match transparency with
              | some trns =>
                if trns.size >= 2 then
                  let keyY := ((trns.get! 0).toNat <<< 8) ||| (trns.get! 1).toNat
                  if val == keyY then 0 else 255
                else 255
              | none => 255
            out := out.push lum; out := out.push lum; out := out.push lum; out := out.push a

      else
        -- No arm above handles this bitDepth: it is outside PNG's standard 5-value set
        -- {1, 2, 4, 8, 16} (RFC 2083 §4.1.1). `parseIhdr` now rejects such a header before it
        -- can reach here, but this dispatch does not rely on that upstream guarantee -- an
        -- unhandled depth is an explicit error, not a silently-empty row, so this function
        -- cannot again produce a truncated/empty pixel buffer the way it did for the class of
        -- input the parser-stability fuzzer (Stdlib/Png/StabilityFuzzer.lean) found.
        throw (.unsupportedBitDepth depth)

    return out

/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- Decodes a PNG byte stream into an in-memory ImageRGBA8 structure across all bit depths and color formats. -/
def decodeImageRGBA8 (bytes : ByteArray) : Except PngError ImageRGBA8 := do
  let sink : MemoryImageSink := {}
  let innerSink ← readPngStream (m := Except PngError) (SinkState := MemoryImageSink) bytes sink
  let (finalSink : MemoryImageSink) ← innerSink
  let (header : PngHeader) ← match finalSink.header with
    | some h => pure h
    | none => throw .missingIhdr

  let rgbaPixels ← unpackScanlinesToRGBA8 header finalSink.pixels finalSink.palette finalSink.transparency
  .ok {
    width  := header.width
    height := header.height
    pixels := rgbaPixels
  }

end Stdlib.Png
