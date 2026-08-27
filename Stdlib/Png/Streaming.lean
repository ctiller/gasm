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

/- REF: docs/STDLIB_PNG.md#21-pngscanlinesink-typeclass -/
/-- Streaming PNG reader feeding decompressed and defiltered scanlines into a PngScanlineSink. -/
partial def readPngStream {m : Type → Type} {SinkState : Type} [Monad m] [PngScanlineSink m SinkState]
    (stream : ByteArray) (initialSink : SinkState) : m (Except PngError SinkState) := do
  if !checkSignature stream then return .error .invalidSignature

  let mut pos := 8
  let mut headerOpt : Option PngHeader := none
  let mut palette : Array (UInt8 × UInt8 × UInt8) := #[]
  let mut transparencyOpt : Option ByteArray := none
  let mut idatAcc := ByteArray.empty
  let mut seenIend := false

  while pos < stream.size && !seenIend do
    match parseChunk stream pos with
    | .error err => return .error err
    | .ok (chunk, nextPos) =>
      pos := nextPos
      if chunk.chunkType == "IHDR" then
        match parseIhdr chunk.data with
        | .error err => return .error err
        | .ok h => headerOpt := some h
      else if chunk.chunkType == "PLTE" then
        let numEntries := chunk.data.size / 3
        let mut pal := #[]
        for i in [0:numEntries] do
          let r := chunk.data.get! (i * 3)
          let g := chunk.data.get! (i * 3 + 1)
          let b := chunk.data.get! (i * 3 + 2)
          pal := pal.push (r, g, b)
        palette := pal
      else if chunk.chunkType == "tRNS" then
        transparencyOpt := some chunk.data
      else if chunk.chunkType == "IDAT" then
        for b in chunk.data do idatAcc := idatAcc.push b
      else if chunk.chunkType == "IEND" then
        seenIend := true

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
/-- Unpacks raw scanlines from 1, 2, 4, 8, or 16-bit PNG color formats into standard 32-bit RGBA8 pixels with tRNS transparency. -/
def unpackScanlinesToRGBA8 (header : PngHeader) (rawScanlines : ByteArray) (palette : Array (UInt8 × UInt8 × UInt8)) (transparency : Option ByteArray := none) : ByteArray :=
  Id.run do
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
          ()

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

    out

/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- Decodes a PNG byte stream into an in-memory ImageRGBA8 structure across all bit depths and color formats. -/
def decodeImageRGBA8 (bytes : ByteArray) : Except PngError ImageRGBA8 := do
  let sink : MemoryImageSink := {}
  let innerSink ← readPngStream (m := Except PngError) (SinkState := MemoryImageSink) bytes sink
  let (finalSink : MemoryImageSink) ← innerSink
  let (header : PngHeader) ← match finalSink.header with
    | some h => pure h
    | none => throw .missingIhdr

  let rgbaPixels := unpackScanlinesToRGBA8 header finalSink.pixels finalSink.palette finalSink.transparency
  .ok {
    width  := header.width
    height := header.height
    pixels := rgbaPixels
  }

end Stdlib.Png
