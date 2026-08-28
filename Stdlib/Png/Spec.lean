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
import Stdlib.Zlib.CRC32

namespace Stdlib.Png

open Stdlib.Zlib

/- REF: docs/STDLIB_PNG.md#32-color-types-bit-depth-matrix -/
/-- Standard PNG color types (RFC 2083 §4.3). -/
inductive PngColorType where
  | grayscale       : PngColorType -- 0
  | truecolorRgb    : PngColorType -- 2
  | indexed         : PngColorType -- 3
  | grayscaleAlpha  : PngColorType -- 4
  | truecolorRgba   : PngColorType -- 6
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/STDLIB_PNG.md#32-color-types-bit-depth-matrix -/
/-- Converts numeric code to PngColorType. -/
def PngColorType.fromNat? : Nat → Option PngColorType
  | 0 => some .grayscale
  | 2 => some .truecolorRgb
  | 3 => some .indexed
  | 4 => some .grayscaleAlpha
  | 6 => some .truecolorRgba
  | _ => none

/- REF: docs/STDLIB_PNG.md#32-color-types-bit-depth-matrix -/
/-- Converts PngColorType to standard numeric code. -/
def PngColorType.toNat : PngColorType → Nat
  | .grayscale      => 0
  | .truecolorRgb   => 2
  | .indexed        => 3
  | .grayscaleAlpha => 4
  | .truecolorRgba  => 6

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Decoded PNG IHDR image header. -/
structure PngHeader where
  width             : Nat
  height            : Nat
  bitDepth          : Nat
  colorType         : PngColorType
  compressionMethod : Nat := 0
  filterMethod      : Nat := 0
  interlaceMethod   : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/STDLIB_PNG.md#32-color-types-bit-depth-matrix -/
/-- Returns the number of channels for a given color type. -/
def PngColorType.channels : PngColorType → Nat
  | .grayscale      => 1
  | .truecolorRgb   => 3
  | .indexed        => 1
  | .grayscaleAlpha => 2
  | .truecolorRgba  => 4

/- REF: docs/STDLIB_PNG.md#32-color-types-bit-depth-matrix -/
/-- Returns bytes per complete pixel (rounded up to 1 for filter distance per RFC 2083 §6.1). -/
def bytesPerPixel (header : PngHeader) : Nat :=
  Nat.max 1 ((header.colorType.channels * header.bitDepth + 7) / 8)

/- REF: docs/STDLIB_PNG.md#32-color-types-bit-depth-matrix -/
/-- Returns the byte length of a single raw scanline for given header. -/
def scanlineByteLength (header : PngHeader) : Nat :=
  (header.width * header.colorType.channels * header.bitDepth + 7) / 8

/- REF: docs/STDLIB_PNG.md#33-pngerror-inductive-taxonomy -/
/-- Inductive error taxonomy for PNG decoding and encoding. -/
inductive PngError where
  | invalidSignature
  | truncatedStream
  | corruptedChunkHeader
  | crcMismatch (expected : UInt32) (actual : UInt32)
  | missingIhdr
  | invalidIhdrDimensions
  | unsupportedBitDepth (depth : Nat)
  | unsupportedColorType (code : Nat)
  | unsupportedCompressionMethod (code : Nat)
  | unsupportedFilterMethod (code : Nat)
  | unsupportedInterlaceMethod (code : Nat)
  | invalidFilterType (filterType : Nat)
  | prematureEof
  | zlibError (msg : String)
  | custom (msg : String)
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Standard 8-byte PNG magic signature: \x89PNG\r\n\x1a\n. -/
def pngSignature : ByteArray :=
  ByteArray.mk #[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Represents a structured PNG chunk with type, payload, and CRC-32. -/
structure PngChunk where
  chunkType : String
  data      : ByteArray
  crc       : UInt32
  deriving DecidableEq, Inhabited

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Validates whether a ByteArray begins with the 8-byte PNG signature. -/
def checkSignature (bytes : ByteArray) : Bool :=
  if bytes.size < 8 then false
  else
    (bytes.get! 0 == 0x89) &&
    (bytes.get! 1 == 0x50) &&
    (bytes.get! 2 == 0x4E) &&
    (bytes.get! 3 == 0x47) &&
    (bytes.get! 4 == 0x0D) &&
    (bytes.get! 5 == 0x0A) &&
    (bytes.get! 6 == 0x1A) &&
    (bytes.get! 7 == 0x0A)

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Serializes a chunk with length, type, payload, and computed CRC-32. -/
def mkChunk (chunkType : String) (data : ByteArray) : ByteArray :=
  Id.run do
    let typeBytes := chunkType.toUTF8
    let mut chunkRaw := ByteArray.empty
    -- Length (4 bytes big-endian)
    let len := data.size.toUInt32
    chunkRaw := chunkRaw.push ((len >>> 24) &&& 0xFF).toUInt8
    chunkRaw := chunkRaw.push ((len >>> 16) &&& 0xFF).toUInt8
    chunkRaw := chunkRaw.push ((len >>> 8) &&& 0xFF).toUInt8
    chunkRaw := chunkRaw.push (len &&& 0xFF).toUInt8
    -- Type (4 bytes)
    for b in typeBytes do chunkRaw := chunkRaw.push b
    -- Data
    for b in data do chunkRaw := chunkRaw.push b
    -- CRC-32 over Type + Data
    let mut crcBuf := ByteArray.empty
    for b in typeBytes do crcBuf := crcBuf.push b
    for b in data do crcBuf := crcBuf.push b
    let crcVal := crc32 crcBuf
    chunkRaw := chunkRaw.push ((crcVal >>> 24) &&& 0xFF).toUInt8
    chunkRaw := chunkRaw.push ((crcVal >>> 16) &&& 0xFF).toUInt8
    chunkRaw := chunkRaw.push ((crcVal >>> 8) &&& 0xFF).toUInt8
    chunkRaw := chunkRaw.push (crcVal &&& 0xFF).toUInt8
    chunkRaw

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Parses a PNG chunk at given byte position. -/
def parseChunk (bytes : ByteArray) (pos : Nat) : Except PngError (PngChunk × Nat) := do
  if pos + 12 > bytes.size then throw .truncatedStream
  let l0 := (bytes.get! pos).toNat
  let l1 := (bytes.get! (pos + 1)).toNat
  let l2 := (bytes.get! (pos + 2)).toNat
  let l3 := (bytes.get! (pos + 3)).toNat
  let length := (l0 <<< 24) ||| (l1 <<< 16) ||| (l2 <<< 8) ||| l3

  let t0 := bytes.get! (pos + 4)
  let t1 := bytes.get! (pos + 5)
  let t2 := bytes.get! (pos + 6)
  let t3 := bytes.get! (pos + 7)
  let typeBytes := ByteArray.mk #[t0, t1, t2, t3]
  -- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks
  -- Found by the parser-stability fuzzer (Stdlib/Png/StabilityFuzzer.lean): `String.fromUTF8!`
  -- panics (a soft Lean runtime panic -- logged, not a proper `Except` rejection) on a chunk
  -- whose 4-byte type field is not valid UTF-8, and it was reached *before* the CRC check
  -- below that would otherwise reject a corrupted chunk -- so a single flipped bit in any
  -- chunk's type field, from arbitrary/attacker-controlled bytes, hit it. `String.fromUTF8?`
  -- makes this a properly-typed rejection instead; behavior on every valid PNG (whose type
  -- bytes are always ASCII chunk names) is unchanged.
  let chunkType ← match String.fromUTF8? typeBytes with
    | some s => pure s
    | none => throw .corruptedChunkHeader

  let dataStart := pos + 8
  let dataEnd := dataStart + length
  if dataEnd + 4 > bytes.size then throw .truncatedStream
  let chunkData := bytes.extract dataStart dataEnd

  let c0 := (bytes.get! dataEnd).toUInt32
  let c1 := (bytes.get! (dataEnd + 1)).toUInt32
  let c2 := (bytes.get! (dataEnd + 2)).toUInt32
  let c3 := (bytes.get! (dataEnd + 3)).toUInt32
  let expectedCrc := (c0 <<< 24) ||| (c1 <<< 16) ||| (c2 <<< 8) ||| c3

  let mut crcBuf := ByteArray.empty
  for b in typeBytes do crcBuf := crcBuf.push b
  for b in chunkData do crcBuf := crcBuf.push b
  let actualCrc := crc32 crcBuf
  if expectedCrc != actualCrc then
    throw (.crcMismatch expectedCrc actualCrc)

  .ok ({ chunkType := chunkType, data := chunkData, crc := expectedCrc }, dataEnd + 4)

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Parses the 13-byte IHDR chunk data payload into a PngHeader. -/
def parseIhdr (data : ByteArray) : Except PngError PngHeader := do
  if data.size < 13 then throw .truncatedStream
  let w0 := (data.get! 0).toNat
  let w1 := (data.get! 1).toNat
  let w2 := (data.get! 2).toNat
  let w3 := (data.get! 3).toNat
  let width := (w0 <<< 24) ||| (w1 <<< 16) ||| (w2 <<< 8) ||| w3

  let h0 := (data.get! 4).toNat
  let h1 := (data.get! 5).toNat
  let h2 := (data.get! 6).toNat
  let h3 := (data.get! 7).toNat
  let height := (h0 <<< 24) ||| (h1 <<< 16) ||| (h2 <<< 8) ||| h3

  if width == 0 || height == 0 then throw .invalidIhdrDimensions

  let bitDepth := (data.get! 8).toNat
  let colorCode := (data.get! 9).toNat
  let compMethod := (data.get! 10).toNat
  let filterMethod := (data.get! 11).toNat
  let interlaceMethod := (data.get! 12).toNat

  let colorType ← match PngColorType.fromNat? colorCode with
    | some ct => pure ct
    | none => throw (.unsupportedColorType colorCode)

  if compMethod != 0 then throw (.unsupportedCompressionMethod compMethod)
  if filterMethod != 0 then throw (.unsupportedFilterMethod filterMethod)
  if interlaceMethod != 0 then throw (.unsupportedInterlaceMethod interlaceMethod)

  .ok {
    width             := width
    height            := height
    bitDepth          := bitDepth
    colorType         := colorType
    compressionMethod := compMethod
    filterMethod      := filterMethod
    interlaceMethod   := interlaceMethod
  }

/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- Standard 8-bit RGBA image memory representation. -/
structure ImageRGBA8 where
  width  : Nat
  height : Nat
  pixels : ByteArray -- width * height * 4 bytes
  deriving DecidableEq, Inhabited

end Stdlib.Png
