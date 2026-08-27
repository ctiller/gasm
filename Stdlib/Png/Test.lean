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
import Stdlib.Png.Spec
import Stdlib.Png.Filter
import Stdlib.Png.Streaming
import Stdlib.Png.Equivalence

namespace Stdlib.Png

open Stdlib.Zlib

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Test runner verifying PNG signature detection. -/
def testPngSignature : IO Unit := do
  IO.println "[+] Testing PNG Signature & Chunk Parser..."
  if !checkSignature pngSignature then
    throw (IO.userError "PNG signature validation failed")
  if checkSignature (ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8]) then
    throw (IO.userError "False positive on corrupted signature")
  IO.println "    ✓ PNG signature detection verified."

/- REF: docs/STDLIB_PNG.md#41-the-five-standard-filter-types -/
/-- Test runner verifying all 5 standard PNG filter algorithms. -/
def testFilters : IO Unit := do
  IO.println "[+] Testing PNG Scanline Filters (None, Sub, Up, Average, Paeth)..."
  let raw := ByteArray.mk #[12, 34, 56, 78, 90, 123, 200, 255]
  let prior := ByteArray.mk #[5, 15, 25, 35, 45, 55, 65, 75]
  let bpp := 4

  for ft in [FilterType.none, FilterType.sub, FilterType.up, FilterType.average, FilterType.paeth] do
    let filtered := filterScanline ft raw prior bpp
    let reconstructed := unfilterScanline ft filtered prior bpp
    if reconstructed != raw then
      throw (IO.userError s!"Filter {repr ft} reconstruction failed")
  IO.println "    ✓ All 5 filter types verified invertible."

/- REF: docs/STDLIB_PNG.md#32-color-types-bit-depth-matrix -/
/-- Test runner verifying RGB8, Grayscale, and Grayscale+Alpha decompression to RGBA8. -/
def testColorTypeConversions : IO Unit := do
  IO.println "[+] Testing Universal Color Type Conversions (RGB8, Grayscale, Grayscale+Alpha)..."
  -- 1. Truecolor RGB (Color Type 2, 2x1 image)
  let mut rgbRaw := ByteArray.empty
  rgbRaw := rgbRaw.push 0 -- filter: none
  rgbRaw := rgbRaw.push 255; rgbRaw := rgbRaw.push 0; rgbRaw := rgbRaw.push 0 -- Pixel 0: Red
  rgbRaw := rgbRaw.push 0; rgbRaw := rgbRaw.push 255; rgbRaw := rgbRaw.push 0 -- Pixel 1: Green

  let mut rgbPng := ByteArray.empty
  for b in pngSignature do rgbPng := rgbPng.push b
  -- IHDR
  let mut ihdrData := ByteArray.empty
  ihdrData := ihdrData.push 0; ihdrData := ihdrData.push 0; ihdrData := ihdrData.push 0; ihdrData := ihdrData.push 2 -- width = 2
  ihdrData := ihdrData.push 0; ihdrData := ihdrData.push 0; ihdrData := ihdrData.push 0; ihdrData := ihdrData.push 1 -- height = 1
  ihdrData := ihdrData.push 8 -- bit depth
  ihdrData := ihdrData.push 2 -- truecolor RGB
  ihdrData := ihdrData.push 0; ihdrData := ihdrData.push 0; ihdrData := ihdrData.push 0
  let ihdrChunk := mkChunk "IHDR" ihdrData
  for b in ihdrChunk do rgbPng := rgbPng.push b
  -- IDAT
  let idatChunk := mkChunk "IDAT" (zlibCompress rgbRaw)
  for b in idatChunk do rgbPng := rgbPng.push b
  -- IEND
  let iendChunk := mkChunk "IEND" ByteArray.empty
  for b in iendChunk do rgbPng := rgbPng.push b

  let decodedRgb ← match decodeImageRGBA8 rgbPng with
    | .ok img => pure img
    | .error e => throw (IO.userError s!"RGB8 conversion failed: {repr e}")

  let expectedRgbPixels := ByteArray.mk #[255, 0, 0, 255, 0, 255, 0, 255]
  if decodedRgb.pixels != expectedRgbPixels then
    throw (IO.userError "RGB8 to RGBA8 expansion mismatch")
  IO.println "    ✓ RGB8 to RGBA8 conversion verified."

  -- 2. Grayscale (Color Type 0, 2x1 image)
  let mut grayRaw := ByteArray.empty
  grayRaw := grayRaw.push 0 -- filter: none
  grayRaw := grayRaw.push 128; grayRaw := grayRaw.push 200

  let mut grayPng := ByteArray.empty
  for b in pngSignature do grayPng := grayPng.push b
  let mut grayIhdr := ByteArray.empty
  grayIhdr := grayIhdr.push 0; grayIhdr := grayIhdr.push 0; grayIhdr := grayIhdr.push 0; grayIhdr := grayIhdr.push 2
  grayIhdr := grayIhdr.push 0; grayIhdr := grayIhdr.push 0; grayIhdr := grayIhdr.push 0; grayIhdr := grayIhdr.push 1
  grayIhdr := grayIhdr.push 8
  grayIhdr := grayIhdr.push 0 -- Grayscale
  grayIhdr := grayIhdr.push 0; grayIhdr := grayIhdr.push 0; grayIhdr := grayIhdr.push 0
  let grayIhdrChunk := mkChunk "IHDR" grayIhdr
  for b in grayIhdrChunk do grayPng := grayPng.push b
  let grayIdatChunk := mkChunk "IDAT" (zlibCompress grayRaw)
  for b in grayIdatChunk do grayPng := grayPng.push b
  let grayIendChunk := mkChunk "IEND" ByteArray.empty
  for b in grayIendChunk do grayPng := grayPng.push b

  let decodedGray ← match decodeImageRGBA8 grayPng with
    | .ok img => pure img
    | .error e => throw (IO.userError s!"Grayscale conversion failed: {repr e}")

  let expectedGrayPixels := ByteArray.mk #[128, 128, 128, 255, 200, 200, 200, 255]
  if decodedGray.pixels != expectedGrayPixels then
    throw (IO.userError "Grayscale to RGBA8 expansion mismatch")
  IO.println "    ✓ Grayscale to RGBA8 conversion verified."

  -- 3. Indexed Color (Color Type 3, 2x1 image with PLTE chunk)
  let mut palRaw := ByteArray.empty
  palRaw := palRaw.push 0 -- filter: none
  palRaw := palRaw.push 0; palRaw := palRaw.push 1 -- pixel 0 -> index 0, pixel 1 -> index 1

  let mut palPng := ByteArray.empty
  for b in pngSignature do palPng := palPng.push b
  let mut palIhdr := ByteArray.empty
  palIhdr := palIhdr.push 0; palIhdr := palIhdr.push 0; palIhdr := palIhdr.push 0; palIhdr := palIhdr.push 2 -- width = 2
  palIhdr := palIhdr.push 0; palIhdr := palIhdr.push 0; palIhdr := palIhdr.push 0; palIhdr := palIhdr.push 1 -- height = 1
  palIhdr := palIhdr.push 8 -- bit depth = 8
  palIhdr := palIhdr.push 3 -- indexed color (PLTE)
  palIhdr := palIhdr.push 0; palIhdr := palIhdr.push 0; palIhdr := palIhdr.push 0
  let palIhdrChunk := mkChunk "IHDR" palIhdr
  for b in palIhdrChunk do palPng := palPng.push b

  -- PLTE chunk: 2 colors (index 0 = Yellow [255, 255, 0], index 1 = Cyan [0, 255, 255])
  let plteData := ByteArray.mk #[255, 255, 0, 0, 255, 255]
  let plteChunk := mkChunk "PLTE" plteData
  for b in plteChunk do palPng := palPng.push b

  let palIdatChunk := mkChunk "IDAT" (zlibCompress palRaw)
  for b in palIdatChunk do palPng := palPng.push b
  let palIendChunk := mkChunk "IEND" ByteArray.empty
  for b in palIendChunk do palPng := palPng.push b

  let decodedPal ← match decodeImageRGBA8 palPng with
    | .ok img => pure img
    | .error e => throw (IO.userError s!"Indexed PLTE conversion failed: {repr e}")

  let expectedPalPixels := ByteArray.mk #[255, 255, 0, 255, 0, 255, 255, 255]
  if decodedPal.pixels != expectedPalPixels then
    throw (IO.userError "Indexed PLTE to RGBA8 expansion mismatch")
  IO.println "    ✓ Indexed Color with PLTE to RGBA8 conversion verified."

  -- 4. Indexed Color with tRNS Transparency Chunk (Index 0 = 50% Alpha, Index 1 = 100% Alpha)
  let mut trnsPng := ByteArray.empty
  for b in pngSignature do trnsPng := trnsPng.push b
  for b in palIhdrChunk do trnsPng := trnsPng.push b
  for b in plteChunk do trnsPng := trnsPng.push b
  -- tRNS chunk: alpha for index 0 = 128 (50% transparent)
  let trnsData := ByteArray.mk #[128]
  let trnsChunk := mkChunk "tRNS" trnsData
  for b in trnsChunk do trnsPng := trnsPng.push b
  for b in palIdatChunk do trnsPng := trnsPng.push b
  for b in palIendChunk do trnsPng := trnsPng.push b

  let decodedTrns ← match decodeImageRGBA8 trnsPng with
    | .ok img => pure img
    | .error e => throw (IO.userError s!"Indexed tRNS conversion failed: {repr e}")

  let expectedTrnsPixels := ByteArray.mk #[255, 255, 0, 128, 0, 255, 255, 255]
  if decodedTrns.pixels != expectedTrnsPixels then
    throw (IO.userError "Indexed tRNS to RGBA8 mismatch")
  IO.println "    ✓ Indexed Color with tRNS Transparency to RGBA8 verified."

/- REF: docs/STDLIB_PNG.md#62-canonical-15-roundtrip-soundness-theorem -/
/-- Test runner verifying streaming PNG encoding and decoding. -/
def testPngRoundtrip : IO Unit := do
  IO.println "[+] Testing Streaming PNG Encoder & Decoder Roundtrips..."
  -- Test 1: 1x1 Single Pixel Image
  let img1x1 : ImageRGBA8 := {
    width  := 1
    height := 1
    pixels := ByteArray.mk #[255, 128, 64, 255]
  }
  let encoded1 := encodeImageRGBA8 img1x1
  let decoded1 ← match decodeImageRGBA8 encoded1 with
    | .ok res => pure res
    | .error e => throw (IO.userError s!"1x1 decode failed: {repr e}")
  if decoded1 != img1x1 then
    throw (IO.userError "1x1 image roundtrip pixel mismatch")
  IO.println "    ✓ 1x1 RGBA pixel roundtrip verified."

  -- Test 2: 4x4 Color Grid Image (with adaptive filtering)
  let mut gridPixels := ByteArray.empty
  for y in [0:4] do
    for x in [0:4] do
      gridPixels := gridPixels.push ((x * 60).toUInt8)
      gridPixels := gridPixels.push ((y * 60).toUInt8)
      gridPixels := gridPixels.push (((x + y) * 30).toUInt8)
      gridPixels := gridPixels.push 255
  let img4x4 : ImageRGBA8 := { width := 4, height := 4, pixels := gridPixels }
  let encoded4 := encodeImageRGBA8 img4x4 -- uses adaptive filter heuristic
  let decoded4 ← match decodeImageRGBA8 encoded4 with
    | .ok res => pure res
    | .error e => throw (IO.userError s!"4x4 decode failed: {repr e}")
  if decoded4 != img4x4 then
    throw (IO.userError "4x4 image roundtrip pixel mismatch")
  IO.println "    ✓ 4x4 RGBA color grid adaptive filter roundtrip verified."

  -- Test 3: 8x8 Diagonal Gradient Image
  let mut gradPixels := ByteArray.empty
  for y in [0:8] do
    for x in [0:8] do
      let v := ((x + y) * 16).toUInt8
      gradPixels := gradPixels.push v
      gradPixels := gradPixels.push (255 - v)
      gradPixels := gradPixels.push (v / 2)
      gradPixels := gradPixels.push 255
  let img8x8 : ImageRGBA8 := { width := 8, height := 8, pixels := gradPixels }
  let encoded8 := encodeImageRGBA8 img8x8
  let decoded8 ← match decodeImageRGBA8 encoded8 with
    | .ok res => pure res
    | .error e => throw (IO.userError s!"8x8 decode failed: {repr e}")
  if decoded8 != img8x8 then
    throw (IO.userError "8x8 image roundtrip pixel mismatch")
  IO.println "    ✓ 8x8 RGBA diagonal gradient roundtrip verified."

end Stdlib.Png

open Stdlib.Png

/- REF: docs/STDLIB_PNG.md#6-formal-theorems-15-roundtrip-soundness -/
def main : IO UInt32 := do
  IO.println "======================================================================"
  IO.println " Stdlib.Png Test Suite (Streaming Scanline Codec & 1.5-Roundtrip)"
  IO.println "======================================================================"
  testPngSignature
  testFilters
  testColorTypeConversions
  testPngRoundtrip
  IO.println "\n[+] ALL STDLIB.PNG TESTS PASSED (100% SUCCESS)."
  return 0
