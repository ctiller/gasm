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

/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- Creates a solid-color ImageRGBA8 buffer with specified dimensions. -/
def createImage (width height : Nat) (r g b a : UInt8 := 0) : ImageRGBA8 :=
  Id.run do
    let totalPixels := width * height
    let mut pixels := ByteArray.empty
    for _ in [0:totalPixels] do
      pixels := pixels.push r
      pixels := pixels.push g
      pixels := pixels.push b
      pixels := pixels.push a
    { width := width, height := height, pixels := pixels }

/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- Retrieves pixel at (x, y) coordinates as (R, G, B, A) tuple. -/
def getPixel (img : ImageRGBA8) (x y : Nat) : (UInt8 × UInt8 × UInt8 × UInt8) :=
  if x >= img.width || y >= img.height then (0, 0, 0, 0)
  else
    let offset := (y * img.width + x) * 4
    let r := img.pixels.get! offset
    let g := img.pixels.get! (offset + 1)
    let b := img.pixels.get! (offset + 2)
    let a := img.pixels.get! (offset + 3)
    (r, g, b, a)

/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- Canonical encoder converting ImageRGBA8 into PNG byte stream (defaults to adaptive filter optimization). -/
def encode (img : ImageRGBA8) (ft : Option FilterType := none) : ByteArray :=
  encodeImageRGBA8 img ft

/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- Canonical decoder converting PNG byte stream into ImageRGBA8 buffer. -/
def decode (bytes : ByteArray) : Except PngError ImageRGBA8 :=
  decodeImageRGBA8 bytes

/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- Encodes an ImageRGBA8 buffer and writes it directly to disk as a PNG file. -/
def encodeFile (path : String) (img : ImageRGBA8) (ft : Option FilterType := none) : IO Unit := do
  let bytes := encode img ft
  IO.FS.writeBinFile path bytes

/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- Reads and decodes a PNG file from disk into an ImageRGBA8 buffer. -/
def decodeFile (path : String) : IO (Except PngError ImageRGBA8) := do
  let bytes ← IO.FS.readBinFile path
  pure (decode bytes)

/- REF: docs/STDLIB_PNG.md#21-pngscanlinesink-typeclass -/
/-- Streaming read of PNG bytes into an arbitrary progressive PngScanlineSink. -/
def readStream {m : Type → Type} {SinkState : Type} [Monad m] [PngScanlineSink m SinkState]
    (stream : ByteArray) (initialSink : SinkState) : m (Except PngError SinkState) :=
  readPngStream stream initialSink

end Stdlib.Png
