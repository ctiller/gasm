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
import Stdlib.Zlib.Adler32
import Stdlib.Zlib.Deflate

namespace Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#51-zlib-format-rfc-1950 -/
/-- Compresses a ByteArray into an RFC 1950 ZLIB container stream. -/
def zlibCompress (data : ByteArray) : ByteArray :=
  Id.run do
    let mut out := ByteArray.empty
    -- CMF: CM=8 (Deflate), CINFO=7 (32K window) -> 0x78
    out := out.push 0x78
    -- FLG: FCHECK such that (0x78 * 256 + FLG) % 31 = 0 -> 0x01
    out := out.push 0x01
    -- DEFLATE payload
    let deflated := compress data
    for b in deflated do
      out := out.push b
    -- ADLER-32 (4 bytes big-endian)
    let adler := adler32 data
    out := out.push ((adler >>> 24) &&& 0xFF).toUInt8
    out := out.push ((adler >>> 16) &&& 0xFF).toUInt8
    out := out.push ((adler >>> 8) &&& 0xFF).toUInt8
    out := out.push (adler &&& 0xFF).toUInt8
    out

/- REF: docs/STDLIB_ZLIB.md#51-zlib-format-rfc-1950 -/
/-- Decompresses an RFC 1950 ZLIB container stream and validates Adler-32 checksum. -/
def zlibDecompress (bytes : ByteArray) : Except String ByteArray := do
  if bytes.size < 6 then throw "ZLIB stream too short"
  let cmf := (bytes.get! 0).toNat
  let flg := (bytes.get! 1).toNat
  if (cmf * 256 + flg) % 31 != 0 then throw "Invalid ZLIB CMF/FLG header checksum"
  let cm := cmf &&& 0x0F
  if cm != 8 then throw s!"Unsupported compression method {cm}"
  let fdict := (flg >>> 5) &&& 1
  let dataStart := if fdict == 1 then 6 else 2
  if bytes.size < dataStart + 4 then throw "ZLIB stream truncated before Adler-32"
  let dataEnd := bytes.size - 4
  let deflateSlice := bytes.extract dataStart dataEnd
  let uncompressed ← match decompress deflateSlice with
    | Except.ok res => pure res
    | Except.error e => throw s!"DEFLATE decompression error: {repr e}"
  let b0 := (bytes.get! (bytes.size - 4)).toUInt32
  let b1 := (bytes.get! (bytes.size - 3)).toUInt32
  let b2 := (bytes.get! (bytes.size - 2)).toUInt32
  let b3 := (bytes.get! (bytes.size - 1)).toUInt32
  let expectedAdler := (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3
  let computedAdler := adler32 uncompressed
  if expectedAdler != computedAdler then
    throw s!"Adler-32 mismatch: expected {expectedAdler}, computed {computedAdler}"
  pure uncompressed

end Stdlib.Zlib
