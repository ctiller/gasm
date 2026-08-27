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
import Stdlib.Zlib.Deflate

namespace Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Compresses a ByteArray into an RFC 1952 GZIP container stream using Fixed Huffman (BTYPE=01). -/
def gzipCompress (data : ByteArray) : ByteArray :=
  Id.run do
    let mut out := ByteArray.empty
    -- Header: ID1=0x1F, ID2=0x8B, CM=8, FLG=0, MTIME=0, XFL=2, OS=3
    out := out.push 0x1F
    out := out.push 0x8B
    out := out.push 0x08
    out := out.push 0x00
    -- MTIME (4 bytes = 0)
    out := out.push 0x00
    out := out.push 0x00
    out := out.push 0x00
    out := out.push 0x00
    -- XFL = 2, OS = 3
    out := out.push 0x02
    out := out.push 0x03
    -- DEFLATE Fixed Huffman payload
    let deflated := compressFixed data
    for b in deflated do
      out := out.push b
    -- CRC-32 (4 bytes little-endian)
    let crcVal := crc32 data
    out := out.push (crcVal &&& 0xFF).toUInt8
    out := out.push ((crcVal >>> 8) &&& 0xFF).toUInt8
    out := out.push ((crcVal >>> 16) &&& 0xFF).toUInt8
    out := out.push ((crcVal >>> 24) &&& 0xFF).toUInt8
    -- ISIZE (4 bytes little-endian)
    let isize := data.size.toUInt32
    out := out.push (isize &&& 0xFF).toUInt8
    out := out.push ((isize >>> 8) &&& 0xFF).toUInt8
    out := out.push ((isize >>> 16) &&& 0xFF).toUInt8
    out := out.push ((isize >>> 24) &&& 0xFF).toUInt8
    out

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Compresses a ByteArray into an RFC 1952 GZIP container using DEFLATE stored block (BTYPE=00). -/
def gzipCompressStored (data : ByteArray) : ByteArray :=
  Id.run do
    let mut out := ByteArray.empty
    -- Header: ID1=0x1F, ID2=0x8B, CM=8, FLG=0, MTIME=0, XFL=0, OS=3
    out := out.push 0x1F
    out := out.push 0x8B
    out := out.push 0x08
    out := out.push 0x00
    out := out.push 0x00
    out := out.push 0x00
    out := out.push 0x00
    out := out.push 0x00
    out := out.push 0x00
    out := out.push 0x03
    -- DEFLATE stored block header
    out := out.push 0x01
    let len := data.size.toUInt16
    let nlen := len ^^^ 0xFFFF
    out := out.push (len &&& 0xFF).toUInt8
    out := out.push ((len >>> 8) &&& 0xFF).toUInt8
    out := out.push (nlen &&& 0xFF).toUInt8
    out := out.push ((nlen >>> 8) &&& 0xFF).toUInt8
    -- Data payload
    for b in data do
      out := out.push b
    -- CRC-32 (4 bytes little-endian)
    let crcVal := crc32 data
    out := out.push (crcVal &&& 0xFF).toUInt8
    out := out.push ((crcVal >>> 8) &&& 0xFF).toUInt8
    out := out.push ((crcVal >>> 16) &&& 0xFF).toUInt8
    out := out.push ((crcVal >>> 24) &&& 0xFF).toUInt8
    -- ISIZE (4 bytes little-endian)
    let isize := data.size.toUInt32
    out := out.push (isize &&& 0xFF).toUInt8
    out := out.push ((isize >>> 8) &&& 0xFF).toUInt8
    out := out.push ((isize >>> 16) &&& 0xFF).toUInt8
    out := out.push ((isize >>> 24) &&& 0xFF).toUInt8
    out

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Decompresses an RFC 1952 GZIP container stream and validates CRC-32 and ISIZE. -/
def gzipDecompress (bytes : ByteArray) : Except String ByteArray := do
  if bytes.size < 18 then throw "GZIP stream too short (< 18 bytes)"
  if bytes.get! 0 != 0x1F || bytes.get! 1 != 0x8B then
    throw "Invalid GZIP magic identifier (expected 0x1F 0x8B)"
  let cm := bytes.get! 2
  if cm != 0x08 then throw s!"Unsupported GZIP compression method {cm}"
  let flg := bytes.get! 3
  let mut pos := 10 -- Skip base 10-byte header

  -- FEXTRA
  if (flg &&& 0x04) != 0 then
    if pos + 2 > bytes.size then throw "Truncated FEXTRA field"
    let xlen := (bytes.get! pos).toNat ||| ((bytes.get! (pos + 1)).toNat <<< 8)
    pos := pos + 2 + xlen

  -- FNAME
  if (flg &&& 0x08) != 0 then
    while pos < bytes.size && bytes.get! pos != 0 do
      pos := pos + 1
    pos := pos + 1 -- skip zero byte

  -- FCOMMENT
  if (flg &&& 0x10) != 0 then
    while pos < bytes.size && bytes.get! pos != 0 do
      pos := pos + 1
    pos := pos + 1 -- skip zero byte

  -- FHCRC
  if (flg &&& 0x02) != 0 then
    pos := pos + 2

  if pos + 8 > bytes.size then throw "Truncated GZIP stream before payload/trailer"
  let dataEnd := bytes.size - 8
  let deflateSlice := bytes.extract pos dataEnd
  let uncompressed ← match decompress deflateSlice with
    | Except.ok res => pure res
    | Except.error e => throw s!"DEFLATE decompression error: {repr e}"

  -- Validate CRC-32 (little-endian)
  let c0 := (bytes.get! (bytes.size - 8)).toUInt32
  let c1 := (bytes.get! (bytes.size - 7)).toUInt32
  let c2 := (bytes.get! (bytes.size - 6)).toUInt32
  let c3 := (bytes.get! (bytes.size - 5)).toUInt32
  let expectedCrc := c0 ||| (c1 <<< 8) ||| (c2 <<< 16) ||| (c3 <<< 24)
  let computedCrc := crc32 uncompressed
  if expectedCrc != computedCrc then
    throw s!"CRC-32 mismatch: expected {expectedCrc}, computed {computedCrc}"

  -- Validate ISIZE (little-endian)
  let s0 := (bytes.get! (bytes.size - 4)).toUInt32
  let s1 := (bytes.get! (bytes.size - 3)).toUInt32
  let s2 := (bytes.get! (bytes.size - 2)).toUInt32
  let s3 := (bytes.get! (bytes.size - 1)).toUInt32
  let expectedIsize := s0 ||| (s1 <<< 8) ||| (s2 <<< 16) ||| (s3 <<< 24)
  let computedIsize := uncompressed.size.toUInt32
  if expectedIsize != computedIsize then
    throw s!"ISIZE mismatch: expected {expectedIsize}, computed {computedIsize}"

  pure uncompressed

end Stdlib.Zlib
