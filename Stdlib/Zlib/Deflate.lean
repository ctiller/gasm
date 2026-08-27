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
import Stdlib.Zlib.Huffman

namespace Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Structured error taxonomy for DEFLATE / INFLATE operations. -/
inductive ZlibError where
  | unexpectedEof
  | invalidBlockType (btype : Nat)
  | invalidStoredBlockLengths
  | corruptedHuffmanTree
  | invalidDistanceCode (code : Nat)
  | invalidLengthCode (code : Nat)
  | custom (msg : String)
  deriving Repr, DecidableEq, Inhabited

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- LSB-first Bitstream Reader over a ByteArray. -/
structure BitReader where
  bytes    : ByteArray
  bytePos  : Nat := 0
  bitBuf   : UInt32 := 0
  bitCount : Nat := 0
  deriving Inhabited

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Initializes a BitReader from a ByteArray. -/
def mkBitReader (bytes : ByteArray) : BitReader :=
  { bytes := bytes, bytePos := 0, bitBuf := 0, bitCount := 0 }

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Ensures at least `n` bits are available in the bit buffer (up to 24 bits). -/
partial def ensureBits (r : BitReader) (n : Nat) : BitReader :=
  let rec loop (cur : BitReader) : BitReader :=
    if cur.bitCount >= n || cur.bytePos >= cur.bytes.size then cur
    else
      let nextByte := cur.bytes.get! cur.bytePos
      let newBuf := (cur.bitBuf.toNat ||| (nextByte.toNat <<< cur.bitCount)).toUInt32
      loop { cur with bytePos := cur.bytePos + 1, bitBuf := newBuf, bitCount := cur.bitCount + 8 }
  loop r

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Reads `n` bits (LSB-first) from the bitstream. -/
def readBits (r : BitReader) (n : Nat) : Except ZlibError (BitReader × Nat) :=
  let r' := ensureBits r n
  if r'.bitCount < n then .error .unexpectedEof
  else
    let mask := (1 <<< n) - 1
    let val := (r'.bitBuf.toNat &&& mask)
    let newBuf := (r'.bitBuf.toNat >>> n).toUInt32
    let newCount := r'.bitCount - n
    .ok ({ r' with bitBuf := newBuf, bitCount := newCount }, val)

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Drops remaining bits in the current byte, byte-aligning the reader. -/
def alignToByte (r : BitReader) : BitReader :=
  { r with bitBuf := 0, bitCount := 0 }

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Decodes a single Huffman symbol from the bitstream using a decode tree. -/
partial def decodeHuffmanSymbol (r : BitReader) (tree : HuffmanTable) : Except ZlibError (BitReader × Nat) :=
  let rec step (curR : BitReader) (node : HuffmanNode) : Except ZlibError (BitReader × Nat) :=
    match node with
    | HuffmanNode.leaf sym => .ok (curR, sym)
    | HuffmanNode.branch l rOpt =>
      match readBits curR 1 with
      | .error e => .error e
      | .ok (nextR, bit) =>
        let nextNode := if bit == 0 then l else rOpt
        match nextNode with
        | some n => step nextR n
        | none => .error .corruptedHuffmanTree
  step r tree.root

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- LSB-first Bitstream Writer accumulating bytes. -/
structure BitWriter where
  bytes    : ByteArray := ByteArray.empty
  bitBuf   : UInt32 := 0
  bitCount : Nat := 0
  deriving Inhabited

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Writes `n` bits (LSB-first) into the bitstream. -/
def writeBits (w : BitWriter) (value : Nat) (n : Nat) : BitWriter :=
  let newBuf := (w.bitBuf.toNat ||| (value <<< w.bitCount)).toUInt32
  let newCount := w.bitCount + n
  let rec flushBytes (buf : UInt32) (cnt : Nat) (acc : ByteArray) : (UInt32 × Nat × ByteArray) :=
    if cnt >= 8 then
      let byteVal := (buf.toNat &&& 0xFF).toUInt8
      flushBytes ((buf.toNat >>> 8).toUInt32) (cnt - 8) (acc.push byteVal)
    else (buf, cnt, acc)
  let (finalBuf, finalCount, finalBytes) := flushBytes newBuf newCount w.bytes
  { bytes := finalBytes, bitBuf := finalBuf, bitCount := finalCount }

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Flushes any pending bits and byte-aligns the output. -/
def flushBitWriter (w : BitWriter) : ByteArray :=
  if w.bitCount > 0 then
    let byteVal := (w.bitBuf.toNat &&& 0xFF).toUInt8
    w.bytes.push byteVal
  else w.bytes

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- RFC 1951 Length base values and extra bits (codes 257–285). -/
def lengthTable : Array (Nat × Nat) := #[
  (3, 0),   (4, 0),   (5, 0),   (6, 0),   (7, 0),   (8, 0),   (9, 0),   (10, 0),
  (11, 1),  (13, 1),  (15, 1),  (17, 1),
  (19, 2),  (23, 2),  (27, 2),  (31, 2),
  (35, 3),  (43, 3),  (51, 3),  (59, 3),
  (67, 4),  (83, 4),  (99, 4),  (115, 4),
  (131, 5), (163, 5), (195, 5), (227, 5),
  (258, 0)
]

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- RFC 1951 Distance base values and extra bits (codes 0–29). -/
def distanceTable : Array (Nat × Nat) := #[
  (1, 0),     (2, 0),     (3, 0),     (4, 0),
  (5, 1),     (7, 1),     (9, 2),     (13, 2),
  (17, 3),    (25, 3),    (33, 4),    (49, 4),
  (65, 5),    (97, 5),    (129, 6),   (193, 6),
  (257, 7),   (385, 7),   (513, 8),   (769, 8),
  (1025, 9),  (1537, 9),  (2049, 10), (3073, 10),
  (4097, 11), (6145, 11), (8193, 12), (12289, 12),
  (16385, 13), (24577, 13)
]

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Permutation order for Dynamic Huffman code length alphabet (RFC 1951 §3.2.7). -/
def clenOrder : Array Nat := #[
  16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15
]

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decodes an uncompressed stored block (BTYPE = 00). -/
def decodeStoredBlock (r : BitReader) (out : ByteArray) : Except ZlibError (BitReader × ByteArray) := do
  let rAligned := alignToByte r
  if rAligned.bytePos + 4 > rAligned.bytes.size then throw .unexpectedEof
  let len0 := (rAligned.bytes.get! rAligned.bytePos).toNat
  let len1 := (rAligned.bytes.get! (rAligned.bytePos + 1)).toNat
  let nlen0 := (rAligned.bytes.get! (rAligned.bytePos + 2)).toNat
  let nlen1 := (rAligned.bytes.get! (rAligned.bytePos + 3)).toNat
  let len := len0 ||| (len1 <<< 8)
  let nlen := nlen0 ||| (nlen1 <<< 8)
  if (len ^^^ 0xFFFF) != nlen then throw .invalidStoredBlockLengths
  let start := rAligned.bytePos + 4
  if start + len > rAligned.bytes.size then throw .unexpectedEof
  let mut newOut := out
  for i in [0:len] do
    newOut := newOut.push (rAligned.bytes.get! (start + i))
  .ok ({ rAligned with bytePos := start + len }, newOut)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decodes LZ77 literals and match back-references using literal and distance Huffman tables. -/
partial def decodeHuffmanStream (r : BitReader) (litTable distTable : HuffmanTable) (out : ByteArray) : Except ZlibError (BitReader × ByteArray) := do
  let mut curR := r
  let mut curOut := out
  let mut done := false
  while !done do
    let (nextR, sym) ← decodeHuffmanSymbol curR litTable
    curR := nextR
    if sym < 256 then
      curOut := curOut.push sym.toUInt8
    else if sym == 256 then
      done := true
    else if sym <= 285 then
      let lenIdx := sym - 257
      let (baseLen, extraBits) := lengthTable[lenIdx]!
      let (rLen, extraVal) ← if extraBits > 0 then readBits curR extraBits else pure (curR, 0)
      curR := rLen
      let matchLen := baseLen + extraVal

      let (rDistSym, distSym) ← decodeHuffmanSymbol curR distTable
      curR := rDistSym
      if distSym >= 30 then throw (.invalidDistanceCode distSym)
      let (baseDist, distExtraBits) := distanceTable[distSym]!
      let (rDist, distExtraVal) ← if distExtraBits > 0 then readBits curR distExtraBits else pure (curR, 0)
      curR := rDist
      let matchDist := baseDist + distExtraVal

      if matchDist == 0 || matchDist > curOut.size then
        throw (.custom s!"Invalid back-reference distance {matchDist} on output size {curOut.size}")
      for _ in [0:matchLen] do
        let srcIdx := curOut.size - matchDist
        let b := curOut.get! srcIdx
        curOut := curOut.push b
    else
      throw (.invalidLengthCode sym)
  .ok (curR, curOut)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decodes a dynamic Huffman block header (BTYPE = 10) and returns the constructed tables. -/
partial def decodeDynamicTables (r : BitReader) : Except ZlibError (BitReader × HuffmanTable × HuffmanTable) := do
  let (r1, hlitVal) ← readBits r 5
  let (r2, hdistVal) ← readBits r1 5
  let (r3, hclenVal) ← readBits r2 4
  let hlit := hlitVal + 257
  let hdist := hdistVal + 1
  let hclen := hclenVal + 4

  let mut curR := r3
  let mut clenArr : Array Nat := Array.replicate 19 0
  for i in [0:hclen] do
    let (nextR, bitLen) ← readBits curR 3
    curR := nextR
    clenArr := clenArr.set! clenOrder[i]! bitLen
  let clenTable := buildHuffmanTable clenArr 7

  let totalLengths := hlit + hdist
  let mut lengths : Array Nat := Array.mkEmpty totalLengths
  while lengths.size < totalLengths do
    let (nextR, sym) ← decodeHuffmanSymbol curR clenTable
    curR := nextR
    if sym <= 15 then
      lengths := lengths.push sym
    else if sym == 16 then
      if lengths.isEmpty then throw .corruptedHuffmanTree
      let lastVal := lengths[lengths.size - 1]!
      let (rRepeat, extra) ← readBits curR 2
      curR := rRepeat
      let repeatCount := extra + 3
      for _ in [0:repeatCount] do
        lengths := lengths.push lastVal
    else if sym == 17 then
      let (rRepeat, extra) ← readBits curR 3
      curR := rRepeat
      let repeatCount := extra + 3
      for _ in [0:repeatCount] do
        lengths := lengths.push 0
    else if sym == 18 then
      let (rRepeat, extra) ← readBits curR 7
      curR := rRepeat
      let repeatCount := extra + 11
      for _ in [0:repeatCount] do
        lengths := lengths.push 0
    else
      throw .corruptedHuffmanTree

  let litLengths := lengths.extract 0 hlit
  let distLengths := lengths.extract hlit totalLengths
  let litTable := buildHuffmanTable litLengths 15
  let distTable := buildHuffmanTable distLengths 15
  .ok (curR, litTable, distTable)

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Core RFC 1951 INFLATE decompressor. -/
partial def decompress (bytes : ByteArray) : Except ZlibError ByteArray := do
  let mut r := mkBitReader bytes
  let mut out := ByteArray.empty
  let mut isFinal := false
  while !isFinal do
    let (rBfinal, bfinal) ← readBits r 1
    let (rBtype, btype) ← readBits rBfinal 2
    r := rBtype
    isFinal := bfinal == 1
    match btype with
    | 0 =>
      let (nextR, nextOut) ← decodeStoredBlock r out
      r := nextR
      out := nextOut
    | 1 =>
      let (nextR, nextOut) ← decodeHuffmanStream r fixedLitLenTable fixedDistTable out
      r := nextR
      out := nextOut
    | 2 =>
      let (rTables, litTbl, distTbl) ← decodeDynamicTables r
      let (nextR, nextOut) ← decodeHuffmanStream rTables litTbl distTbl out
      r := nextR
      out := nextOut
    | _ =>
      throw (.invalidBlockType btype)
  .ok out

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Reverses the lowest `len` bits of a number for LSB-first bitstream packing. -/
def reverseBits (code : Nat) (len : Nat) : Nat :=
  Id.run do
    let mut res := 0
    let mut c := code
    for _ in [0:len] do
      res := (res <<< 1) ||| (c &&& 1)
      c := c >>> 1
    res

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Encodes match length (3..258) into symbol code, extra bit count, and extra bit value. -/
def encodeLength (len : Nat) : (Nat × Nat × Nat) :=
  if len < 3 then (257, 0, 0)
  else if len <= 10 then (257 + len - 3, 0, 0)
  else if len <= 12 then (265, 1, len - 11)
  else if len <= 14 then (266, 1, len - 13)
  else if len <= 16 then (267, 1, len - 15)
  else if len <= 18 then (268, 1, len - 17)
  else if len <= 22 then (269, 2, len - 19)
  else if len <= 26 then (270, 2, len - 23)
  else if len <= 30 then (271, 2, len - 27)
  else if len <= 34 then (272, 2, len - 31)
  else if len <= 42 then (273, 3, len - 35)
  else if len <= 50 then (274, 3, len - 43)
  else if len <= 58 then (275, 3, len - 51)
  else if len <= 66 then (276, 3, len - 59)
  else if len <= 82 then (277, 4, len - 67)
  else if len <= 98 then (278, 4, len - 83)
  else if len <= 114 then (279, 4, len - 99)
  else if len <= 130 then (280, 4, len - 115)
  else if len <= 162 then (281, 5, len - 131)
  else if len <= 194 then (282, 5, len - 163)
  else if len <= 226 then (283, 5, len - 195)
  else if len <= 257 then (284, 5, len - 227)
  else (285, 0, 0)

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Encodes match backward distance (1..32768) into distance symbol code, extra bit count, and extra bit value. -/
def encodeDistance (dist : Nat) : (Nat × Nat × Nat) :=
  if dist <= 4 then (dist - 1, 0, 0)
  else if dist <= 6 then (4, 1, dist - 5)
  else if dist <= 8 then (5, 1, dist - 7)
  else if dist <= 12 then (6, 2, dist - 9)
  else if dist <= 16 then (7, 2, dist - 13)
  else if dist <= 24 then (8, 3, dist - 17)
  else if dist <= 32 then (9, 3, dist - 25)
  else if dist <= 48 then (10, 4, dist - 33)
  else if dist <= 64 then (11, 4, dist - 49)
  else if dist <= 96 then (12, 5, dist - 65)
  else if dist <= 128 then (13, 5, dist - 97)
  else if dist <= 192 then (14, 6, dist - 129)
  else if dist <= 256 then (15, 6, dist - 193)
  else if dist <= 384 then (16, 7, dist - 257)
  else if dist <= 512 then (17, 7, dist - 385)
  else if dist <= 768 then (18, 8, dist - 513)
  else if dist <= 1024 then (19, 8, dist - 769)
  else if dist <= 1536 then (20, 9, dist - 1025)
  else if dist <= 2048 then (21, 9, dist - 1537)
  else if dist <= 3072 then (22, 10, dist - 2049)
  else if dist <= 4096 then (23, 10, dist - 3073)
  else if dist <= 6144 then (24, 11, dist - 4097)
  else if dist <= 8192 then (25, 11, dist - 6145)
  else if dist <= 12288 then (26, 12, dist - 8193)
  else if dist <= 16384 then (27, 12, dist - 12289)
  else if dist <= 24576 then (28, 13, dist - 16385)
  else (29, 13, dist - 24577)

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- LZ77 match search finding longest matching substring in sliding lookback window. -/
def findLongestMatch (data : ByteArray) (pos : Nat) (maxLookback : Nat := 32768) (maxTries : Nat := 128) : (Nat × Nat) :=
  Id.run do
    let total := data.size
    if pos + 3 > total then return (0, 0)
    let startLookback := if pos > maxLookback then pos - maxLookback else 0
    let mut bestLen := 0
    let mut bestDist := 0
    let maxMatchLen := Nat.min 258 (total - pos)

    let mut candidate := pos
    let mut tries := 0
    while candidate > startLookback && tries < maxTries do
      candidate := candidate - 1
      tries := tries + 1
      if data.get! candidate == data.get! pos &&
         data.get! (candidate + 1) == data.get! (pos + 1) &&
         data.get! (candidate + 2) == data.get! (pos + 2) then
        let mut len := 3
        while len < maxMatchLen && data.get! (candidate + len) == data.get! (pos + len) do
          len := len + 1
        if len > bestLen then
          bestLen := len
          bestDist := pos - candidate
          if bestLen == 258 then
            return (bestLen, bestDist)

    if bestLen >= 3 then (bestLen, bestDist) else (0, 0)

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Core RFC 1951 DEFLATE compressor (emits Fixed Huffman BTYPE=01 compressed blocks with LZ77). -/
def compress (data : ByteArray) : ByteArray :=
  Id.run do
    let mut w : BitWriter := {}
    -- BFINAL = 1 (1 bit)
    w := writeBits w 1 1
    -- BTYPE = 01 (Fixed Huffman, 2 bits -> value 1)
    w := writeBits w 1 2

    let total := data.size
    let mut pos := 0

    while pos < total do
      let (matchLen, matchDist) := findLongestMatch data pos 32768 128
      if matchLen >= 3 then
        -- 1. Emit Length Code + extra bits
        let (lenCode, lenExtraBits, lenExtraVal) := encodeLength matchLen
        let (code, bitLen) := match fixedLitLenTable.codes[lenCode]! with | some p => p | none => (0, 8)
        w := writeBits w (reverseBits code bitLen) bitLen
        if lenExtraBits > 0 then
          w := writeBits w lenExtraVal lenExtraBits

        -- 2. Emit Distance Code + extra bits
        let (distCode, distExtraBits, distExtraVal) := encodeDistance matchDist
        let (dCode, dBitLen) := match fixedDistTable.codes[distCode]! with | some p => p | none => (0, 5)
        w := writeBits w (reverseBits dCode dBitLen) dBitLen
        if distExtraBits > 0 then
          w := writeBits w distExtraVal distExtraBits

        pos := pos + matchLen
      else
        -- Literal byte (0..255)
        let b := (data.get! pos).toNat
        let (code, bitLen) := match fixedLitLenTable.codes[b]! with | some p => p | none => (0, 8)
        w := writeBits w (reverseBits code bitLen) bitLen
        pos := pos + 1

    -- End of block (symbol 256)
    let eobCode := reverseBits 0 7
    w := writeBits w eobCode 7

    flushBitWriter w

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Pure RFC 1951 Fixed Huffman block compressor matching assembly machine code engine. -/
def compressFixed (data : ByteArray) : ByteArray :=
  Id.run do
    let mut w : BitWriter := {}
    -- BFINAL = 1 (1 bit), BTYPE = 01 (2 bits) -> 3 bits of 0b011 = 3
    w := writeBits w 3 3

    let mut pos := 0
    while pos < data.size do
      let (matchLen, matchDist) := findLongestMatch data pos 32768 128
      if matchLen >= 3 then
        -- 1. Emit Length Code + extra bits
        let (lenSymbol, lenExtraBits, lenExtraVal) :=
          if matchLen == 258 then (285, 0, 0)
          else if matchLen <= 10 then (257 + matchLen - 3, 0, 0)
          else if matchLen <= 18 then (265 + (matchLen - 11) / 2, 1, (matchLen - 11) &&& 1)
          else if matchLen <= 34 then (269 + (matchLen - 19) / 4, 2, (matchLen - 19) &&& 3)
          else if matchLen <= 66 then (273 + (matchLen - 35) / 8, 3, (matchLen - 35) &&& 7)
          else if matchLen <= 130 then (277 + (matchLen - 67) / 16, 4, (matchLen - 67) &&& 15)
          else (281 + (matchLen - 131) / 32, 5, (matchLen - 131) &&& 31)

        if lenSymbol <= 279 then
          let code := reverseBits (lenSymbol - 256) 7
          w := writeBits w code 7
        else
          let code := reverseBits (lenSymbol - 280 + 0xC0) 8
          w := writeBits w code 8

        if lenExtraBits > 0 then
          w := writeBits w lenExtraVal lenExtraBits

        -- 2. Emit Distance Code + extra bits (5-bit Fixed Huffman distance code = rev5(distCode))
        let (distCode, distExtraBits, distExtraVal) := encodeDistance matchDist
        let dCode := reverseBits distCode 5
        w := writeBits w dCode 5
        if distExtraBits > 0 then
          w := writeBits w distExtraVal distExtraBits

        pos := pos + matchLen
      else
        let byteVal := (data.get! pos).toNat
        if byteVal <= 143 then
          let code := reverseBits (byteVal + 0x30) 8
          w := writeBits w code 8
        else
          let code := reverseBits (byteVal - 144 + 0x190) 9
          w := writeBits w code 9
        pos := pos + 1

    -- End of block (symbol 256 = 7 bits of 0)
    w := writeBits w 0 7
    flushBitWriter w

end Stdlib.Zlib
