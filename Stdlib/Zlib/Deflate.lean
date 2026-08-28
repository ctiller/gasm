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
def ensureBits (r : BitReader) (n : Nat) : BitReader :=
  let rec loop (cur : BitReader) : BitReader :=
    if cur.bitCount >= n || cur.bytePos >= cur.bytes.size then cur
    else
      let nextByte := cur.bytes.get! cur.bytePos
      let newBuf := (cur.bitBuf.toNat ||| (nextByte.toNat <<< cur.bitCount)).toUInt32
      loop { cur with bytePos := cur.bytePos + 1, bitBuf := newBuf, bitCount := cur.bitCount + 8 }
  termination_by cur.bytes.size - cur.bytePos
  decreasing_by simp_all; omega
  loop r

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Total number of unconsumed bits remaining in a `BitReader`: bits already buffered
    plus 8 bits for every unread byte. This is the natural termination measure for any
    loop that consumes bits from a `BitReader` via `readBits`/`decodeHuffmanSymbol`. -/
def remainingBits (r : BitReader) : Nat :=
  r.bitCount + 8 * (r.bytes.size - r.bytePos)

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- `ensureBits.loop` only moves bits from the unread byte suffix into the bit buffer;
    it never consumes or fabricates bits, so `remainingBits` is invariant. Proved via
    `ensureBits.loop`'s own `.induct` principle, available now that `ensureBits` is
    well-founded rather than `partial` (its equation lemma makes this statable at all). -/
theorem ensureBits_loop_remainingBits (n : Nat) (cur : BitReader) :
    remainingBits (ensureBits.loop n cur) = remainingBits cur := by
  induction cur using ensureBits.loop.induct (n := n) with
  | case1 x hx => rw [ensureBits.loop.eq_1, if_pos hx]
  | case2 x hx nextByte newBuf ih =>
    rw [ensureBits.loop.eq_1, if_neg hx, ih]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hx
    simp only [remainingBits]
    omega

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- `ensureBits` (the top-level wrapper) preserves `remainingBits`. -/
theorem ensureBits_remainingBits (r : BitReader) (n : Nat) :
    remainingBits (ensureBits r n) = remainingBits r := by
  rw [ensureBits.eq_1]
  exact ensureBits_loop_remainingBits n r

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
/-- A successful `readBits r n` consumes exactly `n` bits: `remainingBits` drops by `n`.
    This is the "successful `readBits` strictly shrinks the measure" fact needed to
    justify well-founded recursion over any loop that decodes a `BitReader` stream. -/
theorem readBits_remainingBits (r : BitReader) (n : Nat) (rOut : BitReader) (v : Nat)
    (hok : readBits r n = .ok (rOut, v)) :
    remainingBits rOut + n = remainingBits r := by
  have heq : remainingBits (ensureBits r n) = remainingBits r := ensureBits_remainingBits r n
  unfold readBits at hok
  dsimp only at hok
  split at hok
  · simp at hok
  · rename_i hge
    obtain ⟨hok1, _⟩ := Prod.mk.injEq .. |>.mp (Except.ok.injEq .. |>.mp hok)
    simp only [remainingBits] at heq ⊢
    have hbc : rOut.bitCount = (ensureBits r n).bitCount - n := by rw [← hok1]
    have hbp : rOut.bytePos = (ensureBits r n).bytePos := by rw [← hok1]
    have hbs : rOut.bytes.size = (ensureBits r n).bytes.size := by rw [← hok1]
    omega

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Drops remaining bits in the current byte, byte-aligning the reader. -/
def alignToByte (r : BitReader) : BitReader :=
  { r with bitBuf := 0, bitCount := 0 }

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Decodes a single Huffman symbol from the bitstream using a decode tree. -/
def decodeHuffmanSymbol (r : BitReader) (tree : HuffmanTable) : Except ZlibError (BitReader × Nat) :=
  let rec step (curR : BitReader) (node : HuffmanNode) : Except ZlibError (BitReader × Nat) :=
    match node with
    | HuffmanNode.leaf sym => .ok (curR, sym)
    | HuffmanNode.branch l rOpt =>
      match readBits curR 1 with
      | .error e => .error e
      | .ok (nextR, bit) =>
        if bit == 0 then
          match l with
          | some n => step nextR n
          | none => .error .corruptedHuffmanTree
        else
          match rOpt with
          | some n => step nextR n
          | none => .error .corruptedHuffmanTree
  termination_by node
  decreasing_by all_goals simp_all; omega
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
/-- Pushes `n` copies of `val` onto the end of `arr` (equivalent to the imperative
    `for _ in [0:n] do arr := arr.push val`, expressed as structural recursion on `n`
    so its `.size` effect is provable by induction). -/
def pushRepeated (arr : Array Nat) (val : Nat) (n : Nat) : Array Nat :=
  match n with
  | 0 => arr
  | n + 1 => pushRepeated (arr.push val) val n

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `pushRepeated` grows the array by exactly `n` elements. -/
theorem pushRepeated_size (arr : Array Nat) (val n : Nat) :
    (pushRepeated arr val n).size = arr.size + n := by
  induction n generalizing arr with
  | zero => simp [pushRepeated]
  | succ n ih => simp [pushRepeated, ih, Array.size_push]; omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decodes a dynamic Huffman block header (BTYPE = 10) and returns the constructed tables. -/
def decodeDynamicTables (r : BitReader) : Except ZlibError (BitReader × HuffmanTable × HuffmanTable) := do
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
  let rec go (br : BitReader) (lengths : Array Nat) :
      Except ZlibError (BitReader × Array Nat) :=
    if lengths.size < totalLengths then
      match decodeHuffmanSymbol br clenTable with
      | .error e => .error e
      | .ok (nextR, sym) =>
        if sym <= 15 then
          go nextR (lengths.push sym)
        else if sym == 16 then
          if lengths.isEmpty then .error .corruptedHuffmanTree
          else
            let lastVal := lengths[lengths.size - 1]!
            match readBits nextR 2 with
            | .error e => .error e
            | .ok (rRepeat, extra) =>
              go rRepeat (pushRepeated lengths lastVal (extra + 3))
        else if sym == 17 then
          match readBits nextR 3 with
          | .error e => .error e
          | .ok (rRepeat, extra) =>
            go rRepeat (pushRepeated lengths 0 (extra + 3))
        else if sym == 18 then
          match readBits nextR 7 with
          | .error e => .error e
          | .ok (rRepeat, extra) =>
            go rRepeat (pushRepeated lengths 0 (extra + 11))
        else
          .error .corruptedHuffmanTree
    else .ok (br, lengths)
  termination_by totalLengths - lengths.size
  decreasing_by
    all_goals simp_all [pushRepeated_size]
    all_goals omega

  let (finalR, lengths) ← go curR (Array.mkEmpty totalLengths)

  let litLengths := lengths.extract 0 hlit
  let distLengths := lengths.extract hlit totalLengths
  let litTable := buildHuffmanTable litLengths 15
  let distTable := buildHuffmanTable distLengths 15
  .ok (finalR, litTable, distTable)

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
/-- An LZ77 token: either a literal byte or a (length, distance) back-reference. -/
inductive LZToken where
  | lit (b : UInt8)
  | ref (len dist : Nat)
  deriving Repr, DecidableEq, Inhabited

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Certifies a candidate LZ77 back-reference at `pos`: RFC 1951 length/distance ranges,
    in-bounds source window, and byte-for-byte agreement of the referenced span with the data
    it claims to repeat. `data.get! (pos - dist + i)` with `i` possibly `≥ dist` is exactly
    the decoder's self-overlapping copy semantics (RFC 1951 §3.2.3, "the referenced string
    may overlap the current position"). The match *search* (`findLongestMatch`) is an
    untrusted heuristic; this total checker is what the tokenizer actually relies on, so a
    future roundtrip proof needs only this predicate, never the search's internals. -/
def matchValid (data : ByteArray) (pos len dist : Nat) : Bool :=
  3 ≤ len && len ≤ 258 && 1 ≤ dist && dist ≤ 32768 && dist ≤ pos &&
  pos + len ≤ data.size &&
  (List.range len).all (fun i => data.get! (pos - dist + i) == data.get! (pos + i))

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Greedy LZ77 tokenizer worker: at each position take the longest *certified* match
    (falling back to a literal when the search returns nothing certifiable). Structural
    recursion on `fuel` — never `partial`/`while` — so equation lemmas exist for future
    proofs. Every step advances `pos` by at least 1, so `fuel = data.size` always suffices. -/
def tokenizeAux (data : ByteArray) : Nat → Nat → Array LZToken → Array LZToken
  | 0, _, acc => acc
  | fuel + 1, pos, acc =>
    if pos < data.size then
      let m := findLongestMatch data pos 32768 128
      if 3 ≤ m.1 ∧ matchValid data pos m.1 m.2 = true then
        tokenizeAux data fuel (pos + m.1) (acc.push (.ref m.1 m.2))
      else
        tokenizeAux data fuel (pos + 1) (acc.push (.lit (data.get! pos)))
    else acc

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Greedy LZ77 tokenization of an entire input buffer. -/
def tokenize (data : ByteArray) : Array LZToken :=
  tokenizeAux data data.size 0 #[]

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Reference token-layer back-reference copy: append `len` bytes read `dist` positions back,
    one at a time — byte-for-byte the self-overlap semantics of `decodeHuffmanStream`'s
    RFC 1951 §3.2.3 match-copy loop, as a total structural recursion the kernel can induct
    on. -/
def lzCopy (dist : Nat) : Nat → ByteArray → ByteArray
  | 0, out => out
  | k + 1, out => lzCopy dist k (out.push (out.get! (out.size - dist)))

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Reference token-layer decode of a single LZ77 token onto an output accumulator. -/
def expandToken (out : ByteArray) : LZToken → ByteArray
  | .lit b => out.push b
  | .ref len dist => lzCopy dist len out

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Reference token-layer decode of an LZ77 token stream from an empty accumulator. This is
    the layer of `decompress` below Huffman coding and bitstream framing; `Stdlib/Zlib/
    Equivalence.lean`'s `lz77_roundtrip_soundness` proves `∀ data, expandTokens (tokenize
    data) = data` — the LZ77 half of the PA16 roundtrip decomposition. -/
def expandTokens (tokens : Array LZToken) : ByteArray :=
  tokens.foldl expandToken ByteArray.empty

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Counts literal/length-symbol and distance-symbol frequencies of a token stream,
    including the mandatory end-of-block symbol 256 (RFC 1951 §3.2.6). -/
def tokenFrequencies (tokens : Array LZToken) : Array Nat × Array Nat :=
  Id.run do
    let mut litFreq : Array Nat := Array.replicate 286 0
    let mut distFreq : Array Nat := Array.replicate 30 0
    for t in tokens do
      match t with
      | .lit b =>
        litFreq := litFreq.set! b.toNat (litFreq[b.toNat]! + 1)
      | .ref len dist =>
        let (lenCode, _, _) := encodeLength len
        litFreq := litFreq.set! lenCode (litFreq[lenCode]! + 1)
        let (distCode, _, _) := encodeDistance dist
        distFreq := distFreq.set! distCode (distFreq[distCode]! + 1)
    litFreq := litFreq.set! 256 (litFreq[256]! + 1)
    return (litFreq, distFreq)

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- A package-merge working item: total weight plus the leaf symbols merged into it. -/
structure PMNode where
  weight : Nat
  syms   : List Nat
  deriving Repr, Inhabited

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Pairs adjacent items of a weight-sorted list into packages (odd trailing item dropped),
    the "package" step of the package-merge length-limited coding algorithm. -/
def pmPackage : List PMNode → List PMNode
  | a :: b :: rest => { weight := a.weight + b.weight, syms := a.syms ++ b.syms } :: pmPackage rest
  | _ => []

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Stable merge of two weight-sorted lists, the "merge" step of package-merge. -/
def pmMerge : List PMNode → List PMNode → List PMNode
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys =>
    if x.weight ≤ y.weight then x :: pmMerge xs (y :: ys)
    else y :: pmMerge (x :: xs) ys
termination_by xs ys => xs.length + ys.length

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Length-limited Huffman code lengths via the package-merge (coin-collector) algorithm:
    build `maxBits` levels of packaged+merged lists over the weight-sorted leaves, take the
    first `2n - 2` items of the final list, and read each symbol's code length off as its
    number of occurrences among the taken items. Produces lengths `≤ maxBits` satisfying the
    Kraft equality (a complete prefix code) for any `n ≥ 2` leaf distribution with
    `2 ^ maxBits ≥ n`; a single-leaf distribution is assigned length 1. -/
def packageMergeLengths (freqs : Array Nat) (maxBits : Nat) : Array Nat :=
  let leaves : List PMNode := (List.range freqs.size).filterMap fun s =>
    if freqs[s]! > 0 then some { weight := freqs[s]!, syms := [s] } else none
  let leaves := leaves.mergeSort (fun a b => a.weight ≤ b.weight)
  match leaves with
  | [] => Array.replicate freqs.size 0
  | [only] => (Array.replicate freqs.size 0).set! (only.syms.headD 0) 1
  | _ =>
    let n := leaves.length
    let final := (List.range (maxBits - 1)).foldl
      (fun cur _ => pmMerge leaves (pmPackage cur)) leaves
    let solution := final.take (2 * n - 2)
    Id.run do
      let mut lengths := Array.replicate freqs.size 0
      for item in solution do
        for s in item.syms do
          lengths := lengths.set! s (lengths[s]! + 1)
      return lengths

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Ensures a frequency array has at least two nonzero entries by bumping the smallest-index
    unused symbols. Mirrors zlib `trees.c`'s `build_tree` invariant: every transmitted tree
    has ≥ 2 codes, so both the literal/length and distance trees are always *complete*
    (Kraft equality) — the shape every RFC 1951 inflater accepts unconditionally. -/
def padFrequencies (freqs : Array Nat) : Array Nat :=
  Id.run do
    let mut f := freqs
    let mut nonzero := 0
    for i in [0:f.size] do
      if f[i]! > 0 then nonzero := nonzero + 1
    for j in [0:f.size] do
      if nonzero < 2 && f[j]! == 0 then
        f := f.set! j 1
        nonzero := nonzero + 1
    return f

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Splits a list into maximal runs of equal values, as `(value, count)` pairs. -/
def runLengthsAux (v : Nat) (cnt : Nat) : List Nat → List (Nat × Nat)
  | [] => [(v, cnt)]
  | x :: xs => if x == v then runLengthsAux v (cnt + 1) xs else (v, cnt) :: runLengthsAux x 1 xs

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Splits a list into maximal runs of equal values, as `(value, count)` pairs. -/
def runLengths : List Nat → List (Nat × Nat)
  | [] => []
  | x :: xs => runLengthsAux x 1 xs

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Encodes a run of `cnt` zero code lengths into RFC 1951 §3.2.7 code-length-alphabet
    symbols: 18 (repeat zero 11–138, 7 extra bits), 17 (repeat zero 3–10, 3 extra bits),
    or bare zeros. Each element is `(clenSymbol, extraBitCount, extraBitValue)`. -/
def encodeZeroRun (cnt : Nat) : List (Nat × Nat × Nat) :=
  if cnt ≥ 11 then
    let k := min cnt 138
    (18, 7, k - 11) :: encodeZeroRun (cnt - k)
  else if cnt ≥ 3 then [(17, 3, cnt - 3)]
  else List.replicate cnt (0, 0, 0)
termination_by cnt
decreasing_by omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Encodes `cnt` repeats of the *previous* (already-emitted) nonzero code length using
    symbol 16 (copy previous 3–6 times, 2 extra bits), falling back to bare literals. -/
def encodeRepeatRun (v : Nat) (cnt : Nat) : List (Nat × Nat × Nat) :=
  if cnt ≥ 3 then
    let k := min cnt 6
    (16, 2, k - 3) :: encodeRepeatRun v (cnt - k)
  else List.replicate cnt (v, 0, 0)
termination_by cnt
decreasing_by omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Run-length encodes the concatenated literal/length + distance code-length sequence into
    the RFC 1951 §3.2.7 code length alphabet (symbols 0–18 with their extra bits). -/
def rleCodeLengths (lengths : List Nat) : List (Nat × Nat × Nat) :=
  (runLengths lengths).flatMap fun (v, cnt) =>
    if v == 0 then encodeZeroRun cnt
    else (v, 0, 0) :: encodeRepeatRun v (cnt - 1)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Exact bit cost of one token under given literal/length and distance code-length arrays. -/
def tokenBitCost (litLen distLen : Array Nat) (t : LZToken) : Nat :=
  match t with
  | .lit b => litLen[b.toNat]!
  | .ref len dist =>
    let (lenCode, lenEB, _) := encodeLength len
    let (distCode, distEB, _) := encodeDistance dist
    litLen[lenCode]! + lenEB + distLen[distCode]! + distEB

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Everything needed to emit (or cost) one dynamic-Huffman (BTYPE=10) block. -/
structure DynPlan where
  litLengths  : Array Nat
  distLengths : Array Nat
  clenLengths : Array Nat
  rleTokens   : List (Nat × Nat × Nat)
  hlit        : Nat
  hdist       : Nat
  hclen       : Nat
  deriving Repr, Inhabited

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Index of the last nonzero entry plus one, floored at `atLeast`. -/
def trimmedSize (arr : Array Nat) (atLeast : Nat) : Nat :=
  Id.run do
    let mut n := atLeast
    for i in [0:arr.size] do
      if arr[i]! > 0 then n := max n (i + 1)
    return n

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Builds the dynamic-Huffman block plan for a token stream: package-merge code lengths for
    the literal/length (≤ 15 bits) and distance (≤ 15 bits) alphabets, the RLE'd code-length
    sequence, code lengths for the code-length alphabet itself (≤ 7 bits), and the
    HLIT/HDIST/HCLEN header counts (RFC 1951 §3.2.7). -/
def buildDynPlan (tokens : Array LZToken) : DynPlan :=
  let (litFreqRaw, distFreqRaw) := tokenFrequencies tokens
  let litFreq := padFrequencies litFreqRaw
  let distFreq := padFrequencies distFreqRaw
  let litLengths := packageMergeLengths litFreq 15
  let distLengths := packageMergeLengths distFreq 15
  let hlit := trimmedSize litLengths 257
  let hdist := trimmedSize distLengths 1
  let rleTokens := rleCodeLengths
    ((litLengths.toList.take hlit) ++ (distLengths.toList.take hdist))
  let clenFreq := Id.run do
    let mut f : Array Nat := Array.replicate 19 0
    for (sym, _, _) in rleTokens do
      f := f.set! sym (f[sym]! + 1)
    return f
  let clenLengths := packageMergeLengths (padFrequencies clenFreq) 7
  let hclen := Id.run do
    let mut n := 4
    for i in [0:19] do
      if clenLengths[clenOrder[i]!]! > 0 then n := max n (i + 1)
    return n
  { litLengths, distLengths, clenLengths, rleTokens, hlit, hdist, hclen }

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Exact total bit cost of the dynamic block for this plan and token stream:
    3 header bits + 14 count bits + 3·HCLEN code-length-length bits + RLE symbols with their
    extra bits + token payload + the end-of-block symbol. -/
def dynPlanBitCost (plan : DynPlan) (tokens : Array LZToken) : Nat :=
  let headerBits := 3 + 14 + 3 * plan.hclen
  let rleBits := plan.rleTokens.foldl
    (fun acc (sym, eb, _) => acc + plan.clenLengths[sym]! + eb) 0
  let payloadBits := tokens.foldl
    (fun acc t => acc + tokenBitCost plan.litLengths plan.distLengths t) 0
  headerBits + rleBits + payloadBits + plan.litLengths[256]!

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Exact total bit cost of the fixed-Huffman (BTYPE=01) encoding of a token stream:
    3 header bits + token payload under the RFC 1951 §3.2.6 fixed code + 7-bit end-of-block. -/
def fixedBitCost (tokens : Array LZToken) : Nat :=
  3 + tokens.foldl
    (fun acc t => acc + tokenBitCost fixedLitLenLengths fixedDistLengths t) 0 + 7

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emits one Huffman-coded symbol (canonical code bit-reversed for LSB-first packing).
    A symbol absent from the table is a plan-construction bug; it emits nothing, which the
    differential fuzzers detect as a corrupt stream rather than masking silently. -/
def emitHuffSymbol (w : BitWriter) (table : HuffmanTable) (sym : Nat) : BitWriter :=
  match table.codes[sym]! with
  | some (code, len) => writeBits w (reverseBits code len) len
  | none => w

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emits one LZ77 token under the given literal/length and distance Huffman tables. -/
def emitToken (litTable distTable : HuffmanTable) (w : BitWriter) (t : LZToken) : BitWriter :=
  match t with
  | .lit b => emitHuffSymbol w litTable b.toNat
  | .ref len dist =>
    let (lenCode, lenEB, lenEV) := encodeLength len
    let w := emitHuffSymbol w litTable lenCode
    let w := if lenEB > 0 then writeBits w lenEV lenEB else w
    let (distCode, distEB, distEV) := encodeDistance dist
    let w := emitHuffSymbol w distTable distCode
    if distEB > 0 then writeBits w distEV distEB else w

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emits a complete token stream followed by the end-of-block symbol 256. -/
def emitTokens (litTable distTable : HuffmanTable) (w : BitWriter) (tokens : Array LZToken) : BitWriter :=
  let w := tokens.foldl (emitToken litTable distTable) w
  emitHuffSymbol w litTable 256

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emits a final (BFINAL=1) fixed-Huffman block (BTYPE=01) for a token stream. -/
def emitFixedBlock (tokens : Array LZToken) : BitWriter :=
  let w : BitWriter := {}
  let w := writeBits w 1 1
  let w := writeBits w 1 2
  emitTokens fixedLitLenTable fixedDistTable w tokens

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emits a final (BFINAL=1) dynamic-Huffman block (BTYPE=10): HLIT/HDIST/HCLEN counts, the
    code-length-alphabet lengths in `clenOrder` permutation, the RLE'd code-length sequence
    under the code-length code, then the token payload under the transmitted tables. The
    encoding tables are built by the *same* `buildHuffmanTable` the decoder uses on the
    transmitted lengths, so encoder and decoder agree by construction. -/
def emitDynamicBlock (plan : DynPlan) (tokens : Array LZToken) : BitWriter :=
  let w : BitWriter := {}
  let w := writeBits w 1 1
  let w := writeBits w 2 2
  let w := writeBits w (plan.hlit - 257) 5
  let w := writeBits w (plan.hdist - 1) 5
  let w := writeBits w (plan.hclen - 4) 4
  let w := (List.range plan.hclen).foldl
    (fun w i => writeBits w plan.clenLengths[clenOrder[i]!]! 3) w
  let clenTable := buildHuffmanTable plan.clenLengths 7
  let w := plan.rleTokens.foldl
    (fun w (sym, eb, ev) =>
      let w := emitHuffSymbol w clenTable sym
      if eb > 0 then writeBits w ev eb else w) w
  let litTable := buildHuffmanTable plan.litLengths 15
  let distTable := buildHuffmanTable plan.distLengths 15
  emitTokens litTable distTable w tokens

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Core RFC 1951 DEFLATE compressor: LZ77 tokenization once, then per-stream selection
    between a fixed-Huffman (BTYPE=01) and a dynamic-Huffman (BTYPE=10) final block by
    exact bit-cost comparison (ties favor fixed, preserving the historical output on inputs
    where dynamic cannot win). Returns the chosen encoding and whether dynamic was used. -/
def compressPlan (data : ByteArray) : Bool × ByteArray :=
  let tokens := tokenize data
  let plan := buildDynPlan tokens
  if dynPlanBitCost plan tokens < fixedBitCost tokens then
    (true, flushBitWriter (emitDynamicBlock plan tokens))
  else
    (false, flushBitWriter (emitFixedBlock tokens))

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Core RFC 1951 DEFLATE compressor (emits a single final Fixed or Dynamic Huffman
    compressed block with LZ77, whichever is smaller in exact bit cost). -/
def compress (data : ByteArray) : ByteArray :=
  (compressPlan data).2

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
