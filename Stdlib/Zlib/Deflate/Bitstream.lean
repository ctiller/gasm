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
/-- A successful `decodeHuffmanSymbol.step` call never *fabricates* bits: the reader it returns
    has never consumed more of the stream than it started with. True for every `HuffmanNode`,
    including a bare `leaf` (0 bits consumed) -- this is the non-strict half of the fact
    `decodeHuffmanStream`/`decompress` need for their termination measure; the strict half
    (`decodeHuffmanSymbol_remainingBits_lt` below) additionally requires the tree's *root* to
    be a `branch`. -/
theorem decodeHuffmanSymbol_step_remainingBits_le (curR : BitReader) (node : HuffmanNode) :
    ∀ (nextR : BitReader) (sym : Nat),
      decodeHuffmanSymbol.step curR node = .ok (nextR, sym) →
      remainingBits nextR ≤ remainingBits curR := by
  induction curR, node using decodeHuffmanSymbol.step.induct with
  | case1 curR sym' =>
    intro nextR sym hok
    rw [decodeHuffmanSymbol.step.eq_def] at hok
    simp only [Except.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨h1, _⟩ := hok
    rw [h1]
    exact Nat.le_refl _
  | case2 curR l rOpt e he =>
    intro nextR sym hok
    rw [decodeHuffmanSymbol.step.eq_def, he] at hok
    simp at hok
  | case3 curR rOpt nextR' bit hread hbit n ih =>
    intro nextR sym hok
    rw [decodeHuffmanSymbol.step.eq_def, hread] at hok
    simp only [hbit, if_true] at hok
    have hle := ih nextR sym hok
    have heq := readBits_remainingBits curR 1 nextR' bit hread
    omega
  | case4 curR rOpt nextR' bit hread hbit =>
    intro nextR sym hok
    rw [decodeHuffmanSymbol.step.eq_def, hread] at hok
    simp [hbit] at hok
  | case5 curR l nextR' bit hread hbit n ih =>
    intro nextR sym hok
    rw [decodeHuffmanSymbol.step.eq_def, hread] at hok
    simp only [hbit] at hok
    have hle := ih nextR sym hok
    have heq := readBits_remainingBits curR 1 nextR' bit hread
    omega
  | case6 curR l nextR' bit hread hbit =>
    intro nextR sym hok
    rw [decodeHuffmanSymbol.step.eq_def, hread] at hok
    simp [hbit] at hok

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- **The termination fact `decodeHuffmanStream`/`decompress` need**: given a `branch`-rooted
    decode tree, a successful `decodeHuffmanSymbol` call strictly shrinks `remainingBits` --
    the root's `branch` case unconditionally reads (and, on success, consumes) 1 bit via
    `readBits curR 1` before any recursive descent, and `decodeHuffmanSymbol_step_remainingBits_le`
    shows the descent below that first read can only consume further bits, never give them back.
    Every `HuffmanTable` this codebase ever constructs satisfies the hypothesis unconditionally
    (`buildHuffmanTable_isBranch`, `Stdlib/Zlib/Huffman.lean`), so this closes the termination
    obligation Lean could not previously discharge for the general `HuffmanTable` type. -/
theorem decodeHuffmanSymbol_remainingBits_lt (r : BitReader) (tree : HuffmanTable)
    (hroot : ∃ l rr, tree.root = HuffmanNode.branch l rr) (nextR : BitReader) (sym : Nat)
    (hok : decodeHuffmanSymbol r tree = .ok (nextR, sym)) :
    remainingBits nextR < remainingBits r := by
  obtain ⟨l, rr, hr⟩ := hroot
  unfold decodeHuffmanSymbol at hok
  rw [hr, decodeHuffmanSymbol.step.eq_def] at hok
  cases hread : readBits r 1 with
  | error e => rw [hread] at hok; simp at hok
  | ok val =>
    obtain ⟨nextR', bit⟩ := val
    rw [hread] at hok
    by_cases hbit : (bit == 0) = true
    · simp only [hbit, if_true] at hok
      cases l with
      | none => simp at hok
      | some n =>
        simp only at hok
        have hle := decodeHuffmanSymbol_step_remainingBits_le nextR' n nextR sym hok
        have heq := readBits_remainingBits r 1 nextR' bit hread
        omega
    · simp only [hbit] at hok
      cases rr with
      | none => simp at hok
      | some n =>
        simp only at hok
        have hle := decodeHuffmanSymbol_step_remainingBits_le nextR' n nextR sym hok
        have heq := readBits_remainingBits r 1 nextR' bit hread
        omega

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Non-strict, hypothesis-free companion to `decodeHuffmanSymbol_remainingBits_lt`: a
    successful `decodeHuffmanSymbol` call never fabricates bits, for *any* tree (leaf-rooted
    included). Used where the decoded symbol's own reader isn't the one driving termination
    (`decodeHuffmanStream`'s distance-symbol decode: the literal/length symbol earlier in the
    same iteration already supplies the strict decrease). -/
theorem decodeHuffmanSymbol_remainingBits_le (r : BitReader) (tree : HuffmanTable)
    (nextR : BitReader) (sym : Nat) (hok : decodeHuffmanSymbol r tree = .ok (nextR, sym)) :
    remainingBits nextR ≤ remainingBits r := by
  unfold decodeHuffmanSymbol at hok
  exact decodeHuffmanSymbol_step_remainingBits_le r tree.root nextR sym hok

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- `decodeHuffmanStream`'s extra-bits reads are each guarded by `if n > 0 then readBits r n
    else pure (r, 0)` (RFC 1951 §3.2.5's zero-extra-bit length/distance codes read nothing);
    either way, on success, the reader never gains bits back. -/
theorem maybeReadBits_remainingBits_le (r : BitReader) (n : Nat) (rOut : BitReader) (v : Nat)
    (hok : (if n > 0 then readBits r n else pure (r, 0)) = .ok (rOut, v)) :
    remainingBits rOut ≤ remainingBits r := by
  split at hok
  · rename_i hpos
    have := readBits_remainingBits r n rOut v hok
    omega
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hok
    rw [← hok.1]
    exact Nat.le_refl _

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

end Stdlib.Zlib
