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
import Stdlib.Zlib.Deflate.Bitstream
import Stdlib.Zlib.Deflate.LZ77
import Stdlib.Zlib.Deflate.Plan

namespace Stdlib.Zlib

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
/-- Body of `compressFixed`'s emit loop: from `pos`, emit one LZ77 token's fixed-Huffman
    codes into `w` and continue. Structural recursion on `fuel` -- never `partial`/`while` --
    so equation lemmas exist for proofs, the same rule `tokenizeAux` follows. Every step
    advances `pos` by at least 1 (a certified match advances by `matchLen >= 3`, a literal by
    1), so `fuel = data.size` always suffices. -/
def compressFixedLoop (data : ByteArray) : Nat → BitWriter → Nat → BitWriter
  | 0, w, _pos => w
  | fuel + 1, w, pos =>
    if pos < data.size then
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
        let w :=
          if lenSymbol <= 279 then writeBits w (reverseBits (lenSymbol - 256) 7) 7
          else writeBits w (reverseBits (lenSymbol - 280 + 0xC0) 8) 8
        let w := if lenExtraBits > 0 then writeBits w lenExtraVal lenExtraBits else w
        -- 2. Emit Distance Code + extra bits (5-bit Fixed Huffman distance code = rev5(distCode))
        let (distCode, distExtraBits, distExtraVal) := encodeDistance matchDist
        let w := writeBits w (reverseBits distCode 5) 5
        let w := if distExtraBits > 0 then writeBits w distExtraVal distExtraBits else w
        compressFixedLoop data fuel w (pos + matchLen)
      else
        let byteVal := (data.get! pos).toNat
        let w :=
          if byteVal <= 143 then writeBits w (reverseBits (byteVal + 0x30) 8) 8
          else writeBits w (reverseBits (byteVal - 144 + 0x190) 9) 9
        compressFixedLoop data fuel w (pos + 1)
      else w

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Pure RFC 1951 Fixed Huffman block compressor matching assembly machine code engine.
    Bit-identical to the `while`-loop form this replaces; `compressFixedLoop` carries the
    loop body as structural fuel recursion. -/
def compressFixed (data : ByteArray) : ByteArray :=
  -- BFINAL = 1 (1 bit), BTYPE = 01 (2 bits) -> 3 bits of 0b011 = 3
  let w : BitWriter := writeBits {} 3 3
  let w := compressFixedLoop data data.size w 0
  -- End of block (symbol 256 = 7 bits of 0)
  flushBitWriter (writeBits w 0 7)

end Stdlib.Zlib
