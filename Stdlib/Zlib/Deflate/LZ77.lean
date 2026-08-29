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
import Stdlib.Zlib.Deflate.Bitstream

namespace Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Inner match-extension step of the LZ77 search: the longest common run starting at
    `candidate` and `pos`, capped at `maxMatchLen`, counting up from `len`. Structural
    recursion on `fuel` -- never `partial`/`while` -- so equation lemmas exist for proofs,
    the same rule `tokenizeAux` below already follows. Every step advances `len` by one and
    stops at `maxMatchLen`, so `fuel = maxMatchLen - len` always suffices. -/
def matchExtend (data : ByteArray) (pos candidate maxMatchLen : Nat) : Nat → Nat → Nat
  | 0, len => len
  | fuel + 1, len =>
    if len < maxMatchLen && data.get! (candidate + len) == data.get! (pos + len) then
      matchExtend data pos candidate maxMatchLen fuel (len + 1)
    else len

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Outer candidate scan of the LZ77 search: walks `candidate` backwards from `pos` while it
    stays above `startLookback`, keeping the longest run seen so far, and stopping early on a
    maximal 258-byte match. Structural recursion on `fuel`, which carries the original
    `tries < maxTries` budget: the loop body ran at most `maxTries` times, so `fuel =
    maxTries` reproduces it exactly. -/
def matchScan (data : ByteArray) (pos startLookback maxMatchLen : Nat) :
    Nat → Nat → Nat → Nat → (Nat × Nat)
  | 0, _candidate, bestLen, bestDist => (bestLen, bestDist)
  | fuel + 1, candidate, bestLen, bestDist =>
    if candidate > startLookback then
      let candidate := candidate - 1
      if data.get! candidate == data.get! pos &&
         data.get! (candidate + 1) == data.get! (pos + 1) &&
         data.get! (candidate + 2) == data.get! (pos + 2) then
        let len := matchExtend data pos candidate maxMatchLen (maxMatchLen - 3) 3
        if len > bestLen then
          if len == 258 then (len, pos - candidate)
          else matchScan data pos startLookback maxMatchLen fuel candidate len (pos - candidate)
        else matchScan data pos startLookback maxMatchLen fuel candidate bestLen bestDist
      else matchScan data pos startLookback maxMatchLen fuel candidate bestLen bestDist
    else (bestLen, bestDist)

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- LZ77 match search finding longest matching substring in sliding lookback window.
    Bit-identical to the `while`-loop form this replaces; `matchScan`/`matchExtend` document
    how the two loop budgets map onto structural fuel. -/
def findLongestMatch (data : ByteArray) (pos : Nat) (maxLookback : Nat := 32768) (maxTries : Nat := 128) : (Nat × Nat) :=
  let total := data.size
  if pos + 3 > total then (0, 0)
  else
    let startLookback := if pos > maxLookback then pos - maxLookback else 0
    let maxMatchLen := Nat.min 258 (total - pos)
    let best := matchScan data pos startLookback maxMatchLen maxTries pos 0 0
    if best.1 >= 3 then best else (0, 0)

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

end Stdlib.Zlib
