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

namespace Stdlib.Zlib

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

end Stdlib.Zlib
