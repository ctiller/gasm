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

namespace Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decodes an uncompressed stored block (BTYPE = 00). -/
def decodeStoredBlock (r : BitReader) (out : ByteArray) : Except ZlibError (BitReader × ByteArray) :=
  let rAligned := alignToByte r
  if rAligned.bytePos + 4 > rAligned.bytes.size then .error .unexpectedEof
  else
    let len0 := (rAligned.bytes.get! rAligned.bytePos).toNat
    let len1 := (rAligned.bytes.get! (rAligned.bytePos + 1)).toNat
    let nlen0 := (rAligned.bytes.get! (rAligned.bytePos + 2)).toNat
    let nlen1 := (rAligned.bytes.get! (rAligned.bytePos + 3)).toNat
    let len := len0 ||| (len1 <<< 8)
    let nlen := nlen0 ||| (nlen1 <<< 8)
    if (len ^^^ 0xFFFF) != nlen then .error .invalidStoredBlockLengths
    else
      let start := rAligned.bytePos + 4
      if start + len > rAligned.bytes.size then .error .unexpectedEof
      else
        let newOut := Id.run do
          let mut acc := out
          for i in [0:len] do
            acc := acc.push (rAligned.bytes.get! (start + i))
          acc
        .ok ({ rAligned with bytePos := start + len }, newOut)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- A successful `decodeStoredBlock` call never fabricates bits: byte-aligning only drops
    (never adds) buffered bits, and the stored payload only advances `bytePos` forward. -/
theorem decodeStoredBlock_remainingBits_le (r : BitReader) (out : ByteArray) (rOut : BitReader)
    (outOut : ByteArray) (hok : decodeStoredBlock r out = .ok (rOut, outOut)) :
    remainingBits rOut ≤ remainingBits r := by
  unfold decodeStoredBlock at hok
  dsimp only at hok
  split at hok
  · simp at hok
  split at hok
  · simp at hok
  split at hok
  · simp at hok
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨hrOut, _⟩ := hok
    rw [← hrOut]
    simp only [remainingBits, alignToByte]
    omega

set_option maxRecDepth 4000 in
/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decodes LZ77 literals and match back-references using literal and distance Huffman tables.
    Requires both tables to be `branch`-rooted (`hLit`/`hDist`) -- the invariant
    `buildHuffmanTable_isBranch` (`Stdlib/Zlib/Huffman.lean`) establishes *unconditionally*, for
    every table this codebase ever constructs (fixed or dynamic, well-formed or adversarial), so
    neither caller (`decompress`, below) needs to validate anything beyond calling
    `buildHuffmanTable` to satisfy these hypotheses.

    Well-founded on `remainingBits curR`: `decodeHuffmanSymbol_remainingBits_lt` (via `hLit`)
    guarantees the literal/length symbol decode alone strictly shrinks the measure on every
    iteration that doesn't terminate (the RFC 1951 §3.2.5/§3.2.6 fact motivating this file's
    invariant design: a canonical Huffman code has no zero-length codeword, so decoding a symbol
    from a genuine, `branch`-rooted table always consumes at least 1 bit). `hDist` is threaded
    for signature symmetry with `hLit` -- both tables are always supplied together, from the
    same `buildHuffmanTable` call sites -- but is not itself load-bearing for *this* termination
    argument: the distance-symbol decode and both extra-bits reads only need the unconditional,
    hypothesis-free `≤` facts (`decodeHuffmanSymbol_remainingBits_le`,
    `maybeReadBits_remainingBits_le`), since the literal/length decode's strict decrease alone
    already dominates the chain. -/
def decodeHuffmanStream (r : BitReader) (litTable distTable : HuffmanTable)
    (hLit : ∃ l rr, litTable.root = HuffmanNode.branch l rr)
    (hDist : ∃ l rr, distTable.root = HuffmanNode.branch l rr)
    (out : ByteArray) : Except ZlibError (BitReader × ByteArray) :=
  let rec go (curR : BitReader) (curOut : ByteArray)
      (hL : ∃ l rr, litTable.root = HuffmanNode.branch l rr)
      (hD : ∃ l rr, distTable.root = HuffmanNode.branch l rr) :
      Except ZlibError (BitReader × ByteArray) :=
    match hsym : decodeHuffmanSymbol curR litTable with
    | .error e => .error e
    | .ok (nextR, sym) =>
      if sym < 256 then
        go nextR (curOut.push sym.toUInt8) hL hD
      else if sym == 256 then
        .ok (nextR, curOut)
      else if sym <= 285 then
        let lenIdx := sym - 257
        let (baseLen, extraBits) := lengthTable[lenIdx]!
        match hlen : (if extraBits > 0 then readBits nextR extraBits else pure (nextR, 0)) with
        | .error e => .error e
        | .ok (rLen, extraVal) =>
          let matchLen := baseLen + extraVal
          match hdsym : decodeHuffmanSymbol rLen distTable with
          | .error e => .error e
          | .ok (rDistSym, distSym) =>
            if distSym >= 30 then .error (.invalidDistanceCode distSym)
            else
              let (baseDist, distExtraBits) := distanceTable[distSym]!
              match hdext : (if distExtraBits > 0 then readBits rDistSym distExtraBits else pure (rDistSym, 0)) with
              | .error e => .error e
              | .ok (rDist, distExtraVal) =>
                let matchDist := baseDist + distExtraVal
                if matchDist == 0 || matchDist > curOut.size then
                  .error (.custom s!"Invalid back-reference distance {matchDist} on output size {curOut.size}")
                else
                  let newOut := Id.run do
                    let mut acc := curOut
                    for _ in [0:matchLen] do
                      let srcIdx := acc.size - matchDist
                      acc := acc.push (acc.get! srcIdx)
                    acc
                  go rDist newOut hL hD
      else
        .error (.invalidLengthCode sym)
  termination_by remainingBits curR
  decreasing_by
    · exact decodeHuffmanSymbol_remainingBits_lt curR litTable hL nextR sym hsym
    · have h1 := decodeHuffmanSymbol_remainingBits_lt curR litTable hL nextR sym hsym
      have h2 := maybeReadBits_remainingBits_le nextR extraBits rLen extraVal hlen
      have h3 := decodeHuffmanSymbol_remainingBits_le rLen distTable rDistSym distSym hdsym
      have h4 := maybeReadBits_remainingBits_le rDistSym distExtraBits rDist distExtraVal hdext
      omega
  go r out hLit hDist

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `decodeHuffmanStream`'s internal loop (`go`) never fabricates bits: a successful call
    returns a reader that has consumed no more of the stream than it started with. Strong
    induction on `remainingBits curR` rather than `go.induct`, since `go`'s own well-founded
    recursion is already on that same measure -- every recursive call in `go`'s body already
    comes with a proof (`decodeHuffmanSymbol_remainingBits_lt`/`_le`,
    `maybeReadBits_remainingBits_le`) that `remainingBits` only shrinks, so the outer induction
    just needs to track that shrinkage to justify recursing. This is the fact `decompress`
    needs to bound the whole-block effect of a fixed- or dynamic-Huffman block, not just one
    symbol. -/
theorem decodeHuffmanStream_go_remainingBits_le (litTable distTable : HuffmanTable)
    (hL : ∃ l rr, litTable.root = HuffmanNode.branch l rr)
    (hD : ∃ l rr, distTable.root = HuffmanNode.branch l rr) :
    ∀ (curR : BitReader) (curOut : ByteArray) (nextR : BitReader) (outOut : ByteArray),
      decodeHuffmanStream.go litTable distTable curR curOut hL hD = .ok (nextR, outOut) →
      remainingBits nextR ≤ remainingBits curR := by
  have main : ∀ n, ∀ curR : BitReader, remainingBits curR = n → ∀ (curOut : ByteArray)
      (nextR : BitReader) (outOut : ByteArray),
      decodeHuffmanStream.go litTable distTable curR curOut hL hD = .ok (nextR, outOut) →
      remainingBits nextR ≤ remainingBits curR := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro curR hn curOut nextR outOut hok
      rw [decodeHuffmanStream.go.eq_def] at hok
      dsimp only at hok
      cases hsym : decodeHuffmanSymbol curR litTable with
      | error e => rw [hsym] at hok; dsimp only at hok; simp at hok
      | ok val =>
        obtain ⟨nextR', sym⟩ := val
        rw [hsym] at hok
        dsimp only at hok
        split at hok
        · -- sym < 256, recurse
          have hlt := decodeHuffmanSymbol_remainingBits_lt curR litTable hL nextR' sym hsym
          have hres := ih (remainingBits nextR') (by omega) nextR' rfl (curOut.push sym.toUInt8) nextR outOut hok
          omega
        · split at hok
          · -- sym == 256, terminal
            simp only [Except.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨h1, _⟩ := hok
            rw [← h1]
            exact decodeHuffmanSymbol_remainingBits_le curR litTable nextR' sym hsym
          · split at hok
            · -- sym ≤ 285
              cases hlen : (if lengthTable[sym - 257]!.2 > 0 then readBits nextR' lengthTable[sym - 257]!.2
                  else pure (nextR', 0)) with
              | error e => rw [hlen] at hok; dsimp only at hok; simp at hok
              | ok val2 =>
                obtain ⟨rLen, extraVal⟩ := val2
                rw [hlen] at hok
                dsimp only at hok
                cases hdsym : decodeHuffmanSymbol rLen distTable with
                | error e => rw [hdsym] at hok; dsimp only at hok; simp at hok
                | ok val3 =>
                  obtain ⟨rDistSym, distSym⟩ := val3
                  rw [hdsym] at hok
                  dsimp only at hok
                  split at hok
                  · -- distSym ≥ 30, error
                    simp at hok
                  · cases hdext : (if distanceTable[distSym]!.2 > 0
                        then readBits rDistSym distanceTable[distSym]!.2 else pure (rDistSym, 0)) with
                    | error e => rw [hdext] at hok; dsimp only at hok; simp at hok
                    | ok val4 =>
                      obtain ⟨rDist, distExtraVal⟩ := val4
                      rw [hdext] at hok
                      dsimp only at hok
                      split at hok
                      · -- invalid match distance, error
                        simp at hok
                      · -- success, recurse
                        have h1 := decodeHuffmanSymbol_remainingBits_lt curR litTable hL nextR' sym hsym
                        have h2 := maybeReadBits_remainingBits_le nextR' lengthTable[sym - 257]!.2 rLen extraVal hlen
                        have h3 := decodeHuffmanSymbol_remainingBits_le rLen distTable rDistSym distSym hdsym
                        have h4 := maybeReadBits_remainingBits_le rDistSym distanceTable[distSym]!.2 rDist
                          distExtraVal hdext
                        have hres := ih (remainingBits rDist) (by omega) rDist rfl _ nextR outOut hok
                        omega
            · -- sym > 285, error
              simp at hok
  intro curR curOut nextR outOut hok
  exact main (remainingBits curR) curR rfl curOut nextR outOut hok

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `decodeHuffmanStream` never fabricates bits: a successful call's output reader has
    consumed no more of the stream than the input reader offered. Thin wrapper around
    `decodeHuffmanStream_go_remainingBits_le` (`go` is called with `curR := r`, `curOut := out`
    at the top). This is the whole-block bound `decompress`'s outer loop needs, mirroring
    `decodeStoredBlock_remainingBits_le` for the other two block kinds. -/
theorem decodeHuffmanStream_remainingBits_le (r : BitReader) (litTable distTable : HuffmanTable)
    (hLit : ∃ l rr, litTable.root = HuffmanNode.branch l rr)
    (hDist : ∃ l rr, distTable.root = HuffmanNode.branch l rr) (out : ByteArray)
    (nextR : BitReader) (nextOut : ByteArray)
    (hok : decodeHuffmanStream r litTable distTable hLit hDist out = .ok (nextR, nextOut)) :
    remainingBits nextR ≤ remainingBits r := by
  unfold decodeHuffmanStream at hok
  exact decodeHuffmanStream_go_remainingBits_le litTable distTable hLit hDist r out nextR nextOut hok

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
/-- Reads `hclen` 3-bit code lengths for the code-length alphabet (RFC 1951 §3.2.7), placing
    each at its `clenOrder` permutation position. Structural recursion on `fuel` (remaining
    codes to read) rather than a `for`/monadic-`forIn` loop, so its bits-consumed effect is
    provable by induction -- see `decodeClenArray_remainingBits_le`. Called with `fuel := hclen`,
    `pos := 0`, this is exactly `decodeDynamicTables`'s original `for i in [0:hclen]` loop. -/
def decodeClenArray (hclen : Nat) : Nat → Nat → BitReader → Array Nat →
    Except ZlibError (BitReader × Array Nat)
  | 0, _pos, curR, clenArr => .ok (curR, clenArr)
  | fuel + 1, pos, curR, clenArr =>
    match readBits curR 3 with
    | .error e => .error e
    | .ok (nextR, bitLen) =>
      decodeClenArray hclen fuel (pos + 1) nextR (clenArr.set! clenOrder[pos]! bitLen)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `decodeClenArray` never fabricates bits: on success, the reader it returns has consumed
    only from the one it started with. Structural induction on `fuel`, unlike the well-founded
    inductions above -- `decodeClenArray` recurses on `fuel` directly, not on a measure derived
    from the `BitReader`. -/
theorem decodeClenArray_remainingBits_le (hclen : Nat) :
    ∀ (fuel pos : Nat) (curR : BitReader) (clenArr : Array Nat) (rOut : BitReader) (arrOut : Array Nat),
      decodeClenArray hclen fuel pos curR clenArr = .ok (rOut, arrOut) →
      remainingBits rOut ≤ remainingBits curR := by
  intro fuel
  induction fuel with
  | zero =>
    intro pos curR clenArr rOut arrOut hok
    simp only [decodeClenArray, Except.ok.injEq, Prod.mk.injEq] at hok
    rw [← hok.1]
    exact Nat.le_refl _
  | succ fuel ih =>
    intro pos curR clenArr rOut arrOut hok
    rw [decodeClenArray] at hok
    cases hread : readBits curR 3 with
    | error e => rw [hread] at hok; simp at hok
    | ok val =>
      obtain ⟨nextR, bitLen⟩ := val
      rw [hread] at hok
      simp only at hok
      have h1 := ih (pos + 1) nextR (clenArr.set! clenOrder[pos]! bitLen) rOut arrOut hok
      have h2 := readBits_remainingBits curR 3 nextR bitLen hread
      omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decodes a dynamic Huffman block header (BTYPE = 10) and returns the constructed tables. -/
def decodeDynamicTables (r : BitReader) : Except ZlibError (BitReader × HuffmanTable × HuffmanTable) := do
  let (r1, hlitVal) ← readBits r 5
  let (r2, hdistVal) ← readBits r1 5
  let (r3, hclenVal) ← readBits r2 4
  let hlit := hlitVal + 257
  let hdist := hdistVal + 1
  let hclen := hclenVal + 4

  let (curR, clenArr) ← decodeClenArray hclen hclen 0 r3 (Array.replicate 19 0)
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

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `decodeDynamicTables`'s internal code-length-parsing loop (`go`) never fabricates bits.
    Induction on `go`'s own well-founded recursion (`totalLengths - lengths.size`, from P0) --
    a different measure than the one this lemma proves a fact *about* (`remainingBits`); each
    step only reads via `decodeHuffmanSymbol`/`readBits`, both bits-only-consuming. -/
theorem decodeDynamicTables_go_remainingBits_le (clenTable : HuffmanTable) (totalLengths : Nat) :
    ∀ (br : BitReader) (lengths : Array Nat) (nextR : BitReader) (lengths' : Array Nat),
      decodeDynamicTables.go clenTable totalLengths br lengths = .ok (nextR, lengths') →
      remainingBits nextR ≤ remainingBits br := by
  intro br lengths
  induction br, lengths using decodeDynamicTables.go.induct (clenTable := clenTable) (totalLengths := totalLengths) with
  | case1 br lengths hlt e he =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, he] at hok
    simp at hok
  | case2 br lengths hlt nextR' bit hsym hle ih =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp only [hle, if_true] at hok
    have h1 := ih nextR lengths' hok
    have h2 := decodeHuffmanSymbol_remainingBits_le br clenTable nextR' bit hsym
    omega
  | case3 br lengths hlt nextR' bit hsym hgt h16 hempty =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp [hgt, h16, hempty] at hok
  | case4 br lengths hlt nextR' bit hsym hgt h16 hne e he =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp [hgt, h16, hne, he] at hok
  | case5 br lengths hlt nextR' bit hsym hgt h16 hne lastVal nextR'' extra hread ih =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp only [hgt, h16, hne, if_false, if_true, hread] at hok
    have h1 := ih nextR lengths' hok
    have h2 := decodeHuffmanSymbol_remainingBits_le br clenTable nextR' bit hsym
    have h3 := readBits_remainingBits nextR' 2 nextR'' extra hread
    omega
  | case6 br lengths hlt nextR' bit hsym hgt h16 h17 e he =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp [hgt, h16, h17, he] at hok
  | case7 br lengths hlt nextR' bit hsym hgt h16 h17 nextR'' extra hread ih =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp only [hgt, h16, h17, if_false, if_true, hread] at hok
    have h1 := ih nextR lengths' hok
    have h2 := decodeHuffmanSymbol_remainingBits_le br clenTable nextR' bit hsym
    have h3 := readBits_remainingBits nextR' 3 nextR'' extra hread
    omega
  | case8 br lengths hlt nextR' bit hsym hgt h16 h17 h18 e he =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp [hgt, h16, h17, h18, he] at hok
  | case9 br lengths hlt nextR' bit hsym hgt h16 h17 h18 nextR'' extra hread ih =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp only [hgt, h16, h17, h18, if_false, if_true, hread] at hok
    have h1 := ih nextR lengths' hok
    have h2 := decodeHuffmanSymbol_remainingBits_le br clenTable nextR' bit hsym
    have h3 := readBits_remainingBits nextR' 7 nextR'' extra hread
    omega
  | case10 br lengths hlt nextR' bit hsym hgt h16 h17 h18 =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_pos hlt, hsym] at hok
    simp [hgt, h16, h17, h18] at hok
  | case11 br lengths hge =>
    intro nextR lengths' hok
    rw [decodeDynamicTables.go.eq_def, if_neg hge] at hok
    simp only [Except.ok.injEq, Prod.mk.injEq] at hok
    rw [← hok.1]
    exact Nat.le_refl _

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Bridges a successful `decodeDynamicTables` call to the two facts `decompress` needs about
    its output: the reader only shrinks (`decodeDynamicTables_go_remainingBits_le` composed with
    three exact `readBits_remainingBits` reads and `decodeClenArray_remainingBits_le`), and both
    tables are literally `buildHuffmanTable` applications -- so `buildHuffmanTable_isBranch`
    (`Stdlib/Zlib/Huffman.lean`) applies to them unconditionally, exactly as it does to the fixed
    tables, regardless of how the transmitted code lengths were chosen. -/
theorem decodeDynamicTables_bridge (r : BitReader) (rOut : BitReader) (litTbl distTbl : HuffmanTable)
    (hok : decodeDynamicTables r = .ok (rOut, litTbl, distTbl)) :
    remainingBits rOut ≤ remainingBits r ∧
    ∃ litLengths distLengths, litTbl = buildHuffmanTable litLengths 15 ∧
      distTbl = buildHuffmanTable distLengths 15 := by
  unfold decodeDynamicTables at hok
  cases h1 : readBits r 5 with
  | error e => rw [h1] at hok; simp only [Bind.bind, Except.bind] at hok; simp at hok
  | ok val1 =>
    obtain ⟨r1, hlitVal⟩ := val1
    rw [h1] at hok
    simp only [Bind.bind, Except.bind] at hok
    cases h2 : readBits r1 5 with
    | error e => rw [h2] at hok; simp only [Bind.bind, Except.bind] at hok; simp at hok
    | ok val2 =>
      obtain ⟨r2, hdistVal⟩ := val2
      rw [h2] at hok
      simp only [Bind.bind, Except.bind] at hok
      cases h3 : readBits r2 4 with
      | error e => rw [h3] at hok; simp only [Bind.bind, Except.bind] at hok; simp at hok
      | ok val3 =>
        obtain ⟨r3, hclenVal⟩ := val3
        rw [h3] at hok
        simp only [Bind.bind, Except.bind] at hok
        cases h4 : decodeClenArray (hclenVal + 4) (hclenVal + 4) 0 r3 (Array.replicate 19 0) with
        | error e => rw [h4] at hok; simp only [Bind.bind, Except.bind] at hok; simp at hok
        | ok val4 =>
          obtain ⟨curR, clenArr⟩ := val4
          rw [h4] at hok
          simp only [Bind.bind, Except.bind] at hok
          cases h5 : decodeDynamicTables.go (buildHuffmanTable clenArr 7)
              (hlitVal + 257 + (hdistVal + 1)) curR (Array.mkEmpty (hlitVal + 257 + (hdistVal + 1))) with
          | error e => rw [h5] at hok; simp only [Bind.bind, Except.bind] at hok; simp at hok
          | ok val5 =>
            obtain ⟨finalR, lengths⟩ := val5
            rw [h5] at hok
            simp only [Bind.bind, Except.bind] at hok
            simp only [Except.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨hrOut, hlitTbl, hdistTbl⟩ := hok
            refine ⟨?_, lengths.extract 0 (hlitVal + 257),
                lengths.extract (hlitVal + 257) (hlitVal + 257 + (hdistVal + 1)),
                hlitTbl.symm, hdistTbl.symm⟩
            have g1 := readBits_remainingBits r 5 r1 hlitVal h1
            have g2 := readBits_remainingBits r1 5 r2 hdistVal h2
            have g3 := readBits_remainingBits r2 4 r3 hclenVal h3
            have g4 := decodeClenArray_remainingBits_le (hclenVal + 4) (hclenVal + 4) 0 r3
              (Array.replicate 19 0) curR clenArr h4
            have g5 := decodeDynamicTables_go_remainingBits_le (buildHuffmanTable clenArr 7)
              (hlitVal + 257 + (hdistVal + 1)) curR (Array.mkEmpty (hlitVal + 257 + (hdistVal + 1)))
              finalR lengths h5
            rw [← hrOut]
            omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Bridges a successful `decodeDynamicTables` call directly to the `branch`-rootedness
    invariant `decompress` needs to call `decodeHuffmanStream` with -- without ever
    pattern-matching on `decodeDynamicTables_bridge`'s existential witness itself (which would
    require eliminating a `Prop` into `decompress`'s `Except ZlibError ByteArray` result type,
    not generally legal). Both conjuncts here are themselves `Prop`s, so this theorem's
    *statement* already is the exact fact `decompress` needs to hand to `decodeHuffmanStream`
    as `hLit`/`hDist`: no witness data ever needs to leave `Prop` land. -/
theorem decodeDynamicTables_isBranch (r rOut : BitReader) (litTbl distTbl : HuffmanTable)
    (hok : decodeDynamicTables r = .ok (rOut, litTbl, distTbl)) :
    (∃ l rr, litTbl.root = HuffmanNode.branch l rr) ∧
    (∃ l rr, distTbl.root = HuffmanNode.branch l rr) := by
  obtain ⟨_, litLengths, distLengths, hlit, hdist⟩ := decodeDynamicTables_bridge r rOut litTbl distTbl hok
  exact ⟨hlit ▸ buildHuffmanTable_isBranch litLengths 15, hdist ▸ buildHuffmanTable_isBranch distLengths 15⟩

set_option maxRecDepth 4000 in
/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Core RFC 1951 INFLATE decompressor. Well-founded on `remainingBits curR`: every iteration
    reads a 3-bit block header (`bfinal` then `btype`, exactly 3 bits via two `readBits` calls
    -- that's where the strict decrease comes from) and then dispatches on `btype` to one of
    the three block-body decoders. Each is proven to only shrink (never grow) `remainingBits`:
    `decodeStoredBlock_remainingBits_le` for BTYPE=00, `decodeHuffmanStream_remainingBits_le`
    (fed the fixed tables' unconditional `buildHuffmanTable_isBranch` witnesses) for BTYPE=01,
    and the same lemma fed `decodeDynamicTables_isBranch`'s witnesses -- composed with
    `decodeDynamicTables_bridge`'s bound on the table-header prefix -- for BTYPE=10. Since
    `buildHuffmanTable_isBranch` (`Stdlib/Zlib/Huffman.lean`) holds unconditionally for every
    table this codebase ever constructs, well-formed or adversarial, this loop can never fail
    to terminate on a malformed dynamic-Huffman table. Malformed input is not silently accepted,
    though: a degenerate (incomplete) transmitted code tree still makes `decodeHuffmanSymbol`
    hit a `none` child, which surfaces as a clean `.error .corruptedHuffmanTree` -- see
    `Stdlib/Zlib/Test.lean`'s `corrupted dynamic Huffman table` case. -/
def decompress (bytes : ByteArray) : Except ZlibError ByteArray :=
  let rec go (curR : BitReader) (curOut : ByteArray) : Except ZlibError ByteArray :=
    match hbf : readBits curR 1 with
    | .error e => .error e
    | .ok (rBfinal, bfinal) =>
      match hbt : readBits rBfinal 2 with
      | .error e => .error e
      | .ok (rBtype, btype) =>
        match btype with
        | 0 =>
          match hblk : decodeStoredBlock rBtype curOut with
          | .error e => .error e
          | .ok (nextR, nextOut) =>
            if bfinal == 1 then .ok nextOut else go nextR nextOut
        | 1 =>
          match hstream : decodeHuffmanStream rBtype fixedLitLenTable fixedDistTable
              (buildHuffmanTable_isBranch fixedLitLenLengths 9)
              (buildHuffmanTable_isBranch fixedDistLengths 5) curOut with
          | .error e => .error e
          | .ok (nextR, nextOut) =>
            if bfinal == 1 then .ok nextOut else go nextR nextOut
        | 2 =>
          match htab : decodeDynamicTables rBtype with
          | .error e => .error e
          | .ok (rTables, litTbl, distTbl) =>
            match hstream : decodeHuffmanStream rTables litTbl distTbl
                (decodeDynamicTables_isBranch rBtype rTables litTbl distTbl htab).1
                (decodeDynamicTables_isBranch rBtype rTables litTbl distTbl htab).2 curOut with
            | .error e => .error e
            | .ok (nextR, nextOut) =>
              if bfinal == 1 then .ok nextOut else go nextR nextOut
        | _ => .error (.invalidBlockType btype)
  termination_by remainingBits curR
  decreasing_by
    · have h1 := readBits_remainingBits curR 1 rBfinal bfinal hbf
      have h2 := readBits_remainingBits rBfinal 2 rBtype _ hbt
      have h3 := decodeStoredBlock_remainingBits_le rBtype curOut nextR nextOut hblk
      omega
    · have h1 := readBits_remainingBits curR 1 rBfinal bfinal hbf
      have h2 := readBits_remainingBits rBfinal 2 rBtype _ hbt
      have h3 := decodeHuffmanStream_remainingBits_le rBtype fixedLitLenTable fixedDistTable
        (buildHuffmanTable_isBranch fixedLitLenLengths 9) (buildHuffmanTable_isBranch fixedDistLengths 5)
        curOut nextR nextOut hstream
      omega
    · have h1 := readBits_remainingBits curR 1 rBfinal bfinal hbf
      have h2 := readBits_remainingBits rBfinal 2 rBtype _ hbt
      have h3 := (decodeDynamicTables_bridge rBtype rTables litTbl distTbl htab).1
      have h4 := decodeHuffmanStream_remainingBits_le rTables litTbl distTbl
        (decodeDynamicTables_isBranch rBtype rTables litTbl distTbl htab).1
        (decodeDynamicTables_isBranch rBtype rTables litTbl distTbl htab).2
        curOut nextR nextOut hstream
      omega
  go (mkBitReader bytes) ByteArray.empty

end Stdlib.Zlib
