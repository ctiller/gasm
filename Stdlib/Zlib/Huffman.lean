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

namespace Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- A canonical Huffman decode tree node. -/
inductive HuffmanNode where
  | leaf (symbol : Nat)
  | branch (left : Option HuffmanNode) (right : Option HuffmanNode)
  deriving Repr, Inhabited

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Structure containing both encoding table and decoding tree for a Huffman alphabet. -/
structure HuffmanTable where
  maxBits : Nat
  codes   : Array (Option (Nat × Nat)) -- symbol -> Option (code, bitLength)
  root    : HuffmanNode
  deriving Repr, Inhabited

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Inserts a canonical prefix code into a binary decode tree. -/
def insertCode (root : HuffmanNode) (symbol : Nat) (code : Nat) (len : Nat) : HuffmanNode :=
  let rec loop (node : HuffmanNode) (curCode : Nat) (remainingBits : Nat) : HuffmanNode :=
    match remainingBits with
    | 0 => HuffmanNode.leaf symbol
    | bits + 1 =>
      let bit := (curCode >>> bits) &&& 1
      match node with
      | HuffmanNode.leaf _ =>
        -- Overwrite branch if needed
        if bit == 0 then
          HuffmanNode.branch (some (loop (HuffmanNode.branch none none) curCode bits)) none
        else
          HuffmanNode.branch none (some (loop (HuffmanNode.branch none none) curCode bits))
      | HuffmanNode.branch l r =>
        if bit == 0 then
          let nextL := match l with | some n => n | none => HuffmanNode.branch none none
          HuffmanNode.branch (some (loop nextL curCode bits)) r
        else
          let nextR := match r with | some n => n | none => HuffmanNode.branch none none
          HuffmanNode.branch l (some (loop nextR curCode bits))
  loop root code len

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Builds a canonical Huffman table from an array of symbol bit lengths (RFC 1951 §3.2.2). -/
def buildHuffmanTable (lengths : Array Nat) (maxBits : Nat := 15) : HuffmanTable :=
  Id.run do
    let numSymbols := lengths.size
    -- Step 1: Count codes of each length
    let mut blCount : Array Nat := Array.replicate (maxBits + 1) 0
    for i in [0:numSymbols] do
      let len := lengths[i]!
      if len > 0 && len <= maxBits then
        blCount := blCount.set! len (blCount[len]! + 1)

    -- Step 2: Find starting code for each length
    let mut code := 0
    let mut nextCode : Array Nat := Array.replicate (maxBits + 1) 0
    for bits in [1:maxBits + 1] do
      code := (code + blCount[bits - 1]!) <<< 1
      nextCode := nextCode.set! bits code

    -- Step 3: Assign numerical codes to symbols & construct decode tree
    let mut codes : Array (Option (Nat × Nat)) := Array.replicate numSymbols none
    let mut root : HuffmanNode := HuffmanNode.branch none none

    for sym in [0:numSymbols] do
      let len := lengths[sym]!
      if len > 0 && len <= maxBits then
        let symCode := nextCode[len]!
        nextCode := nextCode.set! len (symCode + 1)
        codes := codes.set! sym (some (symCode, len))
        root := insertCode root sym symCode len

    { maxBits := maxBits, codes := codes, root := root }

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Generates the RFC 1951 §3.2.6 Fixed Literal/Length bit length array (288 symbols). -/
def fixedLitLenLengths : Array Nat :=
  Id.run do
    let mut arr : Array Nat := Array.replicate 288 0
    for i in [0:144] do
      arr := arr.set! i 8
    for i in [144:256] do
      arr := arr.set! i 9
    for i in [256:280] do
      arr := arr.set! i 7
    for i in [280:288] do
      arr := arr.set! i 8
    arr

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Generates the RFC 1951 §3.2.6 Fixed Distance bit length array (32 symbols, each 5 bits). -/
def fixedDistLengths : Array Nat :=
  Array.replicate 32 5

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Prebuilt RFC 1951 Fixed Literal/Length Huffman Table. -/
def fixedLitLenTable : HuffmanTable :=
  buildHuffmanTable fixedLitLenLengths 9

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Prebuilt RFC 1951 Fixed Distance Huffman Table. -/
def fixedDistTable : HuffmanTable :=
  buildHuffmanTable fixedDistLengths 5

end Stdlib.Zlib
