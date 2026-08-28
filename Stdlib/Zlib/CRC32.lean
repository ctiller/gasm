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

/- REF: docs/STDLIB_ZLIB.md#22-crc-32-iso-3309-ieee-8023 -/
/-- Standard IEEE 802.3 / ISO 3309 CRC-32 polynomial (reversed). -/
def crc32Polynomial : UInt32 := 0xEDB88320

/- REF: docs/STDLIB_ZLIB.md#22-crc-32-iso-3309-ieee-8023 -/
/-- Computes a single entry of the 256-element CRC-32 lookup table. -/
def mkCrcTableEntry (n : Nat) : UInt32 :=
  let rec loop (c : UInt32) (k : Nat) : UInt32 :=
    match k with
    | 0 => c
    | k + 1 =>
      let newC := if (c &&& 1) != 0 then (c >>> 1) ^^^ crc32Polynomial else c >>> 1
      loop newC k
  loop (n.toUInt32) 8

/- REF: docs/STDLIB_ZLIB.md#22-crc-32-iso-3309-ieee-8023 -/
/-- Precomputed 256-entry CRC-32 table. -/
def crc32Table : Array UInt32 :=
  Id.run do
    let mut arr := Array.mkEmpty 256
    for i in [0:256] do
      arr := arr.push (mkCrcTableEntry i)
    arr

/- REF: docs/STDLIB_ZLIB.md#22-crc-32-iso-3309-ieee-8023 -/
/-- Updates a running CRC-32 checksum with a slice of bytes. -/
def updateCrc32 (crc : UInt32) (buf : ByteArray) (start : Nat := 0) (len : Nat := buf.size) : UInt32 :=
  Id.run do
    let mut c := crc ^^^ 0xFFFFFFFF
    let tbl := crc32Table
    let stop := Nat.min buf.size (start + len)
    for i in [start:stop] do
      let b := buf.get! i
      let idx := ((c ^^^ b.toUInt32) &&& 0xFF).toNat
      let entry := if h : idx < tbl.size then tbl[idx] else mkCrcTableEntry idx
      c := (c >>> 8) ^^^ entry
    c ^^^ 0xFFFFFFFF

/- REF: docs/STDLIB_ZLIB.md#22-crc-32-iso-3309-ieee-8023 -/
/-- Computes the standard CRC-32 checksum of a ByteArray. -/
def crc32 (buf : ByteArray) : UInt32 :=
  updateCrc32 0 buf 0 buf.size

/- REF: docs/STDLIB_ZLIB.md#61-checksum-invariance-theorems -/
/-- Universal Theorem: Computing CRC-32 on an empty ByteArray yields 0. -/
theorem crc32_empty : crc32 ByteArray.empty = 0 := by
  simp [crc32, updateCrc32, Id.run]
  decide

end Stdlib.Zlib
