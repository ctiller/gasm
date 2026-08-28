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

/- REF: docs/STDLIB_ZLIB.md#21-adler-32-rfc-1950 -/
/-- RFC 1950 Adler-32 modulus constant (largest prime smaller than 65536). -/
def adlerBase : UInt32 := 65521

/- REF: docs/STDLIB_ZLIB.md#21-adler-32-rfc-1950 -/
/-- Updates a running Adler-32 checksum with a slice of bytes. -/
def updateAdler32 (adler : UInt32) (buf : ByteArray) (start : Nat := 0) (len : Nat := buf.size) : UInt32 :=
  Id.run do
    let mut s1 := adler &&& 0xFFFF
    let mut s2 := (adler >>> 16) &&& 0xFFFF
    let stop := Nat.min buf.size (start + len)
    for i in [start:stop] do
      let b := buf.get! i
      s1 := (s1 + b.toUInt32) % adlerBase
      s2 := (s2 + s1) % adlerBase
    (s2 <<< 16) ||| s1

/- REF: docs/STDLIB_ZLIB.md#21-adler-32-rfc-1950 -/
/-- Computes the standard Adler-32 checksum of a ByteArray. -/
def adler32 (buf : ByteArray) : UInt32 :=
  updateAdler32 1 buf 0 buf.size

/- REF: docs/STDLIB_ZLIB.md#61-checksum-invariance-theorems -/
/-- Universal Theorem: Computing Adler-32 on an empty ByteArray yields 1. -/
theorem adler32_empty : adler32 ByteArray.empty = 1 := by
  simp [adler32, updateAdler32, Id.run]
  decide

end Stdlib.Zlib
