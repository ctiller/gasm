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
import Stdlib.Zlib.DynamicRoundtrip

/-
## PA16 retirement: the DEFLATE `*_inst` checks as corollaries of the universal theorem

These four theorems used to be single-ground-instance `native_decide` checks
(Law 10 `grandfathered` allowlist entries). With `deflate_roundtrip_soundness`
kernel-checked and unconditional, each is now a one-line instantiation — no
`native_decide`, no `decide`, no enumeration. Statements are byte-for-byte the
originals from `Stdlib/Zlib/Equivalence.lean`; only the proofs changed.
-/

namespace Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- `ByteArray` equality is reflexive (its `BEq` compares the backing arrays). -/
theorem byteArray_beq_self (b : ByteArray) : (b == b) = true := by
  show (b.data == b.data) = true
  exact beq_self_eq_true _

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Empty-input DEFLATE roundtrip: direct instance of `deflate_roundtrip_soundness`. -/
theorem deflate_roundtrip_empty_inst :
    (match decompress (compress ByteArray.empty) with
     | Except.ok res => res == ByteArray.empty
     | Except.error _ => false) = true := by
  rw [deflate_roundtrip_soundness]
  exact byteArray_beq_self _

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Hello-world DEFLATE roundtrip: direct instance of `deflate_roundtrip_soundness`. -/
theorem deflate_roundtrip_soundness_inst :
    let data := "Hello, World! Verified DEFLATE in Lean 4.".toUTF8
    (match decompress (compress data) with
     | Except.ok res => res == data
     | Except.error _ => false) = true := by
  intro data
  rw [deflate_roundtrip_soundness]
  exact byteArray_beq_self _

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Repetitive-run DEFLATE roundtrip: direct instance of `deflate_roundtrip_soundness`. -/
theorem deflate_roundtrip_repetitive_inst :
    let data := ByteArray.mk #[42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42]
    (match decompress (compress data) with
     | Except.ok res => res == data
     | Except.error _ => false) = true := by
  intro data
  rw [deflate_roundtrip_soundness]
  exact byteArray_beq_self _

/- REF: docs/STDLIB_ZLIB.md#63-canonical-15-roundtrip-soundness-theorems -/
/-- Canonical 1.5-roundtrip for DEFLATE: both decompressions are instances of
    `deflate_roundtrip_soundness` — the first at the fixed literal, the second at
    whatever it decompressed to. -/
theorem deflate_idempotent_canonical_roundtrip_inst :
    let testStream := compress "Canonical 1.5-roundtrip theorem test.".toUTF8
    (match decompress testStream with
     | Except.error _ => false
     | Except.ok data =>
       match decompress (compress data) with
       | Except.ok res => res == data
       | Except.error _ => false) = true := by
  intro testStream
  rw [show testStream = compress "Canonical 1.5-roundtrip theorem test.".toUTF8 from rfl,
    deflate_roundtrip_soundness]
  show (match decompress (compress "Canonical 1.5-roundtrip theorem test.".toUTF8) with
    | Except.ok res => res == "Canonical 1.5-roundtrip theorem test.".toUTF8
    | Except.error _ => false) = true
  rw [deflate_roundtrip_soundness]
  exact byteArray_beq_self _

end Stdlib.Zlib
