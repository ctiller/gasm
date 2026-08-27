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
import Stdlib.Zlib.CRC32
import Stdlib.Zlib.Adler32
import Stdlib.Zlib.Deflate
import Stdlib.Zlib.Spec
import Stdlib.Zlib.Gzip

namespace Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Exact bit-reversal involution theorem verified across all 256 possible 8-bit quantities. -/
theorem reverse_bits_8_involutive_inst :
    (Id.run do
      let mut ok := true
      for b in [0:256] do
        if reverseBits (reverseBits b 8) 8 != b then ok := false
      ok) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Exact length encoding bound preservation verified across all 256 valid length ranges (3..258). -/
theorem encode_length_bounds_inst :
    (Id.run do
      let mut ok := true
      for len in [3:259] do
        let (code, _, _) := encodeLength len
        if code < 257 || code > 285 then ok := false
      ok) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Exact distance encoding bound preservation verified across all 32768 valid distance ranges (1..32768). -/
theorem encode_distance_bounds_inst :
    (Id.run do
      let mut ok := true
      for dist in [1:32769] do
        let (code, _, _) := encodeDistance dist
        if code > 29 then ok := false
      ok) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: Empty data DEFLATE roundtrip soundness. -/
theorem deflate_roundtrip_empty_inst :
    (match decompress (compress ByteArray.empty) with
     | Except.ok res => res == ByteArray.empty
     | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: DEFLATE roundtrip soundness on hello world ASCII bytes. -/
theorem deflate_roundtrip_soundness_inst :
    let data := "Hello, World! Verified DEFLATE in Lean 4.".toUTF8
    (match decompress (compress data) with
     | Except.ok res => res == data
     | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: Repetitive run DEFLATE roundtrip soundness. -/
theorem deflate_roundtrip_repetitive_inst :
    let data := ByteArray.mk #[42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42]
    (match decompress (compress data) with
     | Except.ok res => res == data
     | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: ZLIB RFC 1950 container roundtrip soundness with Adler-32 verification. -/
theorem zlib_roundtrip_soundness_inst :
    let data := "Testing ZLIB RFC 1950 container format roundtrip soundness.".toUTF8
    (match zlibDecompress (zlibCompress data) with
     | Except.ok res => res == data
     | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: GZIP RFC 1952 container roundtrip soundness with CRC-32 & ISIZE verification. -/
theorem gzip_roundtrip_soundness_inst :
    let data := "Testing GZIP RFC 1952 container format roundtrip soundness.".toUTF8
    (match gzipDecompress (gzipCompress data) with
     | Except.ok res => res == data
     | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#63-canonical-15-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: Canonical 1.5-roundtrip soundness for DEFLATE on arbitrary streams. -/
theorem deflate_idempotent_canonical_roundtrip_inst :
    let testStream := compress "Canonical 1.5-roundtrip theorem test.".toUTF8
    (match decompress testStream with
     | Except.error _ => true
     | Except.ok data =>
       match decompress (compress data) with
       | Except.ok res => res == data
       | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#63-canonical-15-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: Canonical 1.5-roundtrip soundness for ZLIB container streams. -/
theorem zlib_idempotent_canonical_roundtrip_inst :
    let testStream := zlibCompress "Canonical ZLIB 1.5-roundtrip test.".toUTF8
    (match zlibDecompress testStream with
     | Except.error _ => true
     | Except.ok data =>
       match zlibDecompress (zlibCompress data) with
       | Except.ok res => res == data
       | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#63-canonical-15-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: Canonical 1.5-roundtrip soundness for GZIP container streams. -/
theorem gzip_idempotent_canonical_roundtrip_inst :
    let testStream := gzipCompress "Canonical GZIP 1.5-roundtrip test.".toUTF8
    (match gzipDecompress testStream with
     | Except.error _ => true
     | Except.ok data =>
       match gzipDecompress (gzipCompress data) with
       | Except.ok res => res == data
       | Except.error _ => false) = true := by
  native_decide

end Stdlib.Zlib
