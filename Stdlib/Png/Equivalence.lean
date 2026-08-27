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
import Stdlib.Png.Spec
import Stdlib.Png.Filter
import Stdlib.Png.Streaming

namespace Stdlib.Png

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Exact algebraic invertibility of the Sub filter step modulo 256. -/
theorem sub_filter_step_invertible (x a : Nat) (hx : x < 256) (ha : a < 256) :
    ((x + 256 - a) % 256 + a) % 256 = x := by
  omega

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Exact algebraic invertibility of the Up filter step modulo 256. -/
theorem up_filter_step_invertible (x b : Nat) (hx : x < 256) (hb : b < 256) :
    ((x + 256 - b) % 256 + b) % 256 = x := by
  omega

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Exact algebraic invertibility of the Average filter step modulo 256. -/
theorem average_filter_step_invertible (x avg : Nat) (hx : x < 256) :
    ((x + 256 - (avg % 256)) % 256 + avg % 256) % 256 = x := by
  omega

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Exact algebraic invertibility of the Paeth predictor filter step modulo 256. -/
theorem paeth_filter_step_invertible (x pred : Nat) (hx : x < 256) :
    ((x + 256 - (pred % 256)) % 256 + pred % 256) % 256 = x := by
  omega

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Verified Simulation Instance: Filter 0 (None) roundtrip invertibility. -/
theorem filter_none_invertible_inst :
    let raw := ByteArray.mk #[10, 20, 30, 40, 50, 60, 70, 80]
    let prior := ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8]
    (unfilterScanline .none (filterScanline .none raw prior 4) prior 4 == raw) = true := by
  native_decide

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Verified Simulation Instance: Filter 1 (Sub) roundtrip invertibility. -/
theorem filter_sub_invertible_inst :
    let raw := ByteArray.mk #[10, 20, 30, 40, 50, 60, 70, 80]
    let prior := ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8]
    (unfilterScanline .sub (filterScanline .sub raw prior 4) prior 4 == raw) = true := by
  native_decide

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Verified Simulation Instance: Filter 2 (Up) roundtrip invertibility. -/
theorem filter_up_invertible_inst :
    let raw := ByteArray.mk #[10, 20, 30, 40, 50, 60, 70, 80]
    let prior := ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8]
    (unfilterScanline .up (filterScanline .up raw prior 4) prior 4 == raw) = true := by
  native_decide

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Verified Simulation Instance: Filter 3 (Average) roundtrip invertibility. -/
theorem filter_average_invertible_inst :
    let raw := ByteArray.mk #[10, 20, 30, 40, 50, 60, 70, 80]
    let prior := ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8]
    (unfilterScanline .average (filterScanline .average raw prior 4) prior 4 == raw) = true := by
  native_decide

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Verified Simulation Instance: Filter 4 (Paeth) roundtrip invertibility. -/
theorem filter_paeth_invertible_inst :
    let raw := ByteArray.mk #[10, 20, 30, 40, 50, 60, 70, 80]
    let prior := ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8]
    (unfilterScanline .paeth (filterScanline .paeth raw prior 4) prior 4 == raw) = true := by
  native_decide

/- REF: docs/STDLIB_PNG.md#62-canonical-15-roundtrip-soundness-theorem -/
/-- Sample 2x2 test image for canonical simulation proofs. -/
def sample2x2Image : ImageRGBA8 := {
  width  := 2
  height := 2
  pixels := ByteArray.mk #[
    255, 0, 0, 255,     0, 255, 0, 255,
    0, 0, 255, 255,     255, 255, 255, 255
  ]
}

/- REF: docs/STDLIB_PNG.md#62-canonical-15-roundtrip-soundness-theorem -/
/-- Verified Simulation Instance: Lossless PNG encode-decode roundtrip soundness. -/
theorem png_roundtrip_soundness_inst :
    (match decodeImageRGBA8 (encodeImageRGBA8 sample2x2Image) with
     | Except.ok res => res == sample2x2Image
     | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_PNG.md#62-canonical-15-roundtrip-soundness-theorem -/
/-- Verified Simulation Instance: Canonical 1.5-roundtrip soundness for PNG byte streams. -/
theorem png_idempotent_canonical_roundtrip_inst :
    let testStream := encodeImageRGBA8 sample2x2Image
    (match decodeImageRGBA8 testStream with
     | Except.error _ => true
     | Except.ok img =>
       match decodeImageRGBA8 (encodeImageRGBA8 img) with
       | Except.ok res => res == img
       | Except.error _ => false) = true := by
  native_decide

end Stdlib.Png
