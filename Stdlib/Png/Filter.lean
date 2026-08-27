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

namespace Stdlib.Png

/- REF: docs/STDLIB_PNG.md#41-the-five-standard-filter-types -/
/-- The 5 standard PNG filter types (RFC 2083 §6). -/
inductive FilterType where
  | none    : FilterType -- 0
  | sub     : FilterType -- 1
  | up      : FilterType -- 2
  | average : FilterType -- 3
  | paeth   : FilterType -- 4
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/STDLIB_PNG.md#41-the-five-standard-filter-types -/
/-- Converts numeric code to FilterType. -/
def FilterType.fromNat? : Nat → Option FilterType
  | 0 => some .none
  | 1 => some .sub
  | 2 => some .up
  | 3 => some .average
  | 4 => some .paeth
  | _ => none

/- REF: docs/STDLIB_PNG.md#41-the-five-standard-filter-types -/
/-- Converts FilterType to numeric code. -/
def FilterType.toNat : FilterType → Nat
  | .none    => 0
  | .sub     => 1
  | .up      => 2
  | .average => 3
  | .paeth   => 4

/- REF: docs/STDLIB_PNG.md#42-paeth-predictor-specification -/
/-- Computes the standard Paeth predictor (RFC 2083 §6.6). -/
def paethPredictor (a b c : Int) : Int :=
  let p := a + b - c
  let pa := (p - a).natAbs
  let pb := (p - b).natAbs
  let pc := (p - c).natAbs
  if pa <= pb && pa <= pc then a
  else if pb <= pc then b
  else c

/- REF: docs/STDLIB_PNG.md#41-the-five-standard-filter-types -/
/-- Applies a filter to a raw scanline producing filtered bytes (without the leading filter byte). -/
def filterScanline (ft : FilterType) (raw prior : ByteArray) (bpp : Nat) : ByteArray :=
  Id.run do
    let len := raw.size
    let mut out := ByteArray.empty
    for i in [0:len] do
      let x := (raw.get! i).toNat
      let a := if i >= bpp then (raw.get! (i - bpp)).toNat else 0
      let b := if i < prior.size then (prior.get! i).toNat else 0
      let c := if i >= bpp && i - bpp < prior.size then (prior.get! (i - bpp)).toNat else 0
      let filteredVal : Nat := match ft with
        | .none => x
        | .sub  => (x + 256 - a) % 256
        | .up   => (x + 256 - b) % 256
        | .average =>
          let avg := (a + b) / 2
          (x + 256 - avg) % 256
        | .paeth =>
          let pred := (paethPredictor (a : Int) (b : Int) (c : Int)).natAbs
          (x + 256 - (pred % 256)) % 256
      out := out.push filteredVal.toUInt8
    out

/- REF: docs/STDLIB_PNG.md#41-the-five-standard-filter-types -/
/-- Reconstructs the raw scanline from filtered bytes given prior reconstructed scanline. -/
def unfilterScanline (ft : FilterType) (filtered prior : ByteArray) (bpp : Nat) : ByteArray :=
  Id.run do
    let len := filtered.size
    let mut out := ByteArray.empty
    for i in [0:len] do
      let filtX := (filtered.get! i).toNat
      let a := if i >= bpp then (out.get! (i - bpp)).toNat else 0
      let b := if i < prior.size then (prior.get! i).toNat else 0
      let c := if i >= bpp && i - bpp < prior.size then (prior.get! (i - bpp)).toNat else 0
      let rawVal : Nat := match ft with
        | .none => filtX
        | .sub  => (filtX + a) % 256
        | .up   => (filtX + b) % 256
        | .average =>
          let avg := (a + b) / 2
          (filtX + avg) % 256
        | .paeth =>
          let pred := (paethPredictor (a : Int) (b : Int) (c : Int)).natAbs
          (filtX + (pred % 256)) % 256
      out := out.push rawVal.toUInt8
    out

/- REF: docs/STDLIB_PNG.md#41-the-five-standard-filter-types -/
/-- Computes the Sum of Absolute Differences (SAD) metric for a filtered scanline. -/
def filterSAD (filtered : ByteArray) : Nat :=
  Id.run do
    let mut sum := 0
    for i in [0:filtered.size] do
      let v := (filtered.get! i).toNat
      let absVal := if v <= 128 then v else 256 - v
      sum := sum + absVal
    sum

/- REF: docs/STDLIB_PNG.md#41-the-five-standard-filter-types -/
/-- Evaluates all 5 standard PNG filters and selects the optimal one minimizing SAD. -/
def chooseBestFilter (raw prior : ByteArray) (bpp : Nat) : FilterType :=
  Id.run do
    let mut bestFt := FilterType.none
    let mut bestSad := filterSAD (filterScanline .none raw prior bpp)

    for ft in [FilterType.sub, FilterType.up, FilterType.average, FilterType.paeth] do
      let filtered := filterScanline ft raw prior bpp
      let sad := filterSAD filtered
      if sad < bestSad then
        bestSad := sad
        bestFt := ft
    bestFt

end Stdlib.Png
