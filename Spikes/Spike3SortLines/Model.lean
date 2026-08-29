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

import Gasm.Effects.Trace
import Spikes.Spike3SortLines.Input

/-! Executable, byte-total specification for Spike 3.

This model is intentionally expressed in bytes before rendering output.  The
lowered programs compare and retain arbitrary bytes, so a `List String` model
would silently exclude malformed UTF-8 from the universal environment domain.
-/

namespace Spikes.Spike3SortLines

open Gasm.Core.Platform
open Gasm.Effects

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#3-in-memory-line-tokenization-lexicographical-ordering -/
/-- The rendering rule used by the WASI `fd_write` host model for arbitrary output bytes. -/
def renderLineBytes (line : List UInt8) : String :=
  let bytes := ByteArray.mk line.toArray
  match String.fromUTF8? bytes with
  | some string => string
  | none => String.ofList (line.map fun byte => Char.ofNat byte.toNat)

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#3-in-memory-line-tokenization-lexicographical-ordering -/
/-- Unsigned lexicographic comparison, matching the target's byte-at-a-time comparison rather
    than Lean's Unicode-string ordering. -/
def byteLineLe : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _, [] => false
  | left :: leftRest, right :: rightRest =>
    if left == right then byteLineLe leftRest rightRest else decide (left < right)

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
def insertByteLine (line : List UInt8) : List (List UInt8) → List (List UInt8)
  | [] => [line]
  | current :: rest =>
    if byteLineLe line current then line :: current :: rest
    else current :: insertByteLine line rest

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
def sortByteLines : List (List UInt8) → List (List UInt8)
  | [] => []
  | line :: rest => insertByteLine line (sortByteLines rest)

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Observable output for a sorted byte-line sequence. Each completed input line is emitted with
    CRLF, then the process exits successfully. -/
def byteSortOutput : List (List UInt8) → List AnyEvent
  | [] => [Inject.inject (ProcessEvent.exit 0)]
  | line :: rest =>
    Inject.inject (ConsoleEvent.out (renderLineBytes line)) ::
      Inject.inject (ConsoleEvent.out "\r\n") :: byteSortOutput rest

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Independent byte-total whole-program specification. Every `Environment.stdin` byte string
    has a meaning: only LF-completed records participate in the sort, exactly as the streaming
    decoder specifies. -/
def spike3ByteSortSpec (environment : Environment) : List AnyEvent :=
  byteSortOutput (sortByteLines (environmentInputLines environment))

end Spikes.Spike3SortLines
