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
import Gasm.Core.Types
import Gasm.Core.Verification
import Gasm.Effects.Inject
import Gasm.Effects.Trace
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.Windows.Win32API
import Spikes.Spike3SortLines.Spec
import Spikes.Spike3SortLines.Windows.Program

namespace Spikes.Spike3SortLines.Windows

open Gasm.Core
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.Windows

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Observable assembly trace on empty stdin. -/
def asmTraceEmpty : List AnyEvent :=
  runAsmTrace (Event := AnyEvent) spike3Instructions spike3Executable.load

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Observable monadic model trace on empty stdin. -/
def modelTraceEmpty : List AnyEvent :=
  runModelTrace (sortLinesSpec : TraceM AnyEvent Unit) []

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Observable assembly trace on canonical 3-line input. -/
def asmTraceCanonical : List AnyEvent :=
  runAsmTrace (Event := AnyEvent) spike3Instructions (spike3Executable.loadWithStdin defaultSampleInput)

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Observable monadic model trace on canonical 3-line input. -/
def modelTraceCanonical : List AnyEvent :=
  runModelTrace (sortLinesSpec : TraceM AnyEvent Unit) defaultInputLines

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof of semantic trace equivalence between high-level sorting spec and lowered machine execution on canonical input. -/
theorem spike3_canonical_effect_trace_equivalence_inst :
    (asmTraceCanonical == modelTraceCanonical) = true := by
  native_decide

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/- REF: docs/REVIEW.md#law-10-kernel-checked-gates-native-evaluation-debt -/
/-- Constructive proof of semantic trace equivalence on empty input, discharged by an **honest
    kernel-checked `decide`** -- no `native_decide`, no `bv_decide`, and therefore no allowlist
    entry (`#print axioms` -> `[propext, Classical.choice, Quot.sound]`).

    **What unblocked this, since it is not where the plan expected it.** The obstruction was never
    the ~350-instruction lowered program or its 95-step empty-stdin execution: that side reduces
    through the kernel fine (measured -- `decide +kernel` closes the trace prefix at fuel
    1/5/20/50/60/65/70/80 with monotonically growing cost, and reaches the single `exit(0)` event at
    fuel 95). The obstruction was on the **model** side, in `Spikes/Spike3SortLines/Spec.lean`:
    `readAllLines` was a `partial def`, which compiles to an `opaque` constant carrying no defining
    equations, so `modelTraceEmpty` was irreducible in 3 seconds -- `(modelTraceEmpty.length == 1) =
    true` failed `decide +kernel` as reduction-**stuck**, with no machine trace consulted at all.
    Converting that one declaration to fuel-based structural recursion (`readAllLinesFueled`, with
    `readAllLinesFueled_trace` proving the bound immaterial below itself) made the model side reduce
    instantly and let this equivalence close. Measured cost of the `decide +kernel` below: ~3
    minutes on the reference machine, versus permanently stuck before.

    **Scope is unchanged and still narrow.** This states exactly what it stated before -- the
    empty-stdin vector only. The `∀ (stdin : ByteArray)` gap described in the domain-honesty note
    below remains open; retiring the oracle does not widen the domain. -/
theorem spike3_empty_effect_trace_equivalence_inst :
    (runAsmTrace (Event := AnyEvent) spike3Instructions spike3Executable.load == modelTraceEmpty) = true := by
  decide +kernel

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#6-end-to-end-simulation-verification-invariant -/
/-- **Domain-honesty note (PA17).** The real domain Law 9's read-binder clause demands here is
    `∀ (stdin : ByteArray)` — arbitrary stdin content of any length — per
    `docs/READ_BINDER_CONTRACT.md`. `Bool` is NOT that domain: it is a two-element
    proxy standing in for exactly the two literal vectors above (`ByteArray.empty` and
    `defaultSampleInput`), chosen so `∀ (b : Bool)` type-checks trivially over a domain of size 2.
    The historical Law 9 mock-verification census classified this composition
    as "Tier 3 — legit pattern" on the reasoning that it is a genuine finite-∀ over an exhaustive
    enum; that reasoning is correct about the *composition* (`cases b` really does cover both
    constructors of `Bool`) but was read by at least one prior author as implying the underlying
    claim covers arbitrary stdin, which it does not. Neither branch below says anything about the
    other ~2^(8·n)-1 stdin byte strings of any given length `n`, including inputs with a trailing
    line lacking a terminating CRLF, a line containing bytes needing dynamic line-buffer growth
    past 256 bytes, or a chunk boundary from `ReadFile`'s 512-byte reads landing mid-line -- all
    real behaviors this program's `stream_read_loop`/`chunk_scan_loop` implement and which a
    genuine `∀ stdin` proof would have to range over. Closing that gap needs induction over the
    streaming-ingestion loop's structure (the technique `docs/PATHFINDER_CRC32.md`
    demonstrates for a buffer-indexed loop), stated against `docs/READ_BINDER_CONTRACT.md`'s
    read-continuation contract shape -- neither of which has landed as of this note, so this task
    does not attempt it. See `spike3_effect_trace_equivalence_for_empty_stdin` and
    `spike3_effect_trace_equivalence_for_canonical_stdin` below for the same two facts restated
    with the restriction made an explicit, checkable hypothesis instead of an implicit `Bool`
    case split. -/
instance : EnvironmentLoader Bool where
  loadEnvironment exe b := if b then exe.loadWithStdin defaultSampleInput else exe.load

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#6-end-to-end-simulation-verification-invariant -/
/-- `spike3Executable.loadWithStdin ByteArray.empty` and `spike3Executable.load` are the same
    initial machine state (`loadWithStdin` only overwrites `stdinBuffer`, which `load` already
    leaves at its `ByteArray.empty` structure default) -- recorded so the honest wrapper theorem
    below can be stated uniformly in terms of `loadWithStdin` for both cases. -/
theorem spike3Executable_loadWithStdin_empty :
    spike3Executable.loadWithStdin ByteArray.empty = spike3Executable.load := rfl

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#6-end-to-end-simulation-verification-invariant -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Honest restatement of `spike3_empty_effect_trace_equivalence_inst` with its real, narrow
    domain made an explicit, machine-checked hypothesis (`h`) rather than an implicit `Bool` case
    split standing in for it. This is the narrow proof boundary
    `docs/SPIKES/SPIKE3_SORT_LINES.md` §6 records when a genuinely universal
    `∀ (stdin : ByteArray)` statement is not reachable in this task: "for all inputs satisfying P,
    with P stated" -- here `P` is deliberately narrow (equality to the one literal vector this
    file already checks) and is not dressed up as broader coverage. -/
theorem spike3_effect_trace_equivalence_for_empty_stdin (stdin : ByteArray)
    (h : stdin = ByteArray.empty) :
    (runAsmTrace (Event := AnyEvent) spike3Instructions (spike3Executable.loadWithStdin stdin) == modelTraceEmpty) = true := by
  subst h
  rw [spike3Executable_loadWithStdin_empty]
  exact spike3_empty_effect_trace_equivalence_inst

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#6-end-to-end-simulation-verification-invariant -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Honest restatement of `spike3_canonical_effect_trace_equivalence_inst`; see
    `spike3_effect_trace_equivalence_for_empty_stdin` immediately above for the rationale, which
    applies identically here. -/
theorem spike3_effect_trace_equivalence_for_canonical_stdin (stdin : ByteArray)
    (h : stdin = defaultSampleInput) :
    (runAsmTrace (Event := AnyEvent) spike3Instructions (spike3Executable.loadWithStdin stdin) == modelTraceCanonical) = true := by
  subst h
  exact spike3_canonical_effect_trace_equivalence_inst

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- First-class VerifiedProgram contract instantiation for Spike 3 (Stdin Lexicographical Line Sorter).
    NOTE (PA17 domain-honesty finding): despite the `∀ (b : Bool)` shape below satisfying
    `VerifiedProgram`'s literal type signature, this is NOT a Law-9-compliant universal claim over
    stdin content -- see the note on `instance : EnvironmentLoader Bool` above. Do not cite this
    declaration as evidence Spike 3 has been verified for arbitrary stdin. -/
def spike3VerifiedProgram : VerifiedProgram Bool AnyEvent := {
  name             := "Spike 3: Stdin Lexicographical Line Sorter"
  executable       := spike3Executable
  instructions     := spike3Instructions
  spec             := fun b => if b then modelTraceCanonical else modelTraceEmpty
  traceEquivalence := fun b => by
    cases b
    · exact spike3_empty_effect_trace_equivalence_inst
    · exact spike3_canonical_effect_trace_equivalence_inst
}

end Spikes.Spike3SortLines.Windows
