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

/-
Gasm/Effects/ReadBinderWiring.lean -- N2/PA6 wiring (docs/READ_BINDER_CONTRACT.md, MODEL_DEBT.md
§C1).

`Gasm/Effects/ReadBinder.lean` states the read-binder contract shape (`ReadBinderObligation`,
`IsValidReadChunk`, `ChunksOf`) as a standalone development, explicitly not yet connected to any
live hook (`docs/READ_BINDER_CONTRACT.md` §1: "no existing typeclass... hook (`readFileHook`,
`recvHook`)... is modified [t]here"). `Gasm/Effects/Network.lean`'s `splitBytes` is the N2
primitive `recvHook`/`sysReadHook`/`sock_recv` now use to cap a delivered read at the syscall's
declared bound instead of ignoring it. This file is the wiring step both documents name as
future work: it proves `splitBytes`'s output is literally a member of `IsValidReadChunk`'s
domain, and uses that connection to make Spike 4's buffer/cap mismatch
(`docs/tasks/N8-spike4-stack-buffer-overflow.md`) a proved-undischargeable obligation rather than
a description.
-/

import Gasm.Core.Types
import Gasm.Effects.Network
import Gasm.Effects.ReadBinder

namespace Gasm.Effects

open Gasm.Core (Byte)

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- `bytes.take cap` never needs more of `bytes` than `min cap bytes.length` actually supplies
-- the fact `IsValidReadChunk`'s second conjunct needs in the shape `chunk = rem.take
chunk.length` rather than `rem.take cap`. -/
private theorem take_eq_take_length_take (bytes : List Byte) (cap : Nat) :
    bytes.take cap = bytes.take (bytes.take cap).length := by
  rw [List.length_take]
  rcases Nat.le_total cap bytes.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.take_of_length_le h, List.take_length]

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- The wiring theorem: N2's `splitBytes` -- the primitive `recvHook` (Windows), `sysReadHook`'s
socket branch (Linux), and `sock_recv` (WASI) are now built on -- always delivers a chunk lying
in PA6's read-binder domain. Before this theorem, `IsValidReadChunk`/`ReadBinderObligation` had
no connection to any live hook; this is that connection, stated once so every current and future
caller of `splitBytes` inherits it rather than re-deriving it. -/
theorem splitBytes_isValidReadChunk (bytes : List Byte) (cap : Nat) :
    IsValidReadChunk bytes cap (splitBytes bytes cap).1 := by
  refine ⟨splitBytes_delivered_le_cap bytes cap, ?_⟩
  exact take_eq_take_length_take bytes cap

/- REF: docs/READ_BINDER_CONTRACT.md#5-integration-with-law-11s-capability-mandate -/
/-- `docs/tasks/N8-spike4-stack-buffer-overflow.md`'s audit finding: Spike 4's `recv`/`read`
calls passed `len = 128` (the syscall's own declared cap, exactly the bound
`ReadBinderObligation` quantifies over, §2) against a stack recv buffer allocated only 16 bytes.
This is a concrete instance of the mismatch `docs/READ_BINDER_CONTRACT.md` §5 describes in the
abstract: no write-safety postcondition bounded by a 16-byte capacity can be proven for *every*
value `ReadBinderObligation 128` is honestly obliged to cover, because that domain contains
chunks of length 17 through 128 a 16-byte buffer cannot absorb. The proof exhibits the witness
directly (a 17-byte chunk) and discharges the negation by the same universal quantifier
`ReadBinderObligation` states -- no `decide`/`native_decide` stands in for the quantifier itself;
only the two closed arithmetic facts (`17 ≤ 128`, `¬ (17 ≤ 16)`) are decided. N8's actual fix
(landed independently, `f433b31`, while this file was being written) widened the buffer to 256
bytes with `len` widened to match, rather than capping the read at 16 --
`spike4_matched_buffer_obligation_discharges_256` below states that shape of fix as the
dischargeable contrast, at the exact numbers that landed. -/
theorem spike4_unsafe_buffer_obligation_undischargeable :
    ¬ ReadBinderObligation 128 (fun bytes => bytes.length ≤ 16) := by
  intro h
  have hb := h (List.replicate 17 (0 : Byte)) (by simp only [List.length_replicate]; omega)
  simp only [List.length_replicate] at hb
  omega

/- REF: docs/READ_BINDER_CONTRACT.md#5-integration-with-law-11s-capability-mandate -/
/-- The contrast case, generalized over any cap: once a buffer's capacity equals the syscall's
declared cap, the same shape of obligation is trivially dischargeable -- every element of a
`cap`-bounded domain is, by definition, no more than `cap` bytes. This is the fix
`docs/READ_BINDER_CONTRACT.md` §5 names ("making `requested` itself bounded by `bufferCapacity`
at the call site... is what makes the obligation dischargeable again"), stated as a proof rather
than an assertion; read together with `spike4_unsafe_buffer_obligation_undischargeable` above,
the pair is the "previously provable now correctly fails / previously unprovable now provable"
demonstration this wiring exists to deliver. -/
theorem spike4_matched_buffer_obligation_discharges (cap : Nat) :
    ReadBinderObligation cap (fun bytes => bytes.length ≤ cap) :=
  fun _bytes h => h

/- REF: docs/READ_BINDER_CONTRACT.md#5-integration-with-law-11s-capability-mandate -/
/-- N8's actual landed fix (`f433b31`, `Spikes/Spike4HttpServer/Windows/Program.lean`'s current
stack layout: a 256-byte recv buffer at `RSP+0x40..0x13F`, with `recv`'s `len` argument widened
to match -- that file's own comment: "recv's `len` argument below always equals this buffer's
size, so the write can never exceed it"): `spike4_matched_buffer_obligation_discharges`
specialized to the exact number the fix that actually shipped uses, closing the loop from
`spike4_unsafe_buffer_obligation_undischargeable`'s 16-byte counterexample to what this
repository's Spike 4 does today. -/
theorem spike4_matched_buffer_obligation_discharges_256 :
    ReadBinderObligation 256 (fun bytes => bytes.length ≤ 256) :=
  spike4_matched_buffer_obligation_discharges 256

end Gasm.Effects
