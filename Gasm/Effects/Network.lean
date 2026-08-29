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
import Gasm.Effects.Inject

namespace Gasm.Effects

open Gasm.Core

/- REF: docs/SYSTEM_EFFECTS.md#11-core-effect-typeclass-hierarchy-gasmeffects -/
/-- Pure domain event for network socket interactions. -/
inductive NetEvent where
  | listen (port : UInt16)
  | accept (client : String)
  | recv   (data : String)
  | send   (data : String)
  | close  (sock : Nat)
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/SYSTEM_EFFECTS.md#11-core-effect-typeclass-hierarchy-gasmeffects -/
instance : IsEvent NetEvent where
  domain := "Network"
  format := fun
    | .listen p => s!"listen({p})"
    | .accept c => s!"accept({c})"
    | .recv d   => s!"recv({d})"
    | .send d   => s!"send({d})"
    | .close s  => s!"close({s})"

/- REF: docs/SYSTEM_EFFECTS.md#2-portable-effect-typeclass-specifications -/
/-- Portable typeclass abstraction for TCP network socket operations. -/
class MonadNetwork (m : Type → Type) where
  listen : UInt16 → m (Option Nat)
  accept : Nat → m (Option Nat)
  -- F1 (Law 9 root fix): `recv` yields the raw bytes a client sent, NOT a `String`. Lean's
  -- `String` is a sequence of Unicode scalar values, so a `String`-typed read result cannot
  -- represent an arbitrary octet stream at all -- which made the only honest per-connection
  -- claim, `∀ (request : ByteArray) ...` (`docs/tasks/PA6-read-binder-contract.md`'s read-binder
  -- domain), literally unstatable: there was no type to quantify over. See `recvDeliver` below
  -- and the note on `Gasm.Effects.TraceState.incomingRequests`.
  recv   : Nat → Nat → m (Option ByteArray)
  send   : Nat → String → m Bool
  close  : Nat → m Unit

/- REF: docs/READ_BINDER_CONTRACT.md#5-integration-with-law-11s-capability-mandate -/
/-- Short-read primitive, byte-domain core (`docs/READ_BINDER_CONTRACT.md`). Splits a logical read source's bytes at a
declared cap: `(delivered, remaining)` where `delivered = bytes.take cap` (never more than
`cap` bytes, whatever `bytes`' true length is) and `remaining = bytes.drop cap` is what a
faithful environment must still hand back on a subsequent read. This is precisely
`ReadBinder.lean`'s `IsValidReadChunk`/`ChunksOf` domain (`docs/READ_BINDER_CONTRACT.md` §7)
applied at the model level for the first time: `splitBytes_isValidReadChunk` below is the wiring
step connecting the two. Before N2, `recvHook`/`sysReadHook`'s socket branch ignored the
syscall's declared cap outright (wrote every byte of the queued logical request regardless of
what the caller asked for); WASI's `sock_recv` respected the cap for the write but then
discarded, rather than queued, the undelivered remainder. `splitBytes` is deliberately the
"deliver as much as is available, capped" default (`delivered = bytes.take cap`, never
less when the cap doesn't bind) rather than a nondeterministic choice of any length up to the
cap -- this is the "default preserving today's behaviour while making other outcomes
expressible" shape: for every existing spike (a request shorter than its call's declared cap),
`bytes.take cap = bytes` and `bytes.drop cap = []`, so delivery stays atomic and unchanged;
the moment a caller's declared cap is smaller than what is actually queued, delivery is now
genuinely partial (a reachable point of `ReadBinderObligation`'s domain the pre-N2 model could
never produce) and the true remainder survives for a following call rather than being
overflow-written past the cap or silently dropped. -/
def splitBytes (bytes : List Byte) (cap : Nat) : List Byte × List Byte :=
  (bytes.take cap, bytes.drop cap)

/- REF: docs/READ_BINDER_CONTRACT.md#5-integration-with-law-11s-capability-mandate -/
/-- The short-read safety invariant (`docs/READ_BINDER_CONTRACT.md`): whatever `splitBytes` hands back as the delivered half, it never
exceeds the declared cap -- a `recv`/`ReadFile` hook built on `splitBytes` cannot write more
than its caller's own declared bound into memory, by construction, for any queued source and
any cap. This is the fact that was simply false of `recvHook`/`sysReadHook`'s pre-N2 socket
branch (which read `s.gprs .r8`/`.rdx` and then never consulted it). -/
theorem splitBytes_delivered_le_cap (bytes : List Byte) (cap : Nat) :
    (splitBytes bytes cap).1.length ≤ cap := by
  simp only [splitBytes, List.length_take]
  exact Nat.min_le_left _ _

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- `splitBytes` never invents or drops bytes: the delivered half concatenated with the
remaining half reconstructs the original source exactly. Together with
`splitBytes_delivered_le_cap`, this is exactly `IsValidReadChunk`'s two conjuncts
(`splitBytes_isValidReadChunk` below states it that way directly). -/
theorem splitBytes_append (bytes : List Byte) (cap : Nat) :
    (splitBytes bytes cap).1 ++ (splitBytes bytes cap).2 = bytes := by
  simp [splitBytes, List.take_append_drop]

/- REF: docs/READ_BINDER_CONTRACT.md#5-integration-with-law-11s-capability-mandate -/
/-- `splitBytes`' byte-array-native counterpart (F1). Same contract -- `delivered` is capped at
`cap`, `remaining` is exactly what a faithful environment must still hand back -- but stated on
`ByteArray`, the type a socket read actually ranges over, rather than on `List Byte` reached via
a `String` detour. Built on `ByteArray.extract` (the same primitive `Syscall.lean`'s
`sysReadHook` already uses on its `stdinBuffer` branch), so it does not route through
`ByteArray.toList`, whose `@[irreducible]` well-founded `toList.loop` does not reduce in the
kernel (measured; see `docs/TRUST_PLAN.md`). -/
def splitByteArray (bytes : ByteArray) (cap : Nat) : ByteArray × ByteArray :=
  (bytes.extract 0 cap, bytes.extract cap bytes.size)

/- REF: docs/READ_BINDER_CONTRACT.md#5-integration-with-law-11s-capability-mandate -/
/-- The N2 safety invariant, byte-array form: a hook built on `splitByteArray` cannot write more
than its caller's own declared bound, for any request and any cap. -/
theorem splitByteArray_delivered_le_cap (bytes : ByteArray) (cap : Nat) :
    (splitByteArray bytes cap).1.size ≤ cap := by
  simp only [splitByteArray, ByteArray.size_extract, Nat.sub_zero]
  exact Nat.min_le_left _ _

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- `splitByteArray` never invents or drops bytes, for **any** request and **any** cap. This is
the fact the pre-F1 `String`-typed queue could not satisfy: its remainder was requeued as
`match String.fromUTF8? remainder with | some r => r :: rest | none => rest`, so a cap landing
inside a multi-byte UTF-8 sequence made the remainder invalid UTF-8 and the `none` branch
**silently discarded every undelivered byte**. Measured before this change: a 6-byte request
read with `cap = 2` delivered 2 bytes and requeued `[]`, losing 4. -/
theorem splitByteArray_append (bytes : ByteArray) (cap : Nat) :
    (splitByteArray bytes cap).1 ++ (splitByteArray bytes cap).2 = bytes := by
  simp only [splitByteArray, ByteArray.extract_append_extract, Nat.zero_min]
  exact ByteArray.extract_zero_max_size

/- REF: docs/READ_BINDER_CONTRACT.md#5-integration-with-law-11s-capability-mandate -/
/-- A `ByteArray`'s bytes as a `List Byte`, for the byte-list-typed APIs this repository already
has (`X86_64Mem.writeBytes`, `Stdlib.Http11.parseRequestLine`).

Deliberately **not** `ByteArray.toList`: that bottoms out in `ByteArray.toList.loop`, an
`@[irreducible]` well-founded recursion that does not reduce in the kernel -- measured directly
(`example : reqBytes.toList.length = 35 := by rfl` fails; `docs/TRUST_PLAN.md` names it as
Spike 4 reduction blocker 1). `List.range`/`List.map`/`getElem!` all reduce, so routing the F1
byte queue through this function instead keeps the recv path and the model's request-line parser
kernel-reducible rather than re-importing the blocker the type change was meant to sidestep. -/
def toByteList (b : ByteArray) : List Byte :=
  (List.range b.size).map (fun i => b[i]!)

-- `toByteList` agrees with `ByteArray.toList` -- it is a reducibility change, not a semantic one.
#guard toByteList "GET / HTTP/1.1\r\n".toUTF8 == "GET / HTTP/1.1\r\n".toUTF8.toList
#guard toByteList ByteArray.empty == []

/- REF: docs/SYSTEM_EFFECTS.md#11-core-effect-typeclass-hierarchy-gasmeffects -/
/-- Renders delivered bytes as the `String` payload `NetEvent.recv` carries. This is the
**Latin-1 injection** -- byte `b` becomes `U+00b` -- chosen because it is *total* and
*injective*: every one of the 256 byte values has a distinct image and no byte string is
unrepresentable, so the event trace remains a faithful observable of what was delivered. On
ASCII (every request vector in this repository) it agrees with UTF-8 decoding, so no existing
trace changes.

Contrast the two pre-F1 spellings this replaces, both of which lost information:
  * `(String.fromUTF8? deliveredArr).getD req` -- on a delivered prefix that is not valid UTF-8
    this fell back to `req`, making the `recv` event report the **whole** request as delivered
    when only a capped prefix reached memory. Measured: a 6-byte request read with `cap = 2`
    emitted `NetEvent.recv` carrying all 6 bytes. The trace lied about the read length, directly
    contradicting `splitBytes_delivered_le_cap`.
  * `X86_64MachineState.readString`'s "UTF-8 if valid, else Latin-1" fallback, which is *not*
    injective (`[0xC3,0xA9]` and `[0xE9]` both render `"é"`).

**Remaining obstruction (not closed by F1):** `NetEvent.recv`'s payload field is still `String`
rather than `ByteArray`, because `ByteArray` has no `Repr` instance in Lean 4.33 (measured) and
`NetEvent` derives `Repr`. The injection above makes that faithful, not merely convenient, but
the honest event type is still `ByteArray`. -/
def bytesToPayload (bytes : ByteArray) : String :=
  String.ofList ((List.range bytes.size).map (fun i => Char.ofNat (bytes[i]!).toNat))

-- `bytesToPayload` really is injective, checked exhaustively over the whole byte domain: all 256
-- byte values round-trip through the Latin-1 injection distinctly. The domain is finite and
-- fully enumerated, so this is a complete check of the claim, not a sampled one.
#guard (List.range 256).all (fun n => (UInt8.ofNat (Char.ofNat (UInt8.ofNat n).toNat).toNat).toNat == n)
#guard ((List.range 256).map (fun n => (Char.ofNat (UInt8.ofNat n).toNat))).eraseDups.length == 256

/- REF: docs/READ_BINDER_CONTRACT.md#5-integration-with-law-11s-capability-mandate -/
/-- The single delivery step every recv-shaped hook in this repository performs: deliver at most
`cap` bytes off the head of the request queue, and requeue whatever is left over. Factored out so
`Gasm/Effects/Trace.lean`'s `MonadNetwork.recv` (the spec side), `Win32API.lean`'s `recvHook`,
`Syscall.lean`'s `sysReadHook` and `WASI/ABI.lean`'s `sock_recv` (the three machine sides) cannot
drift apart -- before F1 the four sites each spelled the same nine lines out by hand. -/
def recvDeliver (req : ByteArray) (cap : Nat) (rest : List ByteArray) : ByteArray × List ByteArray :=
  let (delivered, remaining) := splitByteArray req cap
  (delivered, if remaining.isEmpty then rest else remaining :: rest)

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- **The recv no-loss law, universally quantified over the real read-binder domain.** For ANY
request byte string and ANY declared cap: what the hook delivers concatenated with the remainder
is exactly the original request, and that remainder is requeued verbatim whenever it is non-empty.
Nothing is invented, truncated away, or silently dropped.

This is the honest theorem F1 exists to make statable. It could not be stated before, let alone
proved: `∀ (request : ByteArray)` had no queue to range over, and the `String`-typed queue's
requeue path made the second conjunct outright false. -/
theorem recvDeliver_lossless (req : ByteArray) (cap : Nat) (rest : List ByteArray) :
    (recvDeliver req cap rest).1 ++ (splitByteArray req cap).2 = req ∧
    (recvDeliver req cap rest).2 =
      (if (splitByteArray req cap).2.isEmpty then rest else (splitByteArray req cap).2 :: rest) :=
  ⟨splitByteArray_append req cap, rfl⟩

/- REF: docs/READ_BINDER_CONTRACT.md#5-integration-with-law-11s-capability-mandate -/
/-- The cap bound, lifted to `recvDeliver`: no recv-shaped hook writes past its caller's declared
bound, for any request and any cap. -/
theorem recvDeliver_delivered_le_cap (req : ByteArray) (cap : Nat) (rest : List ByteArray) :
    (recvDeliver req cap rest).1.size ≤ cap :=
  splitByteArray_delivered_le_cap req cap

end Gasm.Effects
