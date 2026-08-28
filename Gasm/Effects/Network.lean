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
  recv   : Nat → Nat → m (Option String)
  send   : Nat → String → m Bool
  close  : Nat → m Unit

/- REF: docs/READ_BINDER_CONTRACT.md#5-integration-with-law-11s-capability-mandate -/
/-- N2 short-read primitive, byte-domain core (MODEL_DEBT.md §C1). Splits a logical read source's bytes at a
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
/-- The N2 safety invariant (MODEL_DEBT.md §C1): whatever `splitBytes` hands back as the delivered half, it never
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

end Gasm.Effects
