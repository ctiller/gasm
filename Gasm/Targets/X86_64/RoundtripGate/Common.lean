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
import Gasm.Targets.X86_64.Instructions.Base

namespace Gasm.Targets.X86_64.RoundtripGate

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#5-stage-b-design-only-not-implemented-by-this-change -/
/-- Byte-level roundtrip equality relation shared by every per-family gate theorem, generalized
    (Stage B) to take the decoder function itself as a parameter rather than hard-coding
    `Decoder.lean`'s global `decodeX86_64Instr`. Each per-family `RoundtripGate/<Family>.lean`
    shard instantiates this with that family's own co-located `tryDecode` (so the shard depends
    only on its own `Instructions/<Family>.lean` file, not on the monolithic decoder — this is
    the specific dependency edge Stage B removes to stop editing one family's decode logic from
    invalidating every other family's gate shard); `DispatchExhaustive.lean` separately
    instantiates it with the real `decodeX86_64Instr` to prove the thin dispatcher agrees with
    each family's own decoder (the "dispatch-reachability" obligation). `AnyX86_64Instruction` (an
    open existential over a hidden concrete type) has no general `DecidableEq` instance to drive a
    `List.all` over a mixed-family list, so this checks the conjunction the design doc specifies
    instead: (a) decoding the encoded bytes succeeds, (b) the decoded length equals the encoded
    byte count, (c) re-encoding the decoded instruction reproduces the original bytes exactly, and
    (d) the `toLean` renderings of the decoded and original instructions match — guarding against
    a same-bytes-different-structure misdecode (the class of bug the 0x8B REX.W soundness fix
    addressed). -/
def decodesOk (tryDecode : ByteArray → Nat → Except String (AnyX86_64Instruction × Nat))
    (i : AnyX86_64Instruction) : Bool :=
  let encoded := X86_64Instruction.encode i
  match tryDecode encoded 0 with
  | .error _ => false
  | .ok (decoded, len) =>
    len == encoded.size &&
    X86_64Instruction.encode decoded == encoded &&
    X86_64Instruction.toLean decoded == X86_64Instruction.toLean i

/- REF: docs/TARGETS/X86_64.md#5-stage-b-design-only-not-implemented-by-this-change -/
/-- **In-bucket exclusivity**, generically derived as a corollary of a family's own
    `decodesOk`-based roundtrip gate rather than a fresh `decide` obligation: if a family's gate
    theorem holds for its whole `roundtripCases` list, then any two witnesses in that list which
    encode to *identical bytes* must render identically too — i.e. `tryDecode` (a deterministic
    function of its byte-array argument) cannot have decoded those shared bytes into something
    that `toLean`-matches two genuinely different instructions at once. This is the precise sense
    in which "no two of a family's own byte patterns collide ambiguously": it does not (and does
    not need to) enumerate all `n²` pairs via `decide` — for a family whose witness lists run into
    the hundreds (e.g. `MovR64Imm64`) a naive pairwise `decide` would be exactly the kind of
    quadratic elaboration cost `docs/TARGETS/X86_64.md`'s intermittent-OOM note already flags as a
    risk, so deriving this logically from the linear-cost gate that already exists is the tractable
    choice, not merely a convenient one. Every per-family shard instantiates this with its own
    `<family>_roundtripGate` proof; the proof term below is the one, family-agnostic argument. -/
theorem inBucketExclusiveOf {tryDecode : ByteArray → Nat → Except String (AnyX86_64Instruction × Nat)}
    {cases : List AnyX86_64Instruction} (h : cases.all (decodesOk tryDecode) = true) :
    ∀ i ∈ cases, ∀ j ∈ cases,
      X86_64Instruction.encode i = X86_64Instruction.encode j →
      X86_64Instruction.toLean i = X86_64Instruction.toLean j := by
  intro i hi j hj heq
  have hi' : decodesOk tryDecode i = true := (List.all_eq_true.mp h) i hi
  have hj' : decodesOk tryDecode j = true := (List.all_eq_true.mp h) j hj
  simp only [decodesOk, heq] at hi' hj'
  cases hcase : tryDecode (X86_64Instruction.encode j) 0 with
  | error e =>
    rw [hcase] at hi'
    simp at hi'
  | ok p =>
    rw [hcase] at hi' hj'
    obtain ⟨decoded, len⟩ := p
    simp only [Bool.and_eq_true, beq_iff_eq] at hi' hj'
    rw [← hi'.2, hj'.2]

end Gasm.Targets.X86_64.RoundtripGate
