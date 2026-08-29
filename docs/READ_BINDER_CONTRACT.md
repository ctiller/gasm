# READ_BINDER_CONTRACT: the universal read-binder contract shape

- REF: docs/REVIEW.md#law-9-universal-quantification-input-completeness-mandate-the-anti-pointwise-law
- REF: docs/REVIEW.md#law-11-memory-access-capability-mandate-fail-to-assemble
- REF: docs/DECISIONS.md#2-proof-architecture-and-tractability
- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence
- REF: docs/SYSTEM_EFFECTS.md#64-input-events-are-causal-anchors-and-coalescing-barriers-protocol-causality
- REF: docs/TECHNICAL_NOTES.md#2-machine-os-model-debts

## 1. Status and scope

This document owns the Law-5-class **contract shape** that makes Law 9's read-binder clause
("every monadic input operation...
binds an arbitrary result, and the verification contract MUST be parametric in that result")
a checkable proof obligation rather than a sentence. `Gasm/Effects/ReadBinder.lean` states the
contract shape as real Lean
declarations and proves — structurally, zero `sorry`, zero new axioms, no `decide`/
`native_decide` standing in for the universal quantifier — that the shape has the property
this design requires: a continuation proof established once, universally, is invariant
to how the environment chunked its input.

**Current implementation boundary.** `Gasm/Effects/CanonicalizeTrace.lean` now supplies causal
trace canonicalization, `Gasm/Effects/Network.lean` supplies the bounded `splitBytes` primitive
used by the current Windows/Linux/WASI receive hooks, and
`Gasm/Effects/ReadBinderWiring.lean` proves that primitive produces a valid read-binder chunk.
What remains is to make the obligation mandatory in live routine/program contracts and to
compose it with the capability model's destination-buffer authority (§5 and §9). The standalone
shape is therefore implemented; repository-wide enforcement is not.

## 2. The contract shape

A monadic read operation is characterized by two things visible to its caller at the point of
the call: a **requested bound** (`nNumberOfBytesToRead`, `maxLen`, a WASI iovec's declared
capacity — always a `Nat`), and a **returned result** (a `ByteArray`, represented in proof text
as `List Byte` per `docs/EQUIVALENCE_PROOFS.md` §4.1's own `memcpy` theorem convention, since
`ByteArray ≃ List UInt8` and every property in this document is representation-independent).
The read-binder contract shape is: **the returned result is a universally-quantified variable
in the calling routine's contract, constrained only by the bound the syscall signature itself
promises (`result.size ≤ requested`), never fixed to one instantiation.**

```lean
/-- The read-binder proof obligation. A program whose next step is "read up to `requested`
bytes, then run `Post` on whatever came back" satisfies Law 9 only if it can discharge
`Post` for every element of the bounded byte-array domain -- not one chosen witness. -/
def ReadBinderObligation (requested : Nat) (Post : List Byte → Prop) : Prop :=
  ∀ (bytes : List Byte), bytes.length ≤ requested → Post bytes
```

This is deliberately *not* a new effect typeclass method and *not* a change to
`MonadFileSystem.readFile`'s or `MonadNetwork.recv`'s signature — those are N2/N9's
implementation surface. `ReadBinderObligation` is the **shape a routine's contract must have**
wherever it contains a read: the precondition/postcondition pair covering "what happens after
this read" must be exactly a proof term of this `Prop`, for the routine's declared `requested`
bound, not a proof term about one instantiated `bytes` value. A contract of the form

```text
-- PROHIBITED shape: pins the read to a concrete vector.
theorem foo_correct : Post (concreteBytes) := ...
```

is not a weaker version of `ReadBinderObligation requested Post` — it is a different,
unrelated proposition (a claim about one point, not a bound variable), and Law 9 review must
treat it as such rather than as an acceptable special case.

## 3. The read-result domain is uniform: no special-casing

`ReadBinderObligation`'s domain is `{ bytes : List Byte // bytes.length ≤ requested }`,
represented above as a plain hypothesis rather than a subtype for readability. Every element of
that domain is ordinary:

- `bytes = []` — the empty read. This is the same domain element whether the caller's intent
  reads it as "nothing available yet" (a would-block-shaped outcome on a non-blocking
  descriptor) or "the stream is closed" (EOF on a blocking file/pipe read). The *contract shape*
  does not and must not try to disambiguate these — that disambiguation, where a target
  actually needs it, is carried out-of-band by the syscall's own return-code/error channel
  (`Except FileError ByteArray` is already `MonadFileSystem.readFile`'s codomain in
  `Gasm/Effects/FileSystem.lean:65`; WASI's `errno` channel is the analogous WASI mechanism,
  `docs/TECHNICAL_NOTES.md` §2), never by adding a second constructor to the bytes domain itself. Adding
  an `EOF` case that is *not* just `bytes = []` reachable through the ordinary quantifier would
  be exactly the special-casing this task's acceptance criteria prohibits.
- `0 < bytes.length < requested` — a short read. An ordinary domain element like any other; nothing
  in `ReadBinderObligation`'s statement distinguishes it from the next case.
- `bytes.length = requested` — a maximal/full read. Also ordinary; a contract proof that only
  discharges this one case (e.g. by implicitly assuming a hook that always returns everything
  requested, as today's `readFileHook` does) is not a proof of `ReadBinderObligation` at all,
  since the obligation's `∀` was never actually instantiated at the other cases.

The three are one quantifier, not three special cases wired together — §7 proves this
concretely: a general theorem about *all* valid chunkings of a fixed logical input specializes
to the empty-first-read, short-read, and single-maximal-read cases as three ordinary
instantiations of the same lemma, with no case-specific proof step anywhere.

## 4. Integration with the M0/M8 causal trace (interface contract)

`docs/SYSTEM_EFFECTS.md` §6.4 requires that input events are first-class, causally-stamped
trace events and coalescing barriers — a contract that quantifies over a read's *result* but
forgets *that a read occurred, and where in the causal order* would silently reintroduce the
"ack for a read is not ack before a read" confusion §6.4 exists to close.
`Gasm/Effects/CanonicalizeTrace.lean` implements the current single-thread representation; this
section states the interface it must preserve as M0/M8 replace that degeneration rather than
inventing a parallel representation.

`Gasm/Core/Types.lean:48` currently carries `VectorClock` (`clock : ThreadId → Nat`, with
`happensBefore`/`join`/`tick`), but that is only a possible cache for a proved transitive relation.
It cannot preserve profile-native relation labels or source-path witnesses by itself. The interface
this document specifies is therefore:

- A read event's trace representation exposes the M0/M8 stable event identity, observable quotient
  position, and profile-selected `ProjectedCausalEdge`/labelled source-path witnesses incident on
  that position — **not** a bare `Event` in a `List Event`, and not merely an `(Event, VectorClock)`
  pair. `ReadBinderObligation`'s bound variable `bytes` is exactly the *payload* associated with this
  causal slot; the canonical causal-position interface supplies the position and path witnesses. A
  relation-specific vector clock may accompany it only as a proved cache.
- The coalescing-barrier property (§6.4: outputs on either side of an input event never merge or
  commute across it) must be stated as a property of the canonical form M8 produces, not
  re-derived per read site. This contract shape does not re-litigate barrier placement; it only
  requires that the canonical form preserves read events as distinguishable
  positions so that the `bytes` values `ReadBinderObligation` quantifies over remain attached to
  a specific causal slot, not merged away by the very congruence this read-binder contract uses to
  state chunk-robustness (§7) correctly. Concretely: `canonicalizeTrace` must not fold two consecutive
  reads' payloads together the way it is licensed to fold two consecutive same-stream writes —
  `docs/SYSTEM_EFFECTS.md` §6.1's own coalescing table already states this for `NetEvent.recv`/
  reads/`accept` ("never coalesced"), so no change to that table is needed; this section simply
  records that the read-binder contract's soundness is one more thing resting on that row.
- Once M8 lands, a routine's read-continuation contract is a dependent pair: the canonical causal
  position/path-witness interface for the read event, plus a
  `ReadBinderObligation requested Post` proof keyed to that position's payload slot. This document
  does not attempt M0/M8's representation work; it names the exact two properties (distinguishable
  position, non-coalescing) that implementation must have for this contract shape to compose with it
  soundly.

## 5. Integration with Law 11's capability mandate

Law 11 requires every memory-touching instruction to carry a proof of a valid, in-scope
`MemoryPerm` capability covering the accessed range (`Gasm/Core/Permissions.lean:32`). The
read-binder contract and Law 11 are **two distinct mechanisms that must compose at exactly one
point, not one mechanism** — collapsing them would hide the very bug class this task exists to
make provable:

- `ReadBinderObligation`'s bound is the **syscall's own declared cap** (`requested`, i.e.
  `nNumberOfBytesToRead` / a WASI iovec's declared length) — this is a property of the *call
  site*, known before the read happens.
- Law 11's `MemoryPerm` bound is the **destination buffer's actual capacity** — a property of
  the *memory the caller allocated*, entirely independent of what the caller happens to pass as
  `requested`.
- In a correct program these two bounds are meant to be equal (the caller is supposed to pass
  its buffer's true capacity as `requested`). **Spike 4's stack-buffer-overflow bug
  is exactly the case where they were not in the historical Spike 4 overflow finding**: a
  16-byte stack buffer at `RSP+0x40`, with `requested = 128` passed to `recv`
  (`Spikes/Spike4HttpServer/Windows/Program.lean:130-136`). Today this is invisible to
  `spike4_windows_*_trace_equivalence` for two independent reasons this document is careful to
  keep separate: (a) the *trace-equivalence* theorems are pointwise (one literal 37-byte request
  string), so they never even *ask* what happens for a longer request — this is what §7's
  chunk-robustness demonstration is about; (b) before the bounded `splitBytes` wiring, even a
  hypothetical universalized version would still not catch it because `recvHook` delivered its
  queued request atomically. The bounded hook now fixes that reachability gap, but destination-
  buffer faulting remains absent (`docs/TECHNICAL_NOTES.md` §2: the memory model has no reachable
  destination-buffer or general memory faults, so a proof of a Zlib routine
  cannot distinguish 'correct' from 'scribbles outside its buffer'"), so a memory-safety
  violation from an over-length write is not an event this model can even produce, let alone
  quantify over. That gap belongs to the bounded-read target work and M1's Law 11 migration, not
  this document.
- **The shape of the composed obligation**, once both land, is: a routine that reads into a
  fixed-capacity buffer must discharge `ReadBinderObligation requested Post` where `Post bytes`
  is itself `∀ (perm : MemoryPerm bufferBase bufferCapacity .Exclusive), bytes.length ≤
  bufferCapacity → <the write of `bytes` into the buffer is safe>` — i.e. the write's Law 11
  safety proof is *inside* the scope of the read's universal quantifier, not outside it. This is
  the precise mechanism that turns Spike 4's bug from "invisible" to "a proof obligation that
  cannot be discharged": `requested` (128) is *not* itself bounded by `bufferCapacity` (16) in
  the contract shape above — the read is honestly allowed to return anything up to `requested`
  — so `Post` must be proven for `bytes.length` values between 17 and 128 as much as for values
  0 through 16, and no such proof exists, because no such proof *can* exist for a buffer that
  small. Making `requested` itself bounded by `bufferCapacity` at the call site (the actual fix)
  is what makes the obligation dischargeable again; the contract shape's job is to make the
  *absence* of that fix a proof failure rather than a silently-passing pointwise check.
- **Conclusion: do not unify the two mechanisms into one.** `ReadBinderObligation`'s quantifier
  must range over the syscall's declared cap, honestly, even when that cap exceeds what any
  attached buffer capability can safely absorb — that mismatch *is* the bug class Law 11 exists
  to make unrepresentable. A design that quietly capped the read's quantifier at the buffer's
  capacity would make Spike 4's bug provable-safe by construction, which is the opposite of
  correct: it would hide the very obligation whose failure to discharge is the point.

## 6. Closing the three evasion shapes

Per `docs/DECISIONS.md` §2's read-as-universal-binder decision and Law 9, three named evasion shapes must
become unrepresentable, not merely discouraged:

- **Hardcoded-output stubs.** A spec whose read-continuation is `Post bytes := (output =
  fixedConstant)` independent of `bytes` cannot be proven as `ReadBinderObligation requested
  Post` unless `fixedConstant` is trivially reachable for *every* `bytes` in the domain — which
  is false for any spec that is supposed to depend on its input (e.g. an echo/copy program).
  The quantifier does not merely make a stub *harder to write*; a stub spec fails
  `ReadBinderObligation`'s proof obligation outright the moment `Post` is instantiated at two
  `bytes` values that would need different constants.
- **Domain-shrinking via purpose-built input enums.** Spike5's `GzipOp | compress` /
  `GunzipOp | decompress` single-constructor pattern quantifies over a type
  with one inhabitant dressed up as a real domain. `ReadBinderObligation`'s domain is
  `{bytes : List Byte // bytes.length ≤ requested}` by construction — there is no single-
  constructor stand-in available, because the bound variable's type is fixed to the real
  byte-array domain the read-binder contract is defined over, not a spec-author-chosen index
  type. A spec cannot substitute a narrower type for `bytes` without changing
  `ReadBinderObligation`'s stated type signature, which review checks against the read's actual
  Win32/WASI/POSIX signature (a `Nat`-bounded byte buffer, always).
- **Pointwise evaluation.** `Post` in `ReadBinderObligation requested Post` is universally
  quantified; no `decide`/`native_decide`/`bv_decide` evaluator can discharge a claim over an
  unbound `bytes : List Byte` (Law 10 already forecloses this for infinite domains generally —
  §7's proof is exactly the kind of induction Law 10 requires in place of evaluation). A
  `*_inst`-suffixed regression check against one instantiated `bytes` value remains legitimate
  as a regression test (Law 8) but cannot be cited as discharging `ReadBinderObligation` itself,
  since it is a different, weaker proposition (§2).

## 7. Worked example: chunk-robustness as a corollary

`Gasm/Effects/ReadBinder.lean` (this task) proves the following, in the spirit of
`docs/EQUIVALENCE_PROOFS.md` §4.1's worked `memcpy` example — a small "read-then-write" program:
copy a logical input of unknown total length through to output, one bounded read at a time.

The read-binder domain for a single read of cap `cap` against remaining true input `rem` is
formalized as `IsValidReadChunk rem cap chunk := chunk.length ≤ cap ∧ chunk = rem.take
chunk.length` — `chunk` is any prefix of what remains, no longer than `cap`; this is literally
`ReadBinderObligation`'s domain (§2) refined with the one additional fact a faithful
environment's reads must respect (each read consumes a genuine prefix of what is left, never
reorders or invents bytes) rather than a separate ad hoc definition.

A **complete chunking** of a logical input `total` under cap `cap` is any finite list of reads
that, played in order, consumes all of `total`:

```lean
inductive ChunksOf : List Byte → Nat → List (List Byte) → Prop where
  | nil  : ChunksOf [] cap []
  | cons {rem chunk chunks} :
      chunk.length ≤ cap →
      chunk = rem.take chunk.length →
      ChunksOf (rem.drop chunk.length) cap chunks →
      ChunksOf rem cap (chunk :: chunks)
```

Nothing in `ChunksOf.cons` forces `chunk` to be nonempty, forces a fixed number of reads, or
distinguishes "the first chunk happens to be everything" from "the input arrives in twenty
one-byte pieces with empty reads interspersed" — every valid `List (List Byte)` satisfying this
relation is an ordinary, equally-legal witness, exactly matching §3's "no special-casing"
requirement. `ChunksOf.flatten_eq_total` proves, by structural induction on the derivation (no
`decide`, no enumeration — the induction is over `ChunksOf`'s own constructors), that
`chunks.flatten = rem` for any witness. **The chunk-robustness corollary,
`chunk_robustness`, then falls out in one line**: for any two complete chunkings `chunksA`,
`chunksB` of the same `total`, `chunksA.flatten = chunksB.flatten` — both equal `total`, so they
equal each other, by `flatten_eq_total` applied twice and `rw`. No separate induction is needed
for chunk-robustness; it is the same theorem read twice, which establishes this document's
acceptance criterion that "chunking robustness is a corollary, not a separate requirement."
`continuation_invariant_to_chunking` restates this at
the level the task cares about most: if a continuation's postcondition `Post` has already been
established for the reconstruction obtained under *one* chunking, it holds automatically for
*every* other chunking of the same logical input — a program proven correct for one chunking is
provably equal, via this composition, to the same program under any other chunking, checked
rather than merely asserted.

`ChunksOf.chunks_are_valid_reads` closes the loop back to §2: every `chunk` appearing in any
witness of `ChunksOf rem cap chunks` satisfies `chunk.length ≤ cap`, i.e. is drawn from exactly
`ReadBinderObligation cap`'s domain — `ChunksOf` is not a parallel notion of "valid read
result," it is the read-binder domain applied at every position of a finite trace.
`ChunksOf.discharges_read_binder_obligation` restates this by name: once a
`ReadBinderObligation cap Post` is proven (established for the *entire* bounded domain), every
chunk in every complete chunking satisfies `Post` for free — a chunking is a sequence of
witnesses into an obligation already discharged, never a new source of proof work.

## 8. Scope boundary: what this task does not attempt

- No modification to `MonadFileSystem`, `MonadNetwork`, `Win32API.lean`'s hooks, or any spike's
  `Equivalence.lean`. §5's Spike 4 discussion is diagnostic (explaining *why* the current model
  cannot see the bug and *what shape* would), not a patch.
- No attempt to prove liveness/termination of a real read-loop. §7's `ChunksOf` characterizes
  *complete* chunkings (finite lists that already reconstruct the whole input) rather than
  defining an executable, fuel-bounded drain loop and proving it terminates — that is an
  **outer** obligation in `docs/EQUIVALENCE_PROOFS.md` §1's inner/outer reactive-program split
  (the ratified `VerifiedReactiveProgram` design in `docs/EQUIVALENCE_PROOFS.md`), independent of the **inner** per-read contract shape this
  document defines. Conflating the two would smuggle a liveness proof into what is supposed to
  be a statement about one read's result domain.
- No attempt to close any of the nine grandfathered Spike 3/4 allowlist entries or any other
  `scripts/gate_allowlist.txt` entry — this is deliberately separate work
  so it does not balloon into "read-binder work plus nine proofs."
- No replacement or expansion of the landed `canonicalizeTrace` and bounded-read implementations.
  §4 states the preservation contract those foundations must satisfy as they are integrated into
  live program contracts.

## 9. What remains

1. **Trace integration has landed at the effect layer.** Preserve §4's distinguishable
   read-event position and non-coalescing properties when attaching a live
   `VerifiedProgram`-successor contract to a `ReadBinderObligation` instance.
2. **Bounded receive-hook wiring has landed.** `splitBytes` now supplies the Windows/Linux/WASI
   receive paths and `splitBytes_isValidReadChunk` proves the connection. File/pipe/console and
   error-channel fidelity remain target-owned model work (`docs/TECHNICAL_NOTES.md` §2).
3. **A `VerifiedProgram` successor** must expose
   a field of type `ReadBinderObligation requested Post` (or its M0/M8-integrated successor from
   §4) as a mandatory struct field, the way `VerifiedProgram.traceEquivalence` is mandatory
   today (`Gasm/Core/Verification.lean`) — this document supplies the shape that field's type
   must have.
4. **The composition calculus** must supply the
   "sequential composition across an input-event coalescing barrier" rule this shape needs;
   §7's
   `continuation_invariant_to_chunking` is offered as a candidate building block for that rule
   (chaining a read's universal obligation into a following computation-then-write step), not a
   substitute for that broader design.
5. **The capability migration in `docs/MEMORY_MODEL.md`** must land before §5's composed obligation (read-quantifier
   inside a Law 11 write-safety proof) can be stated against real `MemoryPerm` tokens in a live
   routine rather than the schematic form given in §5.
6. **The nine grandfathered Spike 3/4 entries** remain separate proof work; §5's Spike 4
   walkthrough is their starting point once a live contract carries the obligation.

This document's own deliverable — the contract shape itself, demonstrated as real,
zero-`sorry`, zero-axiom Lean declarations with the chunk-robustness property checked rather
than merely asserted — is complete. Items 1-6 above are the named remaining work and landed
foundations, owned by the cited current documents and source modules rather than a retired task ledger.
