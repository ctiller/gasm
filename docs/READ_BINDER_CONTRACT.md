# READ_BINDER_CONTRACT: the PA6 read-binder contract shape

- REF: docs/REVIEW.md#law-9-universal-quantification--input-completeness-mandate-the-anti-pointwise-law
- REF: docs/REVIEW.md#law-11-memory-access-capability-mandate-fail-to-assemble
- REF: docs/adr/0015-read-as-universal-binder.md
- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence
- REF: docs/SYSTEM_EFFECTS.md#64-input-events-are-causal-anchors-and-coalescing-barriers-protocol-causality
- REF: MODEL_DEBT.md (§C1)
- REF: docs/tasks/PA6-read-binder-contract.md

## 1. Status and scope

This document is the Law-5-class design doc `docs/tasks/PA6-read-binder-contract.md` requires:
the **contract shape** that makes Law 9's read-binder clause ("every monadic input operation...
binds an arbitrary result, and the verification contract MUST be parametric in that result")
a checkable proof obligation rather than a sentence. It is design, not implementation: no
existing typeclass (`MonadFileSystem`, `MonadNetwork`), hook (`readFileHook`, `recvHook`), or
spike contract is modified here. `Gasm/Effects/ReadBinder.lean` (new, this task) is a
self-contained, standalone development that states the contract shape as real Lean
declarations and proves — structurally, zero `sorry`, zero new axioms, no `decide`/
`native_decide` standing in for the universal quantifier — that the shape has the property
this task exists to deliver: a continuation proof established once, universally, is invariant
to how the environment chunked its input.

**Honest dependency note.** PA6's own frontmatter lists `after: [PA5, N2]`, and its task file
explains why in detail: PA5 (`canonicalizeTrace`) is not yet in the tree (`grep -rn
canonicalizeTrace` finds zero hits outside the task/design docs), and N2 (the `ReadFile`/`recv`
short-read model rebuild) has not landed either — `readFileHook` still computes
`count := min maxLen avail` and unconditionally sets `RAX := 1`
(`Gasm/Targets/Windows/Win32API.lean:85-104`), and `recvHook` still delivers one complete
logical request atomically (`Gasm/Targets/Windows/Win32API.lean` `recvHook`,
`Gasm/Effects/Trace.lean`'s `MonadNetwork` instance). Precedent for proceeding anyway exists in
this same tree: PA17 (`docs/tasks/PA17-spike3-spike4-domain-honesty.md`, landed at `b74295d`)
was itself sequenced `after: [PA7, PA8]`, neither of which had landed, and its own report states
plainly that full universalization "needs PA6's read-binder contract... neither of which has
landed" — it shipped an honest partial closure instead of waiting. This document follows the
same discipline: **the contract shape itself does not depend on PA5's trace representation or
N2's short-read model existing in the tree today** — it is a mathematical statement about what a
read's result domain must look like and how a continuation's proof must range over it. What
*does* depend on PA5/N2 is (a) wiring this shape into the live `VerifiedProgram`/trace machinery
(§4 below states the interface PA5 must satisfy; it cannot be implemented against PA5 code that
does not exist), and (b) making any *live* Windows/WASI contract's use of this shape
non-vacuous, since the model can currently only produce one point of the domain this contract
quantifies over (`MODEL_DEBT.md` §C1's own words: "a `∀ read-result` contract proven against a
model that can only produce maximal reads proves nothing about chunk-robustness"). Both (a) and
(b) are named explicitly as **not done** in §9; claiming otherwise would be exactly the
"universal in form but vacuous in substance" failure this design is written to avoid.

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

```lean
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
  `MODEL_DEBT.md` §C8), never by adding a second constructor to the bytes domain itself. Adding
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

## 4. Integration with PA5's causal trace (interface contract)

`docs/SYSTEM_EFFECTS.md` §6.4 requires that input events are first-class, causally-stamped
trace events and coalescing barriers — a contract that quantifies over a read's *result* but
forgets *that a read occurred, and where in the causal order* would silently reintroduce the
"ack for a read is not ack before a read" confusion §6.4 exists to close. Because PA5's
`canonicalizeTrace` and its causal-stamp representation do not exist yet, this section states
the **interface PA5 must satisfy** for this contract shape to attach to it, rather than
inventing a parallel representation (the exact trap PA6's own task file warns against).

`Gasm/Core/Types.lean:48` already carries the right primitive dormant in the tree:
`VectorClock` (`clock : ThreadId → Nat`, with `happensBefore`/`join`/`tick`) is named in
`MODEL_DEBT.md` §D as "the right hook" for causal position and is currently unused outside
`Gasm/Core/Callable.lean`/`State.lean`. The interface this document specifies:

- A read event's trace representation must be a pair `(event : Event, stamp : VectorClock)` (or
  whatever concrete wrapper PA5 settles on with equivalent information content) — **not** a bare
  `Event` in a `List Event`. `ReadBinderObligation`'s bound variable `bytes` is exactly the
  *payload* half of this pair; PA5 supplies the *position* half.
- The coalescing-barrier property (§6.4: outputs on either side of an input event never merge or
  commute across it) must be stated as a property of the canonical form PA5 produces, not
  re-derived per read site. This contract shape does not re-litigate barrier placement; it only
  requires that whatever canonical form PA5 produces preserves read events as distinguishable
  positions so that the `bytes` values `ReadBinderObligation` quantifies over remain attached to
  a specific causal slot, not merged away by the very congruence PA6 depends on to state
  chunk-robustness (§7) correctly. Concretely: `canonicalizeTrace` must not fold two consecutive
  reads' payloads together the way it is licensed to fold two consecutive same-stream writes —
  `docs/SYSTEM_EFFECTS.md` §6.1's own coalescing table already states this for `NetEvent.recv`/
  reads/`accept` ("never coalesced"), so no change to that table is needed; this section simply
  records that the read-binder contract's soundness is one more thing resting on that row.
- Once PA5 lands, a routine's read-continuation contract is a dependent pair: the `VectorClock`
  (or successor) position of the read event, plus a `ReadBinderObligation requested Post` proof
  keyed to that position's payload slot. This document does not attempt PA5's representation
  work; it names the exact two properties (distinguishable position, non-coalescing) any PA5
  implementation must have for this contract shape to compose with it soundly.

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
  (`docs/tasks/N8-spike4-stack-buffer-overflow.md`) is exactly the case where they are not**: a
  16-byte stack buffer at `RSP+0x40`, with `requested = 128` passed to `recv`
  (`Spikes/Spike4HttpServer/Windows/Program.lean:130-136`). Today this is invisible to
  `spike4_windows_*_trace_equivalence` for two independent reasons this document is careful to
  keep separate: (a) the *trace-equivalence* theorems are pointwise (one literal 37-byte request
  string), so they never even *ask* what happens for a longer request — this is what §7's
  chunk-robustness demonstration and PA17's finding are about; (b) even a hypothetical
  universalized version proven against **today's** `recvHook` would still not catch it, because
  `recvHook` always delivers its one queued request atomically with no destination-buffer
  faulting (`MODEL_DEBT.md` §B3: "the memory model has no faults... a proof of a Zlib routine
  cannot distinguish 'correct' from 'scribbles outside its buffer'"), so a memory-safety
  violation from an over-length write is not an event this model can even produce, let alone
  quantify over. That gap is N2's (short reads) and Law 11 migration's (PA4's) to close, not
  this document's.
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

Per `docs/adr/0015-read-as-universal-binder.md` and Law 9, three named evasion shapes must
become unrepresentable, not merely discouraged:

- **Hardcoded-output stubs.** A spec whose read-continuation is `Post bytes := (output =
  fixedConstant)` independent of `bytes` cannot be proven as `ReadBinderObligation requested
  Post` unless `fixedConstant` is trivially reachable for *every* `bytes` in the domain — which
  is false for any spec that is supposed to depend on its input (e.g. an echo/copy program).
  The quantifier does not merely make a stub *harder to write*; a stub spec fails
  `ReadBinderObligation`'s proof obligation outright the moment `Post` is instantiated at two
  `bytes` values that would need different constants.
- **Domain-shrinking via purpose-built input enums.** Spike5's `GzipOp | compress` /
  `GunzipOp | decompress` single-constructor pattern (`docs/adr/0015`) quantifies over a type
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
for chunk-robustness; it is the same theorem read twice, which is precisely the claim in `docs/
tasks/PA6-read-binder-contract.md`'s acceptance criteria that "chunking robustness is a
corollary, not a separate requirement." `continuation_invariant_to_chunking` restates this at
the level the task cares about most: if a continuation's postcondition `Post` has already been
established for the reconstruction obtained under *one* chunking, it holds automatically for
*every* other chunking of the same logical input — a program proven correct for one chunking is
provably equal, via this composition, to the same program under any other chunking, exactly as
`docs/tasks/PA6-read-binder-contract.md` asks this task to check rather than merely assert.

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
  (PA7's `VerifiedReactiveProgram`), independent of the **inner** per-read contract shape this
  document defines. Conflating the two would smuggle a liveness proof into what is supposed to
  be a statement about one read's result domain.
- No attempt to close any of the nine grandfathered Spike 3/4 allowlist entries PA17 flagged, or
  any other `scripts/gate_allowlist.txt` entry — `docs/tasks/PA6-read-binder-contract.md` is
  explicit that this is separate work for PA8/PA17, deliberately excluded from this task's scope
  so it does not balloon into "PA6 plus nine proofs."
- No implementation of PA5's `canonicalizeTrace` or N2's short-read model. §4 states the
  interface contract PA5 must satisfy; it is not PA5's implementation.

## 9. What remains

1. **PA5** must implement `canonicalizeTrace` satisfying §4's two properties (distinguishable
   read-event position, non-coalescing across reads) before any live `VerifiedProgram`-successor
   contract can attach a `VectorClock` position to a `ReadBinderObligation` instance.
2. **N2** must rebuild `readFileHook`/`recvHook` (and their WASI analogues, `MODEL_DEBT.md` §C8)
   so that the *model* can actually produce more than one point of the domain
   `ReadBinderObligation` quantifies over — otherwise a live contract stated in this shape is
   sound but vacuous, exactly the risk this document's §1 names.
3. **PA9** (`VerifiedProgram`-successor) is where a live routine/program contract first exposes
   a field of type `ReadBinderObligation requested Post` (or its PA5-integrated successor from
   §4) as a mandatory struct field, the way `VerifiedProgram.traceEquivalence` is mandatory
   today (`Gasm/Core/Verification.lean`) — this document supplies the shape that field's type
   must have; PA9 wires it into the struct.
4. **PA2's composition calculus** (not yet designed as of this writing — `docs/tasks/
   PA2-step-lemma-composition-design.md`'s `design` field is still empty) must supply the
   "sequential composition across an input-event coalescing barrier" rule `docs/
   tasks/PA6-read-binder-contract.md` asks this shape to be compatible with; §7's
   `continuation_invariant_to_chunking` is offered as a candidate building block for that rule
   (chaining a read's universal obligation into a following computation-then-write step), not a
   substitute for PA2's own design.
5. **PA4's capability migration** must land before §5's composed obligation (read-quantifier
   inside a Law 11 write-safety proof) can be stated against real `MemoryPerm` tokens in a live
   routine rather than the schematic form given in §5.
6. **PA17/PA8** (explicitly out of scope here, §8) can attempt the nine grandfathered Spike 3/4
   entries against this shape once PA5/N2 above land enough of the surrounding machinery for a
   live instantiation to be non-vacuous; §5's Spike 4 walkthrough is intended as their starting
   point.

This document's own deliverable — the contract shape itself, demonstrated as real,
zero-`sorry`, zero-axiom Lean declarations with the chunk-robustness property checked rather
than merely asserted — is complete. Items 1-6 above are the named remaining work, each already
tracked under its own task id.
