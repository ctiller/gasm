# Trust Plan — retiring the 78

**Status**: proposed, pending independent review and owner ratification. No step below is
started unless marked DISPATCHED.

The goal is `scripts/gate_allowlist.txt` at zero. This document is the schedulable step
list, refilled whenever it drops below 15 open steps.

## The actual composition (measured 2026-08-28, `main` at `75cfe3e`)

78 entries: 34 `grandfathered`, 44 `axiom-only`, 0 `finite-forall`.

| file | grandfathered | axiom-only |
|---|---|---|
| `Spikes/Spike4HttpServer/` | 9 | 12 |
| `Spikes/Spike5Gzip/` | 7 | 11 |
| `Stdlib/Zlib/Equivalence.lean` | 8 | 0 |
| `Spikes/Spike3SortLines/` | 5 | 11 |
| `Spikes/Spike2Fibonacci/` | 3 | 3 |
| `Stdlib/Png/Equivalence.lean` | 2 | 0 |

**The structural fact that shapes the plan**: `axiom-only` entries are *propagation*. They
exist because a `native_decide` in an `Equivalence.lean` propagates into that spike's
`Emit.lean` / `Test.lean` / `main`. They are not independent debt — retiring a
`grandfathered` root should cascade to its dependents.

So the leverage is concentrated: **Spike 4's 9 roots gate ~21 entries; Spike 5's 7 gate ~18;
Spike 3's 5 gate ~16.** Those three spikes are 68 of 78.

## What is already established

- **Spike 4's 9 and Spike 5's 7 are categorically blocked**, not slow. Measured, not assumed:
  `decide`/`decide +kernel` fail with reduction-**stuck** errors, not timeouts.
  - Spike 5 **Wall 1**: `findLongestMatch` (`Stdlib/Zlib/Deflate.lean:944`) is a `while`/`return`
    loop elaborating through `Lean.Loop.forIn` → `repeatM` → an order-theoretic least fixpoint.
    No equation lemmas, no kernel reduction. `tokenize`, `compressFixed`, `gzipCompress` all
    inherit it.
  - Spike 5 **Wall 2**: `decompress` / `decodeHuffmanStream` are well-founded recursions;
    `Acc.rec` does not reduce, even on the empty token stream.
- **`Spikes/Spike3SortLines/TraceStepLemmas.lean` is built, oracle-free, and has zero
  consumers.** No spike has built an induction on it. It is the intended mechanism for
  exactly this class of proof.
- **Spike 2's verified routine is off the emitted program's execution path.**
  `spike2WasmInstructions` (`_start`) calls only `fd_write` and `proc_exit`, never the
  verified `fibIter`; output comes from `spike2DataSegments` computed at compile time. The
  x86 side is the same shape. This is a Law 8 question, not a proof problem.
- **`gzipCompress` calls `compressFixed`, not `compress`.** Every zlib theorem landed so far
  is about `compress`/`emitFixedBlock`. `compressFixed` has exactly two occurrences tree-wide
  — its definition and that one call site — with nothing connecting them. A Law 12 unlinked
  twin sitting between the proofs and the spike that needs them.

## Steps

Each step names its retirement target so progress is measurable rather than narrative.
Every step's output is reviewed by an independent agent before it counts as done.

### Track A — remove the reduction walls (gates Spike 5's ~18)

- **A1** — Convert `findLongestMatch` to fuel-based structural recursion. Kills Wall 1.
  Precedented twice: `tokenizeAux`'s own comment states the rationale, and `ccba443` did it
  for the Wasm interpreter. Behaviour bit-identical, measured by `gzip_fuzzer` 108/108 with
  the 55/53 split preserved. **DISPATCHED.**
- **A2** — Convert `decodeHuffmanStream` / `decompress` off well-founded recursion to fuel.
  Kills Wall 2. Larger than A1 and touches the dynamic path; sequence after the in-flight
  L2v work lands to avoid collision.
- **A3** — Prove `compressFixed data = flushBitWriter (emitFixedBlock (tokenize data))`.
  This is a **Law 12 connection theorem**, not an incidental lemma: without it, no zlib
  theorem reaches Spike 5. Depends on A1.
- **A4** — PA16 L3: `findLongestMatch` validity (every emitted match is a real match, length
  within bounds). Load-bearing because `compressFixed` accepts any `matchLen ≥ 3` while
  `tokenizeAux` also requires `matchValid` — without L3 the roundtrip is genuinely false,
  not merely unproven. Half-proved already in scratch (`extend_loop_eq`, `extendRef_spec`).
- **A5** — `∀ data, gzipDecompress (gzipCompress data) = .ok data`. Retires
  `gzip_roundtrip_soundness_inst` and `gzip_idempotent_canonical_roundtrip_inst`
  (the latter free by PA16 §3/L12). **Retires 2.** Depends on A1–A4.
- **A6** — The 5 Spike 5 trace equivalences by structural trace proof. Depends on A2 + the
  Track B technique. **Retires 5 + ~11 propagated.**

### Track B — Spike 4 (gates ~21)

- **B1** — Fix HTTP method validation in all three lowerings. None validates the method;
  `FOO / HTTP/1.1` returns 200 where the model returns 400. A real defect with a checked
  witness (`witnessMethodNotValidatedDivergence`). **DISPATCHED.**
- **B2** — Build the **first induction on `TraceStepLemmas.lean`**. This is the pathfinder
  step for Tracks A6, B, and C — the module exists and nothing uses it, so its fitness for
  purpose is unproven. Scope deliberately to one target and one route.
- **B3** — Generic recv-buffer content proof via `recvHook` / `X86_64Mem.writeBytes`.
- **B4** — Symbolic case-split through the 3-way `cmp`/`je` route dispatch.
- **B5** — Connect the dispatch proof to `Stdlib.Http11` parser semantics.
- **B6** — Retire the 9 Spike 4 trace equivalences. **Retires 9 + ~12 propagated.**
  Depends on B1–B5. Note the general `∀ request` statement is *false* pre-B1; after B1,
  re-establish whether it becomes true or whether a stated `method = GET` scope limit is
  needed — with the excluded case separately witnessed either way.

### Track C — Spike 3 (gates ~16)

- **C1** — The 96-step empty-stdin chain for Spike 3 Windows. `IATLemmas.lean` landed
  (`alignUp_ge`, `foldl_append_size`, `loadMemory_excludes_sections`, four IAT self-reference
  facts, all axiom-clean); what remains is hand-tracing register/stack state through ~96
  instructions across two inlined subroutine calls. Mechanical but large. **Retires 2.**
- **C2** — Spike 3 Linux equivalent. **Retires 2.**
- **C3** — Spike 3 Wasm equivalent. **Retires 1 + ~11 propagated across the three.**

### Track D — Spike 2 (gates ~6) — a Law 8 question first

- **D1** — Establish whether the emitted Spike 2 programs *should* call their verified
  routines. Today they do not: output is precomputed data. Retiring these three entries by
  proof would verify a routine the program never runs. **This step is a design ruling, not
  a proof**, and it needs the owner. Two honest outcomes: change the programs to call the
  verified routine, or document that Spike 2 verifies a library routine and its trace
  equivalence is about data emission.
- **D2** — Execute D1's outcome. **Retires 3 + 3 propagated** only if D1 chooses to connect
  them; otherwise these entries are re-categorized, not retired, and the count does not move.

### Track E — Stdlib codecs (10)

- **E1** — L2v: canonical-code value accounting. **In flight** (`f6d72a1`, `4bcc3fc`).
- **E2** — L2h: Huffman table inversion for arbitrary transmitted lengths.
- **E3** — Dynamic L5: stream induction for the dynamic branch.
- **E4** — The 8 `Stdlib/Zlib/Equivalence.lean` codec entries. **Retires 8.** Depends on
  E1–E3 plus L2d (landed).
- **E5** — The 2 `Stdlib/Png/Equivalence.lean` entries. Status unestablished — first action
  is to determine whether they are blocked like Spikes 4/5 or simply unattempted.

### Track F — measurement and hygiene

- **F1** — Establish the blocked-vs-unattempted status of the 18 entries whose obstruction
  has never been measured (Spike 3's 5, Spike 2's 3, PNG's 2, and the 8 Zlib codec entries).
  Spikes 4 and 5 were measured; these were not. Cheap, and it decides whether Tracks C/D/E
  are proof work or research.
- **F2** — Reconcile the 78-vs-68 gap. `check_gates_axioms` reports 68 declarations depending
  on a non-standard axiom against 78 allowlist entries. Ten entries may be covering
  unloadable modules — or may be unnecessary. If unnecessary, the score currently
  *overstates* the debt and must be corrected downward honestly.
- **F3** — Land the stranded branches. Nine branches carry completed, gate-verified work that
  never reached `main`. **DISPATCHED.**
- **F4** — Citation adequacy review (Law 1's semantic half). **DISPATCHED.**

## Rules

1. **Every change is reviewed by an independent agent** — not the agent that made it.
2. **This plan is reviewed by an independent agent** before execution proceeds past the
   currently-dispatched steps.
3. **6–8 agents live at all times**, all on steps from this list.
4. **Refill this list whenever it drops below 15 open steps.**
5. No step counts as done until its retirement target is measured against
   `scripts/gate_allowlist.txt`, before and after.
6. **Do not spend effort on `bv_decide`.** ADR-0037/D28 ratified it as an accepted trust
   rung. It is settled, and work against it is not progress toward this goal.
