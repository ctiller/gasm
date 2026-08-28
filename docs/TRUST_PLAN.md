# Trust Plan — retiring the 78

**Status**: proposed, pending independent review and owner ratification. No step below is
started unless marked DISPATCHED.

The goal is `scripts/gate_allowlist.txt` at zero. This document is the schedulable step
list, refilled whenever it drops below 15 open steps.

## The actual composition (measured 2026-08-28, `main` at `75cfe3e`)

78 entries: 34 `grandfathered`, 44 `axiom-only`, 0 `finite-forall`.

**Corrected 2026-08-28 after independent review** — the first version of this table undercounted
Spike 3 by 2 and Spike 2 by 5, and its `axiom-only` column summed to 37 rather than 44. These
counts are re-measured directly from `scripts/gate_allowlist.txt` and sum correctly.

| area | grandfathered | axiom-only | total |
|---|---|---|---|
| `Spikes/Spike4HttpServer/` | 9 | 12 | 21 |
| `Spikes/Spike3SortLines/` | 5 | 13 | 18 |
| `Spikes/Spike5Gzip/` | 7 | 11 | 18 |
| `Spikes/Spike2Fibonacci/` | 3 | 8 | 11 |
| `Stdlib/Zlib/Equivalence.lean` | 8 | 0 | 8 |
| `Stdlib/Png/Equivalence.lean` | 2 | 0 | 2 |
| **total** | **34** | **44** | **78** |

The three largest spikes hold **57 of 78**, not the 68 first claimed.

**The structural fact that shapes the plan**: `axiom-only` entries are *propagation*. They
exist because a `native_decide` in an `Equivalence.lean` propagates into that spike's
`Emit.lean` / `Test.lean` / `main`. They are not independent debt — retiring a
`grandfathered` root should cascade to its dependents.

So the leverage is concentrated: **Spike 4's 9 roots gate ~21 entries; Spike 5's 7 gate ~18;
Spike 3's 5 gate ~16.** Those three spikes are 68 of 78.

## What is already established

- **Spike 4's 9 are NOT categorically blocked.** An earlier characterization in this plan said
  they were; commit `3341d92`'s agent measured it properly and disproved it. Reduction
  **succeeds** by plain `rfl` through fuel 29 — WSAStartup, socket, bind, listen, accept and
  the `recv` event, 3 of 5 events — and fails from fuel 30, the first instruction inspecting a
  `recvHook` product (`cmp rax, 0`). The blocker is `recvHook`
  (`Gasm/Targets/Windows/Win32API.lean:207`) routing through `@[extern]`
  `String.toUTF8`/`fromUTF8?`, which the kernel cannot unfold. The program is 130 instructions
  and the full canonical trace costs **59 steps** — not a scale problem. The remaining gap is
  roughly **two rewrite lemmas**: what `recvHook` leaves in `RAX`, and what `writeBytes` leaves
  at the buffer, both stated over an abstract `ByteArray`. Recorded in PA17's Notes.
- **Spike 5's 7 are categorically blocked**, not slow. Measured, not assumed:
  `decide`/`decide +kernel` fail with reduction-**stuck** errors, not timeouts.
  - Spike 5 **Wall 1**: `findLongestMatch` (`Stdlib/Zlib/Deflate.lean:944`) was a `while`/`return`
    loop elaborating through `Lean.Loop.forIn` → `repeatM` → an order-theoretic least fixpoint.
    **Converted to structural fuel recursion in `cdc98bf`** (241,480-pair differential, 0
    mismatches); `decide +kernel` on `(tokenize _).size > 0` was stuck before and succeeds now.
    `compressFixed` carries a **second, independent** `while` loop (`Deflate.lean` ~1325) that
    the conversion did not cover, so `compressFixed` and `gzipCompress` remain stuck.
  - Spike 5 **Wall 2**: `decompress` / `decodeHuffmanStream` are well-founded recursions;
    `Acc.rec` does not reduce, even on the empty token stream.
- **Three purpose-built, oracle-free modules exist on `main` with zero consumers**:
  `Spikes/Spike3SortLines/{TraceStepLemmas,InstructionStepLemmas,InterceptLemmas}.lean`. No
  spike has built an induction on any of them. They are the intended mechanism for this class
  of proof and their fitness is unproven — **C1 is now the step that establishes it**, since
  the correction to Track B removed the step that was going to.
- **`Spikes/Spike3SortLines/Windows/IATLemmas.lean` has NOT landed.** An earlier version of
  this plan said it had. It is stranded on unmerged branch `spike3-empty-trace-equivalence`
  (`8044ffb`), so **C1 has a hard dependency on F3**.
- **No `runWasiTrace` peeling lemmas exist.** C3 and two of Spike 2's three entries need a
  WASI trace-step lemma family that nothing in this plan currently provides. See G1.
- **Spike 2's Wasm program — and only the Wasm one — emits precomputed data.**
  `spike2WasmInstructions` (`_start`) calls only `fd_write` and `proc_exit`, never the
  verified `fibIter`; its output comes from `spike2DataSegments` computed at compile time.
  **The x86 claim was false and is retracted**: `spike2SymbolicProgram` computes Fibonacci at
  runtime in registers (recurrence at `Spikes/Spike2Fibonacci/Windows/Program.lean:176-179`,
  a real `div_r64` digit loop, empty `dataItems` in both linkers). So Track D's Law 8 premise
  applies to **1 of 3** entries, not 3 — the Windows and Linux entries are ordinary proof
  obligations. This error came from generalizing a Wasm measurement to all three targets
  without checking.
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
  for the Wasm interpreter. **DONE — `cdc98bf`. Retirement: 0.** Allowlist was 78 before and
  78 after. Recorded as zero rather than as progress: this is the shape the owner named as
  hedging, and A1 is only justified retrospectively by A3 consuming it.
- **A2** — Convert `decodeHuffmanStream` / `decompress` off well-founded recursion to fuel.
  **GATED — do not dispatch without a named consumer and an owner ruling.** It would
  re-convert functions that were *deliberately* made well-founded at `4ae2ab8`/`542041f`, and
  its own retirement target is zero. Same shape as A1. If Wall 2 must fall, the case has to be
  made on a specific theorem that needs it, not on tractability in the abstract.
- **A3** — Prove `compressFixed data = flushBitWriter (emitFixedBlock (tokenize data))`.
  This is a **Law 12 connection theorem**, not an incidental lemma: without it, no zlib
  theorem reaches Spike 5. Depends on A1.
- **A4** — PA16 L3: `findLongestMatch` validity (every emitted match is a real match, length
  within bounds). Load-bearing because `compressFixed` accepts any `matchLen ≥ 3` while
  `tokenizeAux` also requires `matchValid` — without L3 the roundtrip is genuinely false,
  not merely unproven. Half-proved already in scratch (`extend_loop_eq`, `extendRef_spec`).
- **A5** — `∀ data, gzipDecompress (gzipCompress data) = .ok data`. **Retires 4**, not the 2
  first claimed: the `Stdlib.Zlib` pair is the same proposition as the Spike 5 pair. E4's
  target drops to 6 correspondingly. Depends on A1, A3, A4.
- **A6** — The 5 Spike 5 trace equivalences by structural trace proof. **Depends on C1**, not
  on the old Track B step — the Track B correction removed the technique pathfinder, and C1 is
  now the step that establishes whether the trace-step lemma modules work. **Retires 5 + ~11
  propagated.**

### Track B — Spike 4 (gates ~21)

- **B1** — Fix HTTP method validation in all three lowerings. None validates the method;
  `FOO / HTTP/1.1` returns 200 where the model returns 400. A real defect with a checked
  witness (`witnessMethodNotValidatedDivergence`). **DISPATCHED.**
- **B2** — **The two rewrite lemmas.** Revised after `3341d92`'s measurement: reduction is not
  categorically blocked, it stops at fuel 30 on `recvHook`'s `@[extern]` opacity. What is
  needed is a lemma for what `recvHook` leaves in `RAX`, and one for what
  `X86_64Mem.writeBytes` leaves at the destination buffer, both stated over an abstract
  `ByteArray` so the kernel never has to unfold `String.toUTF8`/`fromUTF8?`. This is the
  highest-leverage step in the plan: **~2 lemmas gate 9 roots and ~12 propagated entries.**
- **B3** — Discharge the remaining trace steps (fuel 30 → 59) using B2. The full canonical
  trace is 59 steps over a 130-instruction program, so this is bounded and small — not the
  96-step hand-trace that Track C faces.
- **B4** — Retire the 9 Spike 4 trace equivalences. **Retires 9 + ~12 propagated.**
  Depends on B2–B3.
- **B5** — Correct the 9 entries' allowlist justification text. They currently cite the
  route-prefix bug **N8 already fixed** as the live falsity reason. It should cite
  `spike4GeneralClaimCounterexamples` and the three surviving `Stdlib.Http11.Error` classes:
  `unsupportedVersion`, `malformedRequestLine`, `invalidTarget`. Bookkeeping, but the ledger's
  justifications are load-bearing under ADR-0038 and currently say something false.

  **Status of the universal claim, measured by `3341d92`**: still false after B1, and for
  reasons enumerated by *class* rather than by witness. `parseRequestLine` can fail exactly
  four ways; the lowerings now implement one (`invalidMethod`). Three survive, each with a
  live checked counterexample. No theorem was narrowed to accommodate them.

### Track C — Spike 3 (gates ~16)

- **C1** — The 96-step empty-stdin chain for Spike 3 Windows. `IATLemmas.lean` landed
  (`alignUp_ge`, `foldl_append_size`, `loadMemory_excludes_sections`, four IAT self-reference
  facts, all axiom-clean); what remains is hand-tracing register/stack state through ~96
  instructions across two inlined subroutine calls. Mechanical but large. **Retires 2.**
- **C2** — Spike 3 Linux equivalent. **Retires 2.**
- **C3** — Spike 3 Wasm equivalent. **Retires 1 + ~11 propagated across the three.**

### Track D — Spike 2 (gates ~6) — a Law 8 question first

**Split after review — the Law 8 premise applies to Wasm only.**

- **D1 (Wasm only)** — Establish whether the emitted Spike 2 **Wasm** program should call its
  verified routine. It does not: `_start` calls `fd_write`/`proc_exit` and output comes from
  `spike2DataSegments` computed at compile time, so retiring that entry by proof would verify
  a routine the program never runs. **This is a design ruling, not a proof**, and it needs the
  owner. Two honest outcomes: change the program to call the verified routine, or document
  that Spike 2's Wasm trace equivalence is about data emission.
- **D2 (Windows + Linux)** — Ordinary proof obligations, **not** blocked on D1. Both programs
  compute Fibonacci at runtime in registers. **Retires 2 + propagated.** These were wrongly
  deferred behind an owner question in the first version of this plan.
- **D3** — Execute D1's outcome for Wasm. **Retires 1 + propagated** only if D1 connects them.

### Track E — Stdlib codecs (10)

- **E1** — L2v: canonical-code value accounting. **In flight** (`f6d72a1`, `4bcc3fc`).
- **E2** — L2h: Huffman table inversion for arbitrary transmitted lengths.
- **E3** — Dynamic L5: stream induction for the dynamic branch.
- **E4** — The 8 `Stdlib/Zlib/Equivalence.lean` codec entries. **Retires 8.** Depends on
  E1–E3 plus L2d (landed).
- **E5** — The 2 `Stdlib/Png/Equivalence.lean` entries. Status unestablished — first action
  is to determine whether they are blocked like Spikes 4/5 or simply unattempted.

### Track G — gaps found by review, previously uncovered

- **G1** — A **WASI trace-step lemma family**. No `runWasiTrace` peeling lemmas exist
  anywhere. C3 needs them, and so do two of Spike 2's three entries. Nothing else in this
  plan provides them, so without G1 those steps are unschedulable.
- **G2** — **Seven entries have no step covering them.** They are exactly the ones the
  original per-file table lost by undercounting Spike 3 (by 2) and Spike 2 (by 5). Identify
  them precisely against `scripts/gate_allowlist.txt` and assign each to a track. Until this
  is done, the plan's retirement targets do not sum to 78.

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

## Standing brief preamble (required in every trust dispatch)

Every agent working a step from this plan is given the following, before its own task:

> **Enumerate the target yourself, and validate the path.**
>
> Run `awk -F'::' '!/^#/ && NF>1 {print $4"  "$1"::"$2}' scripts/gate_allowlist.txt | sort`
> and read the result. That is the complete debt: every entry, its category, and the
> declaration it authorizes. Do not take this plan's per-file table as authoritative — an
> earlier version of it undercounted by seven entries.
>
> Then answer, before starting: **is the step you were assigned on the shortest path to
> zero?** Specifically —
>
> - Does retiring your target actually reduce the count, or does it produce infrastructure
>   that some later step must still consume? A step with a zero retirement target is only
>   legitimate if a *named* consumer follows it. A1 landed and retired nothing.
> - Does something else in the enumeration retire more for the same effort? Say so.
> - Is your step blocked on something the plan does not name? Three obstruction claims in
>   this plan were asserted without measurement and later disproved.
> - Does the propagation claim hold for *your* entries — that retiring a `grandfathered`
>   root cascades to its `axiom-only` dependents? It was verified at four points, not
>   universally.
>
> **"This is the wrong step, and here is the shorter one" is a first-class deliverable.**
> It outranks completing the step you were given. The coordinator decomposed this plan
> without holding every entry in view, and has been wrong about sequencing before.

The purpose is to put the whole target in front of whoever is closest to the work. The
coordinator's decomposition is a hypothesis; the agent holding the enumeration is better
placed to falsify it than the coordinator is.
