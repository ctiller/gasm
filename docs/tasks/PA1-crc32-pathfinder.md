---
id: PA1
title: crc32 pathfinder — contract → asm → kernel ∀-proof → composition sketch
status: designing
blocked_on: ""
after: [TC4]
related: []
bar: bar-2
track: proof-arch
priority: 9.6
priority_set: 2026-08-27T18:25:47Z
design: "docs/PATHFINDER_CRC32.md"
design_review: "needs-rework 2026-08-27"
date: 2026-08-27
---

# PA1: crc32 pathfinder — contract → asm → kernel ∀-proof → composition sketch

## Context

This is the single most important task on the board right now, despite sitting under a track
titled "critical path for everything below." It was **pulled forward** out of its natural
Phase-4 position (PLAN.md originally scheduled the pathfinder after step-lemma library design)
because of a self-audit finding recorded verbatim in PLAN.md's gaps register:

> **Pull the crc32 pathfinder FORWARD** (start when decoder lands, parallel to Phase 2 docs): the
> Phase 4 proof architecture is untested hypothesis until one routine goes
> contract→asm→kernel-proof→composition end-to-end; it will find what the design is missing
> faster than more design will.

Read that carefully: the entire modular-contracts-and-composition architecture described in
`docs/VISION.md` §4 (routine contracts + local proofs + composition rules, D2 in PLAN.md) is, at
the moment this task starts, **a hypothesis nobody has tested**. PA2 (step-lemma library design
doc) is explicitly sequenced *after* this task specifically so that its design doc is informed by
what actually breaks here, rather than guessing. Do not treat this as "just prove one theorem" —
treat it as a fire drill for the whole Phase-4/D2/D11 approach, and report friction honestly even
where the proof succeeds.

### Why crc32 specifically

`TASKS.md`'s own note explains the choice: "small, loop-heavy, dual-implemented → connection
theorem for free, no syscalls." Concretely:

- **No syscalls** means no `Environment`/`EnvironmentLoader` machinery, no `VerifiedProgram`
  trace-equivalence obligation (§5 of `docs/EQUIVALENCE_PROOFS.md`) — this task is scoped to a
  pure functional routine, which is exactly what keeps it tractable as a first end-to-end proof.
- **Loop-heavy** means the proof must handle the one thing Law 7 explicitly prohibits doing badly:
  a dynamically-bounded loop over the input buffer, proven by induction on buffer length rather
  than by a hardcoded jump table (Law 7's "Prohibited Proof Anti-Patterns" #1 — manual
  offset-to-index tables in proof files are rejected outright).
- **Dual-implemented** is the interesting part. The Lean spec (`Stdlib/Zlib/CRC32.lean`) computes
  CRC-32 via a 256-entry lookup table (`crc32Table`, built by `mkCrcTableEntry`, an 8-iteration
  per-bit loop applying the reversed IEEE 802.3 polynomial `0xEDB88320`); the assembly realization
  (`crc32SymbolicProgram` in `Stdlib/Zlib/Windows.lean`) computes the **same per-bit polynomial
  update inline, 8x unrolled, with no table at all** — each byte is XORed into EAX and then
  shifted-and-conditionally-XORed 8 times (see the `crc_sub_bit0`..`crc_sub_bit7` label chain).
  This is a genuine Law-12 connection-theorem shape: two encodings of the same fact (a
  precomputed table vs. the closed-form per-bit recurrence that generates each table entry), and
  the pathfinder proof is, at its core, exactly that connection theorem generalized across the
  whole buffer by induction. This previews the kind of proof PA1's sibling entry in PLAN.md's
  "zlib to infinity" candidate epic anticipates needing at scale (table-driven vs SIMD
  `PCLMULQDQ` CRC, eventually) — this task is the cheap, small-scale rehearsal of that exact proof
  shape, not a one-off.

### Scope discipline: same-file churn only

`TASKS.md` explicitly annotates this task "(same-file churn only)." That is a deliberate
constraint, not an oversight: this task must NOT migrate `crc32SymbolicProgram` onto the Core
capability machinery (`MemoryPermissions`/`BlockM`/obligations) — that migration is PA4's job,
scheduled later and on its own track, specifically so PA1's proof isn't entangled with a second
untested hypothesis (Law 11 adoption) at the same time. Keep the contract's memory-safety
obligation simple and explicit (a precondition capturing "the routine only reads `[rcx, rcx+rdx)`
and only writes EAX/R8/R9/R10/R11/flags") rather than reaching for capability tokens that don't
exist on this code path yet.

### What "contract" means here — the Three Split Theorems

`docs/EQUIVALENCE_PROOFS.md` §4 specifies that every verified routine exports three
**independent** theorems for three distinct consumers, using `memcpy` as the worked example
(§4.1–§4.3). This pathfinder should produce the same three for `crc32SymbolicProgram`, adapted to
a routine with no callees and no capabilities yet:

1. **Functional equivalence** (§4.1 pattern): for all input pointers/lengths satisfying the
   memory-readability precondition, running `crc32SymbolicProgram` to completion produces `EAX =
   Stdlib.Zlib.crc32 buf` where `buf` is exactly the `rdx`-byte window read from `[rcx, rcx+rdx)`
   in the initial machine state — universally quantified over the buffer contents and length
   (Law 9: no pinned buffer, no domain-shrinking enum standing in for `ByteArray`), discharged by
   **structural kernel-checked proof** (induction on remaining length), never by
   `native_decide`/`decide` (Law 10 — this is an infinite-domain claim over `ByteArray`/`Nat`, not
   an exhaustive finite one).
2. **Callability & ABI preservation** (§4.2 pattern): what the routine does to
   caller-saved/callee-saved registers and the stack — even without a full `AbiDiscipline`
   instance wired up yet, state explicitly which registers the routine clobbers (`RAX`, `R8`–`R11`,
   flags per the instruction sequence) vs. preserves, since this is exactly the fact PA4/PA9 will
   later need to compose this routine into a caller.
3. **Memory safety** (§4.3 pattern, simplified): the routine's memory footprint is read-only over
   `[rcx, rcx+rdx)` and touches no other memory — state this even though full `MemoryPerm`
   capability tokens (Law 11) are out of scope per the same-file-churn constraint above; a
   precise, explicit frame condition here is what PA4 will later upgrade into a real capability
   obligation, and getting the frame condition right now is most of that future work.

### The "composition sketch" deliverable

This is the part most likely to be shortchanged, and it is the part PA2 is waiting on. After the
proof lands, write a short (does not need to be long) note — inline in this file's eventual
`## Design` section, or as its own note if it grows — answering: what would it take to compose
this routine's contract into a caller's proof (e.g., a hypothetical gzip-header routine that
calls `crc32SymbolicProgram` and then appends bytes)? What did the step-by-step instruction proof
actually look like — is there a reusable per-instruction step lemma shape here (Law 9/D11: "DSLs
are the unit of proof leverage" — is the assembly DSL's step-lemma library test-flown correctly by
this proof, or did the proof have to route around missing infrastructure)? This sketch is PA2's
primary input; PA2 (step-lemma library + composition calculus design doc) is explicitly sequenced
`after: PA1 (learnings)` in `TASKS.md` for exactly this reason — do not treat the composition
sketch as optional polish.

### BAR 2 triggers directly after this task — but its scope is the whole codebase

`TASKS.md`: "**BAR 2 — after PA1: fresh-agent review of the proof architecture against the
pathfinder evidence.**" Read that trigger correctly: PA1 landing is what *schedules* BAR 2, but a
BAR is never a scoped review of the triggering work alone. Per
`docs/adr/0010-bar-triggered-deep-re-reviews.md` (the ratified correction to an earlier, narrower
framing), every BAR is a **full deep
re-review of the entire codebase from scratch** by fresh Opus agents — the same shape as the
original multi-agent deep review that started the repair epic — blinded to prior review
conclusions (a BAR reviewer may read `PLAN.md`/`TASKS.md`/the ledgers as the *claimed* state, in
order to check it against reality, but not as a substitute for looking). Each BAR reports: (a)
drift between docs/laws/ADRs and code reality anywhere in the tree, not just in recently-touched
files; (b) whether recently-merged work's claimed outcomes hold in the merged tree; (c) new
findings ranked, across the *whole* codebase, not the recent diff; (d) a tracking verdict against
the plan (on/off course); (e) the convergence metric — what fraction of findings are right-theorem
questions vs. mechanical catches (the north-star ratio from `docs/VISION.md` §2).

The reason PA1 is still the right trigger even though BAR 2's scope is global: a scoped review of
*this* task's diff is exactly what an adversarial reviewer already does before merge (per D6) —
that catches what's local. A BAR exists to catch what a scoped review structurally cannot:
unknown-unknowns, cross-branch interactions, and rot in corners of the tree nobody has touched
recently. PA1 landing is a meaningful milestone to hang a full re-review on (the whole D2/D11
modular-contracts hypothesis has now been tested once), but the reviewer dispatched for BAR 2 must
not confine itself to the proof-architecture files — it re-derives the whole codebase's standing
from scratch. Whatever this task's completion report says — including any friction, workarounds,
or places the §4 theorem template didn't fit cleanly — is important input for that reviewer, not
because it scopes their search, but because a reviewer re-deriving everything from scratch still
benefits from knowing what the most recent claimed changes were. Under-reporting friction here
still weakens the review, just not by narrowing what gets checked.

## Deliverables & acceptance criteria

- A stated contract for `crc32SymbolicProgram` following the three-split-theorem shape above
  (functional equivalence, ABI/callability, memory safety), each independently statable even
  though this routine has no callees.
- All three theorems proven by **kernel-checked structural proof** (induction over buffer length
  for the functional-equivalence theorem — this is the load-bearing one). `native_decide`/`decide`
  is acceptable only for genuinely exhaustive finite sub-obligations (e.g. an 8-iteration bit-loop
  fact fully instantiated at all 256 byte values, matching `crc32Table`'s own construction) —
  never as a stand-in for the buffer-length induction itself (Law 10).
- No pinned/hardcoded buffer anywhere in the proof or its supporting lemmas (Law 9) — the moment a
  concrete `ByteArray` literal appears in a hypothesis rather than a universally bound variable,
  the theorem has silently become a regression test and must be renamed `*_inst` and moved out of
  the proof-architecture path (Law 10's `*_inst` convention).
- The connection between `crc32SymbolicProgram`'s inline per-bit unrolled update and
  `Stdlib.Zlib.crc32`'s table-driven spec made explicit somewhere in the proof (even if only as a
  lemma reusing `mkCrcTableEntry`'s own loop shape) — this is the Law-12 connection-theorem
  content the task was chosen to exercise.
- A written composition sketch (see above) — what a caller-composition proof would need, and
  whether anything in this proof had to route around missing per-instruction step-lemma
  infrastructure. This is required input for PA2, not optional.
- Completion report must state explicitly, for BAR 2's benefit: what the §4 template got right,
  what it had to bend to fit, and any place a per-instruction step lemma had to be
  hand-derived from scratch (i.e., candidate content for PA2/PA3's lemma library).
- Per this project's evidence convention: since this is proof work (not a fuzzer/gate), the
  acceptance evidence is the kernel-checked proof itself (zero `sorry`, passes
  `lake exe check_gates_axioms` — confirms no unauthorized axiom, including no accidental
  `native_decide` dependency on the infinite-domain theorem) plus `scripts/check_refs.py` citing
  this work back to `docs/STDLIB_ZLIB.md#22-crc-32-iso-3309-ieee-8023` and to
  `docs/EQUIVALENCE_PROOFS.md#4-the-three-independent-split-theorems`.

## Pointers

- `Stdlib/Zlib/CRC32.lean:7` (`crc32Polynomial`), `:11-18` (`mkCrcTableEntry`, the per-bit loop
  the asm inlines), `:22-27` (`crc32Table`), `:31-41` (`updateCrc32`, the running-CRC fold — the
  induction target), `:45-46` (`crc32`, the top-level spec function the contract's postcondition
  refers to).
- `Stdlib/Zlib/Windows.lean:36-119` (`crc32SymbolicProgram` — verified by grep at time of writing:
  `mov_r32 .eax 0xFFFFFFFF` init, `xor_r32 .r8d .r8d` zeroes the byte index, `label
  "crc32_calc_loop"` at line 40 through `label "crc32_calc_done"` at line 119, the 8x
  `crc_sub_bit0`..`crc_sub_bit7` unrolled conditional-XOR chain starting line 52). Confirm current
  line numbers by grep before writing the proof file, since this file has had recent unrelated
  commits (dynamic Huffman, LZ77 compression landed same day per git log).
- `docs/EQUIVALENCE_PROOFS.md` §4 (`4.1`–`4.3`, lines ~87–148) — the exact three-theorem template
  to instantiate; §5 (`VerifiedProgram`, lines ~152–172) for contrast — this task does NOT need
  `VerifiedProgram`/`EnvironmentLoader` since there are no syscalls, and should say so explicitly
  rather than silently omitting the environment quantifier.
- `docs/REVIEW.md` Law 7 (Target Separation & Equivalence Proof Purity — the anti-jump-table,
  anti-hardcoded-layout rules that a loop-heavy proof is most tempted to violate), Law 9 (universal
  quantification — the buffer/length must be bound variables, never pinned), Law 10 (kernel-checked
  vs `native_decide` boundary), Law 12 (connection theorems — the table/closed-form duplication
  this routine exhibits).
- `docs/VISION.md` §4 ("Tractability: Modular Contracts, Composed Proofs") and §4's DSL paragraph
  ("DSLs are the unit of proof leverage") — the architecture this task is empirically testing.
- PLAN.md, Decisions D2 and D11, and the "Findings ledger" / gaps-register entry quoted above
  (the pull-forward rationale) — cite both in the completion report.
- `docs/adr/0003-universal-equivalence-via-modular-decomposition.md` (D2) records the modular-
  contracts architecture this pathfinder tests; the pull-forward sequencing itself is recorded as
  a self-audit finding in PLAN.md's gaps register (quoted above) rather than as its own numbered
  ADR — cite both together in the completion report.

## Notes

- 2026-08-27: priority 9.6 — explicitly pulled forward out of its natural Phase-4 slot per PLAN.md's gaps register: 'the single most important task on the board right now' — it tests the entire modular-contracts hypothesis (D2/D11) that everything in PA2-PA9 and F4/F6 assumes.

_(none yet — first entries append here as work begins; consolidate into a `## Design` section
before implementation starts per the task-lifecycle convention in `TASKS.md`. Given this task's
role as an architecture test, expect its Notes to be unusually information-dense — capture every
place the §4 template needed bending, verbatim, for BAR 2 and for PA2's design doc.)_
