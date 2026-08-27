---
id: PA4
title: capability adoption (Law 11) — Core machinery as mandatory authoring surface
status: ready
blocked_on: ""
after: [PA2]
related: []
bar: ""
track: proof-arch
priority: 7.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# PA4: capability adoption (Law 11) — Core machinery as mandatory authoring surface

## Context

This task executes Decision D3 in PLAN.md:

> **D3 — Memory safety**: adopt the dormant Core capability machinery
> (`MemoryPermissions`/`BlockM`/obligations) as the authoring surface; memory access without a
> capability proof must fail to assemble (Law 11).

`docs/REVIEW.md` Law 11 states the mandate this task is answerable to, in full:

> Every instruction that reads or writes memory MUST carry proof of a valid, in-scope capability
> (`MemoryPerm`) covering the accessed range. Program construction MUST fail — the artifact must be
> unbuildable — when that proof is absent... Memory safety is foundational, not advisory: it is
> enforced at authoring/assembly time by construction, never audited after the fact. The Core
> capability machinery is the authoring surface: `MemoryPermissions`, permission tokens, obligation
> ledgers, and the `BlockM` typestate monad are the mandated path for memory-touching programs.
> Authoring paths that bypass them... are prohibited in migrated modules; unmigrated modules are
> tracked as critical backlog, and new programs MUST NOT be authored on the bypass path.

### Why this task exists now, not academically

This machinery is not new — it is dormant. PLAN.md's findings ledger records the exact state of
disuse this task is meant to end:

> Dead Core machinery: ComposedState/BlockM/CpuTerminator/Callable/AbiDiscipline/obligations/
> permissions have zero call sites → being resurrected via D3/Phase 4.

Zero call sites is not a style problem — it is a live soundness gap. `MODEL_DEBT.md` §B3 states,
in its own words, exactly why this matters *now* and not as future-proofing:

> The memory model has no faults, no permissions, no canonicality, no alignment. `memory : Address
> → Byte` is total and everywhere-defined; `write8`/`write64` succeed at any address. There is no
> page table, no unmapped region, no W^X, no canonical-address check, no `#GP`/`#PF`... Consequence:
> a proof of a Zlib routine cannot distinguish "correct" from "scribbles outside its buffer" —
> precisely the risk PLAN.md flags for `Zlib/Windows.lean`'s hand-offset 4096-byte scratch. **This
> is what Law 11 capabilities are for; until they bind, the memory model actively hides the bug
> class.**

That last sentence is the operative one: the underlying x86-64 memory model in
`Gasm/Targets/X86_64/Registers.lean` cannot itself distinguish an in-bounds write from an
out-of-bounds one (every address is writable), so nothing short of a capability-token discipline
enforced at proof-construction time closes this gap — the memory model will not close it for you.

### The concrete risk this migration is aimed at

`Stdlib/Zlib/Windows.lean` is named explicitly by PLAN.md's findings ledger as the sharpest instance
of this gap:

> `Zlib/Windows.lean`: 4096-byte stack scratch with hand-computed offsets (+8-for-push corrections)
> in dynamic-Huffman path — most fragile code in repo; only guarded by external Python fuzzer. Fixed
> 8MB/8MB VirtualAlloc split, no bounds checks (→ Law 11).

Grep-confirmed at time of writing: `Stdlib/Zlib/Windows.lean:903-904` allocates 4096 bytes of stack
scratch for the dynamic-Huffman table-building path (`sub_r64_imm32 .rsp 4096`) and releases it at
`:2218,2223` (`add_r64_imm32 .rsp 4096`); the fixed 8MB input-buffer / 16MB `VirtualAlloc` split
appears at `:2239-2312`. This file has had active recent development — the git log shows dynamic
Huffman decompression and sliding-window LZ77 compression landing the same day this task file was
written — so the scratch-space arithmetic is not stable legacy code being slowly retired; it is
live, growing surface with zero mechanical bounds enforcement today.

### Ordering: this is why Zlib/Windows.lean goes last, not first

PLAN.md's Phase 2 bullet for this task states the migration order explicitly:

> **Capability adoption/migration plan** (Law 11): how SymbolicInstr authoring path acquires
> capability obligations; migration order (new code first, then Stdlib/Zlib/Windows.lean
> last/biggest).

This ordering is deliberate, not a convenience: `Zlib/Windows.lean` is simultaneously the biggest
migration target (most memory-touching instructions) and the file where the risk is sharpest (the
hand-offset scratch space above). Migrating smaller/newer code first lets the migration plan itself
get validated on lower-stakes surface before it is applied to the file that most needs it — the
same "validate before building on it" discipline `docs/VISION.md` §3.3 states for model growth
generally. Do not front-load `Zlib/Windows.lean` to "get the hard part over with"; the ordering is
the point.

### Relationship to PA1 and PA2

PA1's pathfinder (`docs/tasks/PA1-crc32-pathfinder.md`) was deliberately scoped "same-file churn
only" and explicitly excluded from migrating `crc32SymbolicProgram` onto this capability machinery,
specifically so PA1's proof would not be entangled with a second untested hypothesis (this
migration) at the same time. That means PA1 does *not* pre-validate this task's approach — PA4 is
its own first real exercise of the capability-adoption plan, though PA1's simplified "precondition
capturing which memory ranges are read/written" framing (its Theorem-3 memory-safety statement) is
exactly the frame condition this task is meant to upgrade into a real `MemoryPerm` capability
obligation; PA1's task file says so directly: "a precise, explicit frame condition here is what PA4
will later upgrade into a real capability obligation, and getting the frame condition right now is
most of that future work." Read PA1's Theorem 3 before designing this migration's frame-condition
shape. This task is sequenced `after: PA2` (not PA1) because its migration plan needs PA2's DSL
framing of capability tokens as composition-rule frame conditions as a design input — but PA1's
concrete memory-safety statement is still the most relevant existing precedent to consult.

## Deliverables & acceptance criteria

- A migration plan (Law-5-class design content, consolidated from Notes into a real design doc
  before implementation per the task-lifecycle convention) covering: how the `SymbolicInstr`
  authoring path acquires capability obligations (what changes about how a routine's assembly is
  written so that every memory-touching instruction carries a `MemoryPerm` proof obligation); the
  concrete migration order (new/small code first, `Stdlib/Zlib/Windows.lean` last and biggest, per
  PLAN.md's explicit ordering above); and how existing dead Core types
  (`ComposedState`/`BlockM`/`CpuTerminator`/`Callable`/`AbiDiscipline`/obligations/permissions —
  currently zero call sites) become live, actually-invoked machinery rather than acquiring their
  first call sites as decoration (Law 8 — no inert abstractions; a typeclass gains a call site only
  by being semantically invoked in the operational execution path).
- Fresh-agent design review of the migration plan before any module's migration implementation is
  dispatched — do not waive review on this track; a wrong migration order or wrong frame-condition
  shape is expensive to unwind once several modules depend on it.
- Migration implementation, in the stated order, for at least the "new code first" tranche; track
  `Stdlib/Zlib/Windows.lean` as the final, largest tranche of this task (or a tracked follow-up, if
  this task's scope is split by module — state explicitly whichever choice is made).
- Every migrated module: memory-touching instructions carry `MemoryPerm` capability proof
  obligations such that a program touching memory without a valid, in-scope capability fails to
  assemble (Law 11's "fail to assemble" bar, not a runtime check or an audit pass).
- Zero `sorry`, zero unauthorized axioms in migrated modules (`lake build` + `lake exe
  check_gates_axioms` clean); `native_decide`/`decide` is never a substitute for the
  infinite-domain capability-validity proofs this migration requires (Law 10) — a capability's
  bounds are typically over `Nat` ranges and must be proven structurally, not by exhaustive
  enumeration.
- `scripts/check_refs.py` clean for all new/migrated declarations, citing back to this task's
  migration-plan design doc and to `docs/REVIEW.md` Law 11.
- Completion report states explicitly, for `Zlib/Windows.lean`'s eventual migration: whether the
  4096-byte dynamic-Huffman scratch space and the 8MB/16MB `VirtualAlloc` split can be expressed as
  capability-bounded regions without changing the file's external behavior, and what (if anything)
  in the migration plan needed revision once applied to a file this size — this is the single most
  informative data point for whether the migration plan as designed actually scales to the file it
  was ultimately aimed at.

## Pointers

- `docs/REVIEW.md` Law 11 (quoted above, in full) — the governing law;
  `docs/adr/0004-adopt-core-capability-machinery-for-memory-safety.md` (D3's ratified ADR).
- `MODEL_DEBT.md` §B3 (quoted above, in full) — why this matters now; §C4 (`VirtualAlloc` modeled
  as a constant — relevant since `Zlib/Windows.lean`'s allocation calls rest on this) and the
  TOP-10 table entry naming `Environment`/loader inventions.
- `Stdlib/Zlib/Windows.lean:903-904,2218,2223` (4096-byte dynamic-Huffman scratch push/pop —
  grep-confirm current line numbers before starting, this file changes often), `:2239-2312`
  (`VirtualAlloc`/`ReadFile` sequence establishing the 8MB/16MB split).
- `docs/tasks/PA1-crc32-pathfinder.md` — its Theorem 3 (memory-safety frame condition) is the
  precedent this migration upgrades into real capability obligations; its "same-file churn only"
  scope note explains why PA1 itself is not already migrated.
- PA2's design doc (path TBD — see `docs/tasks/PA2-step-lemma-composition-design.md`) — the DSL
  framing of capability tokens as composition-rule frame conditions this migration plan should be
  consistent with.
- `Gasm/Core/Permissions.lean:50` (`MemoryPermissions`), `Gasm/Core/Obligations.lean:8,14,27,52`
  (`IsObligation`, `ObligationToken`, `ArenaPageToken`, `ObligationLedger`),
  `Gasm/Core/BlockM.lean:9` (`BlockM`), `Gasm/Core/Callable.lean:16` (`Callable`),
  `Gasm/Core/State.lean:11` (`ComposedState`) — the dormant machinery this task must give real call
  sites to.
- PLAN.md Phase 2 "Capability adoption/migration plan" bullet and the findings-ledger "Dead Core
  machinery" entry (both quoted above).
- `docs/VISION.md` §4's closing sentence ("Memory safety and proof modularity are the same
  feature...") — the architectural reason this task's frame-condition design matters beyond memory
  safety in isolation.

## Notes

- 2026-08-27: priority 7.0 — capability adoption (Law 11) unblocks PA9 and G6; necessary before any routine's memory-safety obligation becomes a real capability token.

_(none yet — first entries append here as work begins; this is Law-5-class proof-architecture
work — consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch; do not waive review on this track.)_
