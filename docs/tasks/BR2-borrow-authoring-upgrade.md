---
id: BR2
title: "Promote MH3's checked program from a fixed frame to a borrow index"
status: blocked
blocked_on: "BR1's Phase 0 measurement must pass its kill criterion, and MH3 must land first — this task changes one type constructor of MH3's surface and keeps the rest verbatim, so it cannot precede it"
after: [BR1, MH3]
related: [PA2, PA4, MH1, N8]
bar: ""
track: proof-arch
priority: 7.0
priority_set: 2026-08-28T00:00:00Z
design: "docs/BORROW_MODEL.md"
design_review: ""
date: 2026-08-28
---

# BR2: Promote MH3's checked program from a fixed frame to a borrow index

## Context

Implements `docs/BORROW_MODEL.md` §6. MH3 builds the capability authoring surface with a
frame fixed for the whole routine — the entry-anchored, non-flow-sensitive line ADR-0040
Q1 accepted, with flow-sensitive typestate explicitly deferred to PA2/PA3
(`docs/MEMORY_HOOK.md` §4.3). This task is that deferral arriving, under the owner's
stated demand (`docs/BORROW_MODEL.md` §10.1).

**The finding this task exists to act on**: MH3's checked-program type and the borrow
monad are the same artifact. A list of checked instructions sharing one frame is exactly
the index-preserving special case of an indexed monad whose index is that frame. Every
other piece of MH3's surface — the region and frame types, the per-access obligation, its
decidable literal case and that case's soundness theorem, the auto-param, erasure, the
granted-footprint definition, the `MemSafe` statement shape, the bypass ledger and its
gate — carries over unchanged. Treating the two as separate surfaces would be a Law 12
unlinked twin; rebuilding MH3 as an indexed monad from scratch would discard four working
pieces to change one.

## Deliverables & acceptance criteria

- The checked-program type promoted from "list of instructions under a fixed frame" to the
  indexed form, with the old type recovered as the index-preserving case. **Acceptance
  bar**: every MH3 artifact that does not mention the program type compiles unchanged —
  measured, not asserted, by building MH3's landed pathfinder before and after.
- Lend, reclaim and donate as authoring operations on the promoted type, so a routine that
  hands out a read and takes it back is expressible and its post-index reflects it
  (`docs/BORROW_MODEL.md` §2.3).
- Loan discharge forced at the routine contract: a routine declaring that it returns what
  it was given must not elaborate with an outstanding loan. **Acceptance evidence
  (Law 13)**: an omitted-discharge mutation must fail to elaborate, with an error naming
  the region and its loan count (BR1's error-quality deliverable is a prerequisite for
  this bar being meetable).
- The share-admission table updated for the `Locked` re-reading, **conditional on the
  owner's Q2 ruling** (`docs/BORROW_MODEL.md` §2.2, §13 Q2): MH3's mapping admits both
  loads and stores for `Locked` identically to `Exclusive`, which is right for authority
  and silent about the atomicity obligation. If Q2 is accepted, a `Locked` region's
  accesses additionally owe an atomicity obligation. If Q2 is declined, record that and
  leave the table as MH3 built it.
- `MemSafe` re-proven over the indexed form for MH3's pathfinder routine — the shape is
  unchanged (`docs/MEMORY_HOOK.md` §4.4), only the program type it quantifies over moves.
- The aliasing gap restated where an author will read it, not only in the design: the
  index tracks region identifiers, and two regions may denote the same bytes at runtime
  (`docs/BORROW_MODEL.md` §11 item 1). This is the one place the design is strictly weaker
  than Rust, which gets disjointness free from provenance.

## Pointers

- `docs/BORROW_MODEL.md` §6 (the subsumption finding and the recommended sequencing), §2.3
  (discharge), §11 (limits), §13 Q1/Q2 (rulings this task depends on).
- `docs/tasks/MH3-capability-authoring-surface.md` — the surface being promoted.
- `docs/MEMORY_HOOK.md` §4.3 (the deferral this closes), §4.4 (`MemSafe`), §4.5 (erasure
  and the bypass ledger, both unchanged by this task).
- `docs/adr/0040-memory-hook-approved.md` — Q1's accepted bounded line and its stated
  upgrade path.
- `docs/tasks/PA2-step-lemma-composition-design.md`, `docs/tasks/PA4-capability-adoption.md`.

## Notes

_(none yet)_
