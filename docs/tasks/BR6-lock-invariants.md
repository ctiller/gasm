---
id: BR6
title: "Lock invariants: cross-region capability transfer licensed by an atomic word"
status: blocked
blocked_on: "All three supporting layers are absent: BR5 (the claim mechanism), MT1 (atomics — the tree has zero atomic forms), and MT2 (the memory model — docs/X86_MEMORY_MODEL.md states it has zero Lean). A lock is unsound if any one is missing, so this cannot start until all three land"
after: [BR5, MT1, MT2]
related: [BR3, MT4, MT5]
bar: ""
track: concurrency
priority: 6.4
priority_set: 2026-08-28T00:00:00Z
design: "docs/BORROW_MODEL.md"
design_review: ""
date: 2026-08-28
---

# BR6: Lock invariants — cross-region capability transfer

## Context

Implements `docs/BORROW_MODEL.md` §9. The owner's framing of what proof-carrying addresses are
for, verbatim: *"by proof carrying memory addresses i'm thinking of 'when this atomic word is 1
the thread that set it has the mutex'."*

The essential observation is that this is **not a claim about the lock word's own bytes**. The
word holds no data; its *value* licenses a claim about memory **elsewhere**. That makes it the
cross-region case of the same mechanism byte typing instantiates reflexively (§9.4): one ghost
claim indexed by a physical location, with byte typing saying "these bytes satisfy `T`" and a
lock invariant saying "the value here licenses ownership of that region". The indirection is the
real difference, and it carries one consequence byte typing does not — the claim must be
**transferable between threads**, which is why it needs atomicity and a memory model.

## Deliverables & acceptance criteria

- The lock-invariant type of `docs/BORROW_MODEL.md` §9.1: ghost state linking a lock region to a
  protected region, with `acquire` moving the protected region's capability *into* the acquiring
  context and `release` moving it out. The physical value and the logical permission move
  together and indivisibly.
- **The `Locked` extension of §9.2, pending the owner's Q2 ruling.** `docs/BORROW_MODEL.md` §3.2
  defines `Locked` as shared-mutable with safety discharged by atomicity; that describes the
  *word* correctly and says nothing about a *linked* region. This task supplies the missing half:
  `Locked` carries an associated ghost claim naming the region it guards, and the atomicity
  obligation on its accesses strengthens to "this access transfers the named capability". That is
  new vocabulary, not a re-reading, and it is the concrete payoff for keeping `Locked` as a third
  authority mode rather than folding it into `Exclusive`.
- **The three-way dependency must be discharged, not assumed** (§9.3). The borrow model supplies
  *what moves*; MT1's atomics supply *indivisibility* (without which two threads both observe 0
  and both acquire); MT2's memory model supplies *visibility* (without which the next acquirer
  does not see the previous holder's writes). Spike 8's spinlock unlocks with a **plain `MOV`**
  (`docs/SPIKES/SPIKE8_MULTITHREADING.md` §3), which is correct only under TSO. A deliverable
  that states the transfer without citing the ordering guarantee that makes the release sound is
  incomplete.
- **No premature claim.** Under one thread any ordering theorem is vacuous, and
  `docs/X86_MEMORY_MODEL.md` §8 explicitly rejects stating one now for exactly that reason. This
  task must not land a lock-shaped artifact that verifies nothing — the failure mode that
  document's own §1.1 catalogues as the fictional `x86_mov_store_is_release`.
- Architecture neutrality preserved obligationally (§13 finding 3). x86's release is a plain
  `MOV`; AArch64's needs `STLR` or an explicit barrier. **The permission transfer is identical
  across targets; only the discharge instruction differs.** The obligation — prior writes must be
  visible before the lock word's release is observable — stays constant, and each target's memory
  model discharges it its own way. Had `Locked` been defined as "one `.rmw` entry released by a
  plain store", ARM could not satisfy it; keep the obligational framing.
- Composition with `docs/BORROW_MODEL.md` §12's race theorem: a `Locked` region's accesses are
  excluded from the conflict relation by hypothesis, and this task is what discharges the
  hypothesis for locks specifically.

## Pointers

- `docs/BORROW_MODEL.md` §9 (the shape, the extension, the dependency), §3.2 (`Locked` as a third
  authority mode), §12 (the race theorem this composes with), §13 finding 3 (ARM neutrality),
  §17 Q2 (the ruling this depends on).
- `docs/X86_MEMORY_MODEL.md` §2.1 (TSO's guarantees, including the plain-store release), §2.3
  Decision 1 (`.rmw` as one indivisible descriptor entry — and §13's note that this is TSO-shaped
  and wrong for AArch64's `LDXR`/`STXR` pair), §8 (why no vacuous single-thread theorem).
- `docs/SPIKES/SPIKE8_MULTITHREADING.md` §3 (the XCHG spinlock this must make sound), §5.1.
- `docs/tasks/MT1-atomic-primitives.md`, `docs/tasks/MT2-multithreaded-machine-state.md`.

## Notes

_(none yet)_
