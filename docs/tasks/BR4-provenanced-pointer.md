---
id: BR4
title: "Provenanced pointer type: region identity, address-free Ptr, and the creation audit"
status: ready
blocked_on: ""
after: [MH1]
related: [BR1, MH3, PA4, BR5]
bar: ""
track: proof-arch
priority: 7.3
priority_set: 2026-08-28T00:00:00Z
design: "docs/BORROW_MODEL.md"
design_review: ""
date: 2026-08-28
---

# BR4: Provenanced pointer type — region identity, address-free `Ptr`, creation audit

## Context

Implements `docs/BORROW_MODEL.md` §2. The owner's premise: *"my assumption is that we'd have a
typed/provenanced pointer type that's required to read to/from at all, correct?"*

This is the task that moves the aliasing obligation from "do these two 64-bit numbers alias"
(undecidable) to "are these two declared regions disjoint" (a closed, declared population).
An earlier revision of the design called the aliasing half unreachable; §2.1 records why that
was an error about the wrong layer — emitted bytes have no provenance, but the Lean term that
produced them can.

**The design decision that must not be quietly dropped**: `Ptr` carries **no address field**.
It is a region tag plus an offset term; the concrete address is computed at lowering from the
frame's anchor register. A pointer type with a `UInt64` inside is one careless helper away from
reintroducing exactly the hole it exists to close.

## Deliverables & acceptance criteria

- `RegionId` (generative identity + length), `Ofs` (literal or register offset), and
  `Ptr (r : RegionId)` with no address field, per `docs/BORROW_MODEL.md` §2.2. Lowering to
  MH1's `MemRef` on x86-64, leaving the landed hook unchanged.
- **Region identity must be generative, not address-derived** (`docs/BORROW_MODEL.md` §7.5): a
  block freed and reallocated at the same address must not produce a region equal to the stale
  one, or a duplicated stale pointer type-checks against the new grant. This is the same defect
  as SmolAlloc's address-keyed `mkFreeObligation` (`Stdlib/SmolAlloc/Spec.lean:56-58`), seen
  from the pointer side.
- Unchecked, provenance-preserving offsetting; the bound obligation attached at **dereference**,
  not at pointer formation — preserving `docs/MEMORY_HOOK.md` §2 boundary decision 1 (address
  computation is free; `LEA` forms out-of-bounds addresses legally).
- **The creation audit, and it is the load-bearing deliverable.** The standard is the one the
  `X86_64Memory` seal resolution established (`Gasm/Targets/X86_64/MemoryCell.lean:52-71`): not
  "unrepresentable" but "cannot be reached without going through a named, audited operation".
  The predicate to enforce: *no declaration produces a `RegionId` or `Ptr` without a `RegionId`
  among its arguments*. A sibling of `Gasm/Targets/X86_64/MemoryFrameAudit.lean`'s seal audit.
  **Acceptance evidence (Law 13 negative control)**: adding `deriving Inhabited` to `Ptr` must
  fail the audit — that single line forges a pointer into every region, and this codebase
  derives `Inhabited` liberally, so it is the realistic regression. Demonstrated, then reverted.
- **Do not claim tier 1.** `docs/BORROW_MODEL.md` §2.3 records why tier-1 opacity here would be
  self-defeating, not merely expensive: `opaque` has no definitional unfolding, and the `decide`
  fast path depends on region lengths and index transitions reducing. Sealing them opaquely
  turns every obligation into an author proof. Tier 3 is the correct and only compatible tier.
- Re-run the twelve forging attacks of `docs/BORROW_MODEL.md` §2.3 against the real type, as a
  committed negative-control module rather than a scratch spike. The measured results there were
  obtained on a simplified stand-in; the assumption that a hand-checked seal behaves as reasoned
  is exactly what failed for `X86_64Memory`.

## Pointers

- `docs/BORROW_MODEL.md` §2 (the type, the attacks, the audit predicate, the retraction), §7.5
  (generative identity), §13 (why the address-free shape is more portable than `MemRef`).
- `Gasm/Targets/X86_64/MemoryCell.lean:52-71` — the seal resolution that sets the standard.
- `Gasm/Targets/X86_64/MemoryFrameAudit.lean` — the audit this one is a sibling of.
- `Gasm/Targets/X86_64/Memory.lean:49-52` — `MemRef`, the lowering target, and *not* a typed
  pointer: a public record anyone can build.
- `Gasm/Core/Permissions.lean` — `MemoryPerm`, `DisjointRanges`, `DisjointTokens`.
- `docs/REVIEW.md` Law 13 (preference tiers), Law 10 (why the fast path is rung 2).

## Notes

_(none yet)_
