---
id: BR5
title: "Transmogrification: one borrow-with-transformation, the view ledger, and leak-freedom"
status: blocked
blocked_on: "BR4 — the view ledger and both transformations are stated over the pointer and region-identity types BR4 builds; there is nothing to lend a transformed view of until they exist"
after: [BR4]
related: [BR1, BR2, PA8, MH3, BR6]
bar: ""
track: proof-arch
priority: 7.0
priority_set: 2026-08-28T00:00:00Z
design: "docs/BORROW_MODEL.md"
design_review: ""
date: 2026-08-28
---

# BR5: Transmogrification — one mechanism, the view ledger, leak-freedom

## Context

Implements `docs/BORROW_MODEL.md` §7 and §8. The owner's framing, verbatim: *"i think the shape
of it is a special kind of borrow with an obligation that discharges the hold on the underlying
memory (and maybe forces a destruction operation)."*

That framing unifies what were designed as two operations. Sub-allocation transforms the
**region** (narrowing); byte typing transforms the **type** (refining); both suspend the parent's
hold over an extent and both are discharged by an inverse. **`malloc`/`free` and
construct/destruct are the same operation at different granularity**, and building them
separately would have produced a Law 12 twin plus a duplicated discharge rule.

**Law 5 demand exists in tree today**, not in prospect: `smol_malloc` carves from `VirtualAlloc`
blocks (`Stdlib/SmolAlloc/Spec.lean`). SmolAlloc is the first consumer, not an analogy.

## Deliverables & acceptance criteria

- The unified operation of `docs/BORROW_MODEL.md` §7.1: `View` (sub-extent or typed extent),
  `lendAs` suspending the parent's hold, and `discharge` as its inverse. One mechanism, two
  instantiations — a design in which sub-allocation and byte typing have separate discharge
  rules fails review.
- **The view ledger** (§7.2): a region's capability state generalized from a scalar to a list of
  outstanding views, with whole-region read loans as the degenerate case. Two independent routes
  force this — the unified operation, and SmolAlloc's two ledgers — and the convergence is the
  finding: the allocator's **named** obligation list *is* the view ledger, its `activeBorrows`
  counter is that ledger's cardinality, and `isSafeToRelease` (`Gasm/Core/Obligations.lean:52`)
  *is* the discharge check, written before the pattern was named.
- The disjointness component `MemoryPerm.split` does not currently return
  (`Gasm/Core/Permissions.lean:38-49`): the result type records both ranges, so `DisjointRanges`
  follows by `omega` from the indices plus the existing `h_wrap`, but no proof is among the
  returned components. Small and self-contained; §7.3's allocator partition needs it.
- The allocator transfer contract (§7.3) with its partition invariant, so that disjointness of
  outstanding regions holds *because the partition says so*, not because each call site proves
  it. `free` returns `Option`: returning a region that is not outstanding is a failure, not a
  no-op.
- **Destruction is not optional** (§7.5). If typed bytes could revert to raw while a typed view
  might still exist, the invariant is stale and the type is a lie. A transmogrify dischargeable
  without its destructor is unsound and must not be constructible.
- Use-after-free caught by the **index**, not by handle linearity (§7.5, §4): handles are
  ordinary Lean values and can be duplicated; after discharge the view is gone from the index, so
  a dereference through a duplicated handle fails the authority check. **Acceptance evidence
  (Law 13)**: a duplicated-handle use-after-discharge mutation must fail to elaborate.
- Asserted typing licensed by roundtrip theorems (§7.4). The roundtrip theorem *is* the
  introduction rule. Landed ∀-quantified instances to build on: `request_roundtrip` /
  `response_roundtrip` (`Stdlib/Http11/Roundtrip.lean:304,444`) and Zlib's fixed-branch
  roundtrips (`Stdlib/Zlib/Equivalence.lean:363,1875,1884`). **PNG is not yet an instance**: its
  roundtrips carry `_inst` (`Stdlib/Png/Equivalence.lean:367,380`), marking them ground-instance
  regression tests under Law 8/Law 10, not general theorems. Do not cite them as if they were.
- **No unchecked transmogrify constructor** (§7.6), pending the owner's Q5 ruling. Asserting a
  type of arbitrary bytes with no proof is the single hole through which all memory safety leaks,
  and it must not be ledgerable: the bypass ledger is for migration states with a defined end,
  and a permanent semantic assertion parked behind a counter is the confidence-manufacturing
  shape Law 8 and TC21 exist to catch. The environment's own assertions (the OS mapped this
  image) are a *separate*, named boundary axiom, not an instance of this operation.
- The leak-freedom statement of §8, **with its three conditions stated wherever the claim is
  stated**: the index-parametric loop rule (§8.1, superseding the too-weak index-preserving rule);
  transfer expressed as donation (§8.2); and **v1 forbidding pointer-valued fields** (§8.3),
  which is the largest limit — it excludes linked lists and most heap structures, pending the
  owner's Q6 ruling. Stated without those conditions the claim is an overclaim.

## Pointers

- `docs/BORROW_MODEL.md` §7 (the unified mechanism), §8 (leak-freedom and its conditions),
  §17 Q4/Q5/Q6 (rulings this task depends on), §18 (the `docs/MEMORY_PROVENANCE.md` overlap).
- `Stdlib/SmolAlloc/Spec.lean` — the first consumer. §7.2 records two observations against the
  current implementation (saturating decrement at `:149`; address-keyed obligation discharge at
  `:145-146`, where `eraseAllChecked` exists and is unused) that the indexed form makes
  unrepresentable. Confirm both with whoever owns SmolAlloc before treating them as defects.
- `docs/MEMORY_PROVENANCE.md` §1.2 — the existing allocation model this must be reconciled with,
  not duplicated.
- `Gasm/Targets/X86_64/MemoryFrame/Common.lean:56-59,73-78` — `ReadsWithin`'s `StoreAgreeOn`
  conjunct, which is what makes a typed view's invariant stable under a step.

## Notes

_(none yet)_
