---
id: PA10
title: PNG filter scanline invertibility — lift proven per-byte algebra to universal roundtrip
status: ready
blocked_on: ""
after: []
related: [PA1]
bar: ""
track: proof-arch
priority: 9.7
priority_set: 2026-08-28T02:00:00Z
design: "inline"
design_review: "waived-mechanical"
date: 2026-08-27
---

# PA10: PNG filter scanline invertibility — lift proven per-byte algebra to universal roundtrip

## Context

Sourced from the 2026-08-27 oracle-debt audit (`docs/ORACLE_DEBT.md`) of `scripts/gate_allowlist.txt`'s
37 `grandfathered` entries. Five of them are in `Stdlib/Png/Equivalence.lean`:
`filter_none_invertible_inst`, `filter_sub_invertible_inst`, `filter_up_invertible_inst`,
`filter_average_invertible_inst`, `filter_paeth_invertible_inst`. Each is a single `native_decide`
check that `unfilterScanline` inverts `filterScanline` on one fixed 8-byte raw scanline and one
fixed 8-byte prior scanline (`ByteArray.mk #[10,20,30,40,50,60,70,80]` / `#[1,2,3,4,5,6,7,8]`).

**The general fact is already proven, unused, in the same file.** `sub_filter_step_invertible`,
`up_filter_step_invertible`, `average_filter_step_invertible`, and `paeth_filter_step_invertible`
(`Stdlib/Png/Equivalence.lean:26-46`) each state the per-byte mod-256 algebraic invertibility
`∀ x a, x < 256 → a < 256 → ((x + 256 - a) % 256 + a) % 256 = x` (and the average/Paeth variants),
proven by `omega` — genuinely universal, zero oracle. `filterScanline`/`unfilterScanline` apply
exactly this per-byte step across an entire scanline byte-by-byte (each output byte depends only on
the corresponding raw byte, prior-scanline byte, and — for Sub/Average/Paeth — the immediately
preceding *already-unfiltered* byte in the same scanline). The five `_inst` theorems are pointwise
instantiations of a fact whose general form is sitting four lines above them, unconnected.

This is the shape Law 12 (connection theorems — no unlinked twins) exists to close, and the cheapest,
lowest-risk item in the entire oracle-debt ledger: no new model, no new proof technique, just
induction over the scanline byte array using the already-proven per-byte step lemma as the
induction's workhorse.

## Deliverables & acceptance criteria

- A general theorem per filter type: `∀ (raw prior : ByteArray) (bpp : Nat), (well-formedness
  precondition: raw.size = prior.size, elements < 256 — true by construction for `ByteArray`),
  unfilterScanline f (filterScanline f raw prior bpp) prior bpp = raw`, proven by induction on
  scanline position using `sub_filter_step_invertible`/`up_filter_step_invertible`/
  `average_filter_step_invertible`/`paeth_filter_step_invertible` as the per-position step —
  `filter_none` needs no algebra (identity), just the induction scaffold.
  covering all five filter types.
- `filter_none_invertible_inst`, `filter_sub_invertible_inst`, `filter_up_invertible_inst`,
  `filter_average_invertible_inst`, `filter_paeth_invertible_inst` deleted from
  `Stdlib/Png/Equivalence.lean` and from `scripts/gate_allowlist.txt`, superseded by the general
  theorems above (or kept as trivial one-line corollaries of the general theorem, if useful as
  regression anchors — but no longer citing `native_decide` themselves).
- Zero `sorry`, zero unauthorized axioms (`lake build` + `lake exe check_gates_axioms` clean);
  `native_decide`/`decide` does not appear anywhere in the new general theorems' proofs.
- `scripts/check_refs.py` clean; new theorems cite `docs/STDLIB_PNG.md#61-filter-roundtrip-invariance`.
- Completion report states the before/after `scripts/gate_allowlist.txt` line count for these five
  entries (37 → 32 grandfathered) and confirms `docs/ORACLE_DEBT.md`'s coverage matrix row for each
  is updated to reflect closure.

## Pointers

- `Stdlib/Png/Equivalence.lean:26-46` (the four already-proven per-byte step lemmas),
  `:48-86` (the five `_inst` theorems this task supersedes).
- `Stdlib/Png/Filter.lean` — `filterScanline`/`unfilterScanline`'s actual per-byte recursion
  (grep to confirm current structure; the induction this task writes must match it, not invent a
  parallel model).
- `docs/STDLIB_PNG.md#61-filter-roundtrip-invariance`.
- `docs/REVIEW.md` Law 9 (no pinned buffer — the general theorem must quantify over the scanline,
  not a fixed 8-byte literal), Law 12 (connection theorems).
- `docs/ORACLE_DEBT.md` — this task's originating audit; Part 2's coverage matrix, Part 3's gap list.

## Notes

- 2026-08-27: priority 9.7 — cheapest, lowest-risk closure in the oracle-debt plan: the general
  per-byte algebra is already proven and unused four lines above the pointwise checks it should
  replace. No prerequisites; start immediately.
