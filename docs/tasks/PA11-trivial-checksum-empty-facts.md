---
id: PA11
title: crc32_empty / adler32_empty — kernel-checked decide, no oracle
status: done
blocked_on: ""
after: []
related: []
bar: ""
track: proof-arch
priority: 9.7
priority_set: 2026-08-28T02:00:00Z
design: "inline"
design_review: "waived-mechanical"
date: 2026-08-27
---

# PA11: crc32_empty / adler32_empty — kernel-checked decide, no oracle

## Context

Sourced from `docs/ORACLE_DEBT.md`'s audit of `scripts/gate_allowlist.txt`. `Stdlib/Zlib/CRC32.lean`'s
`crc32_empty : crc32 ByteArray.empty = 0` and `Stdlib/Zlib/Adler32.lean`'s
`adler32_empty : adler32 ByteArray.empty = 1` are both proven by `native_decide`, and both are listed
`grandfathered`. Neither needs to be.

Both `crc32`/`adler32` route through an `Id.run do ... for i in [start:stop] do ...` loop where
`stop := Nat.min buf.size (start + len)`. For `buf := ByteArray.empty`, `buf.size = 0`, so `stop = 0`
and the loop body never executes — the entire computation reduces to the initial accumulator XORed
back out (`crc32`) or returned directly (`adler32`), with **no table lookup, no iteration, no
well-founded recursion** in the reduction path. This is exactly the shape `crc32Table_size`
(`Stdlib/Zlib/CRC32Equivalence.lean:93`) already discharges with plain `simp`/`rw` (no oracle) for an
analogous closed, non-parametric fact — the precedent already exists in this tree.

`native_decide` here is not wrong, it is simply stronger than the fact requires: an oracle-backed
axiom for a claim that plain kernel reduction can settle. Per the owner's zero-axiom mandate, replacing
it with `decide` (fully kernel-checked, no `native_decide.ax_*` axiom, no allowlist entry needed at
all) is strictly better and should be close to free.

## Deliverables & acceptance criteria

- `crc32_empty` and `adler32_empty` re-proven with `decide` (or `rfl`/`simp` if either goes through
  even more directly once the empty-loop reduction is unfolded — try the cheapest tactic first).
- If `decide` does not terminate promptly (confirm empirically, do not assume): fall back to an
  explicit unfold/`simp` proof that the `stop = 0` loop is definitionally the identity on the
  accumulator, then close by `rfl`. Either way, the proof must not depend on any `_native.*` axiom —
  confirm via `#print axioms crc32_empty` / `#print axioms adler32_empty` in the completion report.
- Both entries deleted from `scripts/gate_allowlist.txt` (no replacement entry needed — a plain
  `decide`/`rfl` proof requires no Law 10 allowance at all).
- `lake build` + `lake exe check_gates_axioms` clean.
- Completion report includes the `#print axioms` output for both theorems pre- and post-fix, and the
  new `scripts/gate_allowlist.txt` count (37 → 35 grandfathered, cumulative with PA10's five, i.e.
  effectively 32 → 30 after both land — completion report should state whichever order these two
  tasks actually land in and the resulting count).

## Pointers

- `Stdlib/Zlib/CRC32.lean:61-67` (`crc32`, `crc32_empty`).
- `Stdlib/Zlib/Adler32.lean:40-46` (`adler32`, `adler32_empty`).
- `Stdlib/Zlib/CRC32Equivalence.lean:88-96` (`crc32Table_size` — the existing precedent for
  discharging a closed, non-parametric fact about a fixed term without `native_decide`).
- `docs/STDLIB_ZLIB.md#61-checksum-invariance-theorems`.
- `docs/ORACLE_DEBT.md` — originating audit.

## Notes

- 2026-08-27: priority 9.7 — tied with PA10 for cheapest closure in the plan: both facts already
  reduce trivially under kernel evaluation once the empty-buffer loop bound is unfolded; `native_decide`
  is doing no real work here. No prerequisites; start immediately.
- 2026-08-28 (F2 status audit, verified against the tree at `3341d92`): `status: ready` -> `done`.
  Closed by `2b35d04` ("feat(proof-arch): migrate PA11/PA18 native_decide checksum and DEFLATE
  bound proofs to decide/structural"). Verified in the tree, not from the commit message:
  `Stdlib/Zlib/CRC32.lean:66-68` proves `crc32_empty` by `simp [crc32, updateCrc32, Id.run]` then
  `decide`, and `Stdlib/Zlib/Adler32.lean:45-47` proves `adler32_empty` the same way -- no
  `native_decide` in either. Both allowlist entries
  (`Stdlib/Zlib/CRC32.lean::crc32_empty` and `Stdlib/Zlib/Adler32.lean::adler32_empty`, both
  `grandfathered`) are deleted from `scripts/gate_allowlist.txt` by that same commit, and neither
  name appears in the file today.
