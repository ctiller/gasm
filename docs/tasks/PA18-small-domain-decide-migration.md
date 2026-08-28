---
id: PA18
title: Small finite-domain DEFLATE bound checks — verify plain decide suffices, drop native_decide
status: ready
blocked_on: ""
after: []
related: []
bar: ""
track: proof-arch
priority: 9.8
priority_set: 2026-08-28T02:00:00Z
design: "inline"
design_review: "waived-mechanical"
date: 2026-08-27
---

# PA18: Small finite-domain DEFLATE bound checks — verify plain decide suffices, drop native_decide

## Context

Sourced from `docs/ORACLE_DEBT.md`, addressing the owner's clarification that `finite-forall`
`native_decide`/`bv_decide` entries still carry axioms (`TCB.md` T14) and are not exempt from the
zero-axiom target just because their category is "permanently allowed under Law 10." Four of the ten
`finite-forall` entries are small, closed, exhaustive checks over concrete Nat/UInt ranges with no
well-founded-recursion obstruction (unlike `Gasm/Targets/Wasm/LEB128.lean`'s witness, see
`docs/tasks/PA12-wasm-trap-guard-and-leb128-witness.md`):

- `reverse_bits_8_involutive_inst` (`Stdlib/Zlib/Equivalence.lean`) and its exact duplicate
  `bit_reversal_8_involution_inst` (`Spikes/Spike5Gzip/Equivalence.lean`) — `∀ b in [0:256],
  reverseBits (reverseBits b 8) 8 = b`.
- `encode_length_bounds_inst` — `∀ len in [3:259], encodeLength len` produces a code in `[257,285]`.
- `encode_distance_bounds_inst` — `∀ dist in [1:32769], encodeDistance dist` produces a code ≤ 29.

All four are currently proven by `native_decide` over an explicit `for`/`Id.run` loop. The question
this task answers, per entry, is: **does plain kernel `decide` already close this goal in reasonable
time, with zero oracle?** This has not been tried — `native_decide` was reached for by default, not
because `decide` was attempted and found too slow. `reverseBits`/`encodeLength` (256-element domains)
are plausible `decide` candidates outright. `encodeDistance` (32768-element domain) is a larger
domain where plain `decide` may or may not finish in acceptable kernel-reduction time — if it does
not, the fallback is a structural proof over DEFLATE's fixed distance-code threshold bands (RFC 1951
§3.2.5's ~30 bands), each closed by `omega`/interval case-split rather than iterating all 32768
values — still zero oracle, just structural instead of brute-force.

## Deliverables & acceptance criteria

- For each of the four entries: attempt plain `decide` first. If it closes in acceptable build time
  (state the wall-clock time observed in the completion report — this is a real engineering
  constraint, not a formality, since kernel reduction can be dramatically slower than native
  evaluation), replace `native_decide` with `decide` and remove the allowlist entry entirely (a
  `decide`-checked closed finite claim needs no Law 10 allowance).
- If plain `decide` does not close in acceptable time for `encode_distance_bounds_inst` specifically
  (the one entry where this is plausible, given its 32768-element domain): fall back to a structural
  proof by case-splitting on `encodeDistance`'s own threshold bands (grep `Stdlib/Zlib/Equivalence.lean`
  and `Stdlib/Zlib/Gzip.lean`/`Deflate.lean` for `encodeDistance`'s actual definition first — this
  connects directly to `docs/tasks/TC12-connection-theorem-linter.md`'s RFC-1951-triple-duplication
  finding, so coordinate rather than duplicate if that task is concurrently touching the same
  function), each band closed by `omega` over its fixed bit-range, no exhaustive enumeration.
- Any entry migrated to plain `decide` or a structural proof is deleted from
  `scripts/gate_allowlist.txt` outright (not re-added under a different category).
- Zero `sorry`; `lake exe check_gates_axioms` clean; `#print axioms` confirms no `_native.*` axiom
  remains on any migrated theorem.
- Completion report: per-entry disposition (plain `decide` succeeded / structural fallback used /
  neither worked and `native_decide` retained with a stated reason — this last outcome should be rare
  given these are the smallest, most tractable entries in the whole ledger, but report honestly if it
  occurs), wall-clock timings observed, and the resulting `scripts/gate_allowlist.txt` count.

## Pointers

- `Stdlib/Zlib/Equivalence.lean:26-56` (`reverse_bits_8_involutive_inst`, `encode_length_bounds_inst`,
  `encode_distance_bounds_inst`).
- `Spikes/Spike5Gzip/Equivalence.lean:94-102` (`bit_reversal_8_involution_inst`, the exact duplicate —
  also flag this to `docs/tasks/TC12-connection-theorem-linter.md`'s twin-detection scope if not
  already covered, since it is a second, unlinked copy of the same fact).
- RFC 1951 §3.2.5 (length/distance code tables — vendored, if present, under `references/`; confirm
  before citing) — the structural fallback's band boundaries.
- `docs/REVIEW.md` Law 10 (the `decide`/`native_decide` boundary this task exercises directly).
- `docs/ORACLE_DEBT.md` — originating audit; Part 2's finite-forall tractability assessment names
  these four as the lowest-risk migration candidates in the whole ledger.

## Notes

- 2026-08-27: priority 9.8 — the single cheapest, lowest-risk item in the entire oracle-debt plan:
  small closed domains, no recursion obstruction, no model dependency, no architecture prerequisite.
  If this task's `decide` attempts succeed as expected, it is very likely a same-day close.
