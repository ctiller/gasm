---
id: PA13
title: CRC32 bit-trick lemmas without a SAT certificate — and_one_cases, G_eq_Gbf, xor_byte_shr8
status: done
blocked_on: ""
after: []
related: [PA1, PA14]
bar: ""
track: proof-arch
priority: 9.3
priority_set: 2026-08-28T02:00:00Z
design: "inline"
design_review: "waived-mechanical"
date: 2026-08-27
---

# PA13: CRC32 bit-trick lemmas without a SAT certificate — and_one_cases, G_eq_Gbf, xor_byte_shr8

## Context

Sourced from `docs/ORACLE_DEBT.md`. `TCB.md` T14 (2026-08-27) established that `bv_decide`, like
`native_decide`, is **not kernel-checked**: `LratCert.toReflectionProof` compiles and runs a native
LRAT-certificate checker and asserts the result as an axiom via the same `nativeEqTrue` routine
`native_decide` calls — the SAT/LRAT search only produces evidence for a native-eval step, the kernel
never replays the certificate. Per the owner's revised target ("no axioms... `bv_decide` was
established earlier today to be NOT kernel-checked"), all four of PA1's `bv_decide` proofs in
`Stdlib/Zlib/CRC32Equivalence.lean` — `and_one_cases`, `G_eq_Gbf`, `xor_byte_shr8`, `G8bf_table` —
carry axioms that should be closed where structurally tractable, not treated as permanently settled
because they are `finite-forall`-allowlisted.

Three of the four are, on inspection, small enough to plausibly avoid a SAT certificate entirely:

- `and_one_cases (c : UInt32) : c &&& 1 = 0 ∨ c &&& 1 = 1` — this is exactly the statement that
  `c &&& 1` (a value in `{0,1}` by construction of AND-with-1) is one of its two possible values.
  Lean/Std's `BitVec`/`UInt32` API likely already exposes this as a derivable fact (e.g. via
  `UInt32.and_one` reducing to `c.toBitVec.getLsb 0`-shaped reasoning, or a direct `omega`-after-
  `toNat`-conversion using `Nat.and_one_eq_mod_two`-style lemmas) — investigate the existing bitvector
  lemma library before assuming a from-scratch proof is needed.
- `xor_byte_shr8 (c : UInt32) (b : UInt8) : (c ^^^ b.toUInt32) >>> 8 = c >>> 8` — XORing in a value
  with no bits above position 7 cannot change any bit at or above position 8; this is a direct
  instance of a `BitVec.shiftRight`/`BitVec.xor` bit-extensionality argument (each output bit at
  position `i ≥ 8` reads input bit `i` for both sides, since `b.toUInt32`'s bit `i` is `false` for all
  `i ≥ 8`) — provable via `BitVec.ext`/`BitVec.getElem_xor`/`BitVec.getElem_ushiftRight`-shaped
  lemmas (or `UInt32` equivalents) without exhaustive search.
- `G_eq_Gbf (poly c : UInt32) : G poly c = Gbf poly c` — already reduces (via `and_one_cases`) to two
  branches, each of which is `(c >>> 1) ^^^ poly = (c >>> 1) ^^^ (poly &&& 0)` and
  `(c >>> 1) ^^^ poly = (c >>> 1) ^^^ (poly &&& 0xFFFFFFFF)` — i.e. `poly &&& 0 = 0` and
  `poly &&& allOnes = poly`, both standard `and_zero`/`and_allOnes`-class lemmas once `0 - (c&&&1)`
  is recognized as `0` or `allOnes` in each branch (an arithmetic fact about `UInt32` subtraction from
  zero, itself provable via `omega`/`BitVec` conversion, not exhaustive search).

`G8bf_table` (the fourth `bv_decide` call, over the full `UInt32 × UInt32` domain applying `Gbf`
eight times) is explicitly **out of scope for this task** — see
`docs/tasks/PA14-crc32-table-identity-structural-closure.md`, which
covers it separately as the one genuinely hard case in this group.

## Deliverables & acceptance criteria

- `and_one_cases`, `xor_byte_shr8`, `G_eq_Gbf` each re-proven without `bv_decide` (structural
  `BitVec`/`UInt32` lemma application, `omega`, `simp` — whatever combination closes each goal), OR a
  documented finding, per lemma, for why a structural proof was not achievable in this pass (do not
  silently leave a lemma on `bv_decide` without recording the attempt and blocker).
- For each lemma successfully migrated: removed from `scripts/gate_allowlist.txt`'s `finite-forall`
  category entirely (a structural proof needs no Law 10 allowance).
- Downstream consumers re-checked: `G_eq_Gbf` is used by `G8_eq_Gbf8` (an `axiom-only` allowlist
  entry) and `crc32ByteStep_eq_G8` (also `axiom-only`) — confirm via `#print axioms` that migrating
  `G_eq_Gbf`/`xor_byte_shr8`/`and_one_cases` off `bv_decide` removes their contribution to those two
  downstream theorems' axiom sets (the residual, if any, should trace only to `G8bf_table`'s
  still-`bv_decide`'d proof, per PA14).
- Zero `sorry`; `lake exe check_gates_axioms` clean; each migrated theorem's `#print axioms` output
  included in the completion report (before/after).
- `scripts/check_refs.py` clean.

## Pointers

- `Stdlib/Zlib/CRC32Equivalence.lean:190-233` (`and_one_cases`, `G_eq_Gbf`, `G8bf_table`),
  `:251-252` (`xor_byte_shr8`).
- `TCB.md` §T14 in full — the `bv_decide`-is-not-kernel-checked finding motivating this task.
- `docs/tasks/PA1-crc32-pathfinder.md` — the task these lemmas originated from; this task is a
  follow-on hardening, not a re-litigation of PA1's own scope.
- `docs/tasks/PA14-crc32-table-identity-structural-closure.md` — the sibling task for `G8bf_table`
  (referenced again here in full for `scripts/check_record.py`'s citation resolver)
  specifically, deliberately out of this task's scope.
- `docs/ORACLE_DEBT.md` — originating audit; Part 2's finite-forall structural-tractability
  assessment names these three as plausibly tractable without a SAT certificate.

## Notes

- 2026-08-27: priority 9.3 — no prerequisite; three of PA1's four `bv_decide` lemmas are small enough
  that a structural bitvector proof is a reasonable bet, distinct from `G8bf_table`'s genuinely harder
  case (PA14). Closing these three shrinks the axiom set on `crc32ByteStep_eq_G8` even if PA14 does
  not land soon.
- 2026-08-28: **done.** Landed in commit `3ca668d` ("feat(zlib): close all four CRC32 bv_decide
  certificates structurally (PA13, PA14)"). `and_one_cases` closes via `UInt32.toNat_and` +
  `Nat.and_one_is_mod` + `omega`; `G_eq_Gbf` case-splits on `and_one_cases` and rewrites each branch
  with `UInt32.and_zero`/`UInt32.zero_sub`/`UInt32.and_neg_one`; `xor_byte_shr8` closes by
  `BitVec.eq_of_getLsbD_eq` (the zero-extended byte's bits at index ≥ 8 are `false`). All three are
  gone from `scripts/gate_allowlist.txt`. Verified 2026-08-28 on `main`: `Stdlib/Zlib/`
  `CRC32Equivalence.lean` contains no `bv_decide` in proof position, and `#print axioms` on
  `and_one_cases`, `G_eq_Gbf`, `xor_byte_shr8`, `G8_eq_Gbf8` and `crc32ByteStep_eq_G8` reports only
  standard axioms (a subset of `[propext, Classical.choice, Quot.sound]`; `and_one_cases` and
  `xor_byte_shr8` do not even need `Classical.choice`). Status flipped in a later change (the implementing
  commit updated the code and the allowlist but left this front-matter on `ready`).
