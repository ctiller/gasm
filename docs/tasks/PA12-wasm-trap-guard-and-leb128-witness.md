---
id: PA12
title: Wasm trap short-circuit + SLEB128 budget witness — structural proofs, no native_decide
status: ready
blocked_on: ""
after: []
related: [B7, TC20]
bar: ""
track: proof-arch
priority: 9.5
priority_set: 2026-08-28T02:00:00Z
design: "inline"
design_review: "waived-mechanical"
date: 2026-08-27
---

# PA12: Wasm trap short-circuit + SLEB128 budget witness — structural proofs, no native_decide

## Context

Sourced from `docs/ORACLE_DEBT.md`. Two of the 37 `grandfathered` entries do not fit either the
"trace equivalence" or "codec roundtrip" shape and were not covered by any existing task:

1. **`trapShortCircuitGuard_inst`** (`Gasm/Targets/Wasm/SemanticsFuzzer.lean`): a single
   `native_decide` pin that `stepWasm (.block (.val .i32) [.i32_const 5, .i32_const 0, .i32_div_u,
   .i32_const 999, .i32_add]) {}` leaves an empty stack — i.e. once `.i32_div_u` traps on the
   div-by-zero, `.i32_add` never runs. It was added mid-review (per `docs/tasks/TC2-wasm-oracle-branch.md`)
   as a mutation-tested regression pin, honestly `_inst`-named, but the underlying property it stands
   in for — **`evalInstr`'s `trapped` guard short-circuits the rest of an instruction sequence, for
   any instruction list, not just this one 5-instruction example** — is a genuine `∀`-statement over
   `List WasmInstr` provable directly by structural induction on `evalInstr`'s own definition (case on
   whether the head instruction traps; if so, `simp` the accumulator-fold to show nothing after it
   executes; if not, recurse). This is a case analysis over a function definition already in the
   tree, not new model surface.
2. **`encodeI32SLEB128_exceeds_i32_budget_inst`** (`Gasm/Targets/Wasm/LEB128.lean`): `native_decide`
   is used *only* here in the file because `encodeSLEB128List` is well-founded-recursive
   (`termination_by val.natAbs`), so kernel `decide` gets stuck on the `Acc.rec` proof term and cannot
   reduce it — a known, structural Lean limitation for this recursion shape, not a claim about an
   infinite domain (the theorem itself is a single ground witness: `encodeI32SLEB128 (2^40)` has size
   ≥ 6). The fix is not a harder proof, it is removing the obstruction: either add a manual
   `@[simp]` unfolding/equation lemma for `encodeSLEB128List` at this ground input (bypassing kernel
   `Acc.rec` reduction) or restructure the function with an explicit fuel parameter (structural
   recursion) so kernel `decide` can reduce it directly, matching the well-founded-vs-structural
   distinction `docs/REVIEW.md` Law 10 already draws for exactly this class.

Neither of these was in scope for any existing task (`docs/tasks/TC20-wasm-emission-roundtrip.md`
built the LEB128 decoder/roundtrip machinery this ground instance sits next to, but did not touch it
— confirmed by grep; no task references `trapShortCircuitGuard_inst` except historical notes in the
already-`done` TC2/TC3).

## Deliverables & acceptance criteria

- `trapShortCircuitGuard_inst` replaced by a general theorem: `∀ (instrs : List WasmInstr) (s :
  WasmState), (evalInstrs instrs s).trapped = true → <no instruction past the trapping one changes
  the stack beyond what the trapping instruction itself left>` (state precisely against
  `evalInstr`'s actual accumulator/fold shape — grep to confirm current signature), proven by
  structural induction/case analysis on the instruction list and the `trapped` guard, not
  `native_decide`. The original 5-instruction case becomes a corollary (or a plain regression test
  in a `*Test.lean`, not the proof-architecture path) if still useful as a control vector.
- `encodeI32SLEB128_exceeds_i32_budget_inst` re-proven without `native_decide`: either an equation
  lemma unblocking kernel `decide`, or a structural-recursion rewrite of `encodeSLEB128List`
  (whichever is cheaper — state which was chosen and why). The general claim this witness stands in
  for (`encodeI32SLEB128`'s size grows with magnitude, no fixed byte budget) may also be stated and
  proven generally if that turns out no harder than fixing the single witness — attempt it, but the
  ground-instance fix alone satisfies this task's minimum bar.
- Both entries removed from `scripts/gate_allowlist.txt` (or replaced by a genuinely finite-forall /
  oracle-free entry if some residual `decide`-shaped allowance is still needed).
- Zero `sorry`, zero unauthorized axioms; `lake exe check_gates_axioms` clean.
- Since the trap-guard theorem is stated against `Gasm/Targets/Wasm/Semantics.lean`'s current
  `evalInstr`, and `docs/tasks/B7-wasm-oob-trap-and-limits.md` is actively changing that same file's
  trap-handling paths (OOB memory access trapping), coordinate sequencing: if B7 lands first, restate
  this task's general theorem against B7's post-fix `evalInstr`; if this task lands first, flag for
  B7's author that the trap-short-circuit theorem may need a one-line update once B7's new trap
  reasons are added (a `TrapReason` case split, not a proof rewrite, per B7's own design).
- Completion report states the before/after allowlist count and confirms via `#print axioms` that
  neither theorem carries a `_native.*` axiom.

## Pointers

- `Gasm/Targets/Wasm/SemanticsFuzzer.lean:925-935` (`trapShortCircuitGuard_inst`, its own comment
  documenting the mutation-testing provenance).
- `Gasm/Targets/Wasm/Semantics.lean` — `evalInstr`'s trap-guard definition (grep to confirm current
  structure and line numbers).
- `Gasm/Targets/Wasm/LEB128.lean:349-367` (`encodeI32SLEB128_exceeds_i32_budget_inst` and its own
  comment explaining the well-founded-recursion obstruction).
- `docs/tasks/TC20-wasm-emission-roundtrip.md` — built the LEB128 decoder/roundtrip machinery
  adjacent to this ground instance without touching it; read its completion notes for the exact
  current shape of `encodeSLEB128List`/`decodeSLEB128List` before choosing a fix.
- `docs/tasks/B7-wasm-oob-trap-and-limits.md` — actively changes `Semantics.lean`'s trap handling;
  coordinate rather than race.
- `docs/REVIEW.md` Law 10 (well-founded vs. structural recursion and the `native_decide` boundary).
- `docs/ORACLE_DEBT.md` — originating audit.

## Notes

- 2026-08-27: priority 9.5 — no architectural prerequisite, both fixes are self-contained proof/
  refactor engineering against code that already exists; flagged `related: [B7]` because B7 touches
  the same `evalInstr` trap machinery this task's first theorem is stated against, not because B7
  blocks starting this task.
