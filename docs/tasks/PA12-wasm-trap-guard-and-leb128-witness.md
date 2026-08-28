---
id: PA12
title: Wasm trap short-circuit + SLEB128 budget witness — structural proofs, no native_decide
status: done
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
- 2026-08-27: **done, with one honestly-scoped residual.** Allowlist: 84 → 82 entries (both
  target entries removed; B7 and the bare-metal-target merge, landed underneath this task, moved
  the pre-task baseline from 80 to 84 — no other entry touched).

  **`trapShortCircuitGuard_inst` → `evalInstr_trapped_next`.** The originating audit's premise
  ("provable directly by structural induction on `evalInstr`'s own definition... not new model
  surface") turned out to be false as stated: `evalInstr`/`evalInstrs`/`evalLoop` were a `mutual
  partial def` group that Lean compiles to a fully **opaque constant** — confirmed empirically,
  including on a from-scratch minimal reproduction (`partial def countdown ...; #print countdown`
  prints `opaque countdown`, and `unfold`/`rfl`/`simp only [countdown]` all fail outright). This is
  a strictly harder obstruction than "kernel `Acc.rec` reduction gets stuck" (which still permits
  equational rewriting via `unfold`/`simp`, as `LEB128.lean`'s existing well-founded-recursion
  proofs already demonstrate) — an opaque constant has *no* defining equation for any tactic to
  use, at any granularity, so no induction was possible against the pre-task definition at all.
  Fix: refactored `Semantics.lean` so the trap/exit guard lives in a new, ordinary (non-`partial`)
  `evalInstr` wrapper — `if s.trapped || s.exitCode.isSome then (s, .next) else evalInstrMatch
  instr s hostCall` — outside the `mutual` group, with `evalInstrMatch` (the renamed original
  per-instruction dispatch, guard stripped) and `evalInstrs`/`evalLoop` remaining inside it;
  `evalInstrs`'s one internal call site inlines the identical guard rather than routing through
  the new external wrapper (which it cannot reference — it is declared after the `mutual` block
  closes). Same signature, same behaviour (confirmed: `lake exe wasm_fuzzer` unchanged, 76/76
  passed). Proved, in `SemanticsFuzzer.lean`:

  ```
  theorem evalInstr_trapped_next (instr : WasmInstr) (s : WasmMachineState)
      (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal)
      (h : s.trapped = true) :
      evalInstr instr s hostCall = (s, .next)
  ```

  universally quantified over every `WasmInstr`, every `WasmMachineState`, every `hostCall` — not
  the one 5-instruction example. Closed by `unfold evalInstr; simp [h]`: structural, zero oracle,
  no allowlist entry. **Honest residual**: `evalInstrs`/`evalLoop` themselves remain opaque —
  `evalLoop`'s own `.br 0` self-recursion on the *same* loop body has no structurally-decreasing
  measure (a real Wasm infinite loop must be able to not terminate), so the whole three-function
  SCC cannot be pulled out of `partial` without a `Fuel`/CCPO-style rewrite of the interpreter — a
  materially larger, semantics-changing project, not proof engineering, and out of this task's
  scope. `evalInstr_trapped_next` is therefore the maximal structural generalization available
  today, documented as such in its own docstring rather than oversold as the full list-level
  claim. The original concrete 5-instruction scenario is preserved as a `#guard` compile-time
  check (same compiled/interpreted evaluation `native_decide` used, but no stored declaration and
  no axiom, so no allowlist entry is needed for it either) rather than restated as a theorem.

  **`encodeI32SLEB128_exceeds_i32_budget_inst`.** This one *did* close exactly as the audit
  expected — no opacity obstruction, since `encodeSLEB128List` is ordinary well-founded recursion
  (`termination_by val.natAbs`), which (unlike `partial def`) still gets a real equation Lean's
  `unfold` tactic can use; the prior `native_decide` was there only because kernel `decide` gets
  stuck evaluating the `Acc.rec` proof term on a huge concrete instance, not because the equation
  itself was unavailable. Proved, in `LEB128.lean`, by plain induction (no Mathlib — this project
  has no such dependency, so `norm_num`/`ring`/`positivity` were replaced by `omega` plus core
  `Int.pow_add`/`Int.pow_pos`/`decide` on small concrete literals):

  ```
  theorem encodeSLEB128List_length_ge (k : Nat) : ∀ (v : Int),
      (2 : Int) ^ (7 * (k + 1)) ≤ v → k + 2 ≤ (encodeSLEB128List v).length
  ```

  i.e. encoding any value at or above `2^(7*(k+1))` needs at least `k+2` bytes, for every `k` —
  the actual "size grows with magnitude, no fixed byte budget" claim the module docstring already
  asserted in prose. Specializing `k = 4` gives `2^35 ≤ v → 6 ≤ length`
  (`encodeSLEB128List_exceeds_budget`), and the original ground instance (`2^40 ≥ 2^35`) falls out
  as a corollary (`encodeI32SLEB128_exceeds_i32_budget_inst`, same name, now a `theorem` with no
  `native_decide` anywhere in its proof). Per the top-level instruction not to overclaim: this is
  a byte-budget *lower bound under an explicit magnitude hypothesis* — it does not (and does not
  need to) claim `encodeI32SLEB128` is "wrong"; the roundtrip theorems already proven above it in
  the same file establish it is arithmetically correct for every `Int` unconditionally, and this
  new theorem only formalizes the separate, real gap TC20 identified: the missing budget
  *precondition* a caller must enforce.

  **Gates** (foreground, direct exit codes, tree rebased onto `main`
  `9072000` first — clean rebase, no conflicts, B7's trap-handling code and the bare-metal-target
  merge both pre-date this task's changes and neither touches the same lines): `lake build`
  (422 jobs) exit 0; `lake exe check_gates_axioms`, `lake exe check_refs_coverage`,
  `lake exe wasm_fuzzer`, `check_gates.py`, `check_refs.py`, `check_licenses.py`, `check_record.py`,
  `check_doc_facade.py`, `check_publishable.py` — see the session's final report for each exit
  code. `#print axioms` on both new top-level theorems (`evalInstr_trapped_next`,
  `encodeI32SLEB128_exceeds_i32_budget_inst`) shows only `{propext, Classical.choice,
  Quot.sound}` — no native-eval axiom, confirming neither needs an allowlist entry.
