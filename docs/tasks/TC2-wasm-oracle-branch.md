---
id: TC2
title: Wasm oracle branch — fail-closed control-flow fuzzing, TRAP-laundering fix
status: done
blocked_on: ""
after: []
related: []
bar: ""
track: trust-core
priority: 7.5
priority_set: 2026-08-27T18:25:47Z
design: predates-discipline
design_review: predates-discipline
date: 2026-08-27
---

# TC2: Wasm oracle branch — fail-closed control-flow fuzzing, TRAP-laundering fix

## Context

This task's substance lives in PLAN.md's Phase-1 history (the "Wasm control-flow fuzzing"
entry, branch `worktree-agent-ad4389e032b10b3d9`, commit `6b5914d` and its fix cycles); this
file records that history since the task predates the current task-lifecycle discipline
(`design: predates-discipline`).

This was the **second** confirmed fail-open oracle found in the same review wave that produced
TC1 — same disease, different harness. The first review verdict was **REJECT**: V8's rejection
of an invalid module was being laundered through a `TRAP:` string prefix into a reported PASS;
3 of 9 cases (branch depth 1/2, loop re-entry — precisely the headline coverage the suite
existed to provide) never actually executed; a machine with no `node` on PATH reported
all-green; a fixed temp file path caused concurrent fuzzer runs to cross-contaminate each
other's results (reproduced by the reviewer); there was a stderr handle leak and no timeouts;
the comparator was blind to memory and locals (store instructions asserted nothing about their
effect); and `local_tee` had been a dead PASS the entire time. The reviewer hand-verified valid
equivalents of the dead cases against the interpreter and confirmed the underlying Wasm
semantic *model* was fine — the harness architecture was what was broken.

The first fix cycle (`f07692f`) applied the same structural medicine as TC1: `Except
OracleFailure`/`WasmRunOutcome` types (fail-closed at the type level, exhaustive match — no
code path can synthesize a passing result), an explicit `INVALID:` vs `TRAP:` split in the node
driver script so real-module-rejection is distinguishable from an intentional trap, mandatory
positive/negative/trap control vectors (node-absent now aborts the run — demonstrated, not
just claimed), a pre-module stack/type assertion, the 3 previously-dead cases fixed to match
V8's actual errors plus `local_tee`, 6 new cases added (loop-vs-block discriminator, branch
depth-2 from a loop, nested trap, 3 store/load cases), de-duplicated ("DRY'd") driver code,
unique per-run temp paths, stderr draining, and timeouts. Result: **65/65 cases, 2424 vectors,
0 divergences, and the formerly-dead cases now genuinely executing.**

A deferred item from this cycle (explicitly same-branch follow-up, not fixed here): a
build-time Lean Wasm module validator (`references/wasm/valid`) — this remains open; see
MODEL_DEBT B9 (Wasm ISA/validation gaps) and TASKS.md's model-debt-intake note on scheduling
Wasm-related work with TC9-era work.

A **second, final** review round (verdict recorded as MERGE-WITH-FIXES) went further: the
reviewer built an independent JS mirror of the interpreter plus a 14-mutation matrix, confirmed
laundering was closed and memory-related mutations were caught, and confirmed the
cross-contamination bug was dead — but found the branch-depth-decrement mutations
(`Semantics.lean:381,415` at review time) were **invisible to all 65 existing cases**, because
`stepWasm` discarded the `ControlSignal` the mutation would have corrupted — the mutated
behavior only manifests if there is trailing code *outside* the loop to observe it. An
endianness compensating-swap bug (a store paired with a `load8_u`) was also invisible, and
`verifyWasmDiffCase` was bypassable by future callers who didn't go through the guarded entry
point. The validator deferral was accepted with the residual risk stated explicitly (external
gate needs CI wiring; validity is only checked for fuzzed states, not spike-emitted modules).

The final fix cycle (`59fb2f1`) closed these: discriminating branch-depth cases using an
explicit mutation-apply-observe-revert cycle on `Semantics.lean` (both known mutations now kill
the *right* cases, and the mutation revert was verified byte-identical to the pre-mutation
file), an endianness pin, structural controls added inside `verifyWasmDiffCase` itself so future
callers cannot bypass the guard, and a `trapShortCircuitGuard_inst` — honestly named as an
`_inst` regression check (Law 8/10 naming discipline), verified by `decide` to be an impossible
case given the current `partial def` control-flow chain. Final state: **67/67 cases, 2524
vectors, 0 divergences — MERGE-READY**, with one merge-time TODO recorded: add a
`trapShortCircuitGuard_inst` entry to `gate_allowlist.txt` (which lived on the concurrently-
developed linter branch, TC3). PLAN.md's "Merge train 2 (2026-08-27) — LANDED" section confirms
this entry was in fact added and the merged tree verified 67/67 (2524 vectors) with both gates
green on day one of the merged tree.

## Deliverables & acceptance criteria

Historical — already merged to main. For the record: `Except`-typed oracle outcomes that
cannot fabricate a pass; `INVALID:`/`TRAP:` disambiguated in the node driver; mandatory
pos/neg/trap control vectors (node-absent demonstrably aborts); mutation-apply-observe-revert
verified discriminating cases for the branch-depth class; `verifyWasmDiffCase` structurally
guarded against bypass; `trapShortCircuitGuard_inst` allowlisted with justification in
`scripts/gate_allowlist.txt`.

## Pointers

- `Gasm/Targets/Wasm/SemanticsFuzzer.lean` — the fuzzer this task hardened; grep-confirmed to
  exist and to reference `gate_allowlist.txt`-relevant identifiers (`trapShortCircuitGuard_inst`
  matched here at time of writing).
- `scripts/gate_allowlist.txt` — contains the `trapShortCircuitGuard_inst` entry this task's
  final cycle added (grep-confirmed present).
- PLAN.md, "Phase 1 — Mechanical trust fixes", the "**Wasm control-flow fuzzing**" bullet — the
  full narrative, including both review rounds' verdicts and the exact line numbers
  (`Semantics.lean:381,415` at review time) for the branch-depth mutation class; read directly
  rather than relying solely on this summary, since those line numbers will have moved.
- PLAN.md, "Merge train 2 (2026-08-27) — LANDED" — confirms the merged-tree verification (67/67,
  2524 vectors) and that both gates (this task's fuzzer and TC3's linter) caught the
  cross-branch `trapShortCircuitGuard_inst` naming issue on first contact.
- MODEL_DEBT B7 (Wasm OOB trap — live soundness gap, structurally invisible to this fuzzer
  because `Fuzzable.lean` only generates in-bounds addresses) and B9 (large ISA/validation
  gaps, including the deferred build-time validator) — open debt this task did not close, only
  discovered.

## Notes

- 2026-08-27: priority 7.5 — done; fixed the Wasm TRAP-laundering fail-open catastrophe — same class/severity as TC1, historical value high.

_(2026-08-27) This task predates the notes→design→review→implementation discipline; its
working history lives in PLAN.md's Phase-1 merge-train record. No further entries expected
unless a later task reopens this branch's deferred validator item (see MODEL_DEBT B9 / TASKS.md
model-debt-intake note)._
