---
id: TC5
title: Gate runner — single entry point for all gates
status: done
blocked_on: ""
after: [TC4]
related: []
bar: bar-1
track: trust-core
priority: 9.5
priority_set: 2026-08-27T18:25:47Z
design: "inline"
design_review: "waived-mechanical"
date: 2026-08-27
---

# TC5: Gate runner — single entry point for all gates

## Context

No CI exists in this repository (`.github` is absent — confirmed by `find .github` returning
nothing at time of writing). Every gate the project relies on — `lake build`, the two Law-10
linters, three differential fuzzers, and the roundtrip test suite — is currently invoked by hand,
per-agent, per-session. PLAN.md's Phase-1 tracker states the consequence bluntly: reviewers have
**repeatedly flagged that "a gate nothing invokes binds nothing."** A gate that exists as a script
in `scripts/` but that no single command runs is not a gate a merge actually passed through — it's
a script an agent may or may not have remembered to run.

This task is the single point where that stops being true. It has no design prerequisite (no
Law-5 stop-and-design item blocks it — it is pure orchestration of gates that already exist),
which is why it sits at `ready` with an empty `design` field: this is a "small mechanical task"
per the task-lifecycle convention in `TASKS.md`, so a `## Design` section inline in *this* file
(once someone starts on it) is enough — no `docs/` design doc is required.

### Why fail-closed, not fail-soft, is the entire point

Three converging findings make "abort on missing prerequisite" the load-bearing requirement,
not a nice-to-have:

1. **D13 (TCB policy)**: everything trusted-but-unprovable — environment, hardware, external
   tools — gets a differential fuzzer validating our model of it, and the oracle environment
   itself (node/NASM/python versions) is currently **unpinned** (PLAN.md "TCB.md ledger" gap
   entry: "oracle environment versions UNPINNED (node/python/NASM — drift silently changes gate
   results; pin + record versions in gate output)"). This task is where that pinning gets
   implemented: the runner must record which NASM/node versions it found and used.
2. **Two prior fail-open catastrophes, both already fixed at the harness level, both regressions
   this runner must not reintroduce at the orchestration level.** PLAN.md's Phase-1 history
   records: (a) the x86 hardware semantics fuzzer was "a silent fail-open no-op" — a bare
   relative spawn path failed on Windows, and a catch block synthesized `faulted:=true` for
   every vector, so the oracle never executed and a 6/49 baseline was reported as passing; fixed
   in `runHardwareBatch` returning `Except` (no synthesizable results) plus mandatory pos/neg
   control-vector checks (see the two `throw (IO.userError ...)` sanity checks around
   `Gasm/Targets/X86_64/HardwareHarness.lean:331-336`, verified present by grep at time of
   writing). (b) the Wasm control-flow fuzzer independently had the same disease — V8
   module-rejection laundered via a `TRAP:` prefix into PASS, node-absent reporting all-green —
   fixed the same way (`Except OracleFailure/WasmRunOutcome`). **Both were caught by adversarial
   review, not by any gate**, which is itself Law 13's point: the review finding must terminate
   in a mechanical prevention, and "the thing that invokes the oracle checks its own control
   vectors" is only half the prevention — the *runner* must not let a missing oracle silently
   skip the check that would have caught this class in the first place.
3. **Self-finding from Merge Train 2** (PLAN.md, "Merge train 2 (2026-08-27) — LANDED"): the
   owner's own first merged-tree verification script "reported tools' exit codes through a pipe
   (got tail's exit) — fail-open reporting." A gate runner that pipes a checker's stdout through
   anything before checking `$?`/`%ERRORLEVEL%` inherits the wrong exit code and silently turns a
   red gate green. **This is a concrete implementation trap for this exact task — capture exit
   codes directly from each invoked process, never through a pipe, `tee`, or shell pager.**

### What "gate" means here, concretely

Per `docs/REVIEW.md` §4.1 (Pillar 1: Mechanical Truth) and §4.4 (Gate 1), the mechanical gates
that must all pass before a PR/merge is even eligible for semantic review are: `lake build` (zero
`sorry`, zero unauthorized axioms), `python scripts/check_refs.py` (citation validity), `python
scripts/regenerate_references.py --verify` (reference corpus integrity), `python
scripts/check_gates.py` (fast source-level Law-10 pre-check), and `lake exe check_gates_axioms`
— **run from the repository root; building the executable is not running it** (this exact
phrasing is in REVIEW.md §4.1 item 4 because a prior agent's dispatch note made exactly this
mistake). This task's list is a superset of that Pillar-1 list, adding the differential fuzzers
that are pull-request-scoped rather than always-on:

- `lake build` (all `defaultTargets` in `lakefile.toml`, which already includes
  `check_gates_axioms` — verified present in the target list at time of writing)
- `python scripts/check_refs.py`
- `python scripts/check_gates.py`
- `lake exe check_gates_axioms` (from repo root — the Tools/CheckGatesAxioms.lean gate; do not
  substitute `lake build check_gates_axioms`, which only compiles it)
- `python scripts/regenerate_references.py --verify`
- `x86_fuzzer` (the hardware semantics differential fuzzer — `Gasm.Targets.X86_64.SemanticsFuzzerCLI`)
- `encoding_fuzzer` (`Gasm.Targets.X86_64.EncodingFuzzerCLI`) — **fail-closed if NASM is absent**;
  PLAN.md records NASM was previously reachable only via a since-removed path, i.e. this
  prerequisite has already silently broken once
- `wasm_fuzzer` (`Gasm.Targets.Wasm.SemanticsFuzzerCLI`) — **fail-closed if node is absent**
- `test_roundtrip` (`Gasm.Targets.X86_64.RoundtripTests`)
- `gzip_fuzzer`/`GzipFuzzer.lean`'s python-subprocess oracle — audited by TC9 (fail-open audit);
  the runner should invoke it, but TC9 is where its own internal fail-open paths get closed
- The registry roundtrip gate shards (already inside `lake build` as native `decide`/`native_decide`
  proofs per instruction family — no separate invocation needed, but the runner's summary should
  distinguish "gate compiled" from "gate's 21 shards each individually reported" if that
  granularity is cheap to surface)

For each externally-invoked oracle (NASM, node, python), the runner must, per D13/TCB and per
Law 13's control-vector rule: (1) detect presence explicitly before running anything that depends
on it, (2) **abort the whole run** (non-zero exit, clearly labeled) rather than skip that gate if
the prerequisite is missing — "abort, not skip" is the exact phrasing from `TASKS.md`'s TC5
entry — and (3) record the detected tool's version string in the run's output, so a future
divergence between gate results across two machines/sessions is attributable to an environment
drift instead of silently re-litigated as a model bug.

### BAR 1 triggers after TC4+TC5 — full codebase scope, not just trust-core

`TASKS.md`: "**BAR 1 — after TC4+TC5: fresh-agent deep re-review of the trust core.**" Per
`docs/adr/0010-bar-triggered-deep-re-reviews.md`, read "of the trust core" as *what triggers* BAR 1, not
as its scope: every BAR is a full deep re-review of the **entire codebase from scratch** by fresh
Opus agents (the same shape as the original multi-agent deep review that started the repair
epic), blinded to prior review conclusions except as a claimed-state cross-check. TC4+TC5 landing
is simply the milestone that schedules it — the dispatched reviewer(s) must re-derive standing
across the whole tree (drift between docs/laws/ADRs and code reality anywhere, not just in
trust-core files; whether recent merges' claimed outcomes hold; ranked new findings tree-wide; an
on/off-course verdict; the right-theorem-vs-mechanical-catch convergence ratio from
`docs/VISION.md` §2) — not confine itself to the gate-runner/registry-gate work that triggered it.

### Relationship to TC6 (CI) and TC9 (fail-open audit)

TC6 (CI establishment) is blocked on this task landing — CI, whenever Craig decides where it
runs, will invoke this one entry point rather than re-deriving the gate list. TC9's fail-open
audit is a per-oracle deep-dive (GzipFuzzer's subprocess handling, spike `Test.lean`'s "100%
sound (in-Lean)" fallback path) that this task's runner should surface but does not itself need
to fix — TC5 is about *invocation and reporting discipline*, TC9 is about *what each oracle does
internally when it can't reach its dependency*. Do not conflate the two: a correct TC5 runner
still faithfully reports a TC9-shaped bug if TC9 hasn't landed yet (i.e., it will report "gate
passed" for an oracle that is itself silently fail-open until TC9 fixes that oracle) — TC5 fixes
the outer loop, TC9 fixes the inner one.

Fail-closed oracle gating as a repo-wide policy is ratified in
`docs/adr/0013-tcb-ledger-and-trust-implies-fuzzer.md` (D13 — trust-implies-fuzzer, and the
control-vector obligation this implies for every world-facing oracle) and
`docs/adr/0009-findings-become-gates.md` (Law 13 — the general findings-become-gates ratchet);
both are already ratified, so this task is not blocked on any further ADR work.

### TCB ledger items this task closes

`TCB.md` (the D13 trusted-computing-base ledger) names this task directly as the fix for two
ranked items and folds in three one-line fixes:

- **T9 — oracle environment unpinned** (TCB priority 3-tie): "node/python/nasm/powershell/OS: no
  version recorded or asserted anywhere; `NASM.lean:41-48` fetches `nasm -v` and **discards the
  banner**." This is the same requirement as the D13/TCB pinning discussion above, restated by
  the ledger in its own terms — capture and print all oracle versions, commit the version tuple
  alongside recorded fuzz results.
- **T4 — gate tooling exists but nothing runs it** (TCB priority 2-tie): "`defaultTargets`
  *builds* `check_gates_axioms`; REVIEW.md itself warns building ≠ running." TCB's proposed fix
  is this task plus a **meta-gate fixture**: a planted `sorry`, an unallowlisted `native_decide`,
  a broken `REF:`, and a duplicate markdown heading, each of which must independently turn its
  respective gate red. Include at least one such planted-defect control vector per gate in this
  task's acceptance evidence, not just a clean-tree pass — a gate that has never been observed to
  fail is unverified in the same sense Law 13(4) requires positive/negative controls for any
  world-facing oracle. (TCB also flags `check_refs.py:35-47`'s slugifier has no duplicate-heading
  disambiguation — a `REF:` to the second identically-titled section silently resolves to the
  first; the duplicate-heading control vector above is exactly the case that exposes this.)
- **One-line fixes folded in from TCB's ledger** (its "One-line fixes to fold into TC5/TC9" note):
  (a) `EncodingFuzzer` currently has **no control vectors at all** — zero Law 13(4) compliance,
  the only oracle in the tree with none; add a mandatory positive/negative pair before this task
  is considered complete. (b) Spike1/2 Wasm `Test.lean` prints "100% sound (in-Lean)" and returns
  exit 0 when no Wasm runner is present — the same fail-open shape TC9 audits, but small enough
  to fix as part of wiring this runner rather than waiting on TC9. (c) `GzipFuzzer.lean:84` reads
  a binary `.gz` file as UTF-8 lines, which destroys its own diagnostic output on any divergence
  (the error message itself is corrupted) — a one-line encoding fix, verify by grep before fixing
  since the file has had recent unrelated commits.

## Deliverables & acceptance criteria

- A single entry point — `scripts/run_gates.ps1` (this repo's primary shell is PowerShell on
  Windows) and/or `scripts/run_gates.sh`, or a `lake` script target if that proves cleaner —
  that invokes every gate enumerated above in a defined order, capturing each process's exit
  code **directly** (no pipe/tee in between; see the Merge-Train-2 self-finding above).
- Fail-closed behavior demonstrated, not just claimed: the completion report for this task must
  include evidence that (a) running with NASM absent from PATH aborts the whole run with a
  labeled failure (not a "skipped" line), and (b) the same for node absent. This is the
  control-vector convention this project uses everywhere an oracle touches the outside world
  (Law 13 preference-order item 4) — a gate-runner claim without this demonstrated is not
  credible under this project's own review standard.
- Oracle versions (NASM, node, python) captured and printed/recorded in the run's output.
- A machine-parseable summary (pass/fail per gate, not just a final exit code) so future CI
  tooling (TC6) and humans can see which specific gate failed without re-running everything.
- `docs/REVIEW.md` §4.1 updated to name the runner as the standard way to execute Pillar 1 (per
  the PLAN.md note: "REVIEW.md §4.1 updated at merge to enumerate it").
- Exit code 0 only when every gate above passed; a non-zero exit from any gate propagates to the
  runner's own exit code.
- Completion report includes: the full list of gates actually invoked, their individual exit
  codes, the two fail-closed demonstrations above, and oracle version strings observed on the
  build machine.
- TCB T9/T4 and the three one-line folds above are explicit deliverables, not optional extras:
  oracle version capture (T9); a meta-gate fixture proving each gate can go red (T4, four planted
  defects — sorry / unallowlisted native_decide / broken REF / duplicate heading); EncodingFuzzer
  positive/negative control vectors; Spike1/2 Wasm `Test.lean` no-runner honesty fix; GzipFuzzer
  UTF-8 diagnostic fix.

## Pointers

- `lakefile.toml:1-16` — `defaultTargets`, already includes `check_gates_axioms`; the executable
  names this task must shell out to are the `[[lean_exe]]` blocks below that list:
  `x86_fuzzer` (`lakefile.toml:113-116`), `encoding_fuzzer` (`:104-106`), `wasm_fuzzer`
  (`:118-121`), `test_roundtrip` (`:108-111`), `gzip_fuzzer` (`:147-150`),
  `check_gates_axioms` (`:35-38`).
- `scripts/check_refs.py`, `scripts/check_gates.py`, `scripts/regenerate_references.py` — existing
  Python gates this task must shell out to (verified present in `scripts/`).
- `Gasm/Targets/X86_64/HardwareHarness.lean:281` (`runHardwareBatch`, returns `Except String (List
  HardwareExecutionResult)` — the fail-closed precedent to imitate at the runner level) and
  `:331-336` (the mandatory positive/negative control-vector checks — the runner should treat an
  oracle's own control-vector failure as a run-aborting condition, distinguishable in its report
  from a plain semantic-mismatch failure).
- `docs/REVIEW.md` §4.1 (Pillar 1 gate enumeration) and §4.4 (Gate 1 approval-state-machine
  wording, including the "run from the repository root" caveat) — this task's runner is the
  literal implementation of that enumerated list.
- PLAN.md, "Phase 1 — Mechanical trust fixes" section, the "**Gate runner**" bullet (the original
  scope note this task file supersedes) and the "Merge train 2 (2026-08-27) — LANDED" section's
  final paragraph (the pipe/exit-code self-finding).
- MODEL_DEBT.md's "TCB.md ledger" gaps-register entry (oracle version pinning) and D13 in
  PLAN.md's Decisions section (oracle-environment differential-fuzzer policy) — the governing
  rationale for why this task pins and records tool versions rather than just checking presence.

## Notes

- 2026-08-27: priority 9.5 — gate runner unblocks TC6/TC9/TC10/TC11/TC12/TC13 and closes TCB T4 (priority-2-tie, 'no gate runner — everything manual') and T9; per owner directive this is the task that 'unblocks everything.'
- 2026-08-27 (oracle-debt audit, `docs/ORACLE_DEBT.md` Part 6): status corrected `implementing` → `done`. `scripts/run_gates.py` exists (1027 lines), self-describes as this task's implementation, and its own docstring documents fail-closed oracle detection, direct exit-code capture (no pipe), `--quick`/full modes, and a machine-parseable summary — matching this file's acceptance criteria. Frontmatter had not been updated to reflect the landed state; corrected on inspection, not on a completion report (none was found appended to this file).
