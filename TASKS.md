# TASKS — the grind list (happens-after DAG)

> Operating mode (Craig, 2026-08-27): phasing is advisory; this DAG is the real plan.
> Each task lists `after:` edges (happens-after). Grind through ready tasks; **BARS**
> are the points worth a deep re-review by fresh Opus agents (replaces per-phase D10).
> Status: [x] done · [~] designing/design-review/implementing · [ ] ready (deps met) · [b] blocked (named).
> Decisions/ledgers/history live in PLAN.md, MODEL_DEBT.md, GRAPHICS_PREBUILD_AUDIT.md,
> TCB.md. Repair-epic exit: **we trust the system enough that spec & model
> review is something we do, implementation review is something we trust mechanically.**

## Where the substance lives

As of 2026-08-27 this file is a thin index. Every task's full brief — context, dependency
rationale, deliverables/acceptance criteria, code pointers, and its own running `## Notes` log —
lives in `docs/tasks/<file>.md`, one file per task, each self-contained enough that a fresh agent
can execute it without this project's conversational history. This file is now just the status
board plus the four BAR definitions. **Once `TC13` (task-DAG checker/regenerator) lands, the
status board below becomes generated output** — it will be regenerated mechanically from
`docs/tasks/*.md` frontmatter rather than hand-edited; until then, keep it in sync by hand when a
task's status changes.

## Task lifecycle (governs every file in `docs/tasks/`)

Every task file carries YAML frontmatter (`id`, `title`, `status`, `blocked_on`, `after`,
`related`, `bar`, `track`, `priority`, `priority_set`, `design`, `design_review`, `date`)
followed by prose sections (`## Context`,
`## Deliverables & acceptance criteria`, `## Pointers`, `## Notes`). `after:` edges are the only
place dependency information lives — a task's reverse edges ("what does this unblock") are
deliberately *not* duplicated in frontmatter, since that would be a second, driftable copy of the
same graph (Law 12's single-source-of-truth spirit, applied to the DAG itself); derive them by
searching other files' `after:` lists, or use `TC13`'s checker once it exists.

**Status enum**: `blocked | ready | designing | design-review | implementing | done`.

1. **Notes accumulate; nothing there is authoritative.** Every task file's `## Notes` section is
   append-only and dated — research findings, review feedback, constraints discovered mid-work,
   dead ends. Anyone may append.
2. **Before implementation begins, Notes are consolidated into a design.** For a task that shapes
   models, specs, contracts, or laws (Law-5-class, per `docs/REVIEW.md` Law 5), that means a real
   design doc under `docs/` — the task file's `design:` field then holds that path. For a smaller
   mechanical task, consolidation means a `## Design` section inline in the task file itself,
   which supersedes the Notes it was distilled from; `design:` then holds the literal string
   `inline`. Implementation dispatches reference the design, never raw Notes — a task with
   implementation underway but no design is a process violation. Already-done tasks that predate
   this discipline are backfilled honestly as `design: predates-discipline` rather than having a
   design invented retroactively.
3. **Law-5-class designs get a design review before any implementation dispatch.** This is a
   distinct, mandatory stage: fresh reviewer agents evaluate the design doc against the ratified
   lenses (`docs/VISION.md`, `docs/REVIEW.md`'s laws, the observation standard in
   `docs/EQUIVALENCE_PROOFS.md` §1.1 / `docs/SYSTEM_EFFECTS.md` §6) *before* implementation is
   dispatched — a design review reads pages, an implementation review reads thousands of lines,
   and findings are cheapest before code exists (`GRAPHICS_PREBUILD_AUDIT.md` is the exemplar: it
   caught an unbuildable trace design, a spec-forbidden bit-exactness claim, and a
   layout-FSM-instead-of-happens-after sync model before a line of graphics Lean existed).
   Implementation review is then expected to be mostly mechanical (gates), per this project's
   exit criterion. The `design_review:` field holds `""` (not yet reviewed), `"approved <date>"`,
   or `"waived-mechanical"` (small mechanical tasks may waive a fresh review). Already-done tasks
   predating this discipline are backfilled as `design_review: predates-discipline`.
4. **The status progression**: `ready → designing → design-review → implementing → done`, with
   `blocked` interrupting at any point pending an external decision (`blocked_on` names it). A
   task with `status: implementing` or `status: done` whose `design:` is a real `docs/` path
   (Law-5-class) must have a non-empty `design_review` — that combination with an empty
   `design_review` is a process violation `TC13`'s checker will eventually flag mechanically.
5. **`priority` and `related` extend the schema (2026-08-27) for leverage ranking.** `priority`
   is a float, 0.0–10.0 convention, for each task's intrinsic importance — sourced honestly from
   the record (TCB.md's and MODEL_DEBT.md's ranked/TOP-10 items, PLAN.md's pull-forward calls,
   the owner's stated eagerness for a track, `blocked_on`-an-owner-decision pushing a task low
   until it clears) rather than invented fresh per file; every file's `## Notes` carries a dated
   one-line rationale for its value. Priority is deliberately not static: `priority_set` (an
   ISO-8601 datetime, stamped whenever `priority` is set or re-triaged) lets a derived
   `effective_priority = priority + 1.0 × hours-since(priority_set)` age upward at read time, so
   a merely-important task already in the queue cannot be permanently outranked by a
   once-more-urgent one nobody ever revisits — bump `priority_set` (and `priority`, if warranted)
   together when deliberately re-triaging a task; that is the only sanctioned way to re-rank it.
   `related: [ids]` is a non-dependency linkset — genuinely informative association, not
   build-order — stored at whichever file is its natural home (a reader should treat it as
   symmetric; don't mirror every link into both files). `scripts/task_frontier.py` reads all of
   this to rank actionable tasks by leverage (PageRank over the happens-after DAG, personalized
   by effective priority, with `related` contributing lower-weight symmetric edges); `TC13`'s
   planned checker may absorb or supersede its validation pass, per that tool's own docstring.

## Status board

- [x] TC1 hygiene branch (fail-closed HW oracle, xor fix) → `docs/tasks/TC1-hygiene-branch.md` — after: —
- [x] TC2 Wasm oracle branch (fail-closed, discriminating cases) → `docs/tasks/TC2-wasm-oracle-branch.md` — after: —
- [x] TC3 Law 10 gates (source pre-check + FQN axiom-totality) → `docs/tasks/TC3-law10-gates.md` — after: —
- [~] TC4 decoder + registry build-gate branch → `docs/tasks/TC4-decoder-registry-gate.md` — after: — (fix cycle landed on integration branch (7194c2a); on main only after merge train 3 ships)
- [ ] TC5 gate-runner: single entry point for all gates → `docs/tasks/TC5-gate-runner.md` — after: TC4
- [~] TC6 CI establishment → `docs/tasks/TC6-ci-establishment.md` — after: TC5 (location decision landed: GitHub Actions, docs/CI.md + .github/workflows/; not [x] since TC6's own acceptance bar wants TC5's single entry point, which hasn't landed on this branch)
- [~] TC7 TCB ledger → `docs/tasks/TC7-tcb-ledger.md` — after: —
- [ ] TC8 trust⇒fuzzer buildout → `docs/tasks/TC8-trust-fuzzer-buildout.md` — after: TC7
- [ ] TC9 fail-open audit completion → `docs/tasks/TC9-fail-open-audit.md` — after: —
- [ ] TC10 continuous fuzzing + regression corpus → `docs/tasks/TC10-continuous-fuzzing-corpus.md` — after: TC5
- [ ] TC11 mutation-coverage tooling for differential suites → `docs/tasks/TC11-mutation-coverage-tooling.md` — after: TC5
- [ ] TC12 connection-theorem linter + known twins → `docs/tasks/TC12-connection-theorem-linter.md` — after: TC5
- [ ] TC13 task-DAG checker (validates docs/tasks/, regenerates this board) → `docs/tasks/TC13-task-dag-tooling.md` — after: TC5
- [ ] TC14 emitter last-mile connection theorem (TCB T5) → `docs/tasks/TC14-emitter-connection-theorem.md` — after: TC4
- [ ] TC15 axiom gate closure coverage (TCB T2) → `docs/tasks/TC15-axiom-gate-closure-coverage.md` — after: —
- [ ] TC16 references pipeline integrity (TCB T8) → `docs/tasks/TC16-references-integrity.md` — after: —
- [ ] TC17 vacuity floors across all fuzzers (TCB T11-b) → `docs/tasks/TC17-vacuity-floors.md` — after: —
- [ ] TC18 fuel-exhaustion honesty + Environment dead fields (TCB T12) → `docs/tasks/TC18-fuel-and-environment-honesty.md` — after: —
- [ ] TC19 HardwareHarness self-hosting (TCB T10) → `docs/tasks/TC19-harness-self-hosting.md` — after: TC4
- [ ] TC20 Wasm emission roundtrip (TCB T7) → `docs/tasks/TC20-wasm-emission-roundtrip.md` — after: —
- [ ] TC21 doc-facade linter (enforcement-claim vs tree-reality drift) → `docs/tasks/TC21-doc-facade-linter.md` — after: —

**BAR 1 — after TC4+TC5: full-codebase fresh-agent deep re-review** (see BAR definitions below).

- [ ] PA1 crc32 pathfinder → `docs/tasks/PA1-crc32-pathfinder.md` — after: TC4
- [ ] PA2 step-lemma library + composition calculus design doc → `docs/tasks/PA2-step-lemma-composition-design.md` — after: PA1
- [ ] PA3 step-lemma + composition implementation → `docs/tasks/PA3-step-lemma-composition-impl.md` — after: PA2
- [ ] PA4 capability adoption (Law 11) → `docs/tasks/PA4-capability-adoption.md` — after: PA2
- [ ] PA5 canonicalizeTrace → `docs/tasks/PA5-canonicalize-trace.md` — after: PA2, N2
- [ ] PA6 read-binder contract shape → `docs/tasks/PA6-read-binder-contract.md` — after: PA5, N2
- [ ] PA7 VerifiedReactiveProgram (inner/outer pairs) → `docs/tasks/PA7-verified-reactive-program.md` — after: PA5
- [ ] PA8 Law 9 migration → `docs/tasks/PA8-law9-migration.md` — after: PA6, PA7
- [ ] PA9 VerifiedProgram as derived theorem → `docs/tasks/PA9-verified-program-derived.md` — after: PA3, PA4

**BAR 2 — after PA1: full-codebase fresh-agent deep re-review** (see BAR definitions below).

- [ ] N1 Win32 API differential harness design doc → `docs/tasks/N1-win32-harness-design.md` — after: —
- [ ] N2 OS1: ReadFile/WriteFile/handle model rebuild vs real OS → `docs/tasks/N2-os1-readfile-writefile-model.md` — after: N1
- [ ] N3 real socket model → `docs/tasks/N3-real-socket-model.md` — after: N2
- [ ] N4 end-to-end socket exercise of Spike4 binaries → `docs/tasks/N4-socket-e2e-spike4.md` — after: N3
- [ ] N5 Spike4 re-verified as VerifiedReactiveProgram → `docs/tasks/N5-spike4-reactive-verified.md` — after: N3, PA7
- [ ] N6 networking buildout (TCP/HTTP/HTTP2/protobuf/gRPC) → `docs/tasks/N6-networking-buildout.md` — after: N5
- [ ] N7 constant-time/secrecy contract class design → `docs/tasks/N7-constant-time-contract-class.md` — after: PA2
- [ ] N8 fix Spike 4 HTTP stack buffer overflow + uninitialized read → `docs/tasks/N8-spike4-stack-buffer-overflow.md` — after: N3

**BAR 3 — before N6 buildout starts: full-codebase fresh-agent deep re-review** (see BAR definitions below).

- [ ] G1 graphics doc rework per GRAPHICS_PREBUILD_AUDIT top-10 → `docs/tasks/G1-graphics-doc-rework.md` — after: —
- [ ] G2 synchronization DSL design → `docs/tasks/G2-synchronization-dsl.md` — after: G1
- [ ] G3 FP kernel DSL design (Deterministic Shader Profile) → `docs/tasks/G3-fp-kernel-dsl.md` — after: G1
- [ ] G4 GPU differential harness design → `docs/tasks/G4-gpu-differential-harness.md` — after: G1
- [ ] G5 SPIR-V emitter + Lean validator + registry-style ∀-shader gate → `docs/tasks/G5-spirv-emitter-validator.md` — after: G2, G3
- [ ] G6 Vulkan host model + GPU capability mapping → `docs/tasks/G6-vulkan-host-model.md` — after: G2, PA4
- [ ] G7 Spike 6: headless parametric compute → PNG → `docs/tasks/G7-spike6-headless-compute.md` — after: G4, G5, G6, PA5
- [ ] G8 GPU/PCIe cost models + calibration → `docs/tasks/G8-gpu-pcie-cost-models.md` — after: G7, F2
- [ ] G9 Spike 7 design (windowed swapchain) → `docs/tasks/G9-spike7-design.md` — after: G7, PA7

**BAR 4 — before G7 implementation: full-codebase fresh-agent deep re-review** (see BAR definitions below).

- [ ] F1 RDTSC harness → `docs/tasks/F1-rdtsc-harness.md` — after: TC4
- [ ] F2 calibration-data governance → `docs/tasks/F2-calibration-data-governance.md` — after: —
- [ ] F3 staged model calibration vs silicon → `docs/tasks/F3-staged-model-calibration.md` — after: F1, F2
- [ ] F4 parametric cost functions → `docs/tasks/F4-parametric-cost-functions.md` — after: F3, PA2
- [ ] F5 composable cost views → `docs/tasks/F5-composable-cost-views.md` — after: F3
- [ ] F6 zlib-to-infinity epic → `docs/tasks/F6-zlib-to-infinity.md` — after: PA8, PA4, F4, TC12

- [x] B1 build-perf iteration 2: Instructions.lean aggregator sharding → `docs/tasks/B1-build-perf-iteration2.md` — after: TC4
- [~] B2 Linux target foundation & strategy → `docs/tasks/B2-linux-strategy.md` — after: TC4 (design in docs/TARGETS/LINUX.md)
- [ ] B3 Stage B decoder modularization → `docs/tasks/B3-stage-b-decoder-modularization.md` — after: TC4, B1
- [ ] B4 pre-index instruction byte offsets in simulator → `docs/tasks/B4-instruction-index-lookup.md` — after: TC4
- [x] B7 Wasm OOB trap semantics + memory limits → `docs/tasks/B7-wasm-oob-trap-and-limits.md` — after: TC2

- [ ] MD1 Model/spec debt intake queue (standing triage, `MODEL_DEBT.md`) → `docs/tasks/MD1-model-spec-debt-intake.md` — after: —

## The four BARs

Per `docs/adr/0010-bar-triggered-deep-re-reviews.md`: a BAR's *trigger* is a milestone on the task
DAG, but its **scope is always the entire codebase, never just the recently-landed work**. Each
BAR dispatches a fresh Opus agent (or agents) with no access to prior review conclusions beyond
`PLAN.md`/`TASKS.md`/the ledgers themselves (read as the *claimed* state, to be checked against
reality, not trusted as-is) to redo the deep codebase review from scratch and report: (a) drift
between docs/laws/ADRs and code reality anywhere in the tree; (b) whether recently-merged work's
claimed outcomes actually hold in the merged tree; (c) new findings, ranked, across the whole
codebase; (d) a tracking verdict against the plan (on/off course); (e) the convergence metric —
what fraction of findings are right-theorem questions vs. mechanical catches (`docs/VISION.md`
§2's north star). Narrowing a BAR to "re-review what just landed" is a process violation of the
ADR — that scoped check is what per-branch adversarial review (D6,
`docs/adr/0007-worktree-agent-workflow-and-adversarial-review.md`) already does; a BAR
exists to catch what scoped review structurally cannot: unknown-unknowns, cross-branch
interactions, and rot in corners nothing recent touched.

- **BAR 1** — triggers after `TC4`+`TC5` land.
- **BAR 2** — triggers after `PA1` lands.
- **BAR 3** — triggers before `N6` (networking buildout) implementation begins.
- **BAR 4** — triggers before `G7` (Spike 6) implementation begins.
