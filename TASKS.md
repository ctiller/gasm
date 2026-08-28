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
board plus the four BAR definitions.

**The status board below is generated output. Do not hand-edit it.** It is derived from
`docs/tasks/*.md` frontmatter by `python scripts/task_frontier.py --regenerate-board`, and
`--check-board` fails when the two disagree. A task's `status:` field is the single source of
truth: to change what the board says, change the task file and regenerate. This replaces the
"keep it in sync by hand when a task's status changes" instruction that stood here until
2026-08-28 — hand-syncing was measured and had failed, with the board wrong about **37 of 81
tasks** (22 tasks had no row at all; 15 rows contradicted their own frontmatter, every one of
them understating progress). Board generation is the one deliverable of
`docs/tasks/TC13-task-dag-tooling.md` landed early; TC13 still owns cycle detection,
reverse-edge derivation, and priority validation.

**A wrong row therefore means a wrong `status:` field, not a wrong board.** Regeneration is
faithful by construction, so where a row disagrees with the tree the defect is in the task
file. Some are known to be stale in exactly that way as of 2026-08-28 — `MH1` reads `ready`
while its deliverables are in the tree and `docs/MEMORY_HOOK.md` §3 documents them as landed.
Those corrections belong to each task's owner and were deliberately not made by the pass that
mechanized this board.

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

- [x] TC1 x86 hygiene branch — fail-closed hardware oracle, xor SF fix → `docs/tasks/TC1-hygiene-branch.md` — after: —
- [x] TC2 Wasm oracle branch — fail-closed control-flow fuzzing, TRAP-laundering fix → `docs/tasks/TC2-wasm-oracle-branch.md` — after: —
- [x] TC3 Law 10 gates — axiom-level native_decide/sorry/axiom gate → `docs/tasks/TC3-law10-gates.md` — after: —
- [x] TC4 Decoder + registry build-gate branch → `docs/tasks/TC4-decoder-registry-gate.md` — after: —
- [x] TC5 Gate runner — single entry point for all gates → `docs/tasks/TC5-gate-runner.md` — after: TC4
- [~] TC6 CI establishment → `docs/tasks/TC6-ci-establishment.md` — after: TC5
- [x] TC7 TCB ledger — trust chosen, not discovered → `docs/tasks/TC7-tcb-ledger.md` — after: —
- [ ] TC8 Trust⇒fuzzer buildout — one validation harness per TCB item → `docs/tasks/TC8-trust-fuzzer-buildout.md` — after: TC7
- [x] TC9 Fail-open audit completion → `docs/tasks/TC9-fail-open-audit.md` — after: —
- [ ] TC10 Continuous fuzzing + regression corpus → `docs/tasks/TC10-continuous-fuzzing-corpus.md` — after: TC5
- [ ] TC11 Mutation-coverage tooling for differential suites → `docs/tasks/TC11-mutation-coverage-tooling.md` — after: TC5
- [ ] TC12 Connection-theorem linter + known twins → `docs/tasks/TC12-connection-theorem-linter.md` — after: TC5
- [ ] TC13 Task-DAG checker — validate docs/tasks/ frontmatter, regenerate TASKS.md's status board → `docs/tasks/TC13-task-dag-tooling.md` — after: TC5
- [ ] TC14 Emitter last-mile connection theorem (PE parser + codeMatches) → `docs/tasks/TC14-emitter-connection-theorem.md` — after: TC4
- [~] TC15 Axiom gate closure coverage (import-closure blind spot) → `docs/tasks/TC15-axiom-gate-closure-coverage.md` — after: —
- [x] TC16 References pipeline integrity (SHA-256 manifest, honest verify) → `docs/tasks/TC16-references-integrity.md` — after: —
- [x] TC17 Vacuity floors — kill zero-vector auto-PASS across all fuzzers → `docs/tasks/TC17-vacuity-floors.md` — after: —
- [ ] TC18 Fuel-exhaustion honesty + Environment dead-field resolution → `docs/tasks/TC18-fuel-and-environment-honesty.md` — after: —
- [ ] TC19 HardwareHarness self-hosting (rebuild oracle machine code from the registry) → `docs/tasks/TC19-harness-self-hosting.md` — after: TC4
- [~] TC20 Wasm emission roundtrip (LEB128 decoder + validator differential) → `docs/tasks/TC20-wasm-emission-roundtrip.md` — after: —
- [x] TC21 doc-facade linter — enforcement-claim vs tree-reality drift → `docs/tasks/TC21-doc-facade-linter.md` — after: —
- [x] TC22 Doc-facade gate gap — fenced lean theorem blocks over nonexistent symbols are invisible to check_doc_facade.py → `docs/tasks/TC22-doc-lean-fence-facade.md` — after: —

- [~] PA1 crc32 pathfinder — contract → asm → kernel ∀-proof → composition sketch → `docs/tasks/PA1-crc32-pathfinder.md` — after: TC4
- [ ] PA2 step-lemma library + composition calculus design doc → `docs/tasks/PA2-step-lemma-composition-design.md` — after: PA1
- [ ] PA3 step-lemma library + composition calculus implementation → `docs/tasks/PA3-step-lemma-composition-impl.md` — after: PA2
- [ ] PA4 capability adoption (Law 11) — Core machinery as mandatory authoring surface → `docs/tasks/PA4-capability-adoption.md` — after: PA2
- [ ] PA5 canonicalizeTrace — causal-stamped observation normal form → `docs/tasks/PA5-canonicalize-trace.md` — after: PA2, N2
- [~] PA6 read-binder contract shape — ∀ read results including partial/EOF → `docs/tasks/PA6-read-binder-contract.md` — after: PA5, N2
- [ ] PA7 VerifiedReactiveProgram — mandatory inner/outer proof pairs for reactive loops → `docs/tasks/PA7-verified-reactive-program.md` — after: PA5
- [ ] PA8 Law 9 migration — Spike5 domain-shrinking fix, then Tier-1 real env quantification → `docs/tasks/PA8-law9-migration.md` — after: PA6
- [ ] PA9 VerifiedProgram as derived theorem — routine contracts + linker facts → `docs/tasks/PA9-verified-program-derived.md` — after: PA3, PA4
- [x] PA10 PNG filter scanline invertibility — lift proven per-byte algebra to universal roundtrip → `docs/tasks/PA10-png-filter-scanline-invertibility.md` — after: —
- [ ] PA11 crc32_empty / adler32_empty — kernel-checked decide, no oracle → `docs/tasks/PA11-trivial-checksum-empty-facts.md` — after: —
- [x] PA12 Wasm trap short-circuit + SLEB128 budget witness — structural proofs, no native_decide → `docs/tasks/PA12-wasm-trap-guard-and-leb128-witness.md` — after: —
- [x] PA13 CRC32 bit-trick lemmas without a SAT certificate — and_one_cases, G_eq_Gbf, xor_byte_shr8 → `docs/tasks/PA13-crc32-bittrick-lemmas-without-sat.md` — after: —
- [x] PA14 G8bf_table structural closure — CRC table/bit-loop identity without a SAT certificate → `docs/tasks/PA14-crc32-table-identity-structural-closure.md` — after: —
- [x] PA15 Fibonacci soundness by loop-invariant induction — replace 91-case native_decide enumeration → `docs/tasks/PA15-fibonacci-loop-invariant-induction.md` — after: —
- [ ] PA16 Zlib/PNG/Gzip codec universal roundtrip soundness — design + structural proof → `docs/tasks/PA16-codec-roundtrip-universal-soundness.md` — after: —
- [ ] PA17 Spike3-Windows and Spike4 route/session domain honesty — beyond Tier-3 "legit" classification → `docs/tasks/PA17-spike3-spike4-domain-honesty.md` — after: PA7, PA8
- [ ] PA18 Small finite-domain DEFLATE bound checks — verify plain decide suffices, drop native_decide → `docs/tasks/PA18-small-domain-decide-migration.md` — after: —

- [ ] MH1 Semantic memory hook — sealed memory field, width API, access descriptors, fault plumbing → `docs/tasks/MH1-semantic-memory-hook.md` — after: —
- [ ] MH2 Memory uop centralization — one provenance-marked cost table, derived per-form uops → `docs/tasks/MH2-memory-uop-centralization.md` — after: MH1
- [ ] MH3 Capability authoring surface v1 — checked programs, erasure, bypass ledger, pathfinder routine → `docs/tasks/MH3-capability-authoring-surface.md` — after: MH1

- [ ] BR1 Borrow index: elaboration-cost measurement, then the capability context and weaving DSL → `docs/tasks/BR1-borrow-index-feasibility.md` — after: MH1
- [b] BR2 Promote MH3's checked program from a fixed frame to a borrow index → `docs/tasks/BR2-borrow-authoring-upgrade.md` — after: BR1, MH3 (blocked on: BR1's Phase 0 measurement must pass its kill criterion, and MH3 must land first — this task changes one type constructor of MH3's surface and keeps the rest verbatim, so it cannot precede it)
- [b] BR3 Cross-thread capability partition and the no-unsynchronized-race theorem → `docs/tasks/BR3-cross-thread-capability-partition.md` — after: BR1, MT2 (blocked on: MT2's multi-threaded machine does not exist (itself blocked on XM1), and cross-thread capability transfer — spawn hands regions to a child, join returns them, a lock acquire grants dynamically — has no design or task anywhere; this task cannot start until there is a machine with more than one thread to state the theorem against)
- [ ] BR4 Provenanced pointer type: region identity, address-free Ptr, and the creation audit → `docs/tasks/BR4-provenanced-pointer.md` — after: MH1
- [b] BR5 Transmogrification: one borrow-with-transformation, the view ledger, and leak-freedom → `docs/tasks/BR5-transmogrification.md` — after: BR4 (blocked on: BR4 — the view ledger and both transformations are stated over the pointer and region-identity types BR4 builds; there is nothing to lend a transformed view of until they exist)
- [b] BR6 Lock invariants: cross-region capability transfer licensed by an atomic word → `docs/tasks/BR6-lock-invariants.md` — after: BR5, MT1, MT2 (blocked on: All three supporting layers are absent: BR5 (the claim mechanism), MT1 (atomics — the tree has zero atomic forms), and MT2 (the memory model — docs/X86_MEMORY_MODEL.md states it has zero Lean). A lock is unsound if any one is missing, so this cannot start until all three land)

- [b] MT1 Atomic primitives: XCHG r64,[m64] with implicit LOCK, plus MFENCE → `docs/tasks/MT1-atomic-primitives.md` — after: MH1 (blocked on: XM1 (TSO ordering vocabulary + machine, filed with docs/X86_MEMORY_MODEL.md §10) — per that design's §6 class 1, the first atomic form and XM1 are one indivisible landing; convert this to an after: [XM1] entry once XM1's task file is stably in-tree)
- [b] MT2 Thread lifecycle and per-thread execution state over XM1's TSO machine → `docs/tasks/MT2-multithreaded-machine-state.md` — after: MH1 (blocked on: XM1 (docs/X86_MEMORY_MODEL.md §2.3) — the two-level TSO state (shared memory + per-thread store buffers), TsoStep/drain, and the single-thread degeneration theorem are XM1's deliverables that this task builds on; convert to after: [XM1] once XM1's task file is stably in-tree)
- [ ] MT3 Causal traces for threads: stampMultiThreaded, sync edges, causal-order equivalence → `docs/tasks/MT3-causal-trace-generalization.md` — after: PA5
- [b] MT4 Emitted-binary litmus battery: SB / MP / SB+MFENCE, reusing XM2's definitions → `docs/tasks/MT4-litmus-battery.md` — after: MT1, MT2, MT3 (blocked on: XM2 (litmus encodings + model outcome enumeration + host silicon harness, filed with docs/X86_MEMORY_MODEL.md §10) — this task consumes XM2's test definitions and enumerated outcome sets rather than re-transcribing them (Law 12); convert to an after: [XM2] entry once XM2's task file is stably in-tree)
- [ ] MT5 Spike 8 Phases A+B: Windows CreateThread + Linux clone spinlock counter, verified → `docs/tasks/MT5-spike8-windows-linux.md` — after: MT4, PA7
- [ ] MT6 Bare-metal SMP bring-up: Stop-and-Design (MP init, trampoline, LAPIC, accel honesty) → `docs/tasks/MT6-baremetal-smp-design.md` — after: MT5

- [~] N1 Win32 API differential harness design doc → `docs/tasks/N1-win32-harness-design.md` — after: —
- [ ] N2 OS1: ReadFile/WriteFile/handle model rebuild vs real OS → `docs/tasks/N2-os1-readfile-writefile-model.md` — after: N1
- [ ] N3 Real socket model (WinSock semantics vs invented hooks) → `docs/tasks/N3-real-socket-model.md` — after: N2
- [ ] N4 End-to-end socket exercise of Spike4 binaries → `docs/tasks/N4-socket-e2e-spike4.md` — after: N3
- [ ] N5 Spike4 re-verified as VerifiedReactiveProgram → `docs/tasks/N5-spike4-reactive-verified.md` — after: N3, PA7
- [ ] N6 Networking buildout: TCP semantics, HTTP/1.1, HTTP/2, protobuf codecs, gRPC server → `docs/tasks/N6-networking-buildout.md` — after: N5
- [ ] N7 Constant-time/secrecy contract class design → `docs/tasks/N7-constant-time-contract-class.md` — after: PA2
- [ ] N8 Fix Spike 4 HTTP Server stack buffer overflow and uninitialized memory read → `docs/tasks/N8-spike4-stack-buffer-overflow.md` — after: N3

- [x] G1 Graphics doc rework per GRAPHICS_PREBUILD_AUDIT top-10 → `docs/tasks/G1-graphics-doc-rework.md` — after: —
- [ ] G2 Synchronization DSL design (Vulkan memory model, happens-before, RAW) → `docs/tasks/G2-synchronization-dsl.md` — after: G1
- [ ] G3 FP kernel DSL design (Deterministic Shader Profile) → `docs/tasks/G3-fp-kernel-dsl.md` — after: G1
- [ ] G4 GPU differential-validation harness design → `docs/tasks/G4-gpu-differential-harness.md` — after: G1
- [ ] G5 SPIR-V emitter + Lean validator + registry-style shader gate → `docs/tasks/G5-spirv-emitter-validator.md` — after: G2, G3
- [ ] G6 Vulkan host model + GPU capability mapping → `docs/tasks/G6-vulkan-host-model.md` — after: G2, PA4
- [ ] G7 Spike 6: headless parametric compute to PNG → `docs/tasks/G7-spike6-headless-compute.md` — after: G4, G5, G6, PA5
- [ ] G8 GPU/PCIe cost models + calibration → `docs/tasks/G8-gpu-pcie-cost-models.md` — after: G7, F2
- [ ] G9 Spike 7 design: windowed swapchain, multi-loop reactive contracts → `docs/tasks/G9-spike7-design.md` — after: G7, PA7

- [ ] F1 RDTSC hardware harness (wsc-technique port; containment + rank criterion) → `docs/tasks/F1-rdtsc-harness.md` — after: TC4
- [~] F2 Calibration-data governance (MODEL_DEBT E5 — the third reference class) → `docs/tasks/F2-calibration-data-governance.md` — after: —
- [ ] F3 Staged model calibration vs silicon (uop/latency, dependency chains, branch model, hierarchy) → `docs/tasks/F3-staged-model-calibration.md` — after: F1, F2
- [ ] F4 Parametric cost functions (loop annotations to closed-form polynomials on contracts) → `docs/tasks/F4-parametric-cost-functions.md` — after: F3, PA2
- [ ] F5 Composable cost views (native precision + µs/ms architect view + validated conversions) → `docs/tasks/F5-composable-cost-views.md` — after: F3
- [ ] F6 zlib-to-infinity epic — optimizing zlib against the state of the art → `docs/tasks/F6-zlib-to-infinity.md` — after: PA8, PA4, F4, TC12

- [~] B1 Build-perf iteration 2 — Instructions.lean aggregator sharding → `docs/tasks/B1-build-perf-iteration2.md` — after: TC4
- [~] B2 Linux target foundation & strategy — ABI, ELF64 linker, syscall semantics, and runner plan → `docs/tasks/B2-linux-strategy.md` — after: TC4
- [x] B3 Stage B decoder modularization (per-instruction tryDecode co-located with encode) → `docs/tasks/B3-stage-b-decoder-modularization.md` — after: TC4, B1
- [ ] B4 Pre-index instruction byte offsets to eliminate O(M * N) re-encoding in simulator → `docs/tasks/B4-instruction-index-lookup.md` — after: TC4
- [x] B7 Enforce WebAssembly trap semantics on out-of-bounds memory access and validate memory limits → `docs/tasks/B7-wasm-oob-trap-and-limits.md` — after: TC2

- [ ] MD1 Model/spec debt intake queue → `docs/tasks/MD1-model-spec-debt-intake.md` — after: —

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
