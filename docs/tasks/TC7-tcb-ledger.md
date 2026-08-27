---
id: TC7
title: TCB ledger — trust chosen, not discovered
status: done
blocked_on: ""
after: []
related: []
bar: ""
track: trust-core
priority: 7.0
priority_set: 2026-08-27T18:25:47Z
design: "predates-discipline"
design_review: "predates-discipline"
date: 2026-08-27
---

# TC7: TCB ledger — trust chosen, not discovered

## Context

D13 (PLAN.md Decisions) states the policy this task exists to execute: **"everything
trusted-but-unprovable (environment, hardware, APIs, tools) gets a differential fuzzer
validating our model of it (TCB.md ledger; Opus research running)."** MODEL_DEBT.md inventories
what the machine/OS *models* omit (correctness and performance debt — things we got wrong or
left out); TCB.md is the companion ledger for a different kind of gap — things this project has
*chosen* to trust rather than prove (the Lean kernel, the toolchain, external tools, the
silicon, the reference-ingestion pipeline) and asks, for each: is this trust irreducible, or
can it be shrunk by proof or validated by a differential fuzzer?

### This research task's own status is more subtle than a single state value

TASKS.md's own DAG entry marks TC7 `[~]` ("running") at time of writing — "TCB ledger (Opus
research running; fold into TCB.md + tasks here)." This task file's frontmatter status is set
to `designing` because **the concrete research deliverable this task exists to produce —
`TCB.md` itself — already exists, is committed at repo root, and is complete**: it opens with
"Opus audit 2026-08-27 @ 1cf58d5" and closes with a "RANKED TOP 8" table and an "Irreducible vs
shrinkable" summary. In that sense the research half of TC7 is *done*. What justifies
`designing` rather than `done` is that TCB.md's own actionable items have not themselves been
turned into dispatched, scoped work yet at the time these task files were written — that
translation is what `designing` is meant to capture (working notes accumulating toward a
design, per the task-lifecycle convention), and it is in fact already substantially complete:
**TCB.md's items have already been spun out into TC14 through TC20** (one task file per
high-priority TCB item — you do not need to write or duplicate those; they exist under
`docs/tasks/` already, e.g. `TC14-emitter-connection-theorem.md` for T5, `TC15-axiom-gate-
closure-coverage.md` for T2), **plus folds into TC5 (gate runner — T9 oracle pinning, T4 gate-
tooling-exists-but-nothing-runs-it) and into two networking-track tasks, N1/N2 (the Win32
differential harness that will validate C1-class OS-model debt referenced throughout TCB.md)**.
A fresh agent should treat TC7 as: research complete, ledger committed, decomposition into
concrete tasks already underway (TC14-TC20 + folds) — what remains under TC7 itself, if
anything, is any TCB item that did *not* get a dedicated task or fold and needs one, and keeping
the ledger itself current as new trust-chosen items are discovered.

### The ledger's own headline numbers (why this matters)

TCB.md's own framing: 170 project `.lean` modules, but only 138 reachable from umbrella import
roots — **32 modules are invisible to the axiom gate that is supposed to be the load-bearing
Law-10 enforcement mechanism** (this is T2, the ledger's own #2-ranked item). 92 theorems exist
tree-wide, and **zero** of them cover the 1,255 lines of `Gasm/Targets/Windows/*.lean` +
`Wasm/{Linker,Binary}.lean` — i.e. the code that actually turns verified instructions into bytes
an OS or engine will run has no proof coverage at all (T5, the ledger's #1-ranked item, "THE
EMITTER LAST MILE"). The allowlist carrying Law 10's escape hatches has 55 entries (36
grandfathered, 13 axiom-only, 6 finite-forall). `references/` holds 1,048 files with **zero
hashes** — Law 4's "authoritative reference" claim currently rests on directory-exists and
file-count checks, not content integrity (T8). There is no CI (T4) — every one of these findings
is presently caught, if at all, by a human or agent remembering to run the right script by
hand.

### Irreducible vs. shrinkable — the ledger's central distinction

TCB.md's closing framing is the one a fresh agent should internalize before touching any T-item:
**irreducible** trust (the Lean kernel/toolchain — T1; the silicon itself — T11; the real
Windows loader, V8, and CPython as external behaviors — T6/T9) gets Law 13(4)-style controls
and recorded provenance, never a proof, because there is nothing to prove *against* — the thing
being trusted *is* the ground truth. **Shrinkable** trust (T2, T3, T4, T5, T7, T10, T12, T13) is
missing *code*, not accepted risk — and per Law 13's stated preference order, proof beats
fuzzer wherever an item is shrinkable, since a differential fuzzer validating a model is a
weaker guarantee than the model being provably connected to what it claims to model. T5 (the
emitter) and T10 (HardwareHarness's hand-written machine code) are called out explicitly as
"genuine self-hosting opportunities" — cases where the thing generating the trusted artifact
could instead *be* the mechanism proven correct, which is a strictly stronger move than fuzzing
the artifact it produces.

## Deliverables & acceptance criteria

The primary deliverable — `TCB.md` at repo root — already exists and is complete; do not
duplicate or rewrite it. Remaining work under this task, if a fresh agent finds any TCB item
without a corresponding dedicated task or fold-in:

- Confirm every T1-T13 item in TCB.md maps to either: a dedicated task (TC14-TC20), a fold into
  an existing task (TC5, N1/N2), an explicit "irreducible, controls-only" disposition (T1, T11,
  T6, T9), or is itself picked up generically by TC8 (the per-TCB-item validation harness
  buildout this task's completion unblocks — TC8's `after: [TC7]` edge exists precisely because
  TC8 cannot be scoped without this ledger).
- If new trust-chosen items are discovered after TCB.md's 2026-08-27 audit (e.g. during TC8's
  per-item harness work, or a future BAR), they get appended to TCB.md rather than left to
  accumulate in scattered task Notes sections — TCB.md is the durable ledger; task files are
  where the work against each item happens.
- Any TCB item found to lack a plausible home in the current task list should be flagged
  explicitly (not silently dropped) — the completion report for this task, if further work is
  dispatched under it, should name any such orphaned item.

## Pointers

- `TCB.md` (repo root, full file) — the deliverable itself; read directly, it is written to be
  self-contained (per its own header: "Feeds docs/tasks/ (TC7→TC8+)").
- `docs/tasks/TC14-emitter-connection-theorem.md` through `docs/tasks/TC20-wasm-emission-
  roundtrip.md` — the already-spun-out per-item tasks (T5, T2, T8-adjacent references
  integrity, T11-b vacuity floors, T12 fuel/environment honesty, T10 harness self-hosting, T7
  Wasm emission roundtrip respectively — confirm exact T-item-to-task mapping by reading each
  file's own Context, since this summary is illustrative, not authoritative).
- `docs/tasks/TC5-gate-runner.md` — where T9 (oracle version pinning) and T4 (gate tooling
  exists but nothing runs it) are explicitly folded in as deliverables, per that file's own
  "TCB ledger items this task closes" section.
- `docs/tasks/N1-win32-harness-design.md` (and its downstream N2) — where TCB's C1-class OS-
  model debt (referenced throughout TCB.md's T6/T9 discussion) gets its differential
  validation.
- PLAN.md, "Model debt ledger" section — records the Opus researcher's original brief that
  produced both MODEL_DEBT.md and (per D13) the TCB.md research this task tracks; also PLAN.md's
  D13 decision text itself.
- `docs/adr/NNNN-tcb-ledger-and-differential-fuzzing.md` (expected — cite once the concurrently-
  drafted ADR set stabilizes; do not block on it, D13 already ratifies the policy this task
  executes).

## Notes

- 2026-08-27: priority 7.0 — TCB ledger already landed as a complete self-contained ledger (status: designing, near-closed) and is the direct source for TC14-TC20's priorities — foundational to this whole backfill.

_(2026-08-27) TCB.md landed as a complete, self-contained ledger on this date; its actionable
items are already substantially decomposed into TC14-TC20 plus folds into TC5/N1/N2 (see
Context above). This task's `designing` status reflects that the research-to-task translation
is essentially complete but not yet formally closed out — a fresh agent picking this up should
first check whether all T1-T13 items have a task home before doing new research, per the
task-lifecycle convention's guidance to consolidate before implementing further._
