---
id: TC13
title: Task-DAG checker — validate docs/tasks/ frontmatter, regenerate TASKS.md's status board
status: ready
blocked_on: ""
after: [TC5]
related: []
bar: ""
track: trust-core
priority: 6.5
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# TC13: Task-DAG checker — validate docs/tasks/ frontmatter, regenerate TASKS.md's status board

## Context

This task exists because of a principle the owner stated directly while this very `docs/tasks/`
conversion was being carried out: **the plan itself should be mechanically checkable, like
everything else in this repository.** `TASKS.md` and `docs/tasks/*.md` are, as of this
conversion, a hand-maintained graph encoded as YAML frontmatter across ~50-plus files. A
hand-maintained graph rots exactly the way hand-maintained anything rots in this codebase: a
dangling `after:` reference to a renamed/deleted task, a cycle introduced by an careless edit, a
duplicate `id:` from a copy-pasted file, or a `status:` typo that silently falls outside the
enumerated set — none of these currently fail anything. Per Law 13 ("Findings Become Gates"),
that is itself the finding: the DAG is a first-class artifact of this repository's trust
apparatus (BARs are scheduled off it; `after:` edges gate what a fresh agent is allowed to pick up
next) and it currently has zero mechanical protection.

Do **not** build this script now — this task file specifies it for a future dispatch. (Per the
task-lifecycle convention: this is a genuinely small mechanical task, so its own eventual `##
Design` section, written inline in this file, is sufficient — no separate `docs/` design doc is
required, and `design_review` may be recorded as `waived-mechanical` once that section lands.)

### Why this sits after TC5, not before

TC5 (gate runner) is the single entry point every mechanical check funnels through. This task's
checker is one more thing TC5's runner should invoke once it exists, so sequencing this after TC5
avoids building a second, competing entry point. It is a soft dependency, not a hard blocker of
authorship — the checker's logic can be written independently of TC5 landing first, but wiring it
into "the" gate list should wait for TC5's runner to exist.

### The status/design/design_review lifecycle this checker enforces

Over the course of this same `docs/tasks/` conversion, the owner ratified a four-part task
lifecycle discipline that every file in this directory follows (see also the "Task lifecycle"
section this conversion added to `TASKS.md`'s header):

1. **Notes accumulate, but are never authoritative.** Every task file has a `## Notes` section
   that is strictly append-only and dated — research findings, review feedback, constraints
   discovered mid-work, dead ends. Anyone (agent or human) may append; nothing there is a
   decision of record.
2. **Before implementation, Notes are consolidated into a design.** For a task whose work shapes
   models, specs, contracts, or laws (a "Law-5-class" task, in the sense of `docs/REVIEW.md` Law
   5), consolidation means authoring a real `docs/` design doc, and the task file's `design:`
   field then holds that doc's path. For a smaller mechanical task, consolidation means writing a
   `## Design` section directly in the task file, which then *supersedes* the Notes it was
   distilled from (Notes are not deleted — they're superseded, in keeping with Law 12's "single
   source of truth, other forms derived" spirit) and the `design:` field holds the literal string
   `inline`.
3. **Before implementation, Law-5-class designs get a design review.** This is a distinct,
   mandatory stage — fresh reviewer agents evaluate the design doc against the ratified lenses
   (`docs/VISION.md`, `docs/REVIEW.md`'s laws, the observation standard in
   `docs/EQUIVALENCE_PROOFS.md` §1.1 / `docs/SYSTEM_EFFECTS.md` §6) **before any implementation
   dispatch is written**, on the principle that a design review reads pages while an
   implementation review reads thousands of lines — findings are cheapest before code exists. The
   graphics pre-build audit (`GRAPHICS_PREBUILD_AUDIT.md`, feeding G1 onward) is the exemplar:
   it caught an unbuildable trace design, a spec-forbidden bit-exactness claim, and a
   layout-FSM-instead-of-happens-after synchronization model, all before a line of graphics Lean
   existed. A mechanical task may instead record `design_review: waived-mechanical` — no fresh
   review is required for work that doesn't shape models/specs/contracts/laws.
4. **The status enum reflects all of this**: `blocked | ready | designing | design-review |
   implementing | done`. A task moves `ready → designing` when someone starts consolidating its
   Notes; `designing → design-review` once a design doc/section exists and (for Law-5-class work)
   a fresh reviewer is evaluating it; `design-review → implementing` once that review approves (or
   is waived); `implementing → done` on completion. `blocked` can interrupt at any point pending
   an external decision (`blocked_on` names it).

This task's checker is the mechanical enforcement of that whole lifecycle, not just of the graph
edges.

## Deliverables & acceptance criteria

A checker script (language/location left to the implementing agent — a Python script alongside
`scripts/check_refs.py`/`scripts/check_gates.py` is the natural fit given this repo's existing
tooling conventions) that:

- Parses YAML frontmatter from every file in `docs/tasks/*.md`.
- **Fails** (non-zero exit, naming the specific file and problem) on: a dangling `after:`
  reference (an id that does not exist as some file's `id:`), a dependency cycle anywhere in the
  graph, a duplicate `id:` across two files, an `id:` that doesn't match its own filename
  convention, and any `status:` value outside `{blocked, ready, designing, design-review,
  implementing, done}`.
- **Fails** on the lifecycle rule: a task whose `status` is `implementing` or `done` AND whose
  `design:` field is a `docs/` path (i.e., genuinely Law-5-class, not the literal `inline` or the
  literal `predates-discipline`) must have a non-empty `design_review` field (`"approved <date>"`
  or `"waived-mechanical"`); a task in that same status/design combination with an empty
  `design_review` fails.
- **Fails** on a `status: blocked` file with an empty `blocked_on`.
- Computes and prints the current **ready set** (tasks whose every `after:` edge points at a
  `status: done` file, themselves not already `done`/`blocked`) — this is the practical payoff:
  a fresh agent or the owner can ask "what can I pick up right now" and get a mechanical answer
  instead of re-deriving it from the prose.
- **Regenerates `TASKS.md`'s status-board section** from the frontmatter (one line per task:
  `[x]/[~]/[ ]/[b] ID title → docs/tasks/<file>.md — after: <deps>`, matching this conversion's
  format) so that hand-editing the board becomes unnecessary and, per this task's own principle,
  actively discouraged — `TASKS.md`'s header should say so once this lands (this conversion's
  version of `TASKS.md` already notes "TC13 makes this section generated thereafter" in
  anticipation).
- Control vectors for the checker itself, per Law 13(4)'s world-facing-oracle discipline extended
  to a build-time linter (Law 13(3) territory — a build-failing check): a planted dangling
  reference, a planted cycle, and a planted duplicate `id:` must each be demonstrated to turn the
  checker red before this task's completion report claims the checker works.
- Wired into TC5's gate list once both have landed (a note in TC5's file, or a follow-up edit to
  it, rather than a new dependency edge — `TASKS.md`/`docs/tasks/` deliberately keep `after:`
  edges to genuine prerequisites, not every task that happens to reference another).

## Pointers

- `docs/tasks/*.md` — the frontmatter schema this checker validates is defined by this very
  conversion; read a handful of files across tracks (e.g. `TC5-gate-runner.md`,
  `PA1-crc32-pathfinder.md`) to see the schema in practice before writing the parser.
- `TASKS.md` — the status-board section this task regenerates, and the "Task lifecycle" header
  text this task file's Context section paraphrases; keep the two in sync if either changes.
- `scripts/check_refs.py`, `scripts/check_gates.py` — existing precedent for this repo's
  Python-linter style (fail-closed parsing, clear per-violation messages) to imitate.
- `docs/REVIEW.md` Law 5 (stop-and-design), Law 12 (single source of truth — the regenerated
  status board is this task's own application of "derive, don't duplicate"), Law 13 (findings
  become gates — this entire task is a Law-13 response to the DAG having no mechanical
  protection).

## Notes

- 2026-08-27: priority 6.5 — task-DAG tooling keeps TASKS.md's status board honest mechanically — this very backfill (priority/related) is exactly the class of drift TC13 would eventually validate; noted directly in scripts/task_frontier.py's docstring.

_(none yet — first entries append here as work begins; per this file's own subject matter,
consolidate into an inline `## Design` section before implementation starts, and mark
`design_review: waived-mechanical` once that section lands.)_
