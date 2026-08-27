# 0027. Planning Output Lives Under `docs/`

## Status

Accepted, 2026-08-27. (PLAN.md D19.)

## Context

Several planning-task deliverables (design docs, architecture audits, model/trust
ledgers) had accumulated at the repository root — `MODEL_DEBT.md`, `TCB.md`,
`GRAPHICS_PREBUILD_AUDIT.md`, `PLAN.md`, `TASKS.md` — originally placed there to keep
process paperwork out of `check_refs.py`'s unreferenced-markdown-section backlog, since
`docs/` is the surface that script indexes as the design-spec corpus. That rationale
stops holding once a backlog-exclusion mechanism exists for directories that need to be
inside `docs/` but outside the backlog count (as is being added for `docs/adr/` and
`docs/tasks/`), leaving root-placement as an arbitrary inconsistency rather than a
principled choice.

## Decision

The owner's own words, in full: "planning tasks: the output goes into docs/."

## Consequences

Every planning task's deliverable is written under `docs/`, not at the repository root.
In-flight designs already comply (`docs/PATHFINDER_CRC32.md`,
`docs/TARGETS/WIN32_DIFFERENTIAL_HARNESS.md`, `docs/CALIBRATION_GOVERNANCE.md`). The
root-placed files that predate this decision — `MODEL_DEBT.md`, `TCB.md`,
`GRAPHICS_PREBUILD_AUDIT.md`, and eventually `PLAN.md`/`TASKS.md` as the coordination
surface — are queued for migration into `docs/` once the backlog-exclusion mechanism
extends to cover them, with every in-repo path reference (task files, ADRs, dispatch
briefs) updated as part of that move. This decision does not itself move any file; it
sets the rule that migration is expected to satisfy.

## Provenance

Owner-stated. The owner's own words, quoted in full above. The specific migration
mechanics (which files, sequencing, the backlog-exclusion dependency) are the
coordinator's plan for satisfying the owner's directive, tracked live in `PLAN.md`'s
operating-mode header.
