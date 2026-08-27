---
id: TC6
title: CI establishment
status: implementing
blocked_on: ""
after: [TC5]
related: []
bar: ""
track: trust-core
priority: 6.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# TC6: CI establishment

## Context

There is no CI in this repository: `.github` is absent (confirmed by TC5's own investigation
and reconfirmed by TCB.md's headline metrics — "No CI, every gate manual"). Every gate this
project relies on (`lake build`, both Law-10 linters, three differential fuzzers, the roundtrip
suite) is currently invoked by hand, per-agent, per-session. TASKS.md's own framing note is
blunt about the consequence: *"Repair-epic exit: we trust the system enough that spec & model
review is something we do, implementation review is something we trust mechanically"* — that
mechanical trust cannot exist without something automatically re-running the gates on every
change, independent of whether any individual agent remembered to run `scripts/run_gates.ps1`
(TC5) themselves.

This task is explicitly listed as `[b]` blocked in TASKS.md, with the block named directly:
**"Craig determining where CI runs."** PLAN.md's Decisions section (D13, in the same paragraph
as the TCB policy) states the same thing: *"CI will be established (location: Craig chasing
down)."* This is not a technical unknown — the gate runner this task will invoke already exists
as a design target (TC5), and the gate list itself is fully enumerated there. What's missing is
an infrastructure/hosting decision only Craig can make: self-hosted runners (relevant given
B2's "Linux strategy: runners/hardware plan... cost factor" — this repo's gates depend on
hardware-level fuzzing against real silicon, which constrains what "a CI runner" can even mean
here — a GitHub-hosted Actions runner cannot run the x86 hardware semantics fuzzer against real
silicon the way a self-hosted runner with the right CPU can), a hosted CI service, or something
else entirely.

Do not attempt to unblock this task by picking a CI platform unilaterally — the block is named
as a decision reserved for Craig, not an open research question. If you are a fresh agent
picking up TASKS.md and see this task still `[b]` blocked, the correct action is to surface the
open question to Craig (or whoever is directing the session), not to guess.

### What happens once unblocked

Once Craig picks a location, this task's job is straightforward given TC5 already exists: wire
whatever CI system is chosen to invoke `scripts/run_gates.ps1`/`.sh` (TC5's single entry point)
on every push/PR, fail the check on any non-zero exit from that runner, and surface TC5's
machine-parseable per-gate summary in the CI UI so a failing check names which specific gate
failed rather than just "build failed." Given TC5's hardware-fuzzer dependency (the x86
oracle needs to run on real silicon that matches the profiles this project's model claims to
validate against — see TCB T11, "the silicon itself"), whatever CI location is chosen will need
either a self-hosted runner on compatible hardware or an explicit, honestly-documented carve-out
where hardware-dependent gates are skipped in CI and only run in local/scheduled sessions (which
would itself need to be a stated, reviewed policy, not a silent gap — Law 13 would treat an
undocumented "CI skips the hardware fuzzer" as exactly the kind of fail-open-by-omission this
project has already been burned by twice, per TC1/TC2's histories).

## Deliverables & acceptance criteria

Cannot be scoped in detail until the location decision lands — that decision changes what "CI"
even means here (hosted service vs. self-hosted runner vs. something else). Once unblocked, the
acceptance bar is: every gate in TC5's enumerated list runs automatically on every push/PR;
a failing gate blocks merge; TC5's per-gate summary is visible in whatever CI UI is chosen;
the hardware-fuzzer dependency is either satisfied by the chosen runner or explicitly and
reviewably carved out, not silently skipped.

## Pointers

- `docs/tasks/TC5-gate-runner.md` — the single entry point this task will wire into whatever CI
  system is chosen; TC6 is a thin wrapper around TC5, not a reimplementation of the gate list.
- PLAN.md, Decisions section, D13 — "CI will be established (location: Craig chasing down)."
- TASKS.md, "Trust core" section, the `[b] TC6` line — the blocked status this file expands on.
- TCB.md headline metrics ("No CI; every gate manual") and T4 ("gate tooling + no runner") —
  the trust-ledger framing of why this gap matters beyond convenience.
- TASKS.md's B2 task ("Linux strategy: runners/hardware plan... blocked: hardware/cost
  decision") — a related, separately-blocked decision that may interact with wherever CI ends
  up running (a Linux CI runner is a different question from a hardware-fuzzing-capable one).

## Notes

- 2026-08-27: priority 6.0 — CI establishment matters but sits status:blocked on Craig's own infra decision — kept moderate rather than low since it's ready-to-land the moment that decision lands.
- 2026-08-27: **the "where CI runs" block is resolved**: GitHub Actions, `windows-latest`
  (hosted) as the primary, fully-covered platform today, plus an `ubuntu-latest` (hosted) job
  covering the portable subset of gates, with the vendor-supplied self-hosted Linux fleet
  joining the same matrix once that hardware is registered. Design and rationale are in
  `docs/CI.md`; workflows are `.github/workflows/ci.yml` (push/PR) and
  `.github/workflows/scheduled.yml` (weekly extended fuzzing). Status moved to `implementing`
  rather than `done` because this task's own acceptance bar is written against TC5 landing
  first ("TC6 is a thin wrapper around TC5, not a reimplementation of the gate list") and TC5's
  consolidated `scripts/run_gates.ps1`/`.sh` entry point has not landed on this branch — `ci.yml`
  currently invokes every gate as its own step instead, which `docs/CI.md` §7/§11 name
  explicitly as the reason this isn't `[x]` yet. The hardware-fuzzer carve-out this task's
  Context section anticipated is real and documented: `perf_fuzzer` (microarchitectural
  cycle-bound fuzzer) is excluded from both hosted-runner workflows, reviewably, per `docs/CI.md`
  §5, rather than silently never wired in.
- 2026-08-27: found and fixed in the course of landing this: every `[[lean_exe]]` in
  `lakefile.toml` carried a Windows-only `-Wl,--subsystem,console` linker flag, which would have
  made every executable-backed gate un-linkable on Linux. Verified redundant on Windows and
  removed repo-wide (see `docs/CI.md` §3) — this is what makes the `ubuntu-latest` job in
  `ci.yml` cover more than just the three `lean_lib` targets.

_(Design and implementation now exist — see `docs/CI.md` for the full design and
`.github/workflows/` for the implementation. Remaining before this can move to `[x]`: TC5
landing on this branch, at which point `ci.yml`/`scheduled.yml` should be simplified to call
its single entry point per this task's original acceptance bar, plus first-real-run validation
of the `ubuntu-latest` job — docs/CI.md §7's "Linux job is new and unverified on real Linux
hardware" gap.)_
