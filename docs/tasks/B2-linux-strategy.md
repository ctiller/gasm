---
id: B2
title: Linux strategy — runners/hardware plan, cost factor
status: blocked
blocked_on: "hardware/cost decision"
after: [TC6]
related: []
bar: ""
track: build-scale
priority: 2.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# B2: Linux strategy — runners/hardware plan, cost factor

## Context

This task is genuinely thin right now, and that is the correct state to record rather than pad
around. TASKS.md states it plainly:

> B2 Linux strategy: runners/hardware plan (Craig has ideas; cost factor), Linux target
> implementation later — after: TC6; blocked: hardware/cost decision

There are two separate blockers layered here, not one:

1. **A hard dependency on TC6** (CI establishment), which is itself blocked — TASKS.md marks TC6
   `[b]` with "blocked: Craig determining where CI runs." Linux runner strategy is downstream of
   knowing where CI itself lives; deciding a Linux hardware/runner plan before CI's location is
   settled would be planning in a vacuum.
2. **An explicit `blocked_on` of its own**: a hardware/cost decision that is Craig's to make, not
   something this task can resolve by more analysis or design work. PLAN.md's operating-mode note
   confirms this is a real, named, external blocker, not a placeholder: "Linux hardware comes once
   the codebase is in better shape (cost a factor; Craig has ideas)."

Both blockers are the same shape: **this is waiting on a decision, not on design work.** There is
nothing productive this task can do right now beyond stating clearly what it's waiting on and why
it matters — which is what the rest of this file does.

### Why it matters when unblocked — the epistemology gap it closes

PLAN.md's gaps register names the reason this eventually has to happen, under "Single-machine/
single-OS epistemology" — quoted in full because it is short and states the concern precisely:

> **Single-machine/single-OS epistemology**: all hardware truth from one i9-13900H; whole oracle
> stack is Windows-only; zen4/skylake profiles unvalidatable; Linux target doc'd but absent from
> PLAN. Perf model must state "validated on exactly N microarchitectures"; Linux runner story
> eventually gates fleet-scale agents.

Two distinct consequences follow from this, and both are relevant to why B2 exists as its own task
rather than being folded into the performance track:

- **Every hardware-differential claim this project makes today — the x86 semantics fuzzer, the
  perf model calibration work in F1/F3, the `zen4Profile`/`skylakeProfile` entries in
  `Gasm/Targets/X86_64/Uop.lean`** — is validated against exactly one physical machine (an i9-13900H)
  running exactly one OS (Windows). `zen4Profile` and `skylakeProfile` currently exist as
  `MicroarchProfile` values with plausible-looking numbers, but nothing in the tree has ever measured
  a real Zen 4 or Skylake chip — they are, in the same sense MODEL_DEBT flags elsewhere, unvalidated
  hypotheses standing in for measurement. A second, independent OS/hardware target (Linux, and
  eventually different silicon) is what would let the project honestly narrow that gap, or at least
  state its validation scope precisely ("validated on exactly N microarchitectures") instead of
  implicitly generalizing from N=1.
- **The whole oracle stack — hardware fuzzer, NASM encoding fuzzer, Wasm/Node oracle, Win32 API
  differential harness — is Windows-only today.** Any target-system ambition that assumes portable
  agent fleets (VISION.md §1's target systems: game engines, operating systems, servers, databases —
  several of which are conventionally deployed on Linux) eventually needs this closed. PLAN.md's own
  phrasing — "Linux runner story eventually gates fleet-scale agents" — states this is not optional
  polish; it is a scaling precondition for the project's stated ambitions, just not one that has to
  be solved today.

## Deliverables & acceptance criteria

Nothing in this task can be delivered until it is unblocked. When Craig's hardware/cost decision
lands (and TC6/CI-location is settled), this task's actual scope becomes:

- A runners/hardware plan: what physical or cloud Linux hardware this project targets, informed by
  whatever cost/vendor factors Craig's decision resolves.
- A cost-factor writeup: what this plan costs (ongoing hosting/hardware spend, setup effort) as
  input to the decision itself, if not already settled by the time this task is picked up.
- Explicitly deferred, per TASKS.md's own phrasing ("Linux target implementation later"): this task
  is the *plan*, not the implementation — porting the oracle stack (hardware fuzzer, NASM fuzzer,
  Wasm/Node harness, Win32 differential harness) to Linux, or building a genuine Linux target model,
  is later work this task's plan sets up but does not itself execute.
- When this task is unblocked and its design work actually starts, it stops being pure policy and
  should get a real design/review pass like any other stop-and-design item (Law 5) — but that is
  future work; do not attempt to pre-write that design now while the hardware/cost decision remains
  open, since the decision's shape (which hardware, which cost model) will materially determine what
  the design needs to cover.

## Pointers

- TASKS.md, "Build/scale" section, B2 line (quoted above) and TC6 line (the CI-location blocker this
  task is also indirectly downstream of).
- PLAN.md, operating-mode note: "Linux hardware comes once the codebase is in better shape (cost a
  factor; Craig has ideas)."
- PLAN.md gaps register, "Single-machine/single-OS epistemology" bullet (quoted in full above) — the
  concrete epistemic gap this task exists to eventually close.
- `Gasm/Targets/X86_64/Uop.lean:87-97` (`skylakeProfile`), `:102-112` (`zen4Profile`) — the two
  cross-vendor/cross-microarchitecture profiles that currently have no real-hardware validation
  behind them; this is the profile data a future Linux/multi-machine validation pass would need to
  actually exercise.
- `docs/VISION.md` §1 ("The Target Systems") — the fleet-scale agent ambition this task's
  "eventually gates fleet-scale agents" language refers to.

## Notes

- 2026-08-27: priority 2.0 — status: blocked on Craig's own hardware/cost decision (blocked_on: 'hardware/cost decision') — kept low per owner directive until that decision unblocks it; nothing productive happens here until then.

_(none yet — blocked on Craig's hardware/cost decision; nothing to consolidate until unblocked.)_
