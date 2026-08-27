---
id: TC1
title: x86 hygiene branch — fail-closed hardware oracle, xor SF fix
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

# TC1: x86 hygiene branch — fail-closed hardware oracle, xor SF fix

## Context

This task's substance lives entirely in PLAN.md's Phase-1 history (the "x86 hygiene" entry,
branch `worktree-agent-a59c163e8b2e2896e`, commit `e67275b` and its fix cycles); this file
records that history for a fresh agent who was not present when it happened, since the task
predates the current notes→design→review→implementation discipline (`design:
predates-discipline`, per TASKS.md's task-lifecycle convention).

The review that merged this branch surfaced a critical discovery, in PLAN.md's own words:
**"the x86 hardware semantics fuzzer has been a silent fail-open no-op"** — a bare relative
spawn path failed on Windows, and a `catch` block synthesized `faulted := true` for every
test vector, so the oracle that was supposed to validate the x86 semantic model against real
silicon never actually executed a single instruction. The baseline this facade reported as
"passing" was 6/49. This is the canonical exhibit for why Law 13 (Findings Become Gates) and
the D13 differential-fuzzer policy exist: a harness that talks to the world (real hardware,
here) can silently stop talking to it and nothing else in the tree notices.

The reviewer fixed the harness locally and re-ran it for real: 49/49 instances passed on real
silicon, all 131 `DIV` states bit-exact — the semantic *model* was correct all along; only the
*harness* was a facade. Other findings from the same review pass: a NASM path change had
regressed the encoding fuzzer (the removed path was the only NASM reachable on the review
host); shift masks were dead code (CL-register shift variants were never varied in the
suite); the `DIV` vector prepend had displaced 14 grid vectors (divisor 5/7 coverage lost,
divisors >7 still untested); and a RAX/RDX aliasing trap existed in the newly added vectors.

The first fix cycle (commit `b03b574`) made the fail-open class structurally impossible going
forward rather than just patching the one instance: `runHardwareBatch` was changed to return
`Except String (List HardwareExecutionResult)` — a type that cannot be populated with
synthesized/fabricated results on the happy path — plus a mandatory positive/negative
control-vector pair that must both pass before any fuzz vector's result counts (Law 13
preference-order item 4, "for harnesses that interact with the world... mandatory positive and
negative control vectors"). NASM was wired via `LOCALAPPDATA` with a hard error instead of a
silent skip; the `DIV` write-order bug was fixed; the fuzz budget was raised 50→150 (yielding
`DIV` 131/131, CL-shift 134/134 coverage).

With the oracle now actually running, it immediately found a genuine pre-existing model bug:
**`xor eax, ebx` produced a Sign Flag mismatch against real silicon (58/59 passing, 4939
vectors)**. The second fix cycle (commit `c578f52`) made `setFlagsLogic` width-parameterized
(Sign Flag now reads from bit `width - 1` rather than assuming 64-bit width), routed the 32-bit
`Xor` path through the width-32 call, and left 64-bit callers untouched; an audit of `Mov`/`Xor`
siblings confirmed `XorR32R32` was the only affected instruction (`Mov r32` is flag-inert).
Result: **59/59 instances, 4939 vectors, bit-exact against silicon.**

Final re-review verdict was **MERGE** — every blocker verified by actual execution, the xor fix
confirmed against real hardware, zero truncation suite-wide. A subsequent micro-cycle
(`52f91b4`) added width-masked flags (so the 64-bit path stays bit-identical and a shift-by-64
edge case is handled), `[SKIP]` labels with an honest summary line (53 fuzzed + 6 skipped, 0
failed, 5008 vectors), and moved sign-boundary cases into a curated "take-6" slice so the
xor-class bug is now caught by deliberate case design, not random luck. Final state: **MERGE-
READY** (landed together with the build-perf branch).

One item was explicitly deferred at merge time (conflicted with the registry-gate work landing
on the same typeclass in TC4): `undefinedFlagsMask` should take machine state to compute exact
CL-dependent masks, and an unreachable `Inhabited HardwareExecutionResult` fabricator
contradicts the harness's own "no fabricating path" docstring. TCB.md's T10 entry (harness
self-hosting) picks up the `Inhabited` fabricator as a still-open finding — see TC19.

## Deliverables & acceptance criteria

Historical — already merged to main. For the record, what "done" meant here: `runHardwareBatch`
returns `Except` (no path can synthesize a passing result when the oracle didn't run);
mandatory pos/neg control vectors gate every fuzz session; NASM presence is a hard error, not a
skip; the xor Sign Flag bug is fixed and verified bit-exact against silicon across 4939
vectors; the suite's skip/fail/pass counts are reported honestly rather than folded into a
single "success" number.

## Pointers

- `Gasm/Targets/X86_64/HardwareHarness.lean:281` — `runHardwareBatch`, confirmed present with
  its `Except String (List HardwareExecutionResult)` signature (grep-verified at time of
  writing).
- `Gasm/Targets/X86_64/HardwareHarness.lean:312-340` — the mandatory positive/negative
  control-vector checks and their `throw (IO.userError ...)` failure paths (grep-verified
  present).
- `Gasm/Targets/X86_64/Registers.lean:152-166` — `setFlagsLogic` (width-parameterized) and
  `setFlagsLogic64` (the 64-bit specialization kept for existing callers) — grep-confirmed
  present, matching PLAN.md's description of the fix.
- `Gasm/Targets/X86_64/Instructions/Xor.lean:31` — `XorR32R32`'s semantics call
  `setFlagsLogic 32 res.toUInt64`, confirming the width-32 routing PLAN.md describes.
- PLAN.md, "Phase 1 — Mechanical trust fixes", the "**x86 hygiene**" bullet — the full
  narrative this file summarizes; read it directly for exact commit hashes and vector counts.
- TCB.md T10 (`HardwareHarness`'s hand-written machine code, the `Inhabited` fabricator) and
  T11-b (vacuity floors) — open follow-on findings against this same harness, picked up by
  TC19 and TC17 respectively, not closed by this task.

## Notes

- 2026-08-27: priority 7.5 — done; fixed a real fail-open hardware-oracle catastrophe (hygiene branch) — historical value: foundational trust fix, high at the time.

_(2026-08-27) This task predates the notes→design→review→implementation discipline
(`TASKS.md`'s task-lifecycle convention, ADRs 0018/0019); its working history lives in PLAN.md's
Phase-1 merge-train record rather than in a design doc or a Notes log here. No further entries
are expected unless a later task (e.g. TC19) reopens this branch's deferred items._
