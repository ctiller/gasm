---
id: TC11
title: Mutation-coverage tooling for differential suites
status: ready
blocked_on: ""
after: [TC5]
related: [TC8]
bar: ""
track: trust-core
priority: 6.5
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# TC11: Mutation-coverage tooling for differential suites

## Context

PLAN.md's Phase-3 tracker names this task directly: **"Mutation-coverage tooling for
differential suites (mechanize what the Wasm reviewer did by hand): automated harness that
applies a catalog of model mutations (drop a decrement, swap a branch polarity, byte-swap,
off-by-one) and requires the fuzz suite to go RED for each — 'executes' ≠ 'discriminates'; a
suite's coverage claims are only as real as the mutations it kills. Law 13-shaped: converts
case-quality review into a mechanical gate."** TASKS.md's one-liner: "mutation-coverage tooling
for differential suites (suite must go red per cataloged model mutation) — after: TC5."

### Where this pattern comes from, and why it was done by hand first

This is not a speculative idea — it already happened manually, twice, in this project's own
merge history, and both instances are the direct evidence this task generalizes into tooling.
TC2's history (the Wasm control-flow fuzzer) records the reviewer, in the final review round,
building "an independent JS mirror of the interpreter plus a 14-mutation matrix" to check
whether the fuzz suite's 65 passing cases actually *discriminated* correct from incorrect
behavior, rather than merely executing without crashing. That process found the branch-depth-
decrement mutations were **invisible to all 65 existing cases** — the suite executed every case
and reported green, but a real bug in that class would have passed undetected, because
`stepWasm` discarded the `ControlSignal` a mutation there would have corrupted, and no case had
trailing code positioned to observe the corruption. The fix that followed
(`Semantics.lean`'s final cycle, commit `59fb2f1`) used an explicit **mutation-apply-observe-
revert** cycle: apply the mutation, confirm the suite goes red, revert the mutation, confirm the
revert is byte-identical to the original file. That specific verified-revert discipline is
exactly the primitive this task's automated tooling needs to generalize and repeat mechanically,
rather than leaving it to a reviewer's one-off diligence.

TC4's history (the decoder + registry gate) shows the same lesson from the correctness-model
side: the re-reviewer's own mutation M3 (miscompiling `add r8, r15` to write `RAX` instead)
passed every existing gate, because **zero of 1419 roundtrip cases exercised both REX.R and
REX.B set simultaneously** — again, "executes" (the gate ran, decided something, returned green)
was not "discriminates" (the gate's actual case coverage never put the mutated behavior under
test). This mutation-testing discipline is precisely PLAN.md's own framing of the *coverage
regression* finding against TC4's registry gate.

### Why this is Law 13's convergence metric, made mechanical

`docs/VISION.md` §2 states the project's own review-quality north star: "are we proving the
right theorems?" — and frames every other review finding as evidence of a missing gate.
`docs/adr/0010-bar-triggered-deep-re-reviews.md` names the tracked convergence metric
explicitly: "what fraction of findings are right-theorem questions vs. mechanical catches." A
reviewer manually constructing a mutation matrix by hand (as happened twice already, per above)
is exactly the kind of mechanical-catch labor Law 13 wants converted into a permanent gate —
every future review should be free to spend its attention on spec adequacy (the north-star
question), not on re-discovering by hand whether last time's case list actually discriminates.

## Deliverables & acceptance criteria

- A catalog of generic model-mutation classes applicable across this project's differential
  suites, at minimum the four already demonstrated as real bug shapes in this project's own
  history: dropping a decrement/counter update (the branch-depth class from TC2's review), a
  branch-polarity swap (inverting a conditional), a byte-swap/endianness flip (the load/store
  endianness class TC2's review also found), and an off-by-one (boundary/width errors — the
  class TC1's xor Sign-Flag bug and TC4's REX.R/REX.B coverage gap both instantiate in their own
  domains). The catalog should be extensible — new mutation classes get added as new bug shapes
  are found, per Law 13's ratchet.
- An automated harness that, for each cataloged mutation and each targeted suite (hardware
  semantics, encoding, Wasm semantics, gzip/deflate, and the registry roundtrip gate at minimum),
  performs the same apply-observe-revert cycle TC2's manual process used: apply the mutation to
  the relevant source file, run the suite, assert it goes RED, revert the mutation, and assert
  the reverted file is byte-identical to the pre-mutation original (this last check is what
  makes the tool safe to run against a live source tree without risking a mutation being left in
  place by a crash or an unhandled error mid-cycle).
- The harness must itself follow Law 13(4)'s control-vector discipline in miniature: a mutation
  that the harness cannot successfully apply (e.g. the target line no longer exists because the
  source changed) must be reported as an error requiring attention, not silently skipped — a
  mutation catalog with stale line-targets that silently no-ops is the same fail-open shape this
  project has already found twice in its actual oracles (TC1, TC2), just relocated into the
  meta-tooling that checks those oracles.
- Wired into TC5's gate runner (per the `after: [TC5]` edge) so mutation-coverage checking runs
  as part of the standard gate sequence, or as an explicitly separate but equally mandatory
  invocation — confirm with TC5's own file which shape fits its existing structure better.
  Given mutation testing is typically slower than a single suite run (N mutations × full suite
  run each), consider whether this needs to run less frequently than every gate invocation
  (e.g. on a schedule, coordinating with TC10) — state that decision explicitly rather than
  silently making mutation coverage optional.
- Completion report must show, for the suites wired in: the mutation catalog applied, which
  mutations were caught (suite went red) vs. missed (suite stayed green — these are the
  actionable findings, exactly like TC2's and TC4's manual discoveries), and for any mutation
  found missed, either a fix to the suite's case coverage or an explicit filed follow-up with the
  specific gap named (do not silently note a miss and move on — a missed mutation is itself a
  Law 13 finding requiring its own gate).

## Pointers

- PLAN.md, "Phase 1 — Mechanical trust fixes", the "Wasm control-flow fuzzing" bullet's final
  review round — the exact manual mutation-testing narrative (14-mutation matrix, the invisible
  branch-depth-decrement mutations, the mutation-apply-observe-revert fix) this task generalizes
  into tooling.
- PLAN.md, "Decoder gaps + REGISTRY GATE" bullet's re-review paragraph — the both-extended-
  register-pair mutation (M3) that passed every gate; the correctness-model-side instance of the
  same lesson.
- `Gasm/Targets/Wasm/Semantics.lean` — the file whose branch-depth-decrement logic was the target
  of TC2's manual mutation cycle (grep for `ControlSignal`/loop-depth handling to locate current
  line numbers; PLAN.md's `:381,415` references are from the review-time tree and have likely
  moved).
- `Gasm/Targets/X86_64/RoundtripGate/*.lean` and `Gasm/Targets/X86_64/Registry.lean` — the
  registry gate machinery TC4's coverage-regression mutation (M3) targeted; this task's harness
  should be able to apply an analogous both-extended-register mutation here as one of its
  catalog entries, verifying TC4's fix (once landed) actually closes this specific gap.
- `docs/tasks/TC10-continuous-fuzzing-corpus.md` — the complementary (not overlapping) task; read
  it to keep the TC10/TC11 boundary clear (TC10 retains real divergences; TC11 verifies
  synthetic-mutation discrimination).
- `docs/REVIEW.md` Law 13 (full text, especially the "check ∀, fix ∀" and control-vector
  sections) and `docs/VISION.md` §2 (the north-star framing this task's convergence-metric
  motivation is drawn from).
- `docs/adr/0010-bar-triggered-deep-re-reviews.md` — names the right-theorem-vs-mechanical-catch
  convergence metric this task mechanizes part of the measurement for.

## Notes

- 2026-08-27: priority 6.5 — mutation-coverage tooling strengthens confidence in the differential suites TC8's buildout produces; not separately ranked in TCB but clearly downstream leverage.
- 2026-08-27: related: [TC8] — TC11's mutation-coverage tooling and TC8's trust-fuzzer buildout both aim at the same question (does a differential suite actually catch injected defects, or does it just run); TC11's tooling is a natural companion check for whatever TC8 builds.

_(none yet — first entries append here as work begins; the mutation-catalog format and the
apply-observe-revert safety mechanism are novel enough model surface (a new kind of tooling
this repo hasn't built before, applying to multiple existing suites) that this likely warrants
a short real design note before implementation, even if not full Law-5-class — use judgment once
work starts on whether an inline `## Design` section suffices or a `docs/` doc is warranted.)_
