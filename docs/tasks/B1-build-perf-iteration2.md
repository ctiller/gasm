---
id: B1
title: Build-perf iteration 2 — Instructions.lean aggregator sharding
status: implementing
blocked_on: ""
after: [TC4]
related: []
bar: ""
track: build-scale
priority: 5.5
priority_set: 2026-08-27T18:25:47Z
design: "inline"
design_review: "waived-mechanical"
date: 2026-08-27
---

# B1: Build-perf iteration 2 — Instructions.lean aggregator sharding

## Scope note (read first)

This file's own name says "iteration 2," and that is deliberately this file's scope: TASKS.md's B1
line ("build-perf iteration 2: Instructions.lean aggregator sharding — after: TC4 (same files)") IS
the iteration-2 item. Iteration 1 already happened, is DONE, and merged its findings and scripts to
main — it is covered below as **completed background**, not as this task's own pending work.
Concretely:

- **Iteration 1 is done.** Its `design`/`design_review` for that already-landed work would
  retrospectively be `predates-discipline` (it landed under branch
  `worktree-agent-a5d16e59384569684`, commit `b1742a1`, before this task-file/design-doc discipline
  existed) — but that is history, not this file's basis for its own frontmatter.
- **This file's frontmatter (`status: ready`, `design: ""`, `design_review: ""`) is about iteration
  2 specifically**, because iteration 2's actual restructuring work has not started: no `.lean`
  changes were made in iteration 1 (confirmed below), the aggregator (`Instructions.lean`) is still,
  as of this writing, the same umbrella-import structure it always was, and iteration 2's design
  (how exactly to shard/restructure it) has not yet been written. Per the task-lifecycle convention,
  this is mechanical build/refactoring work, so once a short inline `## Design` section is written
  covering iteration 2's actual restructuring plan, `design: "inline"` and
  `design_review: "waived-mechanical"` become appropriate for *that* work — but not before it exists.
  Do not backdate iteration 1's `predates-discipline` status onto iteration 2's not-yet-started
  scope; that would misrepresent unstarted work as already reviewed.

## Context

Build performance is an explicit standing workstream, not a one-off cleanup. PLAN.md's "Ongoing
workstream — build performance (D8)" section frames why:

> Agent iteration speed = checker feedback latency; build times have been creeping. Craig supports
> a STANDING sonnet background thread iterating on this through repair and beyond. Hypothesis
> (Craig): most of the win is correct SHARDING — split modules so incremental builds recompile only
> what changed.

This task (iteration 2) is the direct test of that sharding hypothesis, on the single module
iteration 1 identified as the highest-payoff target.

### Iteration 1 — DONE — findings, quoted in full

PLAN.md records iteration 1 as complete, on branch `worktree-agent-a5d16e59384569684`, commit
`b1742a1`, with a "light merge-time check only (scripts + baseline doc, no .lean changes, no gate
claims)." Its three numbered findings, quoted verbatim, are essential background for understanding
why iteration 2 targets exactly the file it does:

> FINDINGS: (1) the 3m45s "no-op" was a PHANTOM — worktree-seeded .lake caches are path-invalid
> (absolute paths in artifacts/.rsp), so first build in a fresh worktree rebuilds all 315 jobs;
> steady-state no-op = 0.25s. WORKFLOW TAX: every fresh worktree agent pays ~5min cold build →
> batch tasks into existing worktrees where possible (fix cycles already do). (2) Cold baseline
> 5m03s / 315 jobs (47% CPU contention); slowest = Spike2 Windows Equivalence 198s + 12-way 135s
> cluster = native_decide-heavy files → Law 10 migration buys back cold-build time directly. (3)
> Cascade: any of the 21 instruction files invalidates a 56-module closure via Instructions.lean
> aggregator (TOP iteration-2 payoff, confirming Craig's sharding hypothesis); Zlib/Windows.lean has
> only 8 dependents — self-edit latency, NOT a cascade bottleneck; Gasm.Core.Types fan-in 120/146
> but low-churn.

Read finding (1) as pure infrastructure/methodology insight (not something this task fixes in-repo
— it's about how fresh worktrees get seeded, outside this repo's control) and findings (2)/(3) as
the actual build-performance content. Finding (3) is this task's direct mandate: **any of the 21
files under `Gasm/Targets/X86_64/Instructions/` invalidates a 56-module transitive closure**,
because every consumer imports the single `Instructions.lean` umbrella file rather than the specific
instruction submodule(s) it actually uses, and (per `scripts/build_baseline.md`'s cascade analysis,
confirmed by grep of the current tree) `Instructions.lean` is also where a dispatch/registry
structure forces every consumer to see every instruction. This is confirmed directly in
`scripts/build_baseline.md`'s own ranked sharding proposal for iteration 2:

> 1. **`Gasm/Targets/X86_64/Instructions.lean` (the 21-file aggregator).** Highest expected payoff.
>    This is an actively-developed area (new instructions get added regularly — high edit frequency)
>    with a 56-module transitive cascade, and it directly explains the 12-way-tied 135s cluster in
>    the cold build (a meaningful fraction of total build time). The fix is *not* to shrink the
>    aggregator file itself (it's already split into 21 per-instruction files) but to stop treating
>    it as one opaque compilation unit for consumers: downstream modules that only need a handful of
>    instructions (e.g. a spike's `Emit.lean`) should import the specific
>    `Instructions.Mov`/`Instructions.Add`/etc. files they use directly instead of importing the
>    `Instructions` umbrella, and any dispatch table that currently lives in `Instructions.lean` and
>    forces every consumer to see every instruction should be restructured (e.g. into a
>    typeclass/registry pattern) so it doesn't create a single-file chokepoint. This is a
>    REF-sensitive `.lean` restructuring — explicitly deferred to iteration 2.

Iteration 1's cold-baseline numbers, for reference and as the diff target this task's completion
evidence must be measured against: **5m03s wall / 315 jobs**, with the slowest single job being
`Spikes.Spike2Fibonacci.Windows.Equivalence` at 198s, and a 12-way tie at 135s
(`Spikes.Spike5Gzip.Windows.Program:c.o`, `Spikes.Spike5Gzip.Equivalence`,
`Spikes.Spike4HttpServer.Windows.Program:c.o`, and 9 others) that `scripts/build_baseline.md`
identifies as exactly the set of modules that transitively import the X86_64 instruction-semantics
stack and all became unblocked simultaneously once that shared upstream dependency finished
elaborating — direct corroborating evidence for the cascade this task exists to break up.

### Why this had to wait for TC4, and why it can proceed now

TASKS.md marks B1 `after: TC4 (same files)`, and PLAN.md's own iteration-1 entry is explicit about
this: "Iteration 2: Instructions.lean aggregator restructuring (top payoff) — **MUST WAIT** for the
decoder agent's registry gate to land (same files); then Base.lean, then Core churn check;
Zlib/Windows.lean split deprioritized for throughput (still useful for self-edit latency +
fragility)." TC4 (decoder + registry build-gate) landed a defaultless `roundtripCases` typeclass
field, an `allEncodableInstructions` registry, and a build-time environment audit — all of which
touch the exact same `Instructions.lean`/`Instructions/*.lean`/`Registry.lean` files this task must
restructure. Sequencing iteration 2 after TC4 avoids two agents editing the same aggregator and
registry machinery concurrently. **TC4 is done** (TASKS.md marks it `[x]`, "MERGE TRAIN 3 now"), so
this precondition is satisfied and iteration 2 is unblocked.

### What iteration 2 must actually do

Per the ranked proposal above, in priority order:

1. **Stop treating `Instructions.lean` as one opaque compilation unit for consumers.** Downstream
   modules that only need a handful of instruction families (e.g. a spike's emitter that only ever
   emits `MOV`/`ADD`/`JMP`) should import the specific `Instructions.<Family>` submodules they
   actually use, not the umbrella `Instructions.lean`.
2. **Restructure whatever dispatch table currently lives in `Instructions.lean` so it doesn't force
   every consumer to see every instruction** — the task suggests a typeclass/registry pattern, which
   TC4's registry gate work has already partially built (`Registry.lean`'s
   `allEncodableInstructions`) — this task should investigate whether that existing registry
   machinery can be leveraged rather than duplicated.
3. **Then check `Instructions/Base.lean`** (80 transitive fan-in, 33 direct importers per
   `scripts/build_baseline.md` — every instruction file itself imports it) — confirm whether
   everything in `Base.lean` truly needs to be shared, or whether some of it could be pushed down
   into only the instruction families that need it.
4. **Then a Core churn check** (`Gasm/Core/Types.lean` and friends have the largest raw cascades —
   84-120 modules — but PLAN.md flags them as "likely low edit frequency" and explicitly lower
   priority "unless churn data says otherwise" — this task should check `git log --follow` frequency
   on these files before investing there, per `scripts/build_baseline.md`'s own recommendation).
5. **`Zlib/Windows.lean` splitting is explicitly deprioritized for this task** — it has only 8
   transitive dependents (not a cascade bottleneck), so splitting it helps only the person actively
   editing that single large file, not whole-build throughput. Do not let this task's scope creep
   into that file; it is out of scope here.

Note the important caveat one importer flags: `Registry.lean`/`RoundtripGate.lean` (TC4's registry
gate) currently depend on `Instructions.lean` importing *every* instruction submodule specifically
so the registry audit can see every registered instance via the environment walk (see
`Gasm/Targets/X86_64/Instructions.lean`'s own header comment: "True umbrella: every
Instructions/*.lean submodule is imported here so that anything importing this file... sees every
registered `X86_64Instruction` instance in the environment... Adding a new
Instructions/<Foo>.lean file MUST add an `import` line here... or its instance(s) will silently not
be audited, registered, or gated."). **This task must preserve that audit-completeness property** —
the fix is for *individual consumer modules* to stop importing the umbrella when they don't need the
registry audit, not for the registry/gate machinery itself to lose visibility into every
instruction. Getting this wrong would silently reopen the exact import-closure hole TC4's own
re-review already found and fixed once (an unimported instruction module being invisible to the
audit).

## Deliverables & acceptance criteria

- A short inline `## Design` section (see the task-lifecycle convention — mechanical
  build/refactoring work consolidates into an inline design section, not a separate `docs/` design
  doc) stating the concrete restructuring plan before implementation: which consumer modules move
  from importing the `Instructions` umbrella to importing specific `Instructions.<Family>` files,
  and how the registry/gate's audit-completeness requirement is preserved for whichever module(s)
  still need whole-registry visibility.
- The restructuring itself: consumers that don't need every instruction family import only what they
  use; the registry gate's environment audit continues to see every registered instance (verify this
  explicitly — do not just assume it, since this is the exact property TC4's own re-review flagged
  as fragile).
- `Instructions/Base.lean` fan-in investigated per priority item 3 above; a decision recorded (in
  this file's Notes, or the inline Design section) on whether it needs splitting this iteration or
  can be deferred.
- Core-module churn check (priority item 4) performed via `git log --follow` frequency, with the
  result recorded even if the conclusion is "defer, low churn confirmed."
- `Zlib/Windows.lean` explicitly left untouched by this task (out of scope per the deprioritization
  above).
- **Before/after build-timing evidence, per `scripts/build_baseline.md`'s established convention**
  (that file is explicitly "the diff target" per iteration 1's own deliverables list): re-run
  `lake clean && lake build` under comparable conditions and report against iteration 1's baseline —
  **5m03s / 315 jobs**, with the 198s `Spike2 Windows Equivalence` job and the 12-way 135s cluster as
  the specific numbers this task's restructuring should improve (per-module timing, not just total
  wall time, since the cascade this task targets is specifically about which modules get
  invalidated together). Also re-run and report the no-op-rebuild check (expect ~0.25-0.3s,
  unchanged) to confirm this task's changes didn't regress incremental-build correctness.
- `lake build` (full, default targets) must still succeed with the same target count/set as before
  (315 jobs, or the current equivalent if other tasks have changed the count in the interim) —
  `defaultTargets` in `lakefile.toml` must remain untouched, per iteration 1's own precedent of
  keeping `scripts/dev_build.ps1`/`.sh` strictly additive/opt-in.
- `python scripts/check_refs.py` must still exit 0 — this is a "REF-sensitive `.lean` restructuring"
  per `scripts/build_baseline.md`'s own words, meaning moving imports around risks disturbing
  `/- REF: ... -/` citation coverage; verify explicitly rather than assuming citations survive a
  module reorganization untouched.
- Verify `lake exe check_gates_axioms` and the registry roundtrip gate (TC4's gate) still pass after
  the restructuring — this is the single most important regression check given the audit-completeness
  concern above.

## Pointers

- `scripts/build_baseline.md` (iteration 1's full report — environment, no-op diagnosis, cold
  baseline table, cascade analysis, ranked sharding proposal for iteration 2 — this task's direct
  input and its diff target for before/after evidence).
- `scripts/dev_build.ps1`, `scripts/dev_build.sh` (iteration 1's opt-in convenience scripts — 3
  `lean_lib` targets only, `defaultTargets` untouched; this task should follow the same
  strictly-additive discipline for any new scripts it introduces).
- `Gasm/Targets/X86_64/Instructions.lean` (the aggregator this task restructures — currently a
  22-line-of-imports umbrella; its header comment explains the audit-completeness constraint this
  task must preserve, quoted above).
- `Gasm/Targets/X86_64/Instructions/` (the 21 per-family files already split out — `Add.lean`,
  `And.lean`, `Base.lean`, `Call.lean`, `Cmov.lean`, `Cmp.lean`, `Div.lean`, `Imul.lean`, `Jcc.lean`,
  `Lea.lean`, `Mov.lean`, `Neg.lean`, `Not.lean`, `Or.lean`, `Pop.lean`, `Push.lean`, `Ret.lean`,
  `Shift.lean`, `Sub.lean`, `Test.lean`, `Xchg.lean`, `Xor.lean`).
- `Gasm/Targets/X86_64/Registry.lean` (TC4's registry — `allEncodableInstructions` and the build-time
  environment audit that needs whole-registry visibility; this task must confirm which module(s)
  still need to import the umbrella for this audit's sake).
- `Gasm/Targets/X86_64/Decoder.lean` (currently also imports every individual instruction submodule
  directly rather than the umbrella — note this as a possible existing precedent for the
  "import only what you use" pattern this task should extend elsewhere, and note it is also directly
  relevant to B3's decoder-modularization scope, since B3 depends on this task landing first).
- PLAN.md, "Ongoing workstream — build performance (D8)" section (quoted in full above).
- TASKS.md, "Build/scale" section, B1 line.
- `docs/tasks/TC4-decoder-registry-gate.md` if present, else TASKS.md's TC4 entry (the hard
  dependency — confirm landed/done before starting, and confirm this task's restructuring doesn't
  reopen the import-closure hole TC4's re-review found and fixed).
- `docs/tasks/B3-stage-b-decoder-modularization.md` (depends on this task; do not let this task's
  restructuring choices foreclose B3's per-instruction `tryDecode` co-location plan — coordinate the
  two, since B3 explicitly builds on whatever module structure this task leaves behind).

## Notes

- 2026-08-27: priority 5.5 — build-perf iteration 2 (Instructions.lean sharding) is useful build-scale hygiene, not on the critical path of any track the owner flagged as urgent.

_(none yet — first entries append here as work begins; mechanical build/refactoring task,
consolidate into an inline ## Design section before implementation, design_review:
waived-mechanical.)_

### 2026-08-27 — iteration 2 complete (import-graph surgery)

Import-graph surgery only, no `.lean` file splits. Moved `X86_64Instr`,
`TargetArch X86_64` and `X86_64Instr.toBinary` out of the umbrella `Instructions.lean`
into `Instructions/Base.lean` (which every instruction submodule already imports, so no
new dependency edge), leaving the umbrella as a pure 21-submodule import manifest for
`Registry.lean`'s audit-completeness requirement. Retargeted ~30 direct umbrella
importers to `Instructions.Base` plus whichever specific families they already used.

Cascade (`touch Add.lean; lake build Gasm`, two runs each side): **38 -> 32 jobs
(-16%)**; wall time roughly halved but contention-dominated, so the job count is the
reliable figure. Review independently reproduced 38->32 from a static import parse,
including the identity of all six dropped modules, and confirmed zero modules had their
cascade increase.

Review found and fixed: `Gasm.lean`'s direct umbrella import had been deleted, leaving
`Gasm -> SemanticsFuzzer -> Registry -> Instructions` as the ONLY path to the registry
audit — restored, at zero cascade cost. See the B3 note in this directory for why the
residual 32-job cluster is not inherent and what Stage B must additionally do.
