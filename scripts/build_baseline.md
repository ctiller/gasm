# Build Performance Baseline — Iteration 1

Date: 2026-08-27
Worktree: `agent-a5d16e59384569684` (isolated git worktree, branch `worktree-agent-a5d16e59384569684`)
Author: build-performance workstream (Claude)

## 0. Environment

- CPU: 13th Gen Intel Core i9-13900H, 14 cores / 20 logical threads
- RAM: 64 GB
- OS: Windows 11 Home 10.0.26200
- Lean/Lake: `leanprover/lean4:v4.33.1` / Lake `5.0.0-src+819816b`
- Repo: 143 `.lean` files under `Gasm/`, `Stdlib/`, `Spikes/` + 3 root aggregators
  (`Gasm.lean`, `Stdlib.lean`, `Spikes.lean`) = 146 modules total
- `lakefile.toml` defines 28 `lean_exe` targets, 3 `lean_lib` targets, and lists
  **every** exe + all 3 libs in `defaultTargets` (i.e. plain `lake build` builds
  everything, including all 5 spikes' Windows+Wasm variants, all fuzzers, and
  `test_roundtrip`).
- Background load: CPU load was measured at 19–47% from other processes during
  these runs (other Claude Code agent worktrees, an IDE, browser, OneDrive sync
  were all running concurrently on this machine). **Absolute wall-clock numbers
  below should be read as approximate; relative rankings (which jobs are
  slowest, which modules have the largest fan-in) are the reliable signal.**

## 1. No-op rebuild diagnosis (Task 1)

**Root cause found: this is not a bug in the project's lakefile/module
structure. `lake build` in this repo is genuinely incremental and a true
no-op rebuild is fast (~0.25s, measured 4 times in a row: 0.28s / 0.26s /
0.25s / 0.25s, all reporting "Build completed successfully (315 jobs)" with
zero `Built`/`Replayed`-as-rebuild lines).**

What actually explains the reported 3m45s "no-op" symptom:

- On arrival in this worktree, `.lake/build` **already existed** (mtime equal
  to the worktree's own creation time), i.e. some external provisioning step
  populates each fresh agent worktree with a `.lake` build cache before the
  agent's first command runs.
- The first `lake build` run in this session, despite that pre-existing
  cache, **rebuilt all 315 jobs from scratch** (4m29s wall) — i.e. it behaved
  exactly like a cold build even though "nothing had changed" from the
  worktree's point of view.
- Immediately after that, a second `lake build` (no file changes) completed
  in 0.28s with no jobs rebuilt. Every subsequent no-op run was equally fast.
- Root cause of the "phantom full rebuild": **Lean/Lake artifacts embed
  absolute file-system paths.** Confirmed directly — e.g.
  `.lake/build/bin/spike1_hello_windows.exe.rsp` (the linker response file)
  contains literal strings like
  `"<worktree>\.lake\build\ir\...\Emit.c.o.noexport"`.
  A `.lake/build` directory that was populated in — or copied/seeded from —
  a *different* absolute path (e.g. another worktree, an integration
  checkout, or a template) will not validate against the current worktree's
  path, so Lake conservatively treats every target as stale and rebuilds the
  entire tree once. That one-time rebuild is what shows up as "315 jobs
  Built" and looks like a no-op that took minutes.
- This was reproduced faithfully in this worktree: pre-seeded `.lake` →
  full rebuild (4m29s) → genuine no-op (0.25–0.28s) from then on. It is very
  likely the same mechanism produced the 3m45s reading on "the integration
  worktree": that worktree's `.lake` cache was not self-consistent for its
  own path at the moment the timing was taken (e.g. it had just been
  (re)provisioned, or its cache had been carried over from elsewhere), so the
  "second" build the owner timed was actually this same one-time
  cache-invalidation rebuild, not a steady-state no-op.
- **This is not fixable from `lakefile.toml` or module structure** — it's a
  structural property of how Lean/Lake stores absolute paths in build
  byproducts, combined with however the outer agent-orchestration
  infrastructure seeds new worktrees. Recommendation (infra-level, outside
  this repo): either (a) don't pre-seed `.lake` into fresh worktrees at all
  and budget one cold build per worktree, or (b) if pre-seeding for speed,
  expect and discount exactly one "phantom full rebuild" per fresh worktree
  — it is not evidence of a persistent per-edit incremental-build defect.
- Also checked and ruled out as a *separate* cause: unconditional relinking.
  A genuine no-op run emits zero `Built` lines for any `:exe` target — exe
  targets are not relinked when nothing changed.

## 2. Cold baseline (Task 2)

Command: `lake clean && lake build` (timed with the `time` builtin).

**Total wall time: 5m3.3s (303.3s)**, 315/315 jobs, success.
(Contention note: background CPU load was ~47% from other processes
immediately before this run; treat the absolute number as an upper bound.)

Top ~15 slowest individual job durations reported by `lake build` (module,
duration as printed by Lake):

| Rank | Duration | Job |
|---|---|---|
| 1 | 198s | `Spikes.Spike2Fibonacci.Windows.Equivalence` |
| 2 | 135s | `Spikes.Spike5Gzip.Windows.Program:c.o` |
| 3 | 135s | `Spikes.Spike5Gzip.Equivalence` |
| 4 | 135s | `Spikes.Spike4HttpServer.Windows.Program:c.o` |
| 5 | 135s | `Spikes.Spike2Fibonacci.Windows.Program:c.o` |
| 6 | 135s | `Spikes.Spike2Fibonacci.Wasm.Test` |
| 7 | 135s | `Spikes.Spike2Fibonacci.Wasm.Equivalence:c.o` |
| 8 | 135s | `Spikes.Spike2Fibonacci.Wasm.Emit` |
| 9 | 135s | `Spikes.Spike1Hello.Windows.Program:c.o` |
| 10 | 135s | `Spikes.Spike1Hello.Windows.Equivalence` |
| 11 | 135s | `Spikes.Spike1Hello.Wasm.Equivalence:c.o` |
| 12 | 135s | `Spikes.Spike1Hello.Wasm.Emit` |
| 13 | 43s | `Spikes.Spike3SortLines.Wasm.Program` |
| 14 | 42s | `Spikes.Spike5Gzip.Wasm.Program` / `Spike4HttpServer.Wasm.Program` / `Spike2Fibonacci.Wasm.Program` / `Spike1Hello.Wasm.Program` / `Gasm.Targets.WASI.ABI:c.o` (5-way tie) |
| 15 | 20s | `Stdlib.SmolAlloc.Wasm:c.o` / `Gasm.Targets.Wasm.Text:c.o` (tie) |

Note on the tied durations: the 12-way tie at exactly 135s and the 5-way tie
at 42s are not a measurement artifact of this script — they are 12 (resp. 5)
independent jobs that all became unblocked at the same moment (once a shared
heavy upstream dependency — `Gasm.Targets.X86_64.Instructions` /
`Semantics`, or the Wasm equivalents — finished elaborating) and then each
ran for essentially the same amount of time. This is corroborating evidence
for the cascade analysis below: everything in the 135s tier is a
Windows-target Program/Equivalence/Emit/Test file that transitively imports
the X86_64 instruction-semantics stack.

## 3. Import-graph cascade analysis (Task 3)

Computed from a static parse of every `import` line across all 146 modules
(direct + transitive reverse-dependency closure). "Transitive fan-in" =
number of other modules that would need recompiling if this module's
`.lean` file changed.

Top fan-in modules:

| Transitive fan-in | Direct importers | Module |
|---|---|---|
| 120 | 91 | `Gasm.Core.Types` |
| 98 | 12 | `Gasm.Core.Arch` |
| 90 | 4 | `Gasm.Core.Obligations` |
| 87 | 2 | `Gasm.Core.Permissions` |
| 86 | 4 | `Gasm.Core.State` |
| 85 | 2 | `Gasm.Core.BlockM` |
| 84 | 5 | `Gasm.Core.CFG` |
| 84 | 6 | `Gasm.Core.Rng` |
| 81 | 47 | `Gasm.Targets.X86_64.Registers` |
| 81 | 4 | `Gasm.Targets.X86_64.Uop` |
| **80** | **33** | **`Gasm.Targets.X86_64.Instructions.Base`** |
| 64 | 20 | `Gasm.Effects.Inject` |
| 59 | 11 | `Gasm.Effects.Console` |
| 59 | 11 | `Gasm.Effects.Process` |
| 58 | 6 | `Gasm.Effects.Network` |
| **56** | **28** | **`Gasm.Targets.X86_64.Instructions`** |
| 50 | 2/3 | `Gasm.Effects.Clock` / `Gasm.Effects.FileSystem` |
| 49 | 17 | `Gasm.Effects.Trace` |
| 43 | 10 | `Gasm.Targets.X86_64.Semantics` |
| 42 | 10 | `Gasm.Targets.Windows.PEFormat` |
| **~40 each** | 9–14 | every individual instruction file: `Instructions.Mov`, `.Add`, `.Jcc`, `.Pop`, `.Lea`, `.Xor`, `.Push`, `.Div`, … |
| **8** | **2** | **`Stdlib.Zlib.Windows`** (Spike5's Windows Program + the `Stdlib` root aggregator only) |
| 0 | 0 | `Gasm.lean` / `Stdlib.lean` / `Spikes.lean` (nothing imports the root aggregators back) |

Key answers to the owner's specific questions:

- **"Does touching one instruction file recompile all spikes?" — Yes.**
  Every individual instruction file (e.g. `Instructions/Mov.lean`) is
  imported only via the `Instructions.lean` umbrella aggregator, which is in
  turn imported by 28 modules directly and 56 transitively — essentially
  every Windows-target spike Program/Equivalence/Test, the encoder/decoder/
  disassembler/assembler, both fuzzers, roundtrip tests, and (via
  `Stdlib.Zlib.Windows`) the zlib windows path. **Editing any one of the 21
  instruction files invalidates the same 56-module closure as editing all of
  them at once**, because the aggregator is a single compilation unit from
  every consumer's point of view. This matches the cold-build data above:
  the 12-way tie at 135s is exactly this closure lighting up together.
- **"Does touching `Zlib/Windows.lean` recompile anything beyond its
  dependents?" — No, and its blast radius is small.** Only 2 direct
  importers (`Spikes.Spike5Gzip.Windows.Program`, and the `Stdlib` root
  aggregator, which is cheap — see below) and 8 transitive total. Despite
  being the single largest file in the repo (2365 lines), it is **not** a
  build-cascade bottleneck for anyone else. Splitting it would mainly buy
  back elaboration/IDE latency for whoever is editing it directly (large
  single-file elaboration time), not reduce blast radius for other spikes.
- The root aggregators (`Gasm.lean`, `Stdlib.lean`, `Spikes.lean`) have
  **zero** downstream fan-in — nothing imports them back. Editing them is
  cheap; they exist purely to give the `lean_lib` targets their `roots`.
- `Gasm.Core.Types` has the single largest fan-in in the whole repo (120/146
  modules, 82%), followed by `Gasm.Core.Arch`/`Obligations`/`Permissions`/
  `State`/`BlockM`/`CFG`/`Rng` (all 84–98). These are foundational
  types/monad-state modules that (by their nature) are expected to change
  rarely — high cascade size but presumably low edit frequency.

### Ranked sharding proposal (edit-frequency × cascade-size), for iteration 2

No `.lean` splits were made this iteration (per instructions); this is a
priority-ordered proposal for the next iteration's module-split work:

1. **`Gasm/Targets/X86_64/Instructions.lean` (the 21-file aggregator).**
   Highest expected payoff. This is an actively-developed area (new
   instructions get added regularly — high edit frequency) with a 56-module
   transitive cascade, and it directly explains the 12-way-tied 135s cluster
   in the cold build (a meaningful fraction of total build time). The fix is
   *not* to shrink the aggregator file itself (it's already split into 21
   per-instruction files) but to stop treating it as one opaque compilation
   unit for consumers: downstream modules that only need a handful of
   instructions (e.g. a spike's `Emit.lean`) should import the specific
   `Instructions.Mov`/`Instructions.Add`/etc. files they use directly instead
   of importing the `Instructions` umbrella, and any dispatch table that
   currently lives in `Instructions.lean` and forces every consumer to see
   every instruction should be restructured (e.g. into a typeclass/registry
   pattern) so it doesn't create a single-file chokepoint. This is a REF-
   sensitive `.lean` restructuring — explicitly deferred to iteration 2.
2. **`Gasm/Targets/X86_64/Instructions/Base.lean`.** 80 transitive fan-in,
   33 direct importers (it's the shared base every instruction file itself
   imports). Any change here is already maximally expensive; worth
   confirming in iteration 2 whether everything in `Base.lean` truly needs
   to be shared, or whether some of it could be pushed down into only the
   instruction families that need it.
3. **`Gasm/Core/Types.lean` and friends (`Arch`, `Obligations`,
   `Permissions`, `State`, `BlockM`, `CFG`, `Rng`).** Largest raw cascade
   (84–120 modules) but likely low edit frequency once the core model
   stabilizes. Lower priority than #1/#2 *unless* churn data (git log
   frequency) says otherwise — worth checking `git log --follow -- Gasm/Core/Types.lean`
   commit frequency before investing here.
4. **`Stdlib/Zlib/Windows.lean` (2365 lines).** Confirmed *low* cascade
   impact (8 transitive dependents). Splitting it is still worthwhile for
   the person actively editing it (faster elaboration / IDE feedback on a
   single huge file) but should be ranked **below** #1–#3 for whole-build
   throughput purposes — it was mis-identified by file-size alone as a top
   suspect; the import graph shows it isn't a fan-out bottleneck.
5. **Root aggregators (`Gasm.lean`, `Stdlib.lean`, `Spikes.lean`) and
   `lakefile.toml`'s `defaultTargets`.** No sharding needed — zero
   transitive fan-in confirmed. Not a cascade risk.

## 4. Fixes applied this iteration (Task 4)

- No `lakefile.toml` / `.lean` changes were made to the *default* build
  path — the full `lake build` target set and behavior are unchanged
  (verified identical: 315/315 jobs, same target list).
- No-op rebuild bug: **root-caused, no code fix required** (see §1) — it is
  not a defect in this repo's build configuration.
- Added `scripts/dev_build.ps1` and `scripts/dev_build.sh`: optional,
  additive convenience scripts for local iteration that build just the 3
  `lean_lib` targets (`Gasm Stdlib Spikes`) via `lake build Gasm Stdlib Spikes`,
  skipping all 25 spike/fuzzer/test executables. This is **opt-in only** —
  `defaultTargets` in `lakefile.toml` is untouched, so plain `lake build`
  (the CI gate) still builds and links everything it always did. Useful for
  an agent that only needs fast type-checking feedback while iterating on
  library code and doesn't need every spike exe relinked.

## 5. Verification

- `lake build` (full, default targets): still succeeds, still reports
  "Build completed successfully (315 jobs)" — same target count / set as
  before this iteration's changes.
- `python scripts/check_refs.py`: exits 0 (unchanged: 155/300 sections
  referenced, 51.7% coverage — same as before touching anything).

## 6. Diff against future iterations

Future iterations should re-run `lake clean && lake build` under similar
background load and compare against the **303.3s** total / the per-job
table above, and re-run the no-op check (expect ~0.25–0.3s) to catch
regressions. If a fresh no-op build ever again takes minutes *and* it is
NOT the worktree's first build since creation, that would indicate a real
regression (unlike the one-time phantom rebuild explained in §1) and should
be investigated as an actual incremental-build bug.

## 7. Iteration 2 — Instructions.lean aggregator sharding (this task)

Date: 2026-08-27. Environment otherwise identical to §0, except background load was
heavier and more variable this time: 14–28 concurrent `lean.exe` processes observed
system-wide during measurement (other agents building concurrently on the same
machine), confirmed via `tasklist`. Absolute wall-clock numbers below are reported but
explicitly flagged as contention-skewed where the variance across repeated runs makes
that clear; **job counts are the reliable, contention-independent signal**.

### Design (mechanical restructuring — design_review: waived-mechanical, REF-preserving)

The umbrella `Instructions.lean` had two logically separate jobs bundled into one file:
(1) being the "true umbrella" — importing all 21 `Instructions/*.lean` submodules so
`Registry.lean`'s whole-environment `run_cmd` audit can see every registered
`X86_64Instruction` instance, and (2) hosting `X86_64Instr` (the `AnyX86_64Instruction`
abbrev), the `TargetArch X86_64` instance, and `X86_64Instr.toBinary` — three
declarations that only need `Instructions/Base.lean` (the open-existential wrapper and
generic typeclass dispatch already live there), not any of the 21 concrete instruction
families. Because both jobs lived in the same file, EVERY consumer that needed job (2)
— which turned out to be nearly everyone, since `X86_64Instr`/`TargetArch X86_64` is the
generic "an x86-64 instruction" vocabulary used throughout `Gasm.Targets.Windows.*`,
`Encoding.lean`, `Semantics.lean`, `HardwareHarness.lean`, `Core.Verification`, every
Spike's `Program.lean`/`Equivalence.lean`, and `Stdlib.SmolAlloc`/`Stdlib.Zlib.Windows`
— was forced to also import job (1)'s full 21-submodule closure, even when it never
touched a specific instruction family by name.

**The fix (import-graph surgery only, no new `.lean` files, no splits beyond relocating
existing declarations between two already-existing files):**
1. Moved `X86_64Instr`, `instance : TargetArch X86_64`, and `X86_64Instr.toBinary` (with
   their REF citations, verbatim) from `Instructions.lean` into `Instructions/Base.lean`,
   in a new `namespace Gasm.Targets.X86_64 ... end` block appended after Base.lean's own
   `Instructions` namespace closes (needed one added import: `Gasm.Core.Arch`, for
   `TargetArch`).
2. `Instructions.lean` is now purely the header comment + the 21-submodule import list —
   no code, no namespace body. It still imports every instruction submodule (the
   audit-completeness invariant is unchanged and explicitly preserved — see §7.4 below).
3. Retargeted the ~30 direct importers of the umbrella: all but two (`Registry.lean`,
   which needs the whole-environment audit, and `Decoder.lean`, which already imported
   every individual instruction submodule directly regardless of the umbrella) now
   import `Instructions.Base` instead, keeping whatever specific `Instructions.<Family>`
   imports they already had.
4. `Instructions/Base.lean` fan-in (80 transitive / 33 direct, per §3's table)
   investigated per the priority-3 item: its content (the `X86_64Instruction`
   typeclass, `AnyX86_64Instruction` wrapper, and ~30 generic helpers — REX/ModRM/SIB
   encoding, curated fuzz values, register lists) is genuinely shared by every single
   instruction family with no natural subdivision; not splitting this round.
5. Core churn check (priority-4 item): `git log --follow` shows `Gasm/Core/Types.lean`
   at 3 commits total and `Gasm/Core/Arch.lean` at 4, over the project's history —
   confirms the low-churn assumption in §3's proposal; deferred, as predicted.
6. `Stdlib/Zlib/Windows.lean` left untouched, per the priority-5 deprioritization.

### 7.1 Cascade measurement (the number that matters) — `touch Add.lean; lake build Gasm`

A comment-only touch to `Instructions/Add.lean` (no declaration change) triggered **zero**
downstream rebuilds beyond `Add.lean` itself — Lake/Lean's dependency tracking appears to
skip re-elaborating a downstream module when an upstream file's recompiled output isn't
semantically different, even though the source text changed. This is a real, useful
finding but not representative of an actual instruction edit, so the cascade numbers
below use a genuine content change instead (one extra `roundtripCases` entry appended to
`AddR64Imm8`, reverted after each measurement):

| | Jobs rebuilt / 93 | Wall time | Contention |
|---|---|---|---|
| Before (2 runs) | 38 / 93 | 147.5s | moderate |
| After, run 1 | 32 / 93 | 76.6s | moderate |
| After, run 2 | 32 / 93 | 70.9s | lighter |

**32/93 both after-runs — a consistent, contention-independent −16% job-count
reduction.** The 6 jobs that dropped out of the cascade entirely:
`Gasm.Targets.Windows.ABI`, `Gasm.Targets.Windows.Win32API`, `Gasm.Targets.X86_64.Semantics`,
`Gasm.Targets.X86_64.Encoding`, `Gasm.Targets.X86_64.HardwareHarness`,
`Gasm.Core.Verification` — exactly the "generic instruction consumer" class this fix
targets. The remaining 32-job cascade is `Add`, the (now-empty) `Instructions` umbrella,
`Assembler`/`Decoder` (which legitimately construct/decode `AddR64*` values — real
coupling, not incidental), `Disassembler` (via `Decoder`), `Roundtrip` (already imported
every family directly, pre-existing), `RoundtripGate.Common` (via `Decoder`), all 21
`RoundtripGate/*.lean` family shards + the `RoundtripGate` aggregator (all transitively
coupled through `Common`→`Decoder`, regardless of which family actually changed), `Registry`
(by design), `SemanticsFuzzer` (via `Registry`, by design), and `Gasm` (the root aggregator,
which directly imports `Add.lean` itself). This is the same "single chokepoint" pattern this
task fixed, but for the roundtrip-gate testing infrastructure — **not inherent**, per
`docs/TARGETS/X86_64.md` §5's own Stage B design: today's monolithic `Decoder.lean` is *why*
editing one instruction's decode branch invalidates every family's gate; Stage B's planned
per-instruction `tryDecode` co-located with a thin dispatcher would make editing one
instruction rebuild only that instruction's file, the dispatcher, and one composition lemma —
explicitly not this task's scope (deferred to B3, which depends on this task's import
restructuring having landed first), but a real fix, not a permanent property of the design.

Note on scope: this measurement is `lake build Gasm` (the `Gasm` library target, 93
modules), matching the task's specified command. The Spike/Stdlib import retargeting
(14 more files, e.g. `Spikes/Spike5Gzip/Windows/Program.lean`,
`Stdlib/Zlib/Windows.lean`) reduces fan-in for a full `lake build`/editing-a-spike
scenario but doesn't show up in this Gasm-scoped number, since `Spikes`/`Stdlib` are
separate `lean_lib` targets.

### 7.2 Cold build — `lake clean && lake build Gasm`

| | Jobs | Wall time |
|---|---|---|
| Before | 93/93 | 183.2s |
| After | 93/93 | 332.3s |

Same job count both sides (expected — no targets added/removed). The wall-time
regression is **not attributed to this task's changes**: it is contention-dominated.
The `Registry.lean` job alone (unchanged content, same `run_cmd` audit) took 10s in the
lightly-contended before-run and 147s in the after-run, with 14–28 concurrent `lean.exe`
processes observed system-wide at the time (other agents building concurrently, per the
task's own contention warning). Re-running the cascade measurement immediately
afterward under lighter load (§7.1, after-run 2) confirms the structural win is real;
the cold-build absolute number here is reported for completeness but should not be read
as a regression.

### 7.3 Full-build and gate verification (after the restructuring)

- `lake build` (full, 375 jobs, default targets): succeeds — same target set/count as
  before this iteration (one transient run failed with exit 1 and no error text mid-log,
  most likely a process kill from extreme concurrent-agent contention — 28 `lean.exe`
  processes observed at that moment; re-running from the same `.lake` cache completed
  the remaining jobs cleanly with no code changes, confirming it wasn't a real error).
- `lake exe test_roundtrip`: 1594/1594 tests passed.
- `python scripts/check_refs.py`: all citations valid, all declarations cited. Note this
  tool's own regex (`LEAN_DECL_REGEX`) does not match `abbrev` declarations at all and
  requires a name token after `instance`, so it only actually exercises coverage for the
  moved `X86_64Instr.toBinary` def among the three relocated declarations — its green
  result does not by itself evidence that the `X86_64Instr` abbrev's or the anonymous
  `TargetArch X86_64` instance's REF comments survived the move correctly. Both did
  survive intact (verified directly: the REF comment text is byte-identical to the
  original, and citations are repo-root-relative doc paths/anchors, which a file move
  cannot break) — just not via this tool's own coverage for those two declarations.
- `python scripts/check_gates.py`: 0 FAILING (not-allowlisted / unattributable /
  finite-forall / stale-entry) across 42 gated occurrences.
- `lake exe check_gates_axioms`: 5051 declarations scanned, 55 non-standard-axiom
  dependents, all 55 allowlisted, 0 not allowlisted.

### 7.4 Registry audit-completeness guarantee — explicitly re-verified

`Registry.lean` still imports the umbrella `Instructions.lean` (unchanged), which still
imports all 21 `Instructions/*.lean` submodules (unchanged) — the closure the audit
walks is identical to before this task. Verified this is still true, and that the
audit's known, pre-existing limitation (documented in both `Instructions.lean`'s and
`Registry.lean`'s own header comments: the audit walks the *live environment reachable
through the import graph*, not a filesystem scan, so a new instruction file that is
never imported anywhere is invisible to it) is unchanged by this task, by direct
experiment: added a scratch `Instructions/ZZZScratchDemo.lean` with a new
`X86_64Instruction` instance, imported nowhere. `lake build Gasm.Targets.X86_64.Instructions.ZZZScratchDemo`
compiled it successfully in isolation (13 jobs — it's valid Lean), but `lake build Gasm`
still reported exactly 93/93 jobs — the file was never scheduled, let alone seen by
`Registry.lean`'s `run_cmd` walk. Deleted immediately after (never committed). This
confirms the audit's closure guarantee is exactly as strong — and exactly as limited —
as it was before this task; this task did not reopen (or further narrow) that gap.
