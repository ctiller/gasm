# Continuous Integration Design

> **Status (2026-08-27): this document is the "CI location" decision.** `PLAN.md`
> records the decision as pending ("CI will be established
> (location: Craig chasing down)"), and `docs/tasks/TC6-ci-establishment.md` is explicitly
> `[b]` blocked on that decision, with instructions that a fresh agent must not pick a
> platform unilaterally. This document **is** that decision landing: GitHub Actions, with a
> `windows-latest`-hosted job as the primary gate today and a self-hosted Linux fleet (vendor
> lined up separately) joining the matrix once that hardware exists. See "Relationship to the
> TC5/TC6 tracker" at the end of this document for exactly what is and is not closed by this
> change.

## 1. Why GitHub Actions, why this split

The repository is about to go Apache-2.0 and public, which unlocks GitHub Actions on
GitHub-hosted runners at no incremental cost for a public repo, plus (once the owner's vendor
delivers) self-hosted Linux runners registered to the same repo. There is no third option that
needs evaluating here: the gates are 100% local verification (Lean's kernel, Python scripts,
CLI oracles already vendored or trivially installable) with **zero external services and zero
secrets** (§6 below), so any CI system that can check out the repo and run a shell is
sufficient, and GitHub Actions is what's already available.

## 2. Gate inventory (Pillar 1, `docs/REVIEW.md` §4.1)

This list is transcribed directly from `docs/REVIEW.md` §4.1 as it reads today, cross-checked
against `lakefile.toml` and `scripts/`, and **every command below was actually executed on
this machine during this task** (§8 has exit codes). Items marked "not present" are gates
`docs/REVIEW.md` or a Law names but that don't exist as a runnable script/target on this
branch — CI cannot invoke what doesn't exist, and this document says so plainly rather than
wiring in a path that would 404 the first time the workflow runs.

| # | Gate | Command | Windows | Linux |
|---|------|---------|:---:|:---:|
| 1 | Type & proof integrity | `lake build` | required | required |
| 2 | Citation audit (Law 1–3) | `python scripts/check_refs.py` | required | required |
| 3 | Reference integrity (Law 6) | `python scripts/check_references.py --offline` | required* | required* |
| 4a | Gate policy pre-check (Law 10) | `python scripts/check_gates.py` | required | required |
| 4b | Gate policy load-bearing check (Law 10) | `lake exe check_gates_axioms` (run from repo root — building it is not running it) | required | required |
| 5 | Apache-2.0 header compliance | `python scripts/check_licenses.py` | required | required |
| 6 | Decision-record integrity (D23/ADR-0035) | `python scripts/check_record.py` | required | required |
| 7 | Doc-facade linter (TC21 + TC22) | `python scripts/check_doc_facade.py` | required | required |
| 8 | Instructions.lean umbrella completeness (B3) | `python scripts/check_instructions_umbrella.py` | required | required |
| — | Roundtrip properties | `lake exe test_roundtrip` | required | required |
| — | Stdlib unit suites | `lake exe test_zlib`, `lake exe test_png`, `lake exe test_smolalloc` | required | required |
| — | x86-64 semantics fuzzer | `lake exe x86_fuzzer` (hardware oracle — emits a native PE and executes it against real silicon) | required | **not run** (§4) |
| — | Wasm semantics fuzzer | `lake exe wasm_fuzzer` (oracle: node) | required | required |
| — | x86-64 encoding fuzzer | `lake exe encoding_fuzzer` (oracle: NASM) | required | required |
| — | GZIP differential fuzzer (in-Lean) | `lake exe gzip_fuzzer` (oracle: python3/python/py) | required | required |
| — | Spike Wasm validator differential | `lake exe validate_spike_wasm` (oracle: node) | required | required |
| — | Spike 1/2/3 Wasm host-execution | `lake exe test_spike1_wasm`, `lake exe test_spike2_wasm`, `lake exe test_spike3_wasm` (oracle: node) | required | required |
| — | Spike 1–5 Windows PE emission | `lake exe spike1_hello_windows` … `lake exe spike5_gunzip_windows` | required | build+run (emit only, see §4) |
| — | Spike 1/2/3/4/5 Windows PE **execution** | `lake exe test_spike1_windows` … `lake exe test_spike5` (executes the emitted `.exe` as a child process) | required | **not run** (§4) |
| — | GZIP native-binary cross-fuzzer | `python scripts/fuzz_gzip.py` (executes the emitted `spike5_gzip.exe`/`spike5_gunzip.exe` natively) | required | **not run** (§4) |
| — | Microarchitectural perf fuzzer | `lake exe perf_fuzzer` | **excluded from hosted CI** (§5) | **excluded from hosted CI** (§5) |
| — | Calibration data governance (Law 14) | `python scripts/check_calibration.py` | **not present** (§7) | **not present** (§7) |
| — | Publishability gate (no third-party prose) | `python scripts/check_publishable.py` | required | required |

\* Item 3 is cache-dependent — see §7.

Everything in this table that is runnable was invoked directly in this task's verification
pass, on this machine, in the foreground, with exit codes captured without a pipe. See §8.

**Item 7 (`check_doc_facade.py`, TC21) rollout: blocking from day one, not a reporting-only
bake-in period.** A gate this large's own author considered starting new gates in a
reporting-only mode until an already-noisy tree goes clean, specifically because a concurrent
Linux-target design workstream (docs/TARGETS/) is actively writing new, legitimately
not-yet-implemented design prose while this gate ships, and a red CI that punishes honest
in-progress design work is worse than no gate (Law 13's own warning: a gate people learn to
ignore protects nothing). That default was overridden here because the actual precondition for
it didn't hold: running `check_doc_facade.py --self-test` and a full run against this tree, in
the foreground, found the tree already clean (0 blocking findings) after one fix (the
`progressProof` instance documented in `scripts/check_doc_facade.py`'s own module docstring and
`docs/REVIEW.md` Law 9) — there is no backlog of pre-existing violations a reporting-only period
would be buying time to clean up. The concurrent-work risk is real but is addressed at the
gate's design level instead: every trigger pattern requires a claim-shaped phrase adjacent to
the identifier (not bare "MUST", which is ordinary spec-writing vocabulary every design doc
uses) and honors the `**Status**:` escape hatch, and both were verified empirically against the
full current `docs/TARGETS/*.md`/`docs/GRAPHICS_ARCHITECTURE.md` tree (including the
in-progress, deliberately-unimplemented Linux target doc) to confirm zero incidental
collisions — see that module's docstring for the specific false positive (`` `warningAsError` ``)
an earlier, broader draft produced and how the design was tightened to eliminate it. Blocking
immediately is correct precisely because the gate is clean on arrival; if a future change makes
it newly noisy against legitimate in-progress work, that is itself a finding against this gate's
precision (Law 13) and should be fixed at the pattern level, not worked around with a
reporting-only carve-out.

## 3. Why removing `-Wl,--subsystem,console` from `lakefile.toml` was necessary and safe

Before this change, every `[[lean_exe]]` test/fuzzer/spike-test target in `lakefile.toml`
carried `moreLinkArgs = ["-Wl,--subsystem,console"]`. `--subsystem` is a PE/COFF-only linker
option (meaningful to `lld-link` / MinGW's `ld`); the ELF linker GitHub's `ubuntu-latest`
images use does not recognize it and would fail every one of those links. Since nearly every
gate above is one of those targets, an unmodified `lakefile.toml` would have meant Linux could
build only the three `lean_lib` targets (`Gasm`, `Stdlib`, `Spikes`) — pure elaboration, none
of the executable-backed gates.

This was verified empirically, not assumed:

1. Stripped the flag from every `[[lean_exe]]` entry.
2. `lake build` — all 380 jobs still succeeded (was already true before the change; this just
   confirms the strip didn't break the TOML).
3. `lake exe test_smolalloc` — still ran to completion, printed its full console output, and
   exited 0, identically to before the strip. Repeated for `check_gates_axioms` (5088
   declarations scanned, same result), `test_roundtrip` (1594/1594), and `x86_fuzzer` — all
   exit 0, output unchanged.

Conclusion: the flag was redundant on Windows (Lean/Lake's default link already produces a
console-subsystem binary there) and was the sole `lakefile.toml`-level obstacle to linking on
Linux. Removing it is a verified no-op on Windows and a verified fix for Linux linking. It does
**not** by itself prove the resulting binaries behave correctly when *run* on Linux — no Linux
machine was available in this task to confirm that — see §4 and §9's honest-gaps section.

## 4. Platform matrix: what Linux does and does not cover, and why

**Windows (`windows-latest`, hosted) is authoritative for every gate today.** It is where this
project's own dev machine lives, where every gate above has actually been run, and where the
x86-64 spikes emit and then *execute* real `.exe` binaries end-to-end.

**Linux (`ubuntu-latest`, hosted, today; self-hosted vendor hardware later) now builds and
runs the large majority of gates**, following the `lakefile.toml` fix in §3. What it still does
not cover, and why each is a *build-time-independent, execution-time* limitation rather than
something the linker fix could touch:

- **`x86_fuzzer`** (`Gasm.Targets.X86_64.SemanticsFuzzerCLI` / `SemanticsFuzzer` /
  `HardwareHarness`) is a *hardware* oracle, not a pure-Lean one: every run emits a native PE
  executable (via `Gasm.Targets.Windows.Emitter`/`Win32API`) and executes it directly against
  the host CPU, unconditionally, as its own mandatory "HARDWARE ORACLE SANITY CHECK" control
  vectors — it is not merely untested on Linux, it structurally cannot produce a result there.
  See the incident bullet below.
- **Executing an emitted Windows PE `.exe`** (`test_spike1_windows`, `test_spike2_windows`,
  `test_spike3_windows`, `test_spike4`, `test_spike5`) needs a Windows loader (or Wine, not
  installed and not proposed — adding an emulation layer to "verify Windows" is worse evidence
  than just running on real Windows). The *emitters* (`spikeN_..._windows`) still build and run
  on Linux — they only write bytes to a file — so Linux still gets signal that the emission
  code path executes without a runtime fault; it just can't confirm the resulting bytes are a
  correct, executable Windows binary. Only `windows-latest` closes that loop.
- **`scripts/fuzz_gzip.py`** spawns `lake exe spike5_gzip_windows`/`spike5_gunzip_windows` and
  then runs the resulting native `.exe` files directly as subprocesses — same limitation as
  above, inherited by a Python script rather than a Lean one.
- **`perf_fuzzer`** is excluded from both hosted platforms for a different reason — see §5.

**`test_spike3_wasm` was Windows-only for a different, now-fixed reason and is portable as of
this revision.** `Spikes/Spike3SortLines/Wasm/Test.lean` used to pipe stdin to `node` via a
hardcoded `cmd := "powershell.exe" ... "Get-Content ... -Raw | node -e ..."` shim (to work
around Lean's `IO.Process` not offering piped-stdin-from-a-file directly). That shim is gone:
the test now spawns `node` directly with `stdin := .piped`, via `IO.Process.output`'s `input?`
parameter, exactly like Spike 1/2's Wasm tests already did. It runs on both platforms now. See
the incident bullet below for why this needed fixing at all, not just for portability.

**Incident: CI run 33137239582 (`build_bare_metal_target`, another team's PR) — two false-red
failures, both CI/harness defects, neither in that team's code.**

1. **The Linux job ran `x86_fuzzer`.** Before this revision, `x86_fuzzer` was listed as
   `required`/`required` in the table above and was an actual (not skipped) step in the Linux
   job's PR-time block. On `ubuntu-latest` the control-vector PE cannot execute at all, so the
   gate's own fail-closed hardware-oracle-sanity check correctly aborted
   ("HARDWARE ORACLE SANITY CHECK FAILED: the harness could not execute the control vectors at
   all ... 0/272 expected bytes (exit code 255)"). That behavior is exactly right — the defect
   was CI running a hardware-execution gate on a platform with no path to execute it, not
   anything in the gate itself or in the PR under test. Fixed by removing the real invocation
   from the Linux job (§2's table now reads `not run` for Linux) and replacing it with an
   explicit always-`if: false` step (see below) so the omission is visible rather than a
   silent absence.
2. **`test_spike3_windows` failed intermittently with a BOM in its piped stdin.** The
   PowerShell shim described above (`Get-Content ... -Raw | .\spike3_sort.exe`) re-encoded the
   test input a second time on its way into the child's stdin; PowerShell's own pipe/console
   encoding is configuration-dependent and was observed injecting a UTF-8 BOM (`EF BB BF`) at
   the start of the piped bytes on some runs (`... got "apple\r\nbanana\r\n\uFEFFcherry\r\n"` —
   the sorter placed `\uFEFFcherry` correctly per its own lexicographic ordering, since `0xEF`
   sorts above `b`; the sorter was not the bug). Fixed in both `Spikes/Spike3SortLines/Windows/Test.lean`
   and `Spikes/Spike3SortLines/Wasm/Test.lean` (which shared the identical pattern) by dropping
   the PowerShell/temp-file intermediary entirely and spawning the child process directly with
   `stdin := .piped`, writing the test's exact bytes via `IO.Process.output`'s `input?`
   parameter (`Handle.putStr`, the same raw-UTF-8-no-BOM primitive `IO.FS.writeFile` itself
   uses) — never tolerating a leading BOM on the read side, which would have masked a real BOM
   defect instead of eliminating its source. A repo-wide search confirmed these were the only
   two stdin-piping call sites using this pattern.

**Visibility mechanism, corrected.** The matrix is written explicitly per-gate in the workflow
YAML (one step per gate, not one opaque "run everything" script), and every gate that is
Windows-only now has a same-named placeholder step in the Linux job's step list with
`if: false`, so GitHub's Checks UI always renders an explicit "Skipped" line for it — never a
gate that is simply absent from the job's step list, which is indistinguishable from nobody
having thought to add it. Before this revision, the claim that "Windows-only gates are named
explicitly rather than silently dropped" was only true at the source-comment level (the gaps
were named in the YAML's *comments*, per the block previously at the end of the Linux job) —
it was not true in the Checks UI itself, where a step with no entry at all in a job's step list
renders no differently from a gate nobody ever wired in. The `if: false` steps close that gap:
the claim is now true in the artifact a downstream team actually looks at, not only in this
document.

## 5. `perf_fuzzer`: the hardware carve-out

`Gasm/Targets/X86_64/PerfFuzzerCLI.lean` validates microarchitectural cycle-bound predictions
against a named CPU profile ("Intel Golden Cove" in the current model). `docs/tasks/TC6-ci-establishment.md`
already names this exact tension: *"a GitHub-hosted Actions runner cannot run the x86 hardware
semantics fuzzer against real silicon the way a self-hosted runner with the right CPU can."*
A shared/virtualized hosted vCPU does not give a trustworthy cycle-count signal (noisy
neighbors, masked/virtualized microarchitecture, no reliable low-level counters) — running
`perf_fuzzer` there would produce pass/fail noise attributable to the runner, not to the model,
which is worse than not running it: a red build that's "probably the runner, rerun it" trains
everyone to ignore red builds.

This is the honestly-documented, reviewed carve-out `docs/tasks/TC6-ci-establishment.md` asks
for, not a silent gap: `perf_fuzzer` is **not** invoked by either hosted workflow. It stays a
local-machine and (once available) vendor-hardware gate, run by hand today and wired into the
self-hosted Linux workflow the day that hardware is registered with a recorded, known CPU
profile (see Law 14 — calibration data governance is the same "measurement needs stated
hardware" principle applied to CI). This carve-out is itself Pillar-1-visible: both `ci.yml`
jobs carry a comment at the point in the step list where `perf_fuzzer` would otherwise go,
naming this section, so the omission reads as a decision, not an oversight.

## 6. Secrets

None. Every gate is local verification against either the Lean kernel, a vendored/generated
corpus, or a CLI oracle (NASM, Node, Python) installed by the workflow itself from each
runner's own package manager (`choco`/`apt-get`) or a pinned `actions/setup-*` action. No
workflow in this design calls an external API, uploads anywhere, or reads a repository secret.
If a future gate needs one, that is a deviation from this design worth a second look before
merging, per the original task brief's own framing.

## 7. Known gaps — named, not silently dropped

- **§4.1 item 3's swap has landed.** The vendored `references/` tree is deleted (1,019
  uncited third-party files plus the manifests removed outright; `references/wasm`'s 20
  files removed after its 99 citations were migrated to `references.json` slugs — see
  `PLAN.md`), `scripts/regenerate_references.py` and its test are deleted as dead code, and
  `ci.yml` now calls `python scripts/check_references.py --offline` followed by
  `python scripts/check_publishable.py` in both jobs, exactly as this section previously
  sketched.
  **New, concrete gap this exposes (not previously visible because the old gate didn't need a
  cache at all):** `--offline` validates against a local cache at `.cache/references/` that
  only `--refresh` populates, no CI step runs `--refresh`, and the cache is gitignored (never
  committed — see `.gitignore` and `scripts/check_references.py`'s own module docstring), so a
  fresh checkout's cache is always cold. Running `--refresh --all` on every push was considered
  and rejected: several registered entries deliberately track a rolling, unpinned upstream (e.g.
  `png-lodepng-cpp`, `spirv-grammar` track `master`/`main`; `vulkan-spec` tracks Khronos's
  rolling "latest" alias) specifically so `--refresh` reports drift when upstream moves — wiring
  that into a blocking every-push gate would turn CI red on a schedule owned by unrelated third
  parties, which is exactly the cadence/staleness problem the second bullet below already named
  as designed-but-not-implemented. Verified directly (§8): `--offline` exits 3 (cache missing)
  both before and after this migration — the failure population changed (was: `intel-sdm`'s
  267 citations plus the 16 pre-existing windows citations; now: those same citations, since
  none of them ever had a cache populated in this checkout either) but the exit code and root
  cause (cold cache, not a citation defect) did not. The 99 migrated wasm citations were
  independently verified clean against this exact gate by populating `.cache/references/`
  locally (uncommitted) with the freshly-fetched, hash-matching pages: 0 failures against any
  `wasm-*` slug. Closing this gap for real needs the scheduled-refresh + staleness-bound design
  in the next bullet, or an equivalent; that remains unimplemented.
- **`--refresh` scheduling — designed here, not yet wired.** `scripts/check_references.py`
  exists now (previous bullet), but this design is still unimplemented: it needs the
  timestamp-read/staleness-bound logic described below added to that script, which has not been
  done. An opt-in `--refresh` with no mandated cadence only moves the upstream-drift gap,
  it doesn't close it. The design: a weekly scheduled job (`schedule: cron: '0 6 * * 1'`, Monday
  06:00 UTC — infrequent because it only refreshes a registry against slow-moving upstream
  specs, not because of cost pressure) runs `python scripts/check_references.py --refresh`,
  commits/records a fresh timestamp file (e.g. `references.json`'s own `last_refreshed` field,
  or a small sidecar `references_refresh.stamp`) on success, and **fails loudly** (non-zero
  exit, not a skip) if the refresh itself can't complete — network failure, upstream 404,
  hash-mismatch on a pinned source. The default, every-push `--offline` gate then reads that
  same timestamp and fails if it is older than a stated bound (proposed: 45 days — long enough
  to absorb a missed week without false alarms, short enough that "the refresh job has been
  broken for months and nobody noticed" cannot happen silently). This makes "the scheduled job
  didn't run" and "the scheduled job ran and found real drift" both loud, on the very check
  that runs on every push, rather than requiring someone to remember to look at a separate
  schedule's history. This is designed, not implemented — implementing it means adding the
  timestamp-read/staleness-bound logic to `scripts/check_references.py --offline`, and adding a
  `--refresh` step to `scheduled.yml`'s weekly job; neither has been done. Until it is,
  `--offline` has a permanently cold cache in every CI run (previous bullet) — this is the gap
  that design would close.
- **`scripts/check_calibration.py` (Law 14) was referenced by `docs/REVIEW.md` line 155 as
  "registered in §4.1 Pillar 1" while §4.1's actual enumerated list did not include it, and
  the file does not exist.** Fixed in a later remediation pass (the D23/decision-record
  integrity pass): line 154 now states plainly that the gate is not yet implemented or
  registered, pending F2. (This item is resolved; left here as the record of what was found
  and when.)
- **`docs/REVIEW.md` §4.4's "Gate 1" line previously omitted `check_licenses.py` even though
  §4.1 item 5 requires it (a pre-existing cross-reference drift within `REVIEW.md` itself).**
  Fixed independently in two places that converged on the same line: the references-migration
  task re-pointed the line at `check_references.py --offline`/`check_publishable.py` while
  adding `check_licenses.py`; the decision-record integrity pass added `check_licenses.py` too
  and additionally appended `check_record.py`. Gate 1 now names every Pillar 1 gate,
  `check_licenses.py` and `check_record.py` included. (Resolved; left here as the record.)
- **The gate-runner single-entry-point (`docs/tasks/TC5-gate-runner.md`) has not landed on this
  branch.** `ci.yml`/`scheduled.yml` therefore invoke every gate as its own step rather than
  through one consolidated `scripts/run_gates.ps1`/`.sh`. This is deliberate, not a shortcut:
  TC5's own deliverables (a single machine-parseable summary, oracle-version pinning inside the
  runner itself, planted-defect meta-gate fixtures) are real, separate work this task does not
  claim to have done. Per-step invocation is also arguably *better* CI ergonomics on GitHub
  specifically — each step gets its own pass/fail in the Checks UI, which is what TC6's
  acceptance bar ("a failing check names which specific gate failed") actually asks for — but
  the day TC5 lands, both workflows should be simplified to call it, per TC5's own note that
  "TC6 is a thin wrapper around TC5, not a reimplementation of the gate list."
- **`test_spike3_wasm`'s `powershell.exe` dependency** (§4) was a Spike-code portability gap,
  previously named here as not fixed in this design's original pass. It is fixed now — see §4's
  incident bullet — and the gate has been moved into the Linux job's required set. (Resolved;
  left here as the record.)
- **Spike 1/2 Windows emit-then-test ordering.** `test_spike1_windows`/`test_spike2_windows`
  do *not* auto-emit their `.exe` if it's missing (unlike Spike 3/4/5, whose `Test.lean` calls
  `emitVerifiedWasmBinary`/equivalent inline) — running the Test executable first fails with
  "the system cannot find the file specified," not a gate failure, just a step-ordering trap.
  Verified directly (§8) and the workflow orders `spike1_hello_windows`/`spike2_fibonacci_windows`
  before their respective `test_spike*_windows` steps to avoid it. Worth fixing at the source
  (make Spike 1/2 self-emitting like 3/4/5) for consistency, but that's a Spike-code change,
  not a CI-wiring one, and is a candidate for the out-of-scope-findings backlog.
- **The Linux job is new and unverified on real Linux hardware.** Everything in §3/§4's
  Linux column is either directly measured on Windows (the linker-flag fix) or reasoned from
  reading the actual Lean source of each gate (portable `IO.Process` oracle names, no
  hardcoded Windows paths outside the items named as Windows-only) — there was no Linux machine
  available to this task to confirm it end-to-end. Expect a short bring-up iteration on the
  first real `ubuntu-latest` run; if a specific "should be portable" gate turns out not to be,
  move it to the Windows-only list in the table in §2 rather than disabling the Linux job.

## 8. Verification performed (this task, on this machine, foreground, direct exit codes)

All commands below were run from the repository root with output redirected to a file (never
piped through another process before the exit code was captured), and the shell's exit code
was captured immediately (`echo "...EXIT=$?"`) on the next line — no pipe, `tee`, or pager sat
between the command and the exit-code read, which is the exact failure this project has already
been bitten by once (Merge Train 2's tail-swallowed-exit-code self-finding, `docs/tasks/TC5-gate-runner.md`).

| Command | Exit code |
|---|---|
| `lake build` (380 jobs, cold-ish, with the old `-Wl,--subsystem,console` flags still present) | 0 (real 4m53s) |
| `lake build` (380 jobs, after stripping the flag from every `[[lean_exe]]`) | 0 (real 7s — mostly relink of already-elaborated modules) |
| `python scripts/check_refs.py` | 0 |
| `python scripts/check_gates.py` | 0 |
| `python scripts/check_licenses.py` | 0 |
| `python scripts/regenerate_references.py --verify` | 0 |
| `lake exe check_gates_axioms` | 0 (5088 declarations scanned, 56/56 allowlisted, 0 unauthorized) |
| `lake exe test_roundtrip` | 0 (1594/1594) |
| `lake exe test_zlib` / `test_png` / `test_smolalloc` | 0 / 0 / 0 |
| `lake exe x86_fuzzer -- -n 20` / `wasm_fuzzer -- -n 20` / `perf_fuzzer -- --count 10` | 0 / 0 / 0 |
| `lake exe validate_spike_wasm` | 0 |
| `lake exe encoding_fuzzer -- --count 5` (real NASM found at the hardcoded personal fallback path) | 0 |
| `lake exe encoding_fuzzer -- --count 5 --nasm doesnotexist_nasm.exe` (**fail-closed control**) | **1**, aborted at the oracle control-vector step with an uncaught-exception message — never a synthesized pass |
| `lake exe gzip_fuzzer -- --count 20` | 0 |
| `lake exe test_spike1_windows` / `test_spike2_windows` (before emitting `hello.exe`/`fib.exe`) | **1** each — "system cannot find the file specified" (§7's ordering trap, not a gate bug) |
| `lake exe spike1_hello_windows` / `spike2_fibonacci_windows` then `test_spike1_windows` / `test_spike2_windows` | 0 / 0 / 0 / 0 |
| `lake exe test_spike3_windows` / `test_spike4` / `test_spike5` (self-emitting) | 0 / 0 / 0 |
| `lake exe test_spike1_wasm` / `test_spike2_wasm` / `test_spike3_wasm` | 0 / 0 / 0 |
| `python scripts/fuzz_gzip.py` | 0 (61 vectors, 5 execution paths) |

The `encoding_fuzzer`/NASM-absent row is this task's fail-closed demonstration (the analogue of
what `docs/tasks/TC5-gate-runner.md` asks for with NASM/node absent): pointing `--nasm` at a
nonexistent path makes the whole run abort with exit 1 at the "verifying NASM oracle control
vectors" step, not a skipped-but-green line. `wasm_fuzzer`/node-absent was not separately
re-demonstrated in this task (node is present on this machine and temporarily hiding it was
judged higher-risk to the rest of the verification pass than the marginal evidence gained) —
`Spikes/Common/WasmHostRunner.lean`'s `HostRunOutcome.runnerAbsent` path (exit code `2`,
documented in `docs/SPIKES.md` §4 item 5) already codifies the same fail-closed contract for
the Spike 1/2 Wasm tests specifically, and was read directly rather than re-triggered.

## 8a. Verification performed for the CI run 33137239582 incident fix (this task)

Same discipline as §8 — every command below was run from the repository root in the
foreground, with its exit code captured directly (`$LASTEXITCODE`/`echo "...EXIT=$?"`) on the
next line, never through a pipe, `tee`, or pager.

| Command | Exit code |
|---|---|
| `lake build` (422 jobs) | 0 (real ~6m50s) |
| `python scripts/check_refs.py` | 0 |
| `python scripts/check_gates.py` | 0 |
| `python scripts/check_licenses.py` | 0 |
| `python scripts/check_record.py` | 0 |
| `python scripts/check_doc_facade.py` | 0 |
| `python scripts/check_publishable.py` | 0 |
| `lake exe check_gates_axioms` | 0 (5818 declarations scanned, 84/84 allowlisted, 0 unauthorized) |
| `lake exe check_refs_coverage` | 0 (1347 top-level declarations scanned, 0 uncited) |
| `lake exe x86_fuzzer -- -n 20` (Windows — unaffected by the CI-wiring fix; run to confirm the code itself was untouched) | 0 |
| `lake exe test_spike3_windows`, run 5 consecutive times | 0 / 0 / 0 / 0 / 0, byte-identical stdout each run (`"apple\r\nbanana\r\ncherry\r\n"`, no BOM) |
| `lake exe test_spike3_wasm`, run 5 consecutive times | 0 / 0 / 0 / 0 / 0, byte-identical stdout each run |

The `test_spike3_windows`/`test_spike3_wasm` repeated runs are the fix's actual evidence: both
now spawn their child process directly with `stdin := .piped` (via `IO.Process.output`'s
`input?` parameter) instead of shelling through `powershell.exe -Command "Get-Content ... -Raw
| ..."`, eliminating the text-mode re-encoding step that had been observed injecting a UTF-8
BOM into the piped bytes. Five consecutive green, byte-identical runs of each is the repeated
demonstration that the flakiness is gone, not merely unreproduced once. A repo-wide grep for
`powershell.exe`/`Get-Content` in `*.lean` before this fix found exactly these two call sites
(`Spikes/Spike3SortLines/Windows/Test.lean`, `Spikes/Spike3SortLines/Wasm/Test.lean`) and none
elsewhere — no other test shares this pattern.

`x86_fuzzer` was re-run on Windows purely as a control: this task's fix to that gate is
CI-wiring only (§2's table, §4), and its Lean source was not touched, so this run confirms the
gate itself still passes and the fix did not regress the platform where it is authoritative.

This task's own branch was pushed to GitHub after these changes so both hosted jobs
(`windows`, `linux`) run for real — a real runner on both platforms is the only authoritative
evidence for the Linux-side half of this fix, which this local machine cannot provide (§7's
"Linux job is new and unverified on real Linux hardware" gap still applies to the *new* Linux
step, `test_spike3_wasm`, exactly as it applied to every other Linux-column entry before it).

## 9. Caching strategy and why it cannot serve a stale or poisoned artifact

Two independent caches, both restored via `actions/cache`:

1. **Toolchain (`~/.elan`, `~\.elan` on Windows).** Key: `${{ runner.os }}-elan-${{ hashFiles('lean-toolchain') }}`.
   The toolchain a given `lean-toolchain` content names is immutable once published upstream
   (a version tag doesn't get silently republished), so this cache never needs an
   OS/toolchain-crossing restore-key fallback — a miss just means a fresh elan install, correct
   either way.
2. **Build artifacts (`.lake/build`).** Key:
   `${{ runner.os }}-lake-${{ hashFiles('lean-toolchain') }}-${{ hashFiles('lakefile.toml', 'lake-manifest.json') }}-${{ hashFiles('Gasm/**/*.lean', 'Stdlib/**/*.lean', 'Spikes/**/*.lean', 'Tools/**/*.lean', '*.lean') }}`,
   with `restore-keys` falling back to progressively shorter prefixes of the same key (toolchain
   match only, then OS only) so a near-miss (one file changed) still seeds from a mostly-current
   cache rather than rebuilding from nothing.

**Soundness argument — why a stale or even deliberately-poisoned cache entry cannot produce a
wrong gate result, only a slower one:** Lake is a content/hash-verified incremental build
system, not a blind mtime cache. Every `.olean`/`.o` Lake considers reusing carries a recorded
trace of the inputs (source hash, dependency hashes, compiler options) that produced it; before
reusing anything from a restored cache, Lake re-derives the current trace from the actual
checked-out source and compares it to what the artifact recorded. A cache entry that doesn't
match — because the key partially missed, because someone hand-edited a cached file, because
two different branches' artifacts collided — is simply not reused; Lake rebuilds that module
from source. The GitHub Actions cache key scheme above exists purely to make cache *hits* more
frequent (faster CI), not to establish correctness — correctness is Lake's own job and would
hold even with a single global cache key shared by every branch. This is also why the key
intentionally does *not* try to be maximally precise (e.g. down to individual file lists it
would need to keep hand-maintained): an imprecise key costs at most a few extra minutes of
rebuild on a near-miss, never a wrong build.

**Build duration as an observable metric.** Both `ci.yml` jobs wrap the `lake build` step with
explicit wall-clock timing (`Measure-Command` on Windows, `time` on Linux) and echo the result
into both the step log and the job summary (`$GITHUB_STEP_SUMMARY`), so a build-time regression
is visible in the Checks UI trend without needing a separate dashboard. Baseline measured in
this task on the owner's dev machine: **cold, 380 jobs, ~4m53s–8m real time** (variance was
almost entirely re-elaboration vs. relink-only — see §8's two `lake build` rows); a
hosted-runner cold run should be budgeted more generously (weaker single-core turbo than a dev
workstation, and the toolchain-cache row above is itself a cold miss the very first time this
workflow runs). Both jobs use a 30-minute job timeout, chosen as roughly 4x the observed local
cold-build time to leave headroom without masking a genuine hang.

## 10. Cost split: push vs. pull request vs. schedule

- **Every push (any branch):** the fast subset only — `lake build`, the four Pillar-1 §4.1
  items (citation, reference, gate-policy ×2, license), and the four quick unit/roundtrip
  suites (`test_roundtrip`, `test_zlib`, `test_png`, `test_smolalloc`). This is the tightest
  feedback loop for iterative work on a branch (which, per the branch list in this repo today,
  is where almost all work actually happens), and every one of these gates completes in low
  tens of seconds once `lake build` itself is warm.
- **Every `pull_request` targeting `main`:** everything in the push set, plus every differential
  fuzzer (`x86_fuzzer`, `wasm_fuzzer`, `encoding_fuzzer`, `gzip_fuzzer`, `validate_spike_wasm`)
  and every spike emission/execution gate, i.e. the full table in §2 minus the two named
  exclusions. This is `docs/REVIEW.md` §4.4 Gate 1 in full, gating the point where code is
  actually proposed for merge — the right point to pay the full ~5–10 extra minutes of fuzzing,
  not on every intermediate commit of a branch still being iterated on.
- **Scheduled (weekly, `workflow_dispatch`-able on demand):** the same fuzzers as the PR set,
  re-run with substantially higher iteration counts (10–50x the PR-time `--count`/`-n`) to catch
  rare divergences a fast PR-time run would miss by construction, on a cadence bounded enough
  that a real regression surfaces within a week rather than only whenever someone happens to
  touch the affected code. §7 also names where the future reference-refresh job slots into this
  same scheduled workflow once its target script exists.

This split is the direct cost lever the brief asked for: push-time cost is bounded by the
fastest gates and scales with how often the owner actually pushes; PR-time cost is paid once
per proposed merge, not once per commit; the expensive, long-running fuzzing campaigns are
paid for on a fixed, small, predictable schedule instead of on every push.

## 11. Relationship to the TC5/TC6 tracker

- **TC6 (`docs/tasks/TC6-ci-establishment.md`)** was blocked on exactly one thing: "Craig
  determining where CI runs." This document, plus the workflows it describes, is that decision
  landing. `TASKS.md` and `TC6-ci-establishment.md`'s status fields are updated alongside this
  document (from `[b]` blocked to `[~]` implementing) to reflect that the blocker is resolved —
  not that TC6 is fully closed, since TC6's own acceptance bar is written against TC5 landing
  first and TC5 has not (next bullet).
- **TC5 (`docs/tasks/TC5-gate-runner.md`)** — the consolidated `scripts/run_gates.ps1`/`.sh`
  entry point, with its own oracle-version-pinning and planted-defect meta-gate-fixture
  deliverables — has **not** landed on this branch. This design invokes every gate directly
  rather than through that not-yet-existing script, per §7's explicit note. Nothing in this
  document should be read as TC5 being complete.

## Reference integrity: why it runs on a schedule, not per push

`scripts/check_references.py --offline` verifies that the bytes in the local
`.cache/references/` still hash to what `references.json` records. That cache can
never exist in a fresh CI checkout, because it holds third-party documentation
prose and D25 forbids committing such prose to the tree. Run per push, the step
therefore fails structurally (exit 3, cold cache) without ever checking anything.

It now runs in `scheduled.yml` as `--refresh`, which re-fetches each registered
document and compares it against the recorded hash. That is the one place a
network fetch is legitimate.

**This is a cadence change, not a dropped gate.** Per-push coverage is unchanged
and network-free:

- `check_refs.py` fails on any citation whose slug is absent from `references.json`.
- `check_publishable.py` fails on any third-party prose in the tree, or any
  citation resolving into `references/`.

What moved is only the part that needs the network: confirming upstream still
serves what the registry pinned. Drift found by the scheduled job is a real
finding requiring a human re-pin (`--acknowledge-drift` with `--reviewer` and
`--review-note`), never a silent hash update.

**Known gap, stated rather than hidden:** nothing yet bounds how stale that
verification may be — if the scheduled job stops running, no gate notices. A
staleness bound belongs with the `last_refresh` timestamp design in
`docs/REFERENCE_INDEX.md`.
