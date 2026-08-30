# Continuous Integration Design

> **Status (2026-08-29): GitHub Actions is the selected CI platform.** Current hosted CI uses an
> Ubuntu-only linter job plus `windows-latest`/`ubuntu-latest` matrices for proof, spike, and
> fuzzer jobs. A self-hosted Linux fleet is future work; it is not part of either current
> workflow. See §11 for the boundary between repository-local gate policy and CI selection.

## 1. Why GitHub Actions, why this split

GitHub Actions can run the repository's Lean, Python, and CLI-oracle checks on hosted Windows
and Ubuntu runners. No repository secrets are required. The workflows are not network-free:
they download toolchains and oracle packages, and the scheduled reference audit fetches the
registered upstream documents. That network use is explicit and is separate from the
deterministic, repository-local checks.

## 2. Current gate inventory and selection

Three inventories have different meanings and must not be conflated:

1. `scripts/run_gates.py --list-groups` is the executable table for the unfiltered local gate.
2. `.github/workflows/ci.yml` and `scheduled.yml` select event- and platform-specific subsets.
3. `lakefile.toml` declares buildable targets. A declared `lean_exe` is not automatically a
   gate, and `lake build` only builds `defaultTargets`; it does not execute test binaries.

The current hosted selection is:

| CI slice | Events | Platform | Commands selected |
|---|---|---|---|
| Linters | push, PR, manual | Ubuntu once | `check_refs`, `check_full_refs_gate_wiring`, `check_no_exception_ledgers`, `check_no_ignored_lean_sources`, `check_verification_authority`, `check_gates`, `check_publishable`, `check_licenses`, `check_doc_facade`, `check_orphan_modules`, `check_instructions_umbrella` |
| Proofs | push, PR, manual | Windows + Ubuntu | `python scripts/build_full.py`, then the complete `proofs` group: the explicitly opted-in full-repository `check_refs_coverage` launcher, `check_gates_axioms`, `test_roundtrip`, `check_x86_obligations`, `check_aarch64_obligations` |
| Fast tests | push | Windows + Ubuntu | `python scripts/build_full.py`, then `test_zlib`, `test_png`, `test_smolalloc` |
| Spike tests | PR, manual | Windows | the three Stdlib tests, Windows Spike 1–5 tests, and Wasm Spike 1–3 tests |
| Spike tests | PR, manual | Ubuntu | the three Stdlib tests, x86 bare-metal/AArch64 bare-metal/AArch64 Linux Spike 1 tests, and Wasm Spike 1–3 tests |
| Fuzzers | PR, manual | Windows, two shards | the complete eight-entry `fuzzers` group, including `perf_fuzzer` and `x86_fuzzer` |
| Fuzzers | PR, manual | Ubuntu, two shards | `wasm_fuzzer`, `encoding_fuzzer`, `gzip_fuzzer`, `png_stability_fuzzer`, `x86_stability_fuzzer`, `elf_stability_fuzzer` |
| Reference refresh | weekly, manual | Windows + Ubuntu | `check_references.py --refresh --all` |
| Extended fuzzing | weekly, manual | Windows + Ubuntu | `x86_fuzzer`, `wasm_fuzzer`, `encoding_fuzzer`, `gzip_fuzzer`; Windows additionally runs `scripts/fuzz_gzip.py` |

The canonical declaration-coverage command is
`python scripts/run_full_refs_coverage.py --full-repository`. CI may instead set
`GASM_RUN_FULL_REFS_COVERAGE=1`. The launcher deliberately refuses an unacknowledged local run
before starting Lake: this authority-preserving gate imports and scans the complete
Gasm/Stdlib/Spikes compiled environment and can schedule hundreds of modules. In one partially
warm incident it scheduled 616 targets, exceeded 23 minutes before cancellation, and was observed
near 28 GiB aggregate memory with one Lean process near 17 GiB. Those observations are diagnostic,
not fixed requirements; cost depends on tree, cache, machine, and concurrency. Focused commands
such as `lake exe test_graphics_foundation` remain useful inner-loop checks but do not replace the
full gate.

Every Lean-bearing hosted job runs `python scripts/check_no_ignored_lean_sources.py` before its
cached build.  The gate requires the filesystem source census, unreplaced `HEAD`, and the sole
ordinary stage-0 index to identify the same Lean sources and bytes (apart from CRLF-to-LF
normalization), and rejects source indirection plus source-less stale `.olean` files.  This ordering
is load-bearing: cache validation cannot establish which source text a missing module came from.

The canonical authoritative build command is `python scripts/build_full.py`. It reads the exact
`defaultTargets` list from `lakefile.toml`, builds those roots sequentially in declared order, and
finishes with `lake --no-build build`. The final step is load-bearing: it proves that the same bare
default closure is current and fails if a phase or target drift left any work undone. This changes
neither proof coverage nor target membership; it prevents independent Gasm/Stdlib/Spikes and gate
roots from becoming runnable in one high-fan-out wave.

Before those roots, the launcher derives each local default-root import closure from the Lean
sources and prebuilds it in dependency-first waves. The automatic wave size budgets approximately
1.8 GiB of physical memory per concurrent module and is capped at 16; set
`GASM_LEAN_NORMALIZATION_BATCH_SIZE` to an exact positive size for a measured host-specific
override. These are redundant builds of modules already in the default closure, not a narrower
validation surface, and the final bare no-build check remains authoritative.

For one or more edited Lean files, use
`python scripts/check_lean.py path/to/Module.lean` instead of `lake env lean path/to/Module.lean`.
The focused launcher builds each module's Lake `:olean` target sequentially under the host-global
lease. This makes the result reusable by later checks and turns an unchanged repeat into a cheap
trace check; direct `lake env lean` elaboration does not populate that module cache. A focused
check remains an inner-loop tool and does not replace `python scripts/build_full.py` before review.

All canonical Lean/Lake launchers also share one host-global OS file lease. The lease is common
across worktrees, releases automatically if its owner crashes, and on Windows keeps an adaptive
reserve before starting a child tree: 30% of commit (capped at 32 GiB) and 25% of physical memory
(capped at 12 GiB), with small-host floors of 4 GiB and 2 GiB respectively. This
reserve protects the desktop app and shared GPU/driver commitments as well as the compiler;
dedicated-video-memory wording does not imply that system commit was uninvolved.
`GASM_LEAN_COMMIT_RESERVE_GIB`, `GASM_LEAN_PHYSICAL_RESERVE_GIB`, and
`GASM_LEAN_LEASE_TIMEOUT_SECONDS` are explicit operational overrides. `run_gates.py --parallel`
keeps proof gates sequential and caps other automatic worker pools at two; even an explicit
`--jobs` value cannot overlap canonical Lean/Lake trees, though non-Lean tools may still overlap.

The unfiltered local command, `python scripts/run_gates.py` with no selection flags, is
intentionally broader than any one hosted job. Its table currently contains one build gate,
twelve linters (including the cache-dependent `check_references_offline`), five proof gates,
nineteen spike/test gates, and eight fuzzers. Grouped, sharded, or `--gate`-filtered invocations
return success for their selected subset; they are CI building blocks, not evidence that the
unfiltered local gate ran. Section 7 records intentional CI omissions separately from wiring
defects and Lake executables that are not registered as gates.

## 3. Why removing `-Wl,--subsystem,console` from `lakefile.toml` was necessary and safe

`--subsystem` is a PE/COFF linker option and is not accepted by the ELF linker used on Ubuntu.
The repository therefore does not attach `-Wl,--subsystem,console` to its `lean_exe` targets.
Lean/Lake already produces console executables on Windows without that override. This is a
link-portability requirement only; it says nothing about whether a target's runtime behavior is
portable. Runtime/platform restrictions are handled by the CI selection in §4.

## 4. Platform matrix: what Linux does and does not cover, and why

The matrix is not an authoritative/secondary split. Both hosted operating systems run builds,
proofs, the roundtrip test, and the fast Stdlib suites. The Python linters run once on Ubuntu
because their behavior is intended to be platform-neutral. PR/manual spike coverage then
diverges by runtime: Windows selects the Windows PE tests, while Ubuntu selects the QEMU-backed
bare-metal and AArch64 tests. Wasm Spike 1–3 tests run on both.

Two gates have genuine hardware/platform constraints:

- `x86_fuzzer` emits and executes a Windows PE hardware-oracle program. Regular Ubuntu PR CI
  correctly omits it. The scheduled workflow currently invokes it on Ubuntu anyway; that is a
  workflow defect, not Linux coverage.
- `scripts/fuzz_gzip.py` executes generated Windows PE binaries and therefore runs only in the
  Windows leg of the scheduled workflow.

The current workflow does not create one GitHub step per gate and has no same-named `if: false`
placeholder steps. Each job invokes a grouped or filtered `run_gates.py` command, so the Checks
UI identifies the failing group/job and the runner's own output identifies the individual gate.
Platform omissions must therefore remain explicit in this document and in the workflow's gate
filters; the UI does not synthesize skipped entries for them.

## 5. `perf_fuzzer`: the hardware carve-out

`Gasm/Targets/X86_64/PerfFuzzerCLI.lean` has two materially different modes. The ordinary
`lake exe perf_fuzzer` command fuzzes deterministic invariants in the Golden Cove *model* and
samples no host timing; it is valid on a hosted runner, and Windows PR/manual CI runs it. The
explicit `lake exe perf_fuzzer -- --hardware` mode emits and executes an RDTSC/RDTSCP harness.
A shared hosted vCPU is not acceptance-grade evidence for that mode: scheduling noise and a
masked or virtualized CPU identity make cycle measurements difficult to interpret. Hardware
mode therefore remains local/self-hosted-only, with calibration provenance under Law 14. No
current workflow passes `--hardware`.

## 6. Secrets

No current workflow reads a repository secret. Hosted jobs do make outbound requests to install
Elan, Node, Python, NASM, and QEMU, and the scheduled reference check fetches URLs from
`references.json`. Those dependencies are public downloads, not secret-backed services. A
future gate that needs credentials is a design change and must document its trust and fork-PR
behavior before being enabled.

## 7. Known gaps — named, not silently dropped

- **Reference refresh has no staleness watchdog.** `scheduled.yml` runs
  `python scripts/check_references.py --refresh --all` in both matrix legs. No durable
  last-success timestamp or PR-time staleness deadline detects a schedule that stopped running.
  The cache-dependent `--offline` audit remains an intentional unfiltered-local gate and is
  intentionally absent from cold-checkout CI.
- **Filtered spike jobs omit required emitter gates.** `run_gates.py` records dependencies for
  `test_spike1_windows`, `test_spike2_windows`, `test_spike1_baremetal`,
  `test_spike1_aarch64_baremetal`, and `test_spike1_aarch64_linux`. The workflow selects those
  tests without their emitter keys. Because dependencies outside the selected key set are
  filtered out, the runner does not schedule the emitters first. This is a CI-selection defect;
  the unfiltered local gate does include and order those emitters.
- **One hosted hardware selection remains contradictory.** The scheduled Ubuntu leg invokes
  `x86_fuzzer`, although that gate emits and
  executes a Windows PE hardware oracle. Regular Ubuntu PR CI correctly omits it.
- **Several runnable checks are outside the consolidated table.** The Lake executables
  `test_spike1_linux`, `test_spike2_linux`, `test_spike3_linux`, `test_http11`, `test_fmt`, and
  `validate_spike_wasm` exist but are absent from `run_gates.py` and both workflows.
  `scripts/fuzz_gzip.py` runs only in the Windows scheduled leg, not in the unfiltered local
  runner or PR CI. These are omissions, not coverage supplied by `lake build`.
- **Calibration governance is still design-only.** `scripts/check_calibration.py` does not
  exist and is not registered in `docs/REVIEW.md` §4.1 or `run_gates.py`; Law 14 and
  `docs/CALIBRATION_GOVERNANCE.md` disclose that status.

## 8. Verification evidence

This document describes current policy and wiring; it is not a durable store for one
developer's machine timings, job counts, tool paths, or historical pass totals. Current evidence
comes from the workflow run attached to the commit and from the gate runner's direct exit codes
and per-gate summary. Gate commands must not be piped through a command that masks their exit
status. Changes to this document are checked by `check_refs.py` and `check_doc_facade.py`.

## 9. Caching strategy

Two independent caches, both restored via `actions/cache`:

1. **Toolchain (`~/.elan`, `~\.elan` on Windows).** Key:
   `${{ runner.os }}-elan-${{ hashFiles('lean-toolchain') }}`. There is no cross-OS restore key.
2. **Build artifacts (`.lake/build`).** Key:
   `${{ runner.os }}-lake-${{ hashFiles('lean-toolchain') }}-${{ hashFiles('lakefile.toml', 'lake-manifest.json') }}-${{ hashFiles('Gasm/**/*.lean', 'Stdlib/**/*.lean', 'Spikes/**/*.lean', 'Tools/**/*.lean', '*.lean') }}`,
   with progressively shorter same-OS restore prefixes so a near match can seed an incremental
   build.

Every Lean-bearing job runs `python scripts/build_full.py` after cache restoration. The cache is an optimization,
not proof evidence by itself. The current workflows do not run `lake clean`, and this document
does not claim that an arbitrary or deliberately modified cache can only affect performance.
Where a clean-rebuild contract is required, use the unfiltered local runner with `--clean` or
add an explicit clean CI job.

The workflows currently do not wrap the phased full build with `Measure-Command`/`time` and do not write
build durations to `$GITHUB_STEP_SUMMARY`. Job logs and GitHub's job duration are the only timing
signals until explicit instrumentation is added.

## 10. Cost split: push vs. pull request vs. schedule

- **Every push (any branch):** the Ubuntu linter subset, Windows+Ubuntu builds and proof group,
  and Windows+Ubuntu `test_zlib`/`test_png`/`test_smolalloc`. This includes `test_roundtrip`, both
  obligation gates, citation coverage, and the axiom gate. It deliberately omits the
  cache-dependent reference-byte audit, spike execution beyond the three Stdlib suites, and all
  fuzzers.
- **Every pull request targeting `main`, plus manual `ci.yml` dispatch:** the push set, the
  platform-specific spike selections, and the sharded fuzzer selections shown in §2. This is
  not the unfiltered local gate: Windows includes model-only `perf_fuzzer`; Ubuntu omits `perf_fuzzer` and
  `x86_fuzzer`; several emitter dependencies and standalone Lake targets remain unwired (§7).
- **Weekly schedule, plus manual `scheduled.yml` dispatch:** higher-count `x86_fuzzer`,
  `wasm_fuzzer`, `encoding_fuzzer`, and `gzip_fuzzer` runs on both matrix legs, plus
  `scripts/fuzz_gzip.py` on Windows and the reference-refresh step. It is not the same set as
  PR fuzzing: the three stability fuzzers and `perf_fuzzer` are absent, while the Ubuntu
  `x86_fuzzer` invocation is currently invalid for that gate's PE hardware oracle.

This is the current cost split, not a claim that every merge-policy gate is covered by a hosted
job. An unfiltered local gate remains a separate sign-off artifact until the omissions in §7 are
resolved or the workflow proves equivalent aggregate coverage.

## 11. Relationship to the consolidated gate runner

`scripts/run_gates.py` is the single repository-local entry point. It records oracle versions,
supports grouped/sharded CI execution, emits a machine-readable summary, and carries planted-
defect controls. `.github/workflows/ci.yml` selects runner groups and platform-specific shards;
its explicit `--gate` filters are a second, event/platform selection list and can drift from the
runner table, as the emitter omissions in §7 demonstrate. Durable merge policy remains in
`docs/REVIEW.md` §4.1. The runner owns the executable superset and dependency metadata; the
workflows own which subsets actually run on each hosted job. Neither layer alone proves full
coverage.

## Reference integrity: why it runs on a schedule, not per push

`scripts/check_references.py --offline` verifies that the bytes in the local
`.cache/references/` still hash to what `references.json` records. That cache can
never exist in a fresh CI checkout, because it holds third-party documentation
prose and `docs/REVIEW.md` Law 4 forbids committing such prose to the tree. Run per push, the step
therefore fails structurally (exit 3, cold cache) without ever checking anything.

The network audit runs in `scheduled.yml` as `--refresh --all`, which re-fetches every
registered document and compares it against the recorded hash.

The per-push layer is network-free and covers the structural half of reference integrity:

- `check_refs.py` fails on broken internal `REF:` citations, broken explicit
  `docs/<file>.md#<anchor>` cross-links, or any external citation whose slug is absent from
  `references.json`.
- `check_publishable.py` fails on any third-party prose in the tree, or any
  citation resolving into `references/`.

Only the part that needs the network moved to the schedule: confirming upstream still serves
what the registry pinned. Drift is a real finding requiring a human re-pin
(`--acknowledge-drift` with `--reviewer` and `--review-note`), never a silent hash update.

Nothing yet bounds how stale that verification may be: if the scheduled job stops running, no
PR gate notices. A staleness bound belongs with the `last_refresh` timestamp design in
`docs/REFERENCE_INDEX.md`.
