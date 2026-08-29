# nop_loop -- cycle-measurement evidence (Golden Cove profile, provisional)

RDTSC cycle measurements for the `nop_loop` kernel, produced by `Gasm/Targets/X86_64/PerfHardwareFuzzer.lean`'s `--hardware` mode.

Raw samples, provenance, and the current reduced value live in `calibration/x86_64/nop_loop.json` -- this stub restates none of them (docs/CALIBRATION_GOVERNANCE.md #6.1), so there is exactly one place the number can be read from. Regenerate via `lake exe perf_fuzzer -- --hardware`.

**Status: provisional.** `python scripts/check_calibration.py` (specified by `docs/CALIBRATION_GOVERNANCE.md` but not yet implemented) does not exist yet to mechanically verify this file's closure hash, bindings, or controls. This file was produced by `Gasm/Targets/X86_64/PerfHardwareFuzzer.lean` following `docs/CALIBRATION_GOVERNANCE.md`'s schema to the best of this task's ability to anticipate it (see `docs/RDTSC_HARNESS.md` #12 for the named gaps: no mechanical closure-hash, no dispersion-guard gate yet).

**Historical producer warning:** the adjacent JSON predates the corrected positive-control unit, affinity provenance, same-address two-pass execution, and exclusion of harness setup from the timed/model-comparison unit. It is invalid as promotion evidence until regenerated; see `docs/RDTSC_HARNESS.md` §9.
