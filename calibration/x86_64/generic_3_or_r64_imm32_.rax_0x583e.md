# generic_3_or_r64_imm32_.rax_0x583e -- cycle-measurement evidence (Golden Cove profile, provisional pending F2)

RDTSC cycle measurements for the `generic_3_or_r64_imm32_.rax_0x583e` kernel, produced by `Gasm/Targets/X86_64/PerfHardwareFuzzer.lean`'s `--hardware` mode.

Raw samples, provenance, and the current reduced value live in `calibration/x86_64/generic_3_or_r64_imm32_.rax_0x583e.json` -- this stub restates none of them (docs/CALIBRATION_GOVERNANCE.md #6.1), so there is exactly one place the number can be read from. Regenerate via `lake exe perf_fuzzer -- --hardware`.

**Status: provisional.** `python scripts/check_calibration.py` (F2, `docs/tasks/F2-calibration-data-governance.md`, status `designing`) does not exist yet to mechanically verify this file's closure hash, bindings, or controls. This file was produced by `Gasm/Targets/X86_64/PerfHardwareFuzzer.lean` following `docs/CALIBRATION_GOVERNANCE.md`'s schema to the best of this task's ability to anticipate it (see `docs/RDTSC_HARNESS.md` #12 for the named gaps: no mechanical closure-hash, no dispersion-guard gate yet).
