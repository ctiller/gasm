/-
Copyright 2026 Craig Tiller

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-
Gasm/Targets/X86_64/Instructions/Obligations.lean - the P4/P5 unified per-instruction
obligation types (docs/X86_ISA_EXPANSION_PREREQUISITES.md P4 and P5).

WHY THIS FILE EXISTS. `docs/X86_ISA_EXPANSION_PREREQUISITES.md` measured, against the tree at
`1e39e7e`, that only ENCODE/DECODE REGISTRATION is mandatory for a new x86-64 instruction: a
probe instruction with identity semantics, an empty uop list, and zero fuzz states compiled
cleanly, failing nothing but the registry audit it was deliberately left out of. Two obligations
were silently optional: (P4) whether ANY oracle -- silicon (`HardwareHarness`) or NASM encoding
-- ever validated the instruction's claimed behavior, and (P5) whether its `toUops` cost
coefficients trace to any real source. The owner's ruling (this task's brief) is that these are
ONE obligation, not two: both are the same failure shape (an instruction lands, the build goes
green, and nothing has established that what it claims is true), so this file defines both
obligation types together and `Instructions/Base.lean` makes both MANDATORY fields on
`X86_64Instruction` (no default -- the same "cannot compile without it" enforcement
`roundtripCases` already uses), not optional ones a Python linter merely nags about.

`ValidationOracle` is per-instance (a function of `ι`, matching `canFuzzHardware`'s existing
shape), not per-type: a single instruction TYPE's instances can genuinely differ in which oracle
covers them (`canFuzzHardware`'s own RSP-safety filtering is exactly this -- `add rax, rsp` and
`add rax, rcx` are the same TYPE, `AddR64R64`, but only one is silicon-safe), so a type-level
constant field could not express what the codebase already needed to express instance-by-instance.
`CoefficientProvenance` reuses Law 14's own ratified vocabulary (`docs/CALIBRATION_GOVERNANCE.md`
#11 -- `modelInternalUnvalidated`) for the honest "uncalibrated" marker rather than inventing a
parallel term, so a report or a future `check_calibration.py` reading either type's output means
the same thing by "unvalidated." -/
import Lean

namespace Gasm.Targets.X86_64.Instructions

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- Which named oracle has actually checked THIS instance's claimed semantics/encoding --
    never a silent absence. `.silicon` claims the instance is real-hardware-fuzzed via
    `HardwareHarness` (i.e. `canFuzzHardware` is true for it, AND its fuzz-vector count clears
    `Tools/CheckX86Obligations.lean`'s vacuity floor); `.nasmEncoding` claims encoding-only
    cross-validation against the NASM oracle (semantics are NOT silicon-checked) and MUST carry a
    non-empty reason. These are the only admitted validation paths. An instruction covered by
    neither oracle cannot be represented as validated and must not enter the registry. -/
inductive ValidationOracle where
  | silicon
  | nasmEncoding (reason : String)
  deriving Repr, DecidableEq, Inhabited

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p5-blocking-for-the-perf-models-integrity-calibration-governance-before-mass-coefficient-entry-f2-f1-a3-cleanup -/
/-- Where THIS instance's `toUops` cost coefficients (latency/port/throughput) came from --
    never a bare, unfalsifiable literal. `.cited` names a real calibration artifact (a
    governed and accepted `calibration/` file, per `docs/CALIBRATION_GOVERNANCE.md`) or a
    `references.json` slug+anchor whose target genuinely publishes cycle-accurate data (the
    combined Intel SDM registered as `intel-sdm` does NOT -- it is the architecture manual, not
    the separate Optimization Reference Manual -- so no coefficient in this tree may cite it
    today; `check_x86_obligations`'s companion report explains why). `.modelInternalUnvalidated`
    is Law 14's own ratified term (`docs/CALIBRATION_GOVERNANCE.md` #11) for an honest, LOUD
    "this number is invented, not measured" marker -- it discharges the obligation by making the
    debt visible, the same way `docs/CALIBRATION_GOVERNANCE.md` #10's `CalibrationStatus` design
    treats an unvalidated profile: never silently defaulted, always an explicit, reviewable
    choice, and never citable as fact (#11: "MUST NOT be cited, in a report, ADR, or code comment,
    as a measured fact"). `docs/CALIBRATION_GOVERNANCE.md` #9 additionally rules out external
    tables (Agner Fog / uops.info) as a `.cited` source for a SHIPPED coefficient -- cross-check
    only, never the source -- so `.modelInternalUnvalidated` is not a shortcut being taken here;
    it is the only honest choice until a governed calibration result is accepted and bound to
    the instance. The RDTSC/RDTSCP harness and provisional artifacts already exist; they do not
    by themselves satisfy that promotion rule (`docs/RDTSC_HARNESS.md`). -/
inductive CoefficientProvenance where
  | cited (artifact : String)
  | modelInternalUnvalidated (reason : String)
  deriving Repr, DecidableEq, Inhabited

end Gasm.Targets.X86_64.Instructions
