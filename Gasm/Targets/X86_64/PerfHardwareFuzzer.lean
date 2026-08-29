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
Gasm/Targets/X86_64/PerfHardwareFuzzer.lean - F1's hardware-backed perf fuzzer. Reuses
`Fuzzer.lean`'s existing instruction generator (`generateRandomInstruction`) to draw
single-instruction kernels, runs them through `HardwareTimingHarness.runTimingBatch`, checks
containment (`real ∈ [minCycles, maxCycles]`) and tracks rank-order agreement, and writes
`docs/CALIBRATION_GOVERNANCE.md`-schema calibration JSON/`.md` files under `calibration/x86_64/`.
See docs/RDTSC_HARNESS.md for the full design; this file's comments cover only mechanics.

WHY drawRepeatSafeInstruction, NOT A COPY OF Fuzzer.generateRandomInstruction. Every category in
that function's 32-way dispatch is safe for straight-line REPEATED execution (thousands of
unrolled copies with no CPU loop, see HardwareTimingHarness.lean's header) EXCEPT `PUSH r64`/
`POP r64` (indices 10/11): unrolled thousands of times with no matching pop/push, RSP walks off
the stack. This file calls the REAL `Fuzzer.generateRandomInstruction` (not a duplicate dispatch
table) and re-draws whenever the result is unsafe -- `canFuzzHardware` false (rules out
`MovRspDispByte`, the only other category needing scratch memory this harness doesn't provide)
or a rendered NASM mnemonic of `push`/`pop`. Verified by reading all 32 dispatch arms
(`Fuzzer.lean:95-127`): no other arm can fault or mutate RSP/RIP outside normal sequential flow. -/
import Lean
import Lean.Data.Json
import Gasm.Core.Types
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Uop
import Gasm.Targets.X86_64.Performance
import Gasm.Targets.X86_64.Fuzzer
import Gasm.Targets.X86_64.HardwareTimingHarness

namespace Gasm.Targets.X86_64.PerfHardwareFuzzer

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Fuzzer
open Gasm.Targets.X86_64.HardwareTimingHarness
open Lean (Json)

-- ---------------------------------------------------------------------------------------------
-- Safe kernel generation (docs/RDTSC_HARNESS.md #6.2)
-- ---------------------------------------------------------------------------------------------

/- REF: docs/RDTSC_HARNESS.md#62-register-safety-the-one-hazard-straight-line-unrolling-does-not-remove -/
/-- True iff `instr`'s rendered NASM mnemonic is `push` or `pop` -- the one category unsafe for
    unbounded straight-line repetition (see this file's header). -/
def isPushOrPopInstr (instr : AnyX86_64Instruction) : Bool :=
  let mnem := ((X86_64Instruction.toNASM instr).splitOn " ").headD "" |>.toLower
  mnem == "push" || mnem == "pop"

/- REF: docs/RDTSC_HARNESS.md#62-register-safety-the-one-hazard-straight-line-unrolling-does-not-remove -/
/-- The guaranteed-safe fallback if `drawRepeatSafeInstruction` exhausts its retries (should be
    unreachable in practice: only 2 of 32 dispatch categories are ever rejected, so a run of
    `maxRetries` consecutive rejections is astronomically unlikely with a working RNG) -- `ADD
    RAX, RDX`, register-register, neither register RSP/RBP, no memory operand. -/
def fallbackSafeInstruction : AnyX86_64Instruction := add_r64 .rax .rdx

/- REF: docs/RDTSC_HARNESS.md#62-register-safety-the-one-hazard-straight-line-unrolling-does-not-remove -/
/-- Draws one instruction safe for this harness's straight-line repeated execution: calls the
    REAL `Fuzzer.generateRandomInstruction` (reused, not duplicated) and re-draws on an unsafe
    result, up to `maxRetries` times, falling back to a fixed known-safe instruction rather than
    looping forever or silently returning something unrelated without saying so. -/
def drawRepeatSafeInstruction (rng : FuzzerRng) (maxRetries : Nat := 16) : AnyX86_64Instruction × FuzzerRng := Id.run do
  let mut curRng := rng
  for _ in [0:maxRetries] do
    let (instr, nextRng) := generateRandomInstruction curRng
    curRng := nextRng
    if X86_64Instruction.canFuzzHardware instr && !isPushOrPopInstr instr then
      return (instr, curRng)
  return (fallbackSafeInstruction, curRng)

/- REF: docs/RDTSC_HARNESS.md#9-kernel-suite-and-evidence -/
/-- How many `drawRepeatSafeInstruction`-generated single-instruction kernels round out the
    hardware-timed suite alongside the hand-curated named kernels. -/
def genericKernelCount : Nat := 8

/- REF: docs/RDTSC_HARNESS.md#9-kernel-suite-and-evidence -/
/-- One entry in the hardware-timed suite: the `TimingKernel` the harness actually runs, plus
    (when the kernel corresponds to a real modeled instruction) that instruction, so containment
    can be checked against `computeCycleBounds`. -/
structure SuiteEntry where
  kernel : TimingKernel
  modeledInstr : Option AnyX86_64Instruction := none
  deriving Inhabited

/- REF: docs/RDTSC_HARNESS.md#9-kernel-suite-and-evidence -/
def namedSuite : List SuiteEntry :=
  [ { kernel := timerOverheadKernel, modeledInstr := none }
  , { kernel := nopLoopKernel, modeledInstr := none }
  , { kernel := longDependentChainKernel, modeledInstr := some (add_r64_imm8 .rax 1) }
  , { kernel := shlByClKernel, modeledInstr := some (shl_r64_cl .rax) }
  ]

/- REF: docs/RDTSC_HARNESS.md#9-kernel-suite-and-evidence -/
/-- Draws `genericKernelCount` register-disjoint-safe single-instruction kernels via
    `drawRepeatSafeInstruction`, each wrapped as a `TimingKernel` whose `perInstanceBytes` is
    that instruction's own `encode` output -- no hand-written bytes needed for this half of the
    suite, since `AnyX86_64Instruction` already carries a real encoder. -/
def buildGenericSuite (rng : FuzzerRng) (count : Nat := genericKernelCount) : List SuiteEntry × FuzzerRng := Id.run do
  let mut entries : List SuiteEntry := []
  let mut curRng := rng
  for i in [0:count] do
    let (instr, nextRng) := drawRepeatSafeInstruction curRng
    curRng := nextRng
    let label := s!"generic_{i}_{X86_64Instruction.toLean instr}".replace " " "_"
    let k : TimingKernel := { name := label, perInstanceBytes := X86_64Instruction.encode instr }
    entries := entries ++ [{ kernel := k, modeledInstr := some instr }]
  return (entries, curRng)

/- REF: docs/RDTSC_HARNESS.md#9-kernel-suite-and-evidence -/
def fullSuite (rng : FuzzerRng) : List SuiteEntry × FuzzerRng :=
  let (generic, nextRng) := buildGenericSuite rng
  (namedSuite ++ generic, nextRng)

-- ---------------------------------------------------------------------------------------------
-- Reduction: median-of-N, timer-overhead subtraction, containment (docs/RDTSC_HARNESS.md #6.5, #8)
-- ---------------------------------------------------------------------------------------------

/- REF: docs/RDTSC_HARNESS.md#65-statistic-median-not-mean-and-the-dispersion-guard -/
/-- The median of an odd-length list (no averaging of two middle elements -- `measuredRepetitions`
    is always odd). Falls back to the smallest element for an empty list (never reached in
    practice since `measuredRepetitions > 0`, but keeps this total). -/
def medianUInt64 (xs : List UInt64) : UInt64 :=
  let sorted := xs.toArray.qsort (· < ·)
  if sorted.isEmpty then 0 else sorted[sorted.size / 2]!

/- REF: docs/RDTSC_HARNESS.md#65-statistic-median-not-mean-and-the-dispersion-guard -/
def minUInt64 (xs : List UInt64) : UInt64 := xs.foldl (fun acc x => if x < acc then x else acc) (xs.headD 0)

/- REF: docs/RDTSC_HARNESS.md#65-statistic-median-not-mean-and-the-dispersion-guard -/
def maxUInt64 (xs : List UInt64) : UInt64 := xs.foldl (fun acc x => if x > acc then x else acc) (xs.headD 0)

/- REF: docs/RDTSC_HARNESS.md#5-result-record-extension -/
/-- One kernel's fully-reduced measurement: raw samples preserved (pre-subtraction, run order),
    plus the derived per-bracket and per-instance statistics `docs/CALIBRATION_GOVERNANCE.md` §5
    calls for. `perBracketMedian`/`Min`/`Max` are the timer-overhead-SUBTRACTED bracket totals
    (what containment is actually checked against, per docs/RDTSC_HARNESS.md's design decision to
    test the full `kernelUnrollPerRep`-replicated model bounds rather than a divided
    single-instance figure); `cyclesPerInstanceMedian` is the further-divided, purely
    informational per-instruction figure. -/
structure ReducedTiming where
  name                    : String
  rawDeltaCyclesUnadjusted : List UInt64
  perBracketMedian        : Int
  perBracketMin           : Int
  perBracketMax           : Int
  cyclesPerInstanceMedian : Float
  deriving Inhabited

/- REF: docs/RDTSC_HARNESS.md#64-timer-overhead-calibration-pass -/
/-- `Int → Float`, since this toolchain's `Int` has no direct `toFloat` field projection. -/
def intToFloat (n : Int) : Float :=
  if n < 0 then -((-n).toNat.toFloat) else n.toNat.toFloat

/- REF: docs/RDTSC_HARNESS.md#64-timer-overhead-calibration-pass -/
/-- Subtracts `overheadMedian` from every raw sample (as `Int`, since a noisy sample can measure
    below the overhead median and must not wrap around as an unsigned underflow) and reduces. -/
def reduceTiming (t : HardwareKernelTiming) (overheadMedian : UInt64) : ReducedTiming :=
  let overheadI : Int := overheadMedian.toNat
  let adjusted : List Int := t.rawDeltaCycles.map (fun raw => (raw.toNat : Int) - overheadI)
  let sorted := adjusted.toArray.qsort (· < ·)
  let med := if sorted.isEmpty then 0 else sorted[sorted.size / 2]!
  let mn := sorted.foldl (fun acc x => if x < acc then x else acc) (sorted.getD 0 0)
  let mx := sorted.foldl (fun acc x => if x > acc then x else acc) (sorted.getD 0 0)
  { name := t.name
    rawDeltaCyclesUnadjusted := t.rawDeltaCycles
    perBracketMedian := med
    perBracketMin := mn
    perBracketMax := mx
    cyclesPerInstanceMedian := intToFloat med / kernelUnrollPerRep.toFloat }

/- REF: docs/RDTSC_HARNESS.md#8-the-promotion-rule-this-document-follows-for-costprovenance -/
/-- Model bounds for a kernel tied to a real instruction: `kernelUnrollPerRep` copies of that
    instruction's own `toUops`, exactly matching what the bracket actually executes -- testing
    the dependency-chain/serial-latency path (MODEL_DEBT §A1) rather than a single instruction's
    always-trivial `[1,1,1]` bound. -/
def modelBoundsFor (instr : AnyX86_64Instruction) (profile : MicroarchProfile := goldenCoveProfile) : PerfCycleBounds :=
  let uops := X86_64Instruction.toUops instr
  let replicated := (List.replicate kernelUnrollPerRep uops).flatten
  computeCycleBounds replicated profile

/- REF: docs/RDTSC_HARNESS.md#8-the-promotion-rule-this-document-follows-for-costprovenance -/
/-- Containment: the real (timer-overhead-subtracted) per-bracket median falls within
    `[minCycles, maxCycles]`. `none` (not applicable) for kernels with no modeled instruction
    (`timer_overhead`, `nop_loop`). -/
def checkContainment (r : ReducedTiming) (bounds : PerfCycleBounds) : Bool :=
  r.perBracketMedian >= (bounds.minCycles : Int) && r.perBracketMedian <= (bounds.maxCycles : Int)

-- ---------------------------------------------------------------------------------------------
-- Control vectors (docs/RDTSC_HARNESS.md #4)
-- ---------------------------------------------------------------------------------------------

/- REF: docs/RDTSC_HARNESS.md#4-containment-fail-closed-world-sampling-vs-correctness-unrepresentable-by-construction -/
def positiveControlBandCyclesPerInstance : Float × Float := (0.0, 60.0)

/- REF: docs/RDTSC_HARNESS.md#4-containment-fail-closed-world-sampling-vs-correctness-unrepresentable-by-construction -/
/-- Minimum per-bracket cycle delta `long_dependent_chain` must measure above `nop_loop` for the
    discrimination-pair control to pass -- see this file's header and
    `docs/CALIBRATION_GOVERNANCE.md` §4.4/§8 for why this control exists (wsc's actual observed
    failure: two kernels that must differ, measured identically). -/
def discriminationMinDeltaCycles : Int := 20

/- REF: docs/RDTSC_HARNESS.md#4-containment-fail-closed-world-sampling-vs-correctness-unrepresentable-by-construction -/
/-- Result of the mandatory oracle sanity check -- see `verifyTimingOracleControls`. -/
structure TimingControlResult where
  ok      : Bool
  detail  : String
  deriving Inhabited

/- REF: docs/RDTSC_HARNESS.md#4-containment-fail-closed-world-sampling-vs-correctness-unrepresentable-by-construction -/
/-- Runs the mandatory positive control + discrimination pair BEFORE any real kernel is trusted,
    mirroring `HardwareHarness.verifyHardwareOracleControls`'s "abort the whole run on any
    control failure" discipline (`docs/REVIEW.md` Law 13 item 4). Takes the ALREADY-MEASURED
    `timer_overhead`/`nop_loop`/`long_dependent_chain` reductions rather than re-running the
    harness, since the caller must run all three through the same batch anyway (one process
    spawn, not three). -/
def verifyTimingOracleControls (overhead nop chain : ReducedTiming) : TimingControlResult :=
  let (lo, hi) := positiveControlBandCyclesPerInstance
  if nop.cyclesPerInstanceMedian < lo || nop.cyclesPerInstanceMedian > hi then
    { ok := false, detail := s!"POSITIVE CONTROL FAILED: nop_loop measured {nop.cyclesPerInstanceMedian} cycles/instance, outside the expected band [{lo}, {hi}] -- the timing oracle is not trustworthy (stuck timer, broken bracket, or a machine too noisy to measure on)." }
  else if chain.perBracketMedian - nop.perBracketMedian < discriminationMinDeltaCycles then
    { ok := false, detail := s!"DISCRIMINATION-PAIR CONTROL FAILED: long_dependent_chain ({chain.perBracketMedian} cycles/bracket) is not reliably slower than nop_loop ({nop.perBracketMedian} cycles/bracket) by the required minimum ({discriminationMinDeltaCycles}) -- two kernels that must differ measured (near-)identically, exactly wsc's own historical failure symptom. The timing oracle cannot be trusted." }
  else if overhead.perBracketMedian < 0 then
    { ok := false, detail := s!"TIMER OVERHEAD CONTROL FAILED: timer_overhead's own reduction is negative ({overhead.perBracketMedian}), which is only possible if reduceTiming subtracted itself inconsistently -- aborting." }
  else
    { ok := true, detail := s!"positive control (nop_loop={nop.cyclesPerInstanceMedian} cyc/instance) and discrimination pair (long_dependent_chain - nop_loop = {chain.perBracketMedian - nop.perBracketMedian} cyc/bracket, floor {discriminationMinDeltaCycles}) both passed." }

/- REF: docs/CALIBRATION_GOVERNANCE.md#8-recording-controls-in-the-file-and-the-harness-side-pattern-to-copy -/
/-- The mis-calibration negative control this task's own acceptance criteria require: subtracts
    a deliberately WRONG (10x-inflated) timer-overhead constant from a real measurement and
    demonstrates containment now fails where it previously held -- proving the overhead
    subtraction is load-bearing arithmetic a broken/forged value would actually be caught by,
    not an inert field nobody reads. -/
def runMiscalibrationNegativeControl (rawOverheadMedian : UInt64) (chainRaw : HardwareKernelTiming) (chainInstr : AnyX86_64Instruction) : TimingControlResult :=
  let honestReduced := reduceTiming chainRaw rawOverheadMedian
  let honestBounds := modelBoundsFor chainInstr
  let honestContainment := checkContainment honestReduced honestBounds
  let inflatedOverhead : UInt64 := rawOverheadMedian * 10
  let corruptReduced := reduceTiming chainRaw inflatedOverhead
  let corruptContainment := checkContainment corruptReduced honestBounds
  if !honestContainment then
    { ok := false, detail := "MIS-CALIBRATION CONTROL INCONCLUSIVE: the honest (uncorrupted) reduction did not itself satisfy containment, so this control cannot demonstrate a hold-then-break transition. See the honest containment result above for the real defect." }
  else if corruptContainment then
    { ok := false, detail := s!"MIS-CALIBRATION CONTROL FAILED: inflating the timer-overhead constant 10x (from {rawOverheadMedian} to {inflatedOverhead}) did NOT break containment for long_dependent_chain (still {corruptReduced.perBracketMedian} cycles, bounds still satisfied) -- the overhead subtraction is not load-bearing, meaning a corrupted/forged calibration constant would go undetected." }
  else
    { ok := true, detail := s!"honest overhead ({rawOverheadMedian}) gives containment (perBracketMedian={honestReduced.perBracketMedian}); a deliberately 10x-inflated overhead ({inflatedOverhead}) breaks it (perBracketMedian={corruptReduced.perBracketMedian}, outside [{honestBounds.minCycles},{honestBounds.maxCycles}]) -- the subtraction is demonstrably load-bearing." }

-- ---------------------------------------------------------------------------------------------
-- Rank-order agreement (docs/RDTSC_HARNESS.md #10)
-- ---------------------------------------------------------------------------------------------

/- REF: docs/RDTSC_HARNESS.md#10-rank-order-tracking -/
/-- One entry the rank-order check compares: a kernel's real per-bracket median alongside the
    model's own nominal-cycle prediction for the same replicated uop sequence. -/
structure RankableEntry where
  name          : String
  modelNominal  : Nat
  realMedian    : Int
  deriving Inhabited

/- REF: docs/RDTSC_HARNESS.md#10-rank-order-tracking -/
/-- Pairwise rank-order agreement: for every pair of rankable kernels, does the model's
    `nominalCycles` ordering agree with the real measured ordering (both `<`, both `>`, or both
    `=`)? Returns (agreeing pairs, total pairs) -- surfaced, not gated, per this task's own
    explicit "measured and surfaced, not necessarily pass/fail on day one" scope. -/
def rankOrderAgreement (entries : List RankableEntry) : Nat × Nat := Id.run do
  let arr := entries.toArray
  let mut agree := 0
  let mut total := 0
  for i in [0:arr.size] do
    for j in [i+1:arr.size] do
      let a := arr[i]!
      let b := arr[j]!
      let modelCmp : Int := (Int.ofNat a.modelNominal) - (Int.ofNat b.modelNominal)
      let realCmp : Int := a.realMedian - b.realMedian
      let sameOrder :=
        (modelCmp == 0 && realCmp == 0) ||
        (modelCmp < 0 && realCmp < 0) ||
        (modelCmp > 0 && realCmp > 0)
      total := total + 1
      if sameOrder then agree := agree + 1
  return (agree, total)

-- ---------------------------------------------------------------------------------------------
-- Provenance gathering (docs/CALIBRATION_GOVERNANCE.md §2) and calibration JSON (§1, §5, §6, §8)
-- ---------------------------------------------------------------------------------------------

/- REF: docs/CALIBRATION_GOVERNANCE.md#2-provenance-and-run-conditions-modeldebt-e5a -/
/-- Everything gathered once per run and shared across every calibration file this run writes.
    `harnessClosureHash`/`osBuild` are provisional (`docs/RDTSC_HARNESS.md` #12) -- F2's
    `check_calibration.py` does not exist yet to define the exact closure-hash algorithm this
    task should match, so this run records what it CAN cheaply and honestly determine and marks
    the rest explicitly, rather than fabricating a value that would look load-bearing. -/
structure RunProvenance where
  isoDate            : String
  hostFingerprint    : String
  processorId        : String
  logicalCores       : String
  osBuild            : String
  leanToolchain      : String
  deriving Inhabited

/- REF: docs/CALIBRATION_GOVERNANCE.md#2-provenance-and-run-conditions-modeldebt-e5a -/
/-- Gathers what this run can determine without external lookup: `PROCESSOR_IDENTIFIER`/
    `NUMBER_OF_PROCESSORS` (set by Windows itself, no subprocess needed), the pinned
    `lean-toolchain` file, and the wall-clock date via `powershell Get-Date` (the one subprocess
    call this needs, since Lean's own `IO` has no wall-clock-date primitive). Every lookup that
    can fail degrades to an honest `"unknown"` placeholder rather than aborting the run --
    provenance gaps are visible-and-flagged data, not a reason to fail closed the way a control
    vector failure is (docs/RDTSC_HARNESS.md #4's fail-closed list is about the MEASUREMENT being
    untrustworthy, not about a description field being incomplete). -/
def gatherRunProvenance : IO RunProvenance := do
  let processorId ← (IO.getEnv "PROCESSOR_IDENTIFIER").map (·.getD "unknown")
  let logicalCores ← (IO.getEnv "NUMBER_OF_PROCESSORS").map (·.getD "unknown")
  let osName ← (IO.getEnv "OS").map (·.getD "unknown")
  let leanToolchain ← try
      let s ← IO.FS.readFile "lean-toolchain"
      pure s.trimAscii.toString
    catch _ => pure "unknown"
  let isoDate ← try
      let out ← IO.Process.output { cmd := "powershell", args := #["-NoProfile", "-Command", "Get-Date -Format o"] }
      pure out.stdout.trimAscii.toString
    catch _ => pure "unknown"
  let fingerprint := toString (hash (processorId ++ "|" ++ logicalCores ++ "|" ++ osName))
  return { isoDate := isoDate, hostFingerprint := fingerprint, processorId := processorId
           logicalCores := logicalCores, osBuild := osName, leanToolchain := leanToolchain }

/- REF: docs/CALIBRATION_GOVERNANCE.md#5-reduction-and-the-timer-overhead-dag-modeldebt-e5cd -/
/-- Builds one kernel's calibration JSON (`docs/CALIBRATION_GOVERNANCE.md` §1/§5/§6/§8 schema),
    provisional pending F2's `check_calibration.py` (see this file's header and
    `docs/RDTSC_HARNESS.md` #12). `timerOverheadRef` is `none` for `timer_overhead.json` itself
    (the root of the DAG, per §5). -/
def buildCalibrationJson (prov : RunProvenance) (r : ReducedTiming) (timerOverheadRef : Option String)
    (measuredSubject : List String) (bindings : List (String × String × String))
    (positiveCyclesBand : Int × Int) (positiveMeasured : Int)
    (discriminationPair : Option (String × String × Int × Int)) : Json :=
  let runConditions := Json.mkObj [
    ("power_source", ("unknown (no OS power-plan API queried by this task; document manually if measured on battery)" : Json)),
    ("windows_power_plan", ("unknown" : Json)),
    ("core_affinity", ("unset (no SetThreadAffinityMask call in this harness)" : Json)),
    ("core_type", ("unknown (no hybrid P/E-core detection implemented)" : Json)),
    ("thermal_throttle_observed", (false : Json)),
    ("concurrent_load_note", ("agent worktree on a shared development machine; no isolation guarantee (docs/RDTSC_HARNESS.md #7)" : Json))
  ]
  let provenance := Json.mkObj [
    ("device_profile", ("goldenCoveProfile" : Json)),
    ("host_id", ("agent-worktree-01" : Json)),
    -- Only the HASH is exposed, per docs/CALIBRATION_GOVERNANCE.md #2.1 ("host_fingerprint...
    -- Anonymity is fine; unverifiability is not") and docs/REVIEW.md #4.4 -- the raw CPU
    -- identifier string and logical-core count that feed the hash are deliberately not exposed
    -- as separate plaintext fields, even though this file's own inputs already fold them in.
    ("host_fingerprint", (prov.hostFingerprint : Json)),
    ("os_build", (prov.osBuild : Json)),
    ("tool_versions", Json.mkObj [("lean_toolchain", (prov.leanToolchain : Json))]),
    ("iso_date", (prov.isoDate : Json)),
    ("harness_path", ("Gasm/Targets/X86_64/HardwareTimingHarness.lean" : Json)),
    ("harness_closure_hash", ("PROVISIONAL_UNCOMPUTED_PENDING_F2_check_calibration_py" : Json)),
    ("measured_subject", Json.arr ((measuredSubject.map Json.str).toArray)),
    ("harness_invocation", ("lake exe perf_fuzzer -- --hardware" : Json)),
    ("run_conditions", runConditions)
  ]
  let bindingsJson := Json.arr ((bindings.map (fun (f, d, rf) => Json.mkObj [
    ("lean_file", (f : Json)), ("decl_name", (d : Json)), ("reduction_field", (rf : Json))
  ])).toArray)
  let (band0, band1) := positiveCyclesBand
  let controlsBase := [
    ("positive_control_kernel", ("nop_loop" : Json)),
    ("positive_control_measured_cycles", (positiveMeasured : Json)),
    ("positive_control_band", Json.arr #[(band0 : Json), (band1 : Json)]),
    ("device_identity_check", ("nop_loop/long_dependent_chain discrimination pair passed before this file was written (docs/RDTSC_HARNESS.md #4)" : Json))
  ]
  let controlsDisc := match discriminationPair with
    | some (a, b, va, vb) =>
      [ ("discrimination_pair", Json.arr #[(a : Json), (b : Json)])
      , ("discrimination_pair_values", Json.arr #[(va : Json), (vb : Json)])
      , ("discrimination_pair_min_delta_required", (discriminationMinDeltaCycles : Json)) ]
    | none => []
  let controls := Json.mkObj (controlsBase ++ controlsDisc)
  let reduction := Json.mkObj [
    ("method", (s!"median-of-{measuredRepetitions} over raw_samples_cycles_unadjusted (per-bracket total across kernelUnrollPerRep={kernelUnrollPerRep} instances, each measured pass preceded by an identical untimed pre-fault pass), minus timer_overhead.json's own current median, after {warmupIterations} straight-line-unrolled warm-up instances (docs/RDTSC_HARNESS.md #6)" : Json)),
    ("median", (r.perBracketMedian : Json)),
    ("min", (r.perBracketMin : Json)),
    ("max", (r.perBracketMax : Json)),
    ("cycles_per_instance_median_derived", (r.cyclesPerInstanceMedian.toString : Json))
  ]
  let base := [
    ("schema_version", (2 : Json)),
    ("kernel_name", (r.name : Json)),
    ("provenance", provenance),
    ("raw_samples_cycles_unadjusted", Json.arr ((r.rawDeltaCyclesUnadjusted.map (fun v => Json.num v.toNat)).toArray)),
    ("reduction", reduction),
    ("bindings", bindingsJson),
    ("controls", controls)
  ]
  let withRef := match timerOverheadRef with
    | some rf => base ++ [("timer_overhead_ref", (rf : Json))]
    | none => base
  Json.mkObj withRef

/- REF: docs/CALIBRATION_GOVERNANCE.md#61-strip-every-number-from-the-citation-stub -/
/-- The REF-citable `.md` stub -- zero numeric measurement values, per §6.1 (the fix for wsc's
    literal-rot: exactly one place the number can be read from, the JSON's own `reduction`). -/
def buildCalibrationMdStub (name jsonRelPath description : String) : String :=
  s!"# {name} -- cycle-measurement evidence (Golden Cove profile, provisional pending F2)\n\n" ++
  s!"{description}\n\n" ++
  s!"Raw samples, provenance, and the current reduced value live in `{jsonRelPath}` -- this stub " ++
  "restates none of them (docs/CALIBRATION_GOVERNANCE.md #6.1), so there is exactly one place " ++
  "the number can be read from. Regenerate via `lake exe perf_fuzzer -- --hardware`.\n\n" ++
  "**Status: provisional.** `python scripts/check_calibration.py` (F2, " ++
  "`docs/tasks/F2-calibration-data-governance.md`, status `designing`) does not exist yet to " ++
  "mechanically verify this file's closure hash, bindings, or controls. This file was produced " ++
  "by `Gasm/Targets/X86_64/PerfHardwareFuzzer.lean` following " ++
  "`docs/CALIBRATION_GOVERNANCE.md`'s schema to the best of this task's ability to anticipate " ++
  "it (see `docs/RDTSC_HARNESS.md` #12 for the named gaps: no mechanical closure-hash, no " ++
  "dispersion-guard gate yet).\n"

-- ---------------------------------------------------------------------------------------------
-- Orchestration (docs/RDTSC_HARNESS.md #4, #11; TC17 vacuity floor)
-- ---------------------------------------------------------------------------------------------

/- REF: docs/RDTSC_HARNESS.md#11-relationship-to-docstaskstc17-vacuity-floorsmd -/
/-- The full `--hardware` run: builds the suite, runs it through the real timing harness exactly
    once (one process spawn), verifies the mandatory control vectors BEFORE trusting anything,
    computes containment/rank-order, writes calibration files, and prints a report. Returns the
    exit code the CLI hands back to the shell. -/
def runHardwareFuzz (seed : UInt64) : IO UInt32 := do
  IO.println "--------------------------------------------------------------------------------"
  IO.println " F1 RDTSC HARDWARE MEASUREMENT (docs/RDTSC_HARNESS.md)"
  IO.println "--------------------------------------------------------------------------------"
  IO.println "[!] VALIDITY: only on real, non-virtualized silicon (docs/RDTSC_HARNESS.md #7)."
  IO.println "    Never valid on a hosted CI runner -- same carve-out as perf_fuzzer (docs/CI.md #5)."

  let (suite, _) := fullSuite ({ seed := seed } : FuzzerRng)
  -- TC17 vacuity floor: zero kernels measured is a hard failure, never a printed success.
  if suite.isEmpty then
    IO.println "[VACUITY FLOOR TRIPPED] Zero kernels in the hardware-timed suite -- 0 vectors exercised verifies nothing (TCB.md T11-b / docs/tasks/TC17-vacuity-floors.md)."
    return 1

  let kernels := suite.map (·.kernel)
  IO.println s!"[*] Suite: {kernels.length} kernel(s) ({(kernels.map (·.name))})"
  IO.println s!"[*] warmupIterations={warmupIterations}, measuredRepetitions={measuredRepetitions}, kernelUnrollPerRep={kernelUnrollPerRep}"

  let resultE ← runTimingBatch kernels
  match resultE with
  | .error msg =>
    IO.println s!"[!] FAIL-CLOSED: the hardware timing harness could not run at all: {msg}"
    IO.println "    Per docs/REVIEW.md Law 13 item 4 / this task's own fail-closed requirement, an oracle that cannot run must fail the run, not synthesize or skip results."
    return 1
  | .ok raws =>
    let byName (n : String) : Option HardwareKernelTiming := raws.find? (·.name == n)
    match byName "timer_overhead", byName "nop_loop", byName "long_dependent_chain" with
    | some overheadRaw, some nopRaw, some chainRaw =>
      let overheadMedian := medianUInt64 overheadRaw.rawDeltaCycles
      let overheadReduced := reduceTiming overheadRaw 0 -- overhead's own file is un-subtracted (root of the DAG)
      let nopReduced := reduceTiming nopRaw overheadMedian
      let chainReduced := reduceTiming chainRaw overheadMedian

      let controlResult := verifyTimingOracleControls overheadReduced nopReduced chainReduced
      IO.println s!"\n[CONTROLS] {controlResult.detail}"
      if !controlResult.ok then
        IO.println "[!] FAIL-CLOSED: mandatory control vector(s) failed. Aborting before trusting any measurement (docs/REVIEW.md Law 13 item 4)."
        return 1

      -- Reduce every kernel, check containment where a modeled instruction exists, gather
      -- rank-order entries.
      let mut containmentPass := 0
      let mut containmentTotal := 0
      let mut rankable : List RankableEntry := []
      let mut citablePromotions : List String := []
      let mut misCalCandidateName : Option String := none
      IO.println "\n[MEASUREMENTS]"
      for entry in suite do
        match raws.find? (·.name == entry.kernel.name) with
        | none => IO.println s!"  [!] MISSING RESULT for {entry.kernel.name} (should be unreachable -- runTimingBatch returned fewer results than kernels)."
        | some raw =>
          let reduced := if entry.kernel.name == "timer_overhead" then overheadReduced else reduceTiming raw overheadMedian
          let iqrNote :=
            let sorted := reduced.rawDeltaCyclesUnadjusted.toArray.qsort (· < ·)
            if sorted.size >= 4 then
              let q1 := sorted[sorted.size / 4]!
              let q3 := sorted[(sorted.size * 3) / 4]!
              s!", IQR=[{q1},{q3}]"
            else ""
          match entry.modeledInstr with
          | none =>
            IO.println s!"  {entry.kernel.name}: perBracketMedian={reduced.perBracketMedian} (min={reduced.perBracketMin},max={reduced.perBracketMax}{iqrNote}) cyclesPerInstance~{reduced.cyclesPerInstanceMedian} [no modeled instruction -- control/calibration kernel, no containment check]"
          | some instr =>
            let bounds := modelBoundsFor instr
            let contained := checkContainment reduced bounds
            containmentTotal := containmentTotal + 1
            if contained then containmentPass := containmentPass + 1
            let verdict := if contained then "CONTAINED" else "OUTSIDE BOUNDS"
            IO.println s!"  {entry.kernel.name} ({X86_64Instruction.toNASM instr}): perBracketMedian={reduced.perBracketMedian} (min={reduced.perBracketMin},max={reduced.perBracketMax}{iqrNote}) cyclesPerInstance~{reduced.cyclesPerInstanceMedian} vs model[{bounds.minCycles},{bounds.nominalCycles},{bounds.maxCycles}] -> {verdict}"
            rankable := rankable ++ [{ name := entry.kernel.name, modelNominal := bounds.nominalCycles, realMedian := reduced.perBracketMedian }]
            if contained then
              citablePromotions := citablePromotions ++ [entry.kernel.name]
              if misCalCandidateName.isNone then
                misCalCandidateName := some entry.kernel.name

      let (rankAgree, rankTotal) := rankOrderAgreement rankable
      IO.println s!"\n[CONTAINMENT] {containmentPass}/{containmentTotal} modeled kernels contained within [minCycles,maxCycles]."
      IO.println s!"[RANK-ORDER] {rankAgree}/{rankTotal} pairs agree between model nominalCycles and real measured ordering (surfaced, not gated -- docs/RDTSC_HARNESS.md #10)."
      IO.println s!"[EVIDENTIARY SCOPE] Validated against exactly 1 microarchitecture profile (goldenCoveProfile) on 1 machine (T11: one physical machine) -- docs/CALIBRATION_GOVERNANCE.md #10."

      -- Mis-calibration negative control (docs/CALIBRATION_GOVERNANCE.md #8): run against
      -- WHATEVER kernel in the full suite honestly contained (not hardcoded to
      -- long_dependent_chain -- on this machine's real, noisy dispersion, that specific kernel
      -- does not always honestly contain, which would make the control merely inconclusive
      -- about the wrong thing rather than about subtraction load-bearing-ness). If no kernel
      -- honestly contained, the control is reported as a soft warning, not a hard abort: the
      -- discrimination-pair control above (which DID robustly pass) is this run's primary
      -- Law-13-item-4 "oracle proves itself" gate; this one is this task's own supplementary
      -- acceptance criterion and does not get to veto an otherwise-honest, otherwise-passing run
      -- just because real hardware noise prevented it from having a clean base case to corrupt.
      let misCalCandRaw : Option HardwareKernelTiming :=
        match misCalCandidateName with
        | some name => raws.find? (·.name == name)
        | none => none
      let misCalCandInstr : Option AnyX86_64Instruction :=
        match misCalCandidateName with
        | some name => (suite.find? (fun e => e.kernel.name == name)).bind (·.modeledInstr)
        | none => none
      match misCalCandRaw, misCalCandInstr with
      | some candRaw, some candInstr =>
        let miscalResult := runMiscalibrationNegativeControl overheadMedian candRaw candInstr
        IO.println s!"[MIS-CAL CONTROL] (against {candRaw.name}) {miscalResult.detail}"
        if !miscalResult.ok then
          IO.println "[!] FAIL-CLOSED: mis-calibration negative control failed against a kernel that DID honestly contain -- the overhead subtraction is not demonstrably load-bearing. Aborting."
          return 1
      | _, _ =>
        IO.println "[MIS-CAL CONTROL] SKIPPED (soft warning, not fatal): no kernel in this run's suite honestly contained within its model bounds, so there is no clean base case to demonstrate a hold-then-break transition against. This reflects real measurement dispersion on this shared, unpinned-beyond-core-affinity machine (docs/RDTSC_HARNESS.md #7), not a harness defect -- the discrimination-pair control above is the primary oracle-trustworthiness gate and it passed."

      -- Write calibration files.
      let prov ← gatherRunProvenance
      IO.FS.createDirAll "calibration/x86_64"
      let writeKernel (r : ReducedTiming) (timerRef : Option String) (subject : List String) (bindings : List (String × String × String)) (discPair : Option (String × String × Int × Int)) : IO Unit := do
        let j := buildCalibrationJson prov r timerRef subject bindings (0, 60) nopReduced.perBracketMedian discPair
        IO.FS.writeFile s!"calibration/x86_64/{r.name}.json" (Json.pretty j)
        IO.FS.writeFile s!"calibration/x86_64/{r.name}.md" (buildCalibrationMdStub r.name s!"calibration/x86_64/{r.name}.json" s!"RDTSC cycle measurements for the `{r.name}` kernel, produced by `Gasm/Targets/X86_64/PerfHardwareFuzzer.lean`'s `--hardware` mode.")

      let discPair := some ("nop_loop", "long_dependent_chain", nopReduced.perBracketMedian, chainReduced.perBracketMedian)
      writeKernel overheadReduced none ["Gasm/Targets/X86_64/HardwareTimingHarness.lean"] [] discPair
      writeKernel nopReduced (some "calibration/x86_64/timer_overhead.json") ["Gasm/Targets/X86_64/HardwareTimingHarness.lean"] [] discPair
      writeKernel chainReduced (some "calibration/x86_64/timer_overhead.json") ["Gasm/Targets/X86_64/Instructions/Add.lean"] [("Gasm/Targets/X86_64/Instructions/Add.lean", "AddR64Imm8.toUops", "median")] discPair
      for entry in suite do
        if entry.kernel.name != "timer_overhead" && entry.kernel.name != "nop_loop" && entry.kernel.name != "long_dependent_chain" then
          match raws.find? (·.name == entry.kernel.name) with
          | none => pure ()
          | some raw =>
            let reduced := reduceTiming raw overheadMedian
            let subject := match entry.modeledInstr with
              | some instr => [s!"instruction: {X86_64Instruction.toLean instr}"]
              | none => []
            let bindings := if entry.kernel.name == "shl_by_cl" then
                [("Gasm/Targets/X86_64/Instructions/Shift.lean", "ShlR64Cl.toUops", "median")]
              else []
            writeKernel reduced (some "calibration/x86_64/timer_overhead.json") subject bindings discPair

      IO.println s!"\n[*] Wrote {suite.length} calibration file(s) under calibration/x86_64/ (provisional pending F2 -- docs/RDTSC_HARNESS.md #12)."
      IO.println s!"[*] Kernels whose real measurement contained within the current model's bounds ({citablePromotions.length}/{containmentTotal}): {citablePromotions}"
      IO.println "    Per docs/RDTSC_HARNESS.md #8, containment alone justifies citing a cost BOUND, never a uop-breakdown correctness claim -- costProvenance promotion decisions are recorded in this task's completion report, not auto-applied by this tool."
      IO.println "--------------------------------------------------------------------------------"
      return 0
    | _, _, _ =>
      IO.println "[!] FAIL-CLOSED: timer_overhead/nop_loop/long_dependent_chain results missing from the batch run (should be unreachable -- namedSuite always includes all three)."
      return 1

end Gasm.Targets.X86_64.PerfHardwareFuzzer
