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
Tools/CheckX86Obligations.lean - the P4/P5 unified per-instruction obligation gate,
LOAD-BEARING half (docs/X86_ISA_EXPANSION_PREREQUISITES.md P4 and P5, ruled by the owner to be
"the same thing").

WHY THIS TOOL EXISTS. The prerequisites document's mutation probe demonstrated that, before this
gate, an `X86_64Instruction` instance with identity semantics, an EMPTY uop list, and ZERO fuzz
states compiled cleanly and passed every check except `Registry.lean`'s registration audit. Two
obligations were convention-only: (P4) whether any named oracle -- silicon (`HardwareHarness`) or
NASM encoding -- ever validates the instance's claimed behavior, with fuzz coverage that actually
exercises it; and (P5) whether its `toUops` cost coefficients trace to any real source, or else
carry an honest, loud "uncalibrated" marker instead of a bare, unfalsifiable literal.

`Instructions/Base.lean` already makes both obligations MANDATORY: `validationOracle` and
`costProvenance` are fields on `X86_64Instruction` with NO default, exactly like `roundtripCases`
-- an instance simply cannot compile without setting both, which is the strongest form of
enforcement in this codebase (`docs/REVIEW.md` #4.1.1's own framing: a Lean-side obligation that
fails the build outright cannot be bypassed by not running a script, unlike a Python linter that
can simply not be invoked). Verified live for this change: temporarily deleting
`AddR64R64.validationOracle`/`costProvenance` and running `lake build
Gasm.Targets.X86_64.Instructions.Add` fails with `error: ...: Fields missing: 'validationOracle',
'costProvenance'`, naming the exact offender -- then reverting restores a clean build. That
control vector is not repeated as an automated `--self-test` here (a real-tree mutation would cost
a ~130s+ rebuild per docs/X86_ISA_EXPANSION_PREREQUISITES.md's own measured per-edit cascade,
which is the wrong cost model for a fast merge gate); it is a one-time, reported, human-verified
control, exactly analogous in spirit to `Registry.lean`'s own header comment describing its
mutation test.

WHAT THIS TOOL CHECKS THAT THE MANDATORY FIELD ALONE CANNOT: field PRESENCE is compile-time and
free; field HONESTY is not. An author could still write `validationOracle _ := .silicon` on an
instance whose `canFuzzHardware` is false, or whose `generateFuzzStates` returns the empty list, or
write `.nasmEncoding ""` (a technically-present-but-vacuous justification). None of that is a type
error. This tool walks `Registry.allEncodableInstructions` (the SAME live, registry-derived witness
list `RoundtripTests.lean`/`SemanticsFuzzer.lean`/`EncodingFuzzer.lean` already derive their own
suites from) and checks, per instance:
  1. `toUops` is non-empty (closes the probe's "empty uop list" defect directly).
  2. `validationOracle = .silicon` IFF `canFuzzHardware` is true (catches a claim that disagrees
     with the field that actually drives `SemanticsFuzzer.lean`'s hardware-fuzz suite).
  3. Whenever `validationOracle = .silicon`, `generateFuzzStates` must clear a VACUITY FLOOR
     (`fuzzStateFloor`, currently 3) -- closes the probe's "zero fuzz states" defect directly; a
     form that claims silicon validation but barely samples any state is not meaningfully
     validated.
  4. `.nasmEncoding`/`.optedOut`/`.cited`/`.modelInternalUnvalidated` all carry a NON-EMPTY,
     non-trivial (≥ `minReasonLen` characters) justification string -- a present-but-empty string
     would satisfy the type checker while carrying zero information.
  5. Every `.optedOut` occurrence (the "neither oracle covers this" escape hatch -- see
     `Instructions/Obligations.lean`'s `ValidationOracle` doc comment) has a matching, justified
     entry in `scripts/x86_obligation_allowlist.txt`, mirroring Law 10's `grandfathered` category:
     never a silent absence. `.silicon`/`.nasmEncoding` need no allowlist entry -- their own
     mandatory reason string IS the record, exactly as Law 14's `modelInternalUnvalidated` marking
     discharges the calibration obligation by being loud rather than by being pre-approved.

THE COST-PROVENANCE OBLIGATION'S HONEST STATE, reported but not gated red: every one of the 88
registered forms is `.modelInternalUnvalidated` today (0 are `.cited`), and that is correct, not a
defect this tool should fail the build over. `docs/CALIBRATION_GOVERNANCE.md` #9 rules out external
tables (Agner Fog / uops.info) as the SOURCE of a shipped coefficient -- cross-check only -- and F1
(the RDTSC harness self-measured calibration would need) is `docs/tasks/F1-rdtsc-harness.md`,
status `ready`, unbuilt. So there is today no legitimate source any of the 88 forms COULD cite; the
gate's job is to make that debt loud and counted (see the summary table this tool prints), per Law
14's "honesty in output" clause -- not to fail the build over a debt this repository has not yet
built the infrastructure to pay down. A future `.cited` entry naming a real calibration artifact or
`references.json` slug is exactly what should start moving this count off zero.

SELF-TEST DESIGN (`--self-test`): unlike `scripts/check_record.py`'s model of planting a defect
into the REAL tree and re-running the live check, this tool's checking logic is a pure function
(`checkInstrData`) over a small extracted record (`InstrCheckData`), not over the compiled
environment -- so the fast, repeatable, no-rebuild-required control vector is to construct
SYNTHETIC good/bad `InstrCheckData` fixtures directly (mirroring `EncodingFuzzer.lean`'s own
`runNasmControlVectors` Law 13(4) pattern: known-good and known-bad vectors run through the EXACT
function real data flows through) and assert `checkInstrData` classifies each one correctly. This
tests the thing that can actually be silently wrong (the checking logic itself), without paying a
real-tree-mutation rebuild cost for a check that requires no Lean elaboration to exercise.
-/
import Lean
import Gasm.Targets.X86_64.Registry
import Gasm.Targets.X86_64.Instructions.Obligations
import Gasm.Targets.X86_64.MemCostModel

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- Minimum `generateFuzzStates` count a `.silicon`-claiming instance must clear -- closes the
    prerequisites document's mutation probe (zero fuzz states, compiled cleanly) directly. Kept
    small and named, not tuned to any family's actual count, so it is legible as a floor rather
    than a coverage target: `generateStandardFuzzStatesFor2Regs`/`For1Reg`/`ForImm` all produce
    well over this by construction (18-56 states per call at default `randCount`), so the floor
    only ever fires on something structurally wrong, not on a thin-but-honest suite. -/
def fuzzStateFloor : Nat := 3

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- Minimum length a `.nasmEncoding`/`.optedOut`/`.cited`/`.modelInternalUnvalidated` reason
    string must clear to count as a real justification rather than a technically-non-empty
    placeholder (`"x"`, `"-"`). Short, not strict prose-quality enforcement (out of scope for a
    mechanical gate) -- just enough to catch the vacuous case. -/
def minReasonLen : Nat := 8

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- Wraps a string in double quotes for a diagnostic message (no escaping of embedded quotes --
    every use site here is a repository-authored reason string, not untrusted input). -/
def q (s : String) : String := "\"" ++ s ++ "\""

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- Repeats a character `n` times, for banner lines (avoids depending on a `String.pushn`-shaped
    API this toolchain may not provide). -/
def repeatChar (c : Char) (n : Nat) : String := String.ofList (List.replicate n c)

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- Everything `checkInstrData` needs from one instance, extracted once so the SAME check function
    runs against both real registry data (`toCheckData`) and synthetic self-test fixtures
    (constructed directly, no `X86_64Instruction` instance required) -- see this file's header for
    why that split is the right shape for this tool's `--self-test`. -/
structure InstrCheckData where
  label          : String
  uopsEmpty      : Bool
  oracle         : ValidationOracle
  canFuzzHW      : Bool
  fuzzStateCount : Nat
  provenance     : CoefficientProvenance
  -- MH2 (docs/tasks/MH2-memory-uop-centralization.md, docs/MEMORY_HOOK.md §5.2 item 3): the
  -- derivation-invariant inputs. `memoryUops` is the instance's ACTUAL memory-class (`.load`/
  -- `.storeAddr`/`.storeData`) uop subset; `derivedMemoryUops` is what `memAccesses` mapped
  -- through `memUops` at the shared `defaultMemCostModel` says it SHOULD be -- checked only when
  -- `hasMemAccesses` (see that field's own comment for why).
  memoryUops        : List X86_64Uop
  derivedMemoryUops : List X86_64Uop
  -- Whether this instance declares any memory access (`memAccesses ≠ []`) -- the derivation
  -- check below fires only when true. IN/OUT (port I/O) legitimately use `.load`/`.storeAddr`/
  -- `.storeData` `UopClass` tags for their own port-bandwidth modeling while correctly declaring
  -- `memAccesses := []` (port I/O is not `X86_64Memory`-space; `MemAccessSpec`'s `Address` type
  -- does not cover it) -- `UopClass` is a generic hardware-port classification shared by both
  -- domains, not itself proof of `X86_64Memory` residency, so gating on the declared descriptor
  -- (not on `uopClass` alone) is what keeps this check scoped to MH2's actual 14-form population
  -- instead of retroactively annexing IN/OUT's pre-existing, unrelated modeling into the hook's
  -- domain. A form that falsely declares `memAccesses := []` while its `step` genuinely touches
  -- `X86_64Memory` is caught at the semantic level instead, by MH1's mandatory `WritesWithin`/
  -- `ReadsWithin` frame-lemma obligation (`MemoryFrame/*.lean`) -- a kernel-checked theorem, not
  -- a build-time linter, and the stronger of the two mechanisms for that specific claim.
  hasMemAccesses    : Bool
deriving Inhabited

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- Extracts `InstrCheckData` from a real registered instance, calling exactly the typeclass
    methods every other consumer (`RoundtripTests.lean`, `SemanticsFuzzer.lean`,
    `EncodingFuzzer.lean`) already calls -- no re-derivation of instance behavior. -/
def toCheckData (rng : Gasm.Core.FuzzerRng) (instr : AnyX86_64Instruction) : InstrCheckData :=
  { label          := X86_64Instruction.toLean instr
    uopsEmpty      := (X86_64Instruction.toUops instr).isEmpty
    oracle         := X86_64Instruction.validationOracle instr
    canFuzzHW      := X86_64Instruction.canFuzzHardware instr
    fuzzStateCount := (X86_64Instruction.generateFuzzStates instr rng).1.length
    provenance     := X86_64Instruction.costProvenance instr
    memoryUops        := (X86_64Instruction.toUops instr).filter isMemoryClassUop
    derivedMemoryUops := derivedMemUops (X86_64Instruction.memAccesses instr) defaultMemCostModel
    hasMemAccesses    := !(X86_64Instruction.memAccesses instr).isEmpty }

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- The obligation gate's actual checking logic (see this file's header, items 1-4; item 5 -- the
    `.optedOut` allowlist cross-check -- needs the allowlist file and lives in `runGate` instead,
    since a pure per-instance function has no business reading a file). Returns a human-readable
    violation for every rule this instance fails; an empty list is a clean pass. Pure and
    deterministic so the self-test fixtures below exercise EXACTLY this function, not a
    re-implementation of it. -/
def checkInstrData (d : InstrCheckData) : List String := Id.run do
  let mut violations : List String := []
  if d.uopsEmpty then
    violations := violations ++ [s!"{d.label}: toUops is empty (P4's mutation-probe defect: an \
      instruction with no micro-ops at all)"]
  -- MH2's derivation invariant (docs/MEMORY_HOOK.md §5.1/§5.2 item 3): for every instance that
  -- DECLARES a memory access, the memory-class subset of `toUops` must equal `memAccesses`
  -- mapped through `memUops` at `defaultMemCostModel` -- this is what closes off memory-class
  -- uop construction outside the hook mechanically (see MemCostModel.lean's header comment for
  -- why a structural private-constructor seal was not pursued instead). Gated on
  -- `hasMemAccesses` (see that field's own comment): IN/OUT's pre-existing, unrelated
  -- `.load`/`.storeAddr`/`.storeData`-tagged port-I/O uops are correctly out of scope.
  if d.hasMemAccesses && !memUopListEq d.memoryUops d.derivedMemoryUops then
    violations := violations ++ [s!"{d.label}: memory-class toUops ({d.memoryUops.length} uop(s)) \
      does not equal memAccesses mapped through memUops ({d.derivedMemoryUops.length} uop(s)) -- \
      a memory-class uop has diverged from the MH2 cost table (docs/MEMORY_HOOK.md §5.1's \
      derivation invariant, §5.2 item 3); construct memory uops only via `memUops`/`derivedMemUops` \
      in Gasm/Targets/X86_64/MemCostModel.lean"]
  match d.oracle with
  | .silicon =>
    if !d.canFuzzHW then
      violations := violations ++ [s!"{d.label}: validationOracle claims .silicon but \
        canFuzzHardware is false for this instance -- the claim and the field that actually \
        drives SemanticsFuzzer.lean's hardware-fuzz suite disagree"]
    if d.fuzzStateCount < fuzzStateFloor then
      violations := violations ++ [s!"{d.label}: validationOracle claims .silicon but only \
        {d.fuzzStateCount} fuzz state(s) were generated (floor: {fuzzStateFloor}) -- P4's \
        mutation-probe defect (zero/near-zero fuzz states) restated for the .silicon claim \
        specifically"]
  | .nasmEncoding reason =>
    if reason.length < minReasonLen then
      violations := violations ++ [s!"{d.label}: validationOracle .nasmEncoding reason \
        {q reason} is shorter than {minReasonLen} characters -- not a real justification"]
    if d.canFuzzHW then
      violations := violations ++ [s!"{d.label}: validationOracle claims .nasmEncoding (no \
        silicon coverage) but canFuzzHardware is true for this instance -- it should be \
        .silicon instead"]
  | .optedOut reason =>
    if reason.length < minReasonLen then
      violations := violations ++ [s!"{d.label}: validationOracle .optedOut reason \
        {q reason} is shorter than {minReasonLen} characters -- not a real justification"]
  match d.provenance with
  | .cited artifact =>
    if artifact.length < minReasonLen then
      violations := violations ++ [s!"{d.label}: costProvenance .cited artifact \
        {q artifact} is shorter than {minReasonLen} characters -- not a real citation"]
  | .modelInternalUnvalidated reason =>
    if reason.length < minReasonLen then
      violations := violations ++ [s!"{d.label}: costProvenance .modelInternalUnvalidated \
        reason {q reason} is shorter than {minReasonLen} characters -- not a real \
        justification"]
  return violations

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- One parsed, valid line of `scripts/x86_obligation_allowlist.txt` -- same 5-field
    `::`-delimited shape as `scripts/gate_allowlist.txt`/`scripts/ref_allowlist.txt`
    (`file::typeDecl::toLeanPrefix::category::justification`; see that file's own header comment
    for exactly what each field means for THIS obligation, since "declaration name"/"fqn" do not
    map onto a per-witness-instance obligation the way they do for the other two allowlists). -/
structure OptOutAllowlistEntry where
  file          : String
  typeDecl      : String
  toLeanPrefix  : String
  category      : String
  justification : String
  lineNum       : Nat
deriving Inhabited

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
def validOptOutCategories : List String := ["validation-optout"]

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
def splitOnMax (s : String) (sep : String) (maxParts : Nat) : List String :=
  let parts := s.splitOn sep
  if parts.length ≤ maxParts then
    parts
  else
    let head := parts.take (maxParts - 1)
    let tail := parts.drop (maxParts - 1)
    head ++ [String.intercalate sep tail]

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- Parses `scripts/x86_obligation_allowlist.txt`. A malformed line is a hard parse failure, same
    discipline as every other allowlist in this repository -- never a silently-skipped line. -/
def parseOptOutAllowlist (contents : String) : List OptOutAllowlistEntry × List String := Id.run do
  let mut entries : List OptOutAllowlistEntry := []
  let mut errors : List String := []
  let mut lineNum := 0
  for rawLine in contents.splitOn "\n" do
    lineNum := lineNum + 1
    let line := rawLine.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then
      continue
    let parts := splitOnMax line "::" 5
    if parts.length != 5 then
      errors := errors ++
        [s!"x86_obligation_allowlist.txt:{lineNum}: expected 5 '::'-delimited fields \
          (file::typeDecl::toLeanPrefix::category::justification), got {parts.length}: {rawLine}"]
      continue
    let file := parts[0]!.trimAscii.toString
    let typeDecl := parts[1]!.trimAscii.toString
    let toLeanPrefix := parts[2]!.trimAscii.toString
    let category := parts[3]!.trimAscii.toString.toLower
    let justification := parts[4]!.trimAscii.toString
    if !validOptOutCategories.contains category then
      errors := errors ++
        [s!"x86_obligation_allowlist.txt:{lineNum}: unknown category \
          {q parts[3]!.trimAscii.toString} (expected one of {validOptOutCategories})"]
      continue
    if toLeanPrefix.isEmpty then
      errors := errors ++
        [s!"x86_obligation_allowlist.txt:{lineNum}: missing toLean prefix (3rd field)"]
      continue
    if justification.isEmpty then
      errors := errors ++ [s!"x86_obligation_allowlist.txt:{lineNum}: missing justification"]
      continue
    entries := entries ++
      [(⟨file, typeDecl, toLeanPrefix, category, justification, lineNum⟩ : OptOutAllowlistEntry)]
  return (entries, errors)

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
def sepLine : String :=
  "======================================================================"

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- The live gate: walks the real registry, checks every instance, cross-checks `.optedOut`
    against the allowlist (including the stale-entry sweep), and prints the P4(c) status table
    (`docs/X86_ISA_EXPANSION_PREREQUISITES.md`: "N forms silicon-validated / M NASM-covered / K
    opted-out") plus the cost-provenance breakdown -- so the debt is measured on every run, not
    merely gated. -/
def runGate : IO UInt32 := do
  let startTime ← IO.monoMsNow
  IO.println sepLine
  IO.println " gasm x86-64 Instruction Obligation Gate (Tools/CheckX86Obligations.lean)"
  IO.println " P4 (validation) + P5 (calibration) unified, per docs/X86_ISA_EXPANSION_PREREQUISITES.md"
  IO.println sepLine

  let allowlistPath : System.FilePath := "scripts" / "x86_obligation_allowlist.txt"
  if !(← allowlistPath.pathExists) then
    IO.eprintln s!"[!] ERROR: {allowlistPath} not found relative to the current directory."
    IO.eprintln "    Run this tool from the repo root, e.g.: `lake exe check_x86_obligations`"
    return 1
  let allowlistText ← IO.FS.readFile allowlistPath
  let (allowlist, parseErrors) := parseOptOutAllowlist allowlistText

  if !parseErrors.isEmpty then
    IO.println s!"\n[!] FAILED: {parseErrors.length} malformed allowlist line(s):"
    for e in parseErrors do
      IO.println s!"    - {e}"
    IO.println sepLine
    return 1

  let rng : Gasm.Core.FuzzerRng := ⟨0xC0FFEE⟩
  let instances := Gasm.Targets.X86_64.Registry.allEncodableInstructions
  let dataList := instances.map (toCheckData rng)

  let mut violations : List String := []
  for d in dataList do
    violations := violations ++ checkInstrData d

  -- Item 5: every `.optedOut` occurrence needs a matching allowlist entry, keyed on the
  -- `toLean`-rendered prefix token (the first whitespace-delimited word, e.g. "add_r64_imm8") --
  -- see `Instructions/Base.lean`/every `toLean` implementation for why this token is a reliable,
  -- per-TYPE-stable key even though individual witness instances vary their trailing operands.
  let leanPrefix (s : String) : String := (s.splitOn " ").headD s
  let mut matchedKeys : List String := []
  for d in dataList do
    match d.oracle with
    | .optedOut _ =>
      let key := leanPrefix d.label
      match allowlist.find? (fun e => e.toLeanPrefix == key) with
      | some _ => matchedKeys := matchedKeys ++ [key]
      | none =>
        violations := violations ++ [s!"{d.label}: validationOracle is .optedOut with no \
          matching scripts/x86_obligation_allowlist.txt entry ('*::*::{key}::validation-optout::\
          ...') -- an opt-out from BOTH oracles must be an explicit, reviewed exception, never a \
          silent absence"]
    | _ => pure ()

  let staleEntries := allowlist.filter (fun e => !matchedKeys.contains e.toLeanPrefix)

  -- --- Summary tables (printed every run, per Law 14's "honesty in output" clause) ---
  let siliconCount := dataList.filter (fun d => d.oracle matches .silicon) |>.length
  let nasmCount := dataList.filter (fun d => d.oracle matches .nasmEncoding _) |>.length
  let optOutCount := dataList.filter (fun d => d.oracle matches .optedOut _) |>.length
  let citedCount := dataList.filter (fun d => d.provenance matches .cited _) |>.length
  let unvalidatedCount := dataList.filter (fun d => d.provenance matches .modelInternalUnvalidated _) |>.length

  IO.println s!"\n[*] {dataList.length} registered instance(s) scanned (registry-derived, same \
    source RoundtripTests.lean/SemanticsFuzzer.lean/EncodingFuzzer.lean already use)."
  IO.println "\n--- P4: VALIDATION OBLIGATION (named oracle per instance) ---"
  IO.println s!"    .silicon (HardwareHarness-fuzzed) : {siliconCount}"
  IO.println s!"    .nasmEncoding (encoding-only)      : {nasmCount}"
  IO.println s!"    .optedOut (neither oracle)         : {optOutCount} \
    ({matchedKeys.eraseDups.length} distinct allowlisted key(s))"
  IO.println "\n--- P5: CALIBRATION OBLIGATION (coefficient provenance per instance) ---"
  IO.println s!"    .cited (real calibration source)          : {citedCount}"
  IO.println s!"    .modelInternalUnvalidated (honest, uncited) : {unvalidatedCount}"
  if citedCount == 0 then
    IO.println "    [i] 0 cited: F1 (RDTSC harness, docs/tasks/F1-rdtsc-harness.md) is unbuilt \
      and docs/CALIBRATION_GOVERNANCE.md #9 rules out external tables (Agner Fog / uops.info) as \
      a coefficient SOURCE -- this is the honest, expected state, not a gate failure. See this \
      file's own header comment."

  -- MH2 (docs/tasks/MH2-memory-uop-centralization.md, docs/MEMORY_HOOK.md §5.3(b)): the memory
  -- cost TABLE's own coefficient provenance, distinct from the per-INSTANCE costProvenance
  -- breakdown above -- 6 named coefficients shared by all 1611 registered instances rather than
  -- one mark per instance. Printed every run, per Law 14's honesty-in-output clause.
  let memTotal := defaultMemCostModel.provenances.length
  let memCalibrated := defaultMemCostModel.calibratedCount
  IO.println "\n--- MH2: MEMORY COST TABLE PROVENANCE (Law 14, docs/MEMORY_HOOK.md §5) ---"
  IO.println s!"    {memCalibrated} of {memTotal} memory coefficients calibrated / \
    {memTotal - memCalibrated} model-internal"
  if memCalibrated == 0 then
    IO.println "    [i] 0 calibrated: same F1/Law-14-#9 reason as the per-instance breakdown \
      above -- every memory coefficient is honestly modelInternalUnvalidated today \
      (Gasm/Targets/X86_64/MemCostModel.lean)."

  let mut failed := false

  if !violations.isEmpty then
    failed := true
    IO.println s!"\n[!] FAILED: {violations.length} obligation violation(s):"
    for v in violations do
      IO.println s!"    - {v}"

  if !staleEntries.isEmpty then
    failed := true
    IO.println s!"\n[!] FAILED: {staleEntries.length} scripts/x86_obligation_allowlist.txt \
      entr(y/ies) matched no current .optedOut instance (stale; prune):"
    for e in staleEntries do
      IO.println s!"    - x86_obligation_allowlist.txt:{e.lineNum} \
        {e.file}::{e.typeDecl}::{e.toLeanPrefix}"

  if !failed then
    IO.println "\n[+] Every registered instance discharges its validation obligation (a named \
      oracle, or a justified, allowlisted opt-out) and its calibration obligation (a cited \
      source, or an honest, loud .modelInternalUnvalidated marker)."

  let elapsedMs := (← IO.monoMsNow) - startTime
  IO.println s!"\n[*] Wall time: {elapsedMs}ms."
  IO.println sepLine
  return if failed then 1 else 0

-- ---------------------------------------------------------------------------------------------
-- --self-test: synthetic good/bad InstrCheckData control vectors run through the real
-- `checkInstrData` function (see this file's header for why this shape, not real-tree mutation,
-- is the right self-test for a PURE function this tool's own correctness rests on). A gate you
-- have only seen pass on real data -- which is always well-formed here BY CONSTRUCTION, since the
-- mandatory typeclass fields already forced every author to set something -- is untested against
-- the malformed data it exists to catch.
-- ---------------------------------------------------------------------------------------------

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- A register-only-shaped good fixture: no memory uops on either side of the MH2 derivation
    check, which must pass vacuously (matching 74 of the 88 real registered forms). -/
def goodFixture : InstrCheckData :=
  { label := "self_test_good", uopsEmpty := false, oracle := .silicon, canFuzzHW := true,
    fuzzStateCount := 24, provenance := .modelInternalUnvalidated "no calibration source exists yet",
    memoryUops := [], derivedMemoryUops := [], hasMemAccesses := false }

/- REF: docs/MEMORY_HOOK.md#52-why-this-is-falsifiable-where-todays-numbers-are-not -/
/-- A memory-shaped good fixture: `toUops`'s memory-class subset genuinely equals what
    `memAccesses` derives via `memUops` -- the real post-migration shape of all 14 memory forms
    (e.g. `PopR64`: one `.load` uop matching `popR64Accesses`'s single load access). -/
def memDerivationMatchFixture : InstrCheckData :=
  { goodFixture with
    label := "self_test_mem_match"
    memoryUops := memUops ⟨.load, .w64, ⟨some .rsp, none, 0⟩⟩ defaultMemCostModel
    derivedMemoryUops := memUops ⟨.load, .w64, ⟨some .rsp, none, 0⟩⟩ defaultMemCostModel
    hasMemAccesses := true }

/- REF: docs/MEMORY_HOOK.md#52-why-this-is-falsifiable-where-todays-numbers-are-not -/
/-- The Law-13 negative control for MH2's derivation invariant, restated as data (mirroring the
    prerequisites document's own mutation-probe fixture below): an instance whose actual
    memory-class `toUops` (a hand-written `latencyCycles := 999` load, the shape a form that
    bypassed `memUops` and invented its own literal would take) disagrees with what its declared
    `memAccesses` derives. `checkInstrData` must flag this. -/
def memDerivationMismatchFixture : InstrCheckData :=
  { goodFixture with
    label := "self_test_mem_mismatch"
    memoryUops :=
      [{ mnemonic := "MEM.load", uopClass := .load, eligiblePorts := [.p2, .p3], latencyCycles := 999 }]
    derivedMemoryUops := memUops ⟨.load, .w64, ⟨some .rsp, none, 0⟩⟩ defaultMemCostModel
    hasMemAccesses := true }

/- REF: docs/MEMORY_HOOK.md#52-why-this-is-falsifiable-where-todays-numbers-are-not -/
/-- IN/OUT's shape restated as data: `.load`-tagged port-I/O uops with NO declared memory
    access -- must pass clean, confirming `hasMemAccesses := false` correctly takes this out of
    the derivation check's scope (found live against the real registry: without this gating, 16
    real IN/OUT witnesses failed the gate for pre-existing, unrelated port-I/O modeling that
    predates and is out of scope for MH2's 14-form migration). -/
def portIOUnaffectedFixture : InstrCheckData :=
  { goodFixture with
    label := "self_test_port_io"
    memoryUops :=
      [{ mnemonic := "IN.load", uopClass := .load, eligiblePorts := [.p2, .p3], latencyCycles := 4 }]
    derivedMemoryUops := []
    hasMemAccesses := false }

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
/-- The prerequisites document's own mutation probe, restated as data: identity semantics
    (irrelevant to this record), an empty uop list, and zero fuzz states, but (unrealistically,
    to isolate exactly this defect) still claiming `.silicon`. -/
def emptyUopsAndZeroFuzzFixture : InstrCheckData :=
  { goodFixture with label := "self_test_probe", uopsEmpty := true, fuzzStateCount := 0 }

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
def siliconCanFuzzMismatchFixture : InstrCheckData :=
  { goodFixture with label := "self_test_mismatch", canFuzzHW := false }

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
def vacuousNasmReasonFixture : InstrCheckData :=
  { goodFixture with label := "self_test_vacuous_reason", oracle := .nasmEncoding "x", canFuzzHW := false }

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
def vacuousCostReasonFixture : InstrCheckData :=
  { goodFixture with provenance := .modelInternalUnvalidated "" }

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
def runSelfTest : IO UInt32 := do
  IO.println (repeatChar '#' 100)
  IO.println "# Tools/CheckX86Obligations.lean --self-test: synthetic good/bad control vectors"
  IO.println (repeatChar '#' 100)

  let cases : List (String × InstrCheckData × Bool) := [
    ("good_fixture_passes_clean", goodFixture, true),
    ("empty_uops_and_zero_fuzz_flagged", emptyUopsAndZeroFuzzFixture, false),
    ("silicon_canfuzz_mismatch_flagged", siliconCanFuzzMismatchFixture, false),
    ("vacuous_nasm_reason_flagged", vacuousNasmReasonFixture, false),
    ("vacuous_cost_reason_flagged", vacuousCostReasonFixture, false),
    ("mem_derivation_match_passes_clean", memDerivationMatchFixture, true),
    ("mem_derivation_mismatch_flagged", memDerivationMismatchFixture, false),
    ("port_io_unaffected_passes_clean", portIOUnaffectedFixture, true)
  ]

  let mut allOk := true
  for (name, fixture, expectClean) in cases do
    let violations := checkInstrData fixture
    let actualClean := violations.isEmpty
    let ok := actualClean == expectClean
    allOk := allOk && ok
    let verdict := if ok then "PASS" else "FAIL"
    IO.println s!"\n[SELF-TEST] {name} ..."
    IO.println s!"  expected_clean={expectClean}  actual_clean={actualClean}  \
      violations={violations.length}  -> {verdict}"
    if !ok then
      for v in violations do
        IO.println s!"    - {v}"

  let overall := if allOk then "PASS" else "FAIL"
  IO.println ("\n" ++ repeatChar '=' 100)
  IO.println s!" SELF-TEST SUMMARY: {overall}"
  IO.println (repeatChar '=' 100)
  return if allOk then 0 else 1

/- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p4-blocking-make-per-instruction-validation-obligations-mandatory-and-visible -/
def main (args : List String) : IO UInt32 :=
  match args with
  | ["--self-test"] => runSelfTest
  | _ => runGate
