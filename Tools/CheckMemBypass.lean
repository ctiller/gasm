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
Tools/CheckMemBypass.lean -- the Law 11 bypass-ledger gate (MH3,
`docs/MEMORY_HOOK.md` #4.5, `docs/tasks/MH3-capability-authoring-surface.md`).

WHY THIS TOOL EXISTS. MH1 sealed machine memory behind `X86_64Mem.read`/`write` and MH3 built the
Layer A capability authoring surface (`Gasm.Targets.X86_64.CheckedAsm`): a checked-program type
whose memory-operand constructors demand an `AccessOK` proof, erasing to today's `SymbolicInstr`
list. That surface is opt-in -- nothing stops a module from continuing to call one of the 14
memory-touching forms' raw smart constructors (`mov_mem64_disp`, `push_r64`, ...) directly,
bypassing the proof obligation entirely. Law 11's text is explicit that this bypass is "prohibited
in migrated modules; unmigrated modules are tracked as critical backlog" -- this tool is the
build-failing check that makes that tracking mechanical instead of a convention nobody enforces.

THE RAW CONSTRUCTOR NAMES ARE DERIVED, NOT HAND-LISTED (`docs/MEMORY_HOOK.md` #4.5's own
requirement). `Gasm.Targets.X86_64.Registry.allEncodableInstructions` is the same live,
registry-derived witness list `Tools/CheckX86Obligations.lean`/the roundtrip/fuzzer suites already
build their own coverage from. Every witness whose `memAccesses` is non-empty is one of the 14
memory-touching forms; its `toLean` rendering's first whitespace-delimited token is EXACTLY the
smart-constructor name an author would type to build one raw (e.g. `MovMem64DispReg64`'s witnesses
all render `"mov_mem64_disp ..."`). Adding a 15th memory form to the registry, or renaming a smart
constructor, changes what this tool checks automatically -- no second list to keep in sync.

HOW A RAW CALL SITE IS DETECTED: this walks every declaration in the compiled environment
(`env.constants`, the same source `Tools/CheckGatesAxioms.lean`/`Tools/CheckRefsCoverage.lean`
walk) whose originating module is under `Gasm`/`Stdlib`/`Spikes`, and inspects each declaration's
elaborated VALUE (`ConstantInfo.value?`) for a reference (`Expr.const`) to one of the 14 raw
constructors' fully-qualified names. This is load-bearing, not a source-text pre-check (unlike
`scripts/check_gates.py`'s stated role for Law 10): a definition's own compiled body cannot hide a
reference to a constant it genuinely calls behind a comment, a re-spelled tactic, or any other
source-level disguise the way a regex scan can be fooled -- the same reasoning `TCB.md` records for
why `Tools/CheckGatesAxioms.lean` reads the kernel-recorded axiom graph instead of grepping for
`native_decide`. Every real call site the earlier population sweep found (Spikes' `Program.lean`s,
`Stdlib/SmolAlloc/Program.lean`, `Stdlib/Zlib/X86_64.lean`, ...) is reachable from the baseline
`import Gasm; import Stdlib; import Spikes` closure -- none of them are the standalone
`def main`/`def runTests` modules `Tools/GateSubprocess.lean`'s subprocess-isolation protocol
exists for -- so, unlike its two siblings, this tool does not need that protocol: the baseline
environment already sees every module a raw memory-operand call site could live in.

DESIGNATED INFRASTRUCTURE (`infraModules`): the decoder, the differential fuzzers, the roundtrip
gate, symbolic-call-target resolution (`Assembler.lean`), and `CheckedAsm.lean` itself -- the ONE
module authorized to call a raw constructor AFTER collecting the `AccessOK` proof it demands
(`docs/MEMORY_HOOK.md` #4.5's own exemption clause: "the ledger + the designated infrastructure
modules (erasure, decoder, fuzzers, roundtrip)"). A reference from any of these needs no ledger
entry; a reference from anywhere else does.

THE LEDGER (`scripts/mem_bypass_allowlist.txt`, 5-field `::`-format) is the migration backlog, not
an approval list: every entry's category is `unmigrated`, review policy rejects new entries (Law
11's text), and entries may only be removed as PA4 migrates a module's last raw call site of a
given form. A module with zero raw call sites never appears and never trips the gate -- "not yet
migrated" and "does not need it" are mechanically distinct, exactly as the design requires.
-/
import Lean
import Gasm
import Stdlib
import Spikes
import Gasm.Targets.X86_64.Registry
import Gasm.Targets.X86_64.Instructions.Base
import Tools.GateSubprocess

open Lean

--------------------------------------------------------------------------------------------------
-- Mechanically-derived raw constructor names (docs/MEMORY_HOOK.md #4.5: "not hand-listed")
--------------------------------------------------------------------------------------------------

namespace Gasm.Targets.X86_64.Instructions

/-- Every one of the 14 memory-touching forms' raw smart-constructor names, derived from the
    registry: filter `allEncodableInstructions` to witnesses with a non-empty `memAccesses`
    (exactly the memory-touching forms, `docs/MEMORY_HOOK.md` #3.3), then take each witness's
    `toLean` rendering's first token -- the exact source spelling an author calls. -/
def memFormRawNames : List String :=
  ((Registry.allEncodableInstructions.filter (fun pkg => X86_64Instruction.memAccesses pkg ≠ []))
    |>.map (fun pkg => ((X86_64Instruction.toLean pkg).splitOn " ").headD ""))
    |>.eraseDups

end Gasm.Targets.X86_64.Instructions

/-- The namespace every raw memory-form smart constructor lives in
    (`Gasm/Targets/X86_64/Instructions/{Mov,Push,Pop,Call,Ret}.lean`, all under one namespace --
    `Gasm/Targets/X86_64/Instructions/Base.lean`'s `namespace Gasm.Targets.X86_64.Instructions`). -/
def instrNamespace : Name := `Gasm.Targets.X86_64.Instructions

/-- Fully-qualified `Name`s of the 14 raw constructors, mechanically derived
    (`Gasm.Targets.X86_64.Instructions.memFormRawNames`) -- the actual match target this tool
    scans the compiled environment for. -/
def memFormConstructorNames : List Name :=
  Gasm.Targets.X86_64.Instructions.memFormRawNames.map (fun s => Name.str instrNamespace s)

--------------------------------------------------------------------------------------------------
-- Designated infrastructure (docs/MEMORY_HOOK.md #4.5's exemption clause)
--------------------------------------------------------------------------------------------------

/-- Modules exempt from the ledger requirement: they exist to construct raw memory-operand
    instructions on purpose. `CheckMemBypass` (this tool) is included for the same reason
    `Tools/CheckGatesAxioms.lean` excludes `Tools/` from its own `projectRootDirs` scope -- this
    file's OWN reference to the 14 names (as `String`/`Name` data, never as a called function) is
    not itself a memory-operand authoring act, but excluding `Tools` entirely keeps the exemption
    list honest about scope the same way its sibling gates do. -/
def infraModules : List Name := [
  `Gasm.Targets.X86_64.Assembler,
  `Gasm.Targets.X86_64.Decoder,
  `Gasm.Targets.X86_64.EncodingFuzzer,
  `Gasm.Targets.X86_64.Fuzzer,
  `Gasm.Targets.X86_64.Roundtrip,
  `Gasm.Targets.X86_64.RoundtripTests,
  `Gasm.Targets.X86_64.RoundtripGate.Call,
  `Gasm.Targets.X86_64.CheckedAsm,
  -- Stage B decoder modularization (`Gasm/Targets/X86_64/Instructions/Base.lean`'s header):
  -- each memory-touching family's own `<family>TryDecode` lives in the SAME module as its smart
  -- constructors and legitimately constructs raw instances from arbitrary decoded bytes -- the
  -- decoder exemption `docs/MEMORY_HOOK.md` #4.5 names, just modularized per-family instead of
  -- living in the monolithic `Decoder.lean` these five modules replace for their own opcodes.
  `Gasm.Targets.X86_64.Instructions.Mov,
  `Gasm.Targets.X86_64.Instructions.Push,
  `Gasm.Targets.X86_64.Instructions.Pop,
  `Gasm.Targets.X86_64.Instructions.Call,
  `Gasm.Targets.X86_64.Instructions.Ret
]

/-- Is `m` exactly one of `infraModules`, or under the `Tools` root? -/
def isInfraModule (m : Name) : Bool :=
  infraModules.contains m || (`Tools).isPrefixOf m

--------------------------------------------------------------------------------------------------
-- Environment walking (mirrors Tools/CheckGatesAxioms.lean's isProjectModule/originatingModule)
--------------------------------------------------------------------------------------------------

/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
def isProjectModule (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some idx =>
    match env.allImportedModuleNames[idx.toNat]? with
    | none => false
    | some modName =>
      (`Gasm).isPrefixOf modName || (`Stdlib).isPrefixOf modName || (`Spikes).isPrefixOf modName

/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
def originatingModule (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | none => none
  | some idx => env.allImportedModuleNames[idx.toNat]?

/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
def isReportableKind : ConstantInfo → Bool
  | .thmInfo _ | .defnInfo _ | .opaqueInfo _ => true
  | _ => false

/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
def isReportable (env : Environment) (name : Name) (info : ConstantInfo) : Bool :=
  isProjectModule env name && isReportableKind info && !name.isInternal

--------------------------------------------------------------------------------------------------
-- Constant-reference collection: which of the 14 raw names does a declaration's compiled VALUE
-- reference? A plain recursive Expr walk -- load-bearing per this file's header comment.
--------------------------------------------------------------------------------------------------

/-- Every `Name` a `const` node anywhere in `e` refers to. Deliberately walks every subterm
    (binder types, `let` values, projections) -- a raw constructor call hidden inside a `let` or a
    binder's type annotation is exactly as real a bypass as one in application-head position. -/
partial def exprConstants (e : Expr) : NameSet :=
  go e {}
where
  go (e : Expr) (acc : NameSet) : NameSet :=
    match e with
    | .const n _ => acc.insert n
    | .app f a => go a (go f acc)
    | .lam _ t b _ => go b (go t acc)
    | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ b => go b acc
    | _ => acc

--------------------------------------------------------------------------------------------------
-- Ledger parsing (mirrors Tools/CheckGatesAxioms.lean's AllowlistEntry/parseAllowlist)
--------------------------------------------------------------------------------------------------

/-- One parsed, valid line of `scripts/mem_bypass_allowlist.txt`. -/
structure LedgerEntry where
  file           : String
  rawName        : String
  fqn            : String
  category       : String
  justification  : String
  lineNum        : Nat
deriving Inhabited

def validCategories : List String := ["unmigrated"]

/-- Splits `s` on `sep`, merging parts beyond `maxParts` back into the final part (so `::` inside
    a free-text justification isn't mistaken for a delimiter) -- identical convention to
    `Tools/CheckGatesAxioms.lean`'s `splitOnMax`. -/
def splitOnMax (s : String) (sep : String) (maxParts : Nat) : List String :=
  let parts := s.splitOn sep
  if parts.length ≤ maxParts then
    parts
  else
    let head := parts.take (maxParts - 1)
    let tail := parts.drop (maxParts - 1)
    head ++ [String.intercalate sep tail]

/-- Turns a project-relative `.lean` file path into the dotted module `Name` Lean's own import
    resolution assigns it -- identical convention to `Tools/CheckGatesAxioms.lean`'s
    `moduleNameOfPath`. -/
def moduleNameOfPath (p : String) : Name :=
  ((System.FilePath.mk p).withExtension "").components.foldl Name.mkStr Name.anonymous

/-- Parses `scripts/mem_bypass_allowlist.txt`. A malformed line (wrong field count, unknown
    category, empty justification) is a hard parse failure -- reported, and the whole run fails,
    rather than silently skipped. -/
def parseLedger (contents : String) : List LedgerEntry × List String := Id.run do
  let mut entries : List LedgerEntry := []
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
        [s!"mem_bypass_allowlist.txt:{lineNum}: expected 5 '::'-delimited fields \
          (file::raw-name::fqn::category::justification), got {parts.length}: {rawLine}"]
      continue
    let file := parts[0]!.trimAscii.toString
    let rawName := parts[1]!.trimAscii.toString
    let fqn := parts[2]!.trimAscii.toString
    let category := parts[3]!.trimAscii.toString.toLower
    let justification := parts[4]!.trimAscii.toString
    if !validCategories.contains category then
      errors := errors ++
        [s!"mem_bypass_allowlist.txt:{lineNum}: unknown category '{parts[3]!.trimAscii.toString}' \
          (expected one of {validCategories})"]
      continue
    if fqn.isEmpty then
      errors := errors ++ [s!"mem_bypass_allowlist.txt:{lineNum}: missing fully-qualified name"]
      continue
    if justification.isEmpty then
      errors := errors ++ [s!"mem_bypass_allowlist.txt:{lineNum}: missing justification"]
      continue
    entries := entries ++ [(⟨file, rawName, fqn, category, justification, lineNum⟩ : LedgerEntry)]
  return (entries, errors)

/-- The two-part match key `docs/MEMORY_HOOK.md`/this file's header both describe: originating
    module × fully-qualified constant name. Keying by fqn alone would let one entry blanket-
    authorize every module (the TC15-class exploit `scripts/gate_allowlist.txt` documents). -/
def matchKey (moduleName fqn : Name) : String := s!"{moduleName}::{fqn}"

--------------------------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------------------------

def sepLine : String :=
  "======================================================================"

def main : IO UInt32 := do
  setupSearchPath

  IO.println sepLine
  IO.println "Law 11 bypass-ledger gate (MH3): scanning for raw memory-operand smart-constructor use"
  IO.println sepLine

  let env ←
    try
      importModules #[{module := `Gasm}, {module := `Stdlib}, {module := `Spikes}]
        {} (trustLevel := 0) (loadExts := false)
    catch e =>
      IO.eprintln s!"[!] ERROR: failed to import Gasm/Stdlib/Spikes: {e.toString}"
      IO.eprintln "    Run this tool from the repo root, e.g.: `lake exe check_mem_bypass`"
      IO.Process.exit 1

  let rawNames := memFormConstructorNames
  IO.println s!"Memory-touching forms (mechanically derived from the registry): {rawNames.length}"
  for n in rawNames do
    IO.println s!"  - {n}"

  let ledgerPath : System.FilePath := "scripts" / "mem_bypass_allowlist.txt"
  let ledgerContents ← IO.FS.readFile ledgerPath
  let (ledgerEntries, parseErrors) := parseLedger ledgerContents
  if !parseErrors.isEmpty then
    IO.println sepLine
    IO.println "LEDGER PARSE ERRORS:"
    for e in parseErrors do
      IO.println s!"  {e}"
    return 1

  let mut ledgerKeySet : Std.HashSet String := {}
  for e in ledgerEntries do
    ledgerKeySet := ledgerKeySet.insert (matchKey (moduleNameOfPath e.file) (nameOfDotted e.fqn))

  IO.println sepLine
  IO.println s!"Ledger entries (scripts/mem_bypass_allowlist.txt): {ledgerEntries.length}"
  IO.println sepLine

  -- Walk every project declaration; for each, find which raw constructors it references (in
  -- either its elaborated VALUE or its TYPE -- a `rfl`-proved step lemma like `step_ret_op`
  -- cites `ret_op` only in its STATEMENT, since the proof term itself need not re-mention the
  -- LHS it reflexively equates; scanning only `.value?` would silently miss exactly that
  -- authoring-adjacent reference class), then classify: infra (exempt), ledgered (known debt),
  -- or a violation.
  let mut violations : List (Name × Name × Name) := []  -- (declName, module, raw constructor)
  let mut ledgerHits : Std.HashSet String := {}
  for (name, info) in env.constants.toList do
    if isReportable env name info then
      match originatingModule env name with
      | none => pure ()
      | some modName =>
        -- A declaration's OWN name is checked in addition to its originating module: Lean
        -- compiles a `def`'s auto-generated unfolding equation lemmas (`foo.eq_1`, ...) lazily,
        -- on first use -- e.g. `Gasm.Targets.X86_64.CheckedAsm.storeReg64.eq_1` can be reported
        -- as originating from WHICHEVER module's `simp [storeReg64]` call first materialized it,
        -- not from `CheckedAsm.lean` itself. A declaration whose own qualified name already lives
        -- under an infra namespace is exempt regardless of that elaboration accident.
        if isInfraModule modName || (`Gasm.Targets.X86_64.CheckedAsm).isPrefixOf name then
          pure ()
        else
          let usedInType := exprConstants info.type
          let usedInValue := match info.value? with
            | none => ({} : NameSet)
            | some val => exprConstants val
          for raw in rawNames do
            if usedInType.contains raw || usedInValue.contains raw then
              let key := matchKey modName raw
              if ledgerKeySet.contains key then
                ledgerHits := ledgerHits.insert key
              else
                violations := violations ++ [(name, modName, raw)]

  IO.println s!"Ledger entries actually matched by a live call site this run: {ledgerHits.size} / {ledgerEntries.length}"
  let stale := ledgerEntries.filter (fun e =>
    !ledgerHits.contains (matchKey (moduleNameOfPath e.file) (nameOfDotted e.fqn)))
  if !stale.isEmpty then
    IO.println s!"Ledger entries with NO matching live call site this run (candidates for removal, not a failure): {stale.length}"
    for e in stale do
      IO.println s!"  scripts/mem_bypass_allowlist.txt:{e.lineNum}: {e.file}::{e.rawName}"

  IO.println sepLine
  if violations.isEmpty then
    IO.println "PASS: every raw memory-operand smart-constructor reference outside designated \
      infrastructure is covered by a ledger entry."
    IO.println sepLine
    return 0
  else
    IO.println s!"FAIL: {violations.length} raw memory-operand reference(s) outside the ledger \
      and outside designated infrastructure:"
    for (declName, modName, raw) in violations do
      IO.println s!"  {modName} :: {declName} references raw constructor '{raw}' \
        with no scripts/mem_bypass_allowlist.txt entry"
    IO.println sepLine
    IO.println "Fix: route this call through Gasm.Targets.X86_64.CheckedAsm's capability-proved \
      wrappers, or add a justified scripts/mem_bypass_allowlist.txt entry if this module is \
      genuinely still on the pre-MH3 raw-authoring path (review policy per Law 11: new entries \
      are rejected -- prefer migrating)."
    return 1
