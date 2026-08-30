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
Tools/CheckRefsCoverage.lean - Law 1 / Law 3 declaration-coverage gate verifier

WHY THIS TOOL EXISTS. scripts/check_refs.py used to detect "un-REF'd Lean
declarations" (Law 1) with a single regex, `LEAN_DECL_REGEX`, matched against
raw source text. That regex REQUIRES an identifier immediately after the
declaration keyword, so it is structurally blind to `instance : Foo X where`
(no name token at all), and it never listed `abbrev`/`initialize` among its
keywords in the first place. Two consequences, both worse than a missed
warning: (1) a `REF:` comment sitting directly above one of these invisible
declarations was silently DROPPED from citation validation entirely (never
checked against anything), and (2) the declaration itself evaded the
un-cited-declaration check. At least 22 Intel `#operation` citations on
anonymous `instance` declarations, plus Wasm declarations, were affected.
This is a vacuous-gate defect: the gate reported green over text it never
actually examined.

THE FIX. Citation *validity* (does a `REF:` target resolve to a real
section) needs no Lean parsing whatsoever and is handled by
scripts/check_refs.py via a straight regex scan for `REF:` lines, decoupled
from any notion of "the following declaration" -- see that script's own
module docstring. THIS tool is the other half: declaration *coverage* (does
every declaration have at least one preceding `REF:`), driven entirely by
Lean's own COMPILED ENVIRONMENT rather than source-text pattern matching.
The environment records what actually exists after elaboration, so no
syntactic declaration FORM -- `abbrev`, anonymous `instance ... where`,
`initialize ... ←`, or any future keyword -- can hide from it the way one
could hide from a regex.

ARCHITECTURE (mirrors Tools/CheckGatesAxioms.lean's Law 10 tool almost
exactly -- see that file's header for the fuller rationale of each piece
reused here): `discoverProjectModules` enumerates every TRACKED `.lean` file
under `Gasm/`, `Stdlib/`, `Spikes/` via `git ls-files` (not via any import
closure, and not via a filesystem walk -- see `enumerateProjectModules` in
Tools/GateSubprocess.lean); `runGate`
does the baseline `importModules #[Gasm, Stdlib, Spikes]` scan, then
per-module standalone scans for whatever the baseline's closure did not
reach, exactly as CheckGatesAxioms.lean does for Law 10 (same TC15 module-
coverage gap, same fix). `Tools/` itself is excluded from scope, matching
`isProjectModule`'s existing Gasm/Stdlib/Spikes-only namespace scope -- this file's own
declarations are therefore not gated by itself, though they still carry
`REF:` citations as a matter of ordinary code quality.

SUBPROCESS ISOLATION (identical fix to Tools/CheckGatesAxioms.lean's, see
that file's header for the fuller rationale of why a fresh OS PROCESS per
module -- not just a fresh `Environment` value in this same long-lived
process -- is required): this tool originally scanned each of the ~33
disk-discovered-but-not-baseline modules with a per-module standalone
`importModules` call INSIDE ITS OWN LOOP, all in this one process. That is
exactly the pattern that drove Tools/CheckGatesAxioms.lean's memory to
~49GB and broke CI on both platforms before ITS fix; a contamination-checked
measurement of this tool's own pre-fix binary (`Get-CimInstance` filtered to
this process's own tree) confirmed the identical failure mode here too: a
single process climbing to ~41GB working set over the run. The fix is the
same shape: `runGate` now re-invokes this same executable as
`--scan-module <dotted module name> <file path>` (`runScanWorker` below),
one module at a time, sequentially, in its own fresh process -- never
batched (batching would reintroduce the bare-`main` collision the isolation
exists to dodge in the first place, per CheckGatesAxioms.lean's header). The
spawn-and-capture-one-`GASM_SCAN_RESULT`-line plumbing itself
(`spawnAndGetResultPayload`, `resultMarker`, `setupSearchPath`,
`nameOfDotted`) is shared verbatim with Tools/CheckGatesAxioms.lean via
Tools/GateSubprocess.lean -- it was byte-for-byte duplicated code before
that file existed, exactly the kind of defect this project's Law 12 is
about. The worker's JSON PAYLOAD SHAPE is NOT shared, though: Law 10's
worker reports axiom-gating info per offending declaration, this tool's
worker instead reports the full `DeclCandidate` shape (fqn, anchor line,
range) each in-scope declaration needs for the containment filter and
`REF:` text-scan that happen back in the parent -- a different question
with a different payload, so sharing the schema would only force one tool's
shape onto the other. `runScanWorker` always exits 0 and reports success or
failure of ITS import via the `GASM_SCAN_RESULT <json>` line (`{"ok":true,
"candidates":[...]}` or `{"ok":false,"error":"..."}`), letting the parent
tell "this module's `.olean` genuinely failed to import" (a real,
reportable finding, folded into `unloadable`) apart from "this OS process
itself crashed, was killed, or emitted nothing parseable" (also folded into
`unloadable`, since both are exactly the blind spot this gate refuses to
hide). The worker carries no allowlist knowledge; the parent alone does
`byKey` matching against whatever candidates come back, exactly as before.

THE HARD PART: BRIDGING NAME TO SOURCE POSITION. The environment gives
declaration NAMES, not source positions; a `REF:` comment is a source-level
concept (physically precedes a declaration in a `.lean` file). Lean's own
`Lean.findDeclarationRanges?` closes this gap -- confirmed empirically
against this exact toolchain (v4.33.1) via a throwaway probe importing a
real project module through plain `importModules` (no `module`/`prelude`
opt-in, no special `OLeanLevel`, no `.olean.server` artifact): every
directly-authored declaration in a plain, non-"module"-system project file
(which is every `.lean` file in this repository) carries a real
`DeclarationRanges` entry, recoverable from an ordinary environment exactly
as this tool builds one. Concretely, for `instance : X86_64Instruction
AddR64R64 where` (an anonymous instance -- the exact case this task exists
to fix): `range.pos.line` lands on the `instance` keyword's own line,
matching the source file exactly. For a `structure Foo where` preceded by a
`/-- doc -/` comment: `range.pos.line` lands on the DOC COMMENT's own start
line (Lean's parser attaches contiguous leading trivia -- including any
further `/- REF: ... -/` comments sitting between the doc comment and the
keyword -- as part of the declaration's own range), while
`selectionRange.pos.line` always lands on the line carrying the declaration
keyword/name itself, regardless of what leading trivia is or is not
attached. This tool uses `selectionRange.pos.line` as the anchor to scan
upward from (see `scanFileForCitedLines` below) -- sound because it is
always the keyword line, and because the upward scan itself (not Lean's
range attachment) is what decides how far back a `REF:` comment run
extends, exactly mirroring scripts/check_refs.py's original block-comment-
aware forward scan, just triggered by a real declaration position instead
of a regex match.

FILTERING OUT COMPILER-SYNTHESIZED DECLARATIONS. Enumerating the raw
environment surfaces far more than what a human wrote: structure field
projections, `rec`/`recOn`/`casesOn`/`noConfusion`, `deriving`-clause
instances, `mk.inj`/`mk.injEq`/`sizeOf_spec`/`match_N` equational
byproducts. None of these are independently "invented" content Law 1 could
sensibly demand a citation for -- they are mechanical consequences of one
human-authored declaration (the `structure`/`inductive`/`deriving` clause
that produced them), and treating each as its own citable unit would make
this gate spuriously noisy on every `deriving DecidableEq, Repr, Inhabited`
in the codebase. Every exclusion below is a real Lean API, not a name-shape
guess:
- `env.isProjectionFn name` -- structure/class field projections.
- `Lean.isAuxRecursor env name` -- `recOn`/`casesOn`/`brecOn`/`binductionOn`.
- `Lean.isNoConfusion env name` -- `noConfusion`/`noConfusionType`.
- `ConstantInfo` KIND exclusion -- `.ctorInfo`/`.recInfo`/`.quotInfo` are
  never producible by hand-written syntax, so they are never in the
  reportable-kind set to begin with (mirrors CheckGatesAxioms.lean's
  `isReportableKind`, extended here to ALSO include `.inductInfo`, since
  Law 1 -- unlike Law 10's axiom analysis -- genuinely does apply to
  `inductive`/`structure`/`class` declarations themselves).
- NO declaration range at all (`findDeclarationRanges? = none`) -- this
  covers most of the remaining equational/injectivity/`match_N` byproducts
  empirically (confirmed via the same probe): Lean's own structure/
  inductive/deriving elaborators simply never call `addDeclarationRanges`
  for these, which is itself a real, environment-native signal that no
  human placed them at an addressable source position, so Law 1 cannot
  apply to them.
- RANGE CONTAINMENT -- the one case the above four do not catch:
  `deriving`-clause-generated instances (e.g. `instDecidableEqFoo`) DO get
  a real range (confirmed empirically: it lands on the `deriving X, Y, Z`
  clause's own line), but that range is always properly nested INSIDE the
  structure's own declaration range (confirmed: `AddR64R64`'s range spans
  its doc comment through its `deriving` line; `instDecidableEqAddR64R64`'s
  range is a strict sub-span of that). A candidate declaration whose range
  is wholly contained within a different candidate's range in the same
  module is excluded -- it is a byproduct of the enclosing declaration, not
  an independent citable unit. This also transparently subsumes field
  projections and `recOn`/`casesOn` as a second layer of defense, and
  correctly does NOT exclude `mutual`-block siblings (each gets its own,
  non-overlapping range -- confirmed against Gasm/Targets/Wasm/Semantics.lean,
  where `evalInstr`/`evalInstrs`/`evalLoop` are sequential siblings, not
  nested, and this project's convention gives each its own `REF:` comment).
  Equal-range ties (should the first four filters ever miss one) are
  resolved deterministically by keeping the lexicographically-smaller name,
  so a genuine tie can never cause BOTH members to vanish.
-/
import Lean
import Lean.Data.Json
import Gasm
import Stdlib
import Spikes
import Tools.GateSubprocess

open Lean

/-- Reportable declaration kinds for Law 1 coverage: everything a human can
actually write at the top level and that Law 1's own text names --
`inductive`, `structure`, `class` (all `.inductInfo`), `def`/`abbrev`
(`.defnInfo`), `opaque` (`.opaqueInfo`), `axiom` (`.axiomInfo`),
`theorem`/`lemma` (`.thmInfo`). Deliberately WIDER than
CheckGatesAxioms.lean's `isReportableKind` (which excludes `.inductInfo`
since inductives cannot carry axiom dependencies) -- Law 1's coverage
question is a different question from Law 10's. `.ctorInfo`/`.recInfo`/
`.quotInfo` are never producible by hand-written declaration syntax and are
excluded by omission, not by an extra check. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def isCoverageReportableKind : ConstantInfo → Bool
  | .thmInfo _ | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ | .inductInfo _ => true
  | _ => false

/-- Is `name`'s ORIGINATING MODULE (not its own namespace-shaped name) one
of the project's? Identical in spirit to CheckGatesAxioms.lean's
`isProjectModule` (same rationale: scopes to "compiled from a project
module," immune to a foreign-namespace evasion a name-prefix check would
miss). -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def isProjectModule (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some idx =>
    match env.allImportedModuleNames[idx.toNat]? with
    | none => false
    | some modName =>
      (`Gasm).isPrefixOf modName || (`Stdlib).isPrefixOf modName || (`Spikes).isPrefixOf modName

/-- The four sound, Lean-API-backed exclusions for compiler-synthesized
declarations that are not independently citable (see module header). Range
containment is applied separately, after all candidates for a module are
collected (it needs the whole candidate set, not just one declaration). -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def isCoverageCandidate (env : Environment) (name : Name) (info : ConstantInfo) : Bool :=
  isProjectModule env name && isCoverageReportableKind info && !name.isInternal
    && !env.isProjectionFn name && !isAuxRecursor env name && !isNoConfusion env name

/-- Is `name`'s originating module EXACTLY `target`? Mirrors
CheckGatesAxioms.lean's `isExactlyModule` (same rationale: a standalone
single-module environment's transitive closure includes every dependency of
`target` too, already counted elsewhere; restricting to exact module
identity keeps each declaration reported exactly once). -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def isExactlyModule (env : Environment) (name : Name) (target : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some idx => env.allImportedModuleNames[idx.toNat]? == some target

/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def isCoverageCandidateForModule (env : Environment) (name : Name) (info : ConstantInfo) (target : Name) : Bool :=
  isExactlyModule env name target && isCoverageReportableKind info && !name.isInternal
    && !env.isProjectionFn name && !isAuxRecursor env name && !isNoConfusion env name

/-- `name`'s originating module. `none` only for a name outside any imported
module (never called on a name that already passed `isCoverageCandidate`/
`isCoverageCandidateForModule`, both of which imply `some`). -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def originatingModule (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | none => none
  | some idx => env.allImportedModuleNames[idx.toNat]?

/-- The project's own top-level source roots. `Tools/` is deliberately
excluded, matching CheckGatesAxioms.lean's identical choice. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def projectRootDirs : List String := ["Gasm", "Stdlib", "Spikes"]

/-- Turns a project-relative `.lean` file path into the dotted module `Name`
Lean's own import resolution would assign it. Mirrors
CheckGatesAxioms.lean's `moduleNameOfPath` exactly. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def moduleNameOfPath (p : System.FilePath) : Name :=
  (p.withExtension "").components.foldl Name.mkStr Name.anonymous

/-- Enumerates every project module from the TRACKED TREE (`git ls-files`),
paired with its file path (so the text-scanning phase below never has to
reconstruct a path from a `Name` -- it reuses the exact `System.FilePath` the
enumeration already produced). Mirrors CheckGatesAxioms.lean's
`discoverProjectModules`, independent of any import closure for the same
reason: it is the ground truth the compiled environment(s) are cross-checked
against.

Restricted to modules some `lakefile.toml` target actually builds -- every
`[[lean_lib]] roots` and every `[[lean_exe]] root`, not the three umbrella libs
this tool used to assume were the whole build.

This used to be a `System.FilePath.walkDir` recursion over every project file
that exists, and this gate went red from the same single uncommitted file that
reddened `lake exe check_gates_axioms` on 2026-08-28, and from the same single
unbuilt orphan -- the identical two defects, in the identical place. See
`enumerateProjectModules` (Tools/GateSubprocess.lean) for the full argument
and for why neither fix weakens the module-coverage check below. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def discoverProjectModules : IO ProjectModuleEnumeration :=
  enumerateProjectModules projectRootDirs

/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def sepLine : String :=
  "======================================================================"

/-- One candidate declaration collected from an environment, carrying
everything the containment filter and the text-scanning phase need. `fqn` is
a plain `String` (`toString` of the real `Name`, taken once at collection
time), not a `Name` -- a standalone-module candidate crosses a worker
subprocess boundary as JSON (see SUBPROCESS ISOLATION in this file's header)
and only ever HAS a string on the far side; every existing use of `fqn`
below (key-matching, tie-breaking, reporting) already went through
`toString` anyway, so this is a representation change with no behavioral
difference for baseline-collected candidates. Mirrors
Tools/CheckGatesAxioms.lean's `Offender.declName`, same rationale. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
structure DeclCandidate where
  fqn         : String
  module      : Name
  file        : System.FilePath
  /-- `selectionRange.pos.line`, 1-indexed -- always the declaration
  keyword/name's own line, the anchor the upward text scan starts from. -/
  anchorLine  : Nat
  /-- `range.pos` / `range.endPos`, used only for the containment check. -/
  rangeStart  : Position
  rangeEnd    : Position
deriving Inhabited

/-- `a` is lexicographically no later than `b` (line, then column). -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def posLE (a b : Position) : Bool :=
  a.line < b.line || (a.line == b.line && a.column <= b.column)

/-- Is `d`'s range wholly contained in `other`'s range? Equal ranges are
resolved by keeping the lexicographically-smaller name as the survivor (see
module header's "Equal-range ties" note) so a genuine tie never excludes
both members. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def containedIn (d other : DeclCandidate) : Bool :=
  d.fqn != other.fqn &&
    posLE other.rangeStart d.rangeStart && posLE d.rangeEnd other.rangeEnd &&
    (other.rangeStart != d.rangeStart || other.rangeEnd != d.rangeEnd ||
      other.fqn < d.fqn)

/-- Drops every candidate that is contained in some other candidate FROM THE
SAME MODULE (containment across different files is never meaningful).
O(n^2) per module; project modules have at most a few hundred declarations
each, so this is fast in practice. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def dropContained (candidates : Array DeclCandidate) : Array DeclCandidate := Id.run do
  let mut out : Array DeclCandidate := #[]
  for d in candidates do
    let isContained := candidates.any (fun other => d.module == other.module && containedIn d other)
    if !isContained then
      out := out.push d
  return out

/-- Collects every reportable, non-synthesized declaration from `env`,
restricted to declarations whose module passes `inScope`. Shared between the
baseline scan and every standalone per-module scan below. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def collectCandidates (env : Environment) (ctx : Core.Context)
    (inScope : Name → ConstantInfo → Bool) (fileOfModule : Name → Option System.FilePath) :
    IO (Array DeclCandidate) := do
  let coreState : Core.State := { env := env }
  let mut out : Array DeclCandidate := #[]
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    match fileOfModule modName with
    | none => pure ()
    | some file =>
      if let some md := env.header.moduleData[i]? then
        for name in md.constNames do
          if let some info := env.find? name then
            if inScope name info then
              let (ranges?, _) ← (Lean.findDeclarationRanges? (m := CoreM) name).toIO ctx coreState
              match ranges? with
              | none => pure ()  -- no addressable source position: not independently citable (see header)
              | some r =>
                out := out.push {
                  fqn := toString name, module := modName, file := file,
                  anchorLine := r.selectionRange.pos.line,
                  rangeStart := r.range.pos, rangeEnd := r.range.endPos
                }
  return out

/-- Does a (trimmed) source line look like a `REF:` citation comment? Looser
than scripts/check_refs.py's `REF_REGEX` deliberately: this tool only needs
"was a citation attempted here" (Law 1 coverage), not "is it valid" (Law 3
validity, which scripts/check_refs.py alone owns via the strict regex). A
line that starts this way but is malformed is correctly invisible to BOTH
mechanisms' strict checks and correctly still counts as "an attempt exists"
here -- validity is not this tool's job. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def looksLikeRefLine (line : String) : Bool :=
  line.trimAscii.toString.startsWith "/- REF:"

/-- Scans `filePath` once and returns the subset of `declLines` that are
"cited": preceded, with only blank lines and comment lines in between, by at
least one `REF:` line. This is the same forward, block-comment-aware scan
scripts/check_refs.py's `collect_lean_citations` implements, just triggered
by real declaration positions (`declLines`, from the compiled environment)
instead of a declaration-shaped regex -- which is the entire point: no
syntactic declaration form can make a line invisible to this scan, because
membership in `declLines` never came from pattern-matching source text. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def scanFileForCitedLines (filePath : System.FilePath) (declLines : Std.HashSet Nat) :
    IO (Std.HashSet Nat) := do
  let content ← IO.FS.readFile filePath
  let rawLines := (content.replace "\r\n" "\n").splitOn "\n"
  let mut inBlockComment := false
  let mut pendingHasRef := false
  let mut cited : Std.HashSet Nat := {}
  let mut lineNum := 0
  for rawLine in rawLines do
    lineNum := lineNum + 1
    let line := rawLine.trimAscii.toString
    let wasInComment := inBlockComment
    if !inBlockComment then
      if (line.splitOn "/-").length > 1 then
        inBlockComment := true
        -- A `-/` on the same line that closes what `/-` just opened (only
        -- possible for a self-contained one-liner, e.g. `/- REF: ... -/`).
        if (line.splitOn "-/").length > 1 then
          inBlockComment := false
    else
      if (line.splitOn "-/").length > 1 then
        inBlockComment := false

    if looksLikeRefLine line then
      pendingHasRef := true
      continue

    if declLines.contains lineNum then
      if pendingHasRef then
        cited := cited.insert lineNum
      pendingHasRef := false
    else if !line.isEmpty && !inBlockComment && !wasInComment
        && !line.startsWith "--" && !line.startsWith "/-" then
      -- A genuine code line with no citation pending above it: whatever was
      -- pending does not belong to whatever declaration comes next.
      pendingHasRef := false
  return cited

/-- One parsed, VALID line of scripts/ref_allowlist.txt -- same 5-field
`::`-delimited shape as scripts/gate_allowlist.txt and
scripts/license_allowlist.txt (see either for the established convention
this mirrors). -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
structure RefAllowlistEntry where
  file           : String
  declName       : String
  fqn            : String
  category       : String
  justification  : String
  lineNum        : Nat
deriving Inhabited

/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def validRefCategories : List String := ["derived-scaffolding", "internal-helper", "grandfathered"]

/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def splitOnMax (s : String) (sep : String) (maxParts : Nat) : List String :=
  let parts := s.splitOn sep
  if parts.length ≤ maxParts then
    parts
  else
    let head := parts.take (maxParts - 1)
    let tail := parts.drop (maxParts - 1)
    head ++ [String.intercalate sep tail]

/-- Parses scripts/ref_allowlist.txt. A malformed line is a HARD parse
failure, same discipline as every other allowlist in this repository. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def parseRefAllowlist (contents : String) : List RefAllowlistEntry × List String := Id.run do
  let mut entries : List RefAllowlistEntry := []
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
        [s!"ref_allowlist.txt:{lineNum}: expected 5 '::'-delimited fields (file::decl::fqn::category::justification), got {parts.length}: {rawLine}"]
      continue
    let file := parts[0]!.trimAscii.toString
    let declName := parts[1]!.trimAscii.toString
    let fqn := parts[2]!.trimAscii.toString
    let category := parts[3]!.trimAscii.toString.toLower
    let justification := parts[4]!.trimAscii.toString
    if !validRefCategories.contains category then
      errors := errors ++
        [s!"ref_allowlist.txt:{lineNum}: unknown category '{parts[3]!.trimAscii.toString}' (expected one of {validRefCategories})"]
      continue
    if fqn.isEmpty then
      errors := errors ++ [s!"ref_allowlist.txt:{lineNum}: missing fully-qualified name (3rd field)"]
      continue
    if justification.isEmpty then
      errors := errors ++ [s!"ref_allowlist.txt:{lineNum}: missing justification"]
      continue
    entries := entries ++ [(⟨file, declName, fqn, category, justification, lineNum⟩ : RefAllowlistEntry)]
  return (entries, errors)

/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def matchKey (moduleName : Name) (fqn : String) : String := s!"{moduleName}::{fqn}"

/-- What a `--scan-module` worker process reported, once its one
`GASM_SCAN_RESULT` JSON line has been parsed. `loadFailed` mirrors the old
in-process `catch` arm (the module's own `importModules` failed); the parent
folds it into `unloadable` exactly as before. `scanned` carries every
candidate the worker collected for its one target module -- `fqn`,
`anchorLine`, and both range endpoints, everything `dropContained` and the
text-scan phase need; `module` and `file` are NOT part of the payload since
the parent already knows both (it is the parent that chose which module to
scan and looked up its file via `discoverProjectModules`). -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
inductive RefsWorkerResult where
  | loadFailed (msg : String)
  | scanned (candidates : Array (String × Nat × Position × Position))

/-- Parses one worker's `GASM_SCAN_RESULT` JSON payload (everything after the
marker). See `runScanWorker` for the shape this is the inverse of. `Position`
already derives `FromJson`/`ToJson` (Lean.Data.Position), so each range
endpoint round-trips through the standard `{"line":_,"column":_}` shape
without any hand-rolled (de)serialization. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def parseRefsWorkerResult (payload : String) : Except String RefsWorkerResult := do
  let j ← Json.parse payload
  let okJ ← j.getObjVal? "ok"
  let ok ← okJ.getBool?
  if !ok then
    let errJ ← j.getObjVal? "error"
    let errS ← errJ.getStr?
    return .loadFailed errS
  else
    let candsJ ← j.getObjVal? "candidates"
    let candsArr ← candsJ.getArr?
    let cands ← candsArr.mapM fun item => do
      let fqnJ ← item.getObjVal? "fqn"
      let fqnS ← fqnJ.getStr?
      let lineJ ← item.getObjVal? "anchorLine"
      let lineN ← lineJ.getNat?
      let rangeStartJ ← item.getObjVal? "rangeStart"
      let rangeStart ← FromJson.fromJson? (α := Position) rangeStartJ
      let rangeEndJ ← item.getObjVal? "rangeEnd"
      let rangeEnd ← FromJson.fromJson? (α := Position) rangeEndJ
      pure (fqnS, lineN, rangeStart, rangeEnd)
    return .scanned cands

/-- The `--scan-module <dotted name> <file path>` worker entry point:
standalone-imports EXACTLY ONE module into a fresh `Environment` -- in this
fresh OS PROCESS, never the parent's -- collects the same `DeclCandidate`
info the baseline scan collects (mirroring the old in-process standalone
loop this replaces), and prints exactly one `GASM_SCAN_RESULT <json>` line
to stdout. `file` is passed in by the parent (it already resolved `target`'s
on-disk path via `discoverProjectModules`) rather than rediscovered here, so
the worker never needs its own disk walk. Always exits `0`: whether the
IMPORT itself succeeded or failed is reported IN the JSON (`ok` field), not
via process exit code -- see this file's header (SUBPROCESS ISOLATION) for
why that split matters. Carries no allowlist knowledge; the parent alone
does `byKey` matching. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def runScanWorker (target : Name) (file : System.FilePath) : IO UInt32 := do
  setupSearchPath
  let ctx : Core.Context := { fileName := "CheckRefsCoverage", fileMap := default }
  let result ←
    try
      let env2 ← importModules #[{module := target}] {} (trustLevel := 0) (loadExts := false)
      let cands ← collectCandidates env2 ctx
        (fun n i => isCoverageCandidateForModule env2 n i target) (fun _ => some file)
      let candsJson := cands.map (fun d => Json.mkObj [
        ("fqn", (d.fqn : Json)),
        ("anchorLine", (d.anchorLine : Json)),
        ("rangeStart", Lean.toJson d.rangeStart),
        ("rangeEnd", Lean.toJson d.rangeEnd)
      ])
      pure (Json.mkObj [("ok", (true : Json)), ("candidates", Json.arr candsJson)])
    catch e =>
      pure (Json.mkObj [("ok", (false : Json)), ("error", (e.toString : Json))])
  IO.println s!"{resultMarker}{result.compress}"
  return 0

/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def runGate : IO UInt32 := do
  let startTime ← IO.monoMsNow

  setupSearchPath

  let allowlistPath : System.FilePath := "scripts" / "ref_allowlist.txt"
  if !(← allowlistPath.pathExists) then
    IO.eprintln s!"[!] ERROR: {allowlistPath} not found relative to the current directory."
    IO.eprintln "    Run the canonical full gate from the repo root: `python scripts/run_full_refs_coverage.py --full-repository`"
    return 1
  let allowlistText ← IO.FS.readFile allowlistPath
  let (allowlist, parseErrors) := parseRefAllowlist allowlistText

  IO.println sepLine
  IO.println " gasm Law 1 / Law 3 DECLARATION-COVERAGE Gate Verifier (Tools/CheckRefsCoverage.lean)"
  IO.println sepLine
  IO.println "[*] Enumerates every reportable project declaration from the COMPILED ENVIRONMENT"
  IO.println "    (not source-text pattern matching), then checks each for a preceding `REF:`."

  if !parseErrors.isEmpty then
    IO.println ""
    IO.println s!"[!] FAILED: {parseErrors.length} malformed allowlist line(s):"
    for e in parseErrors do
      IO.println s!"    - {e}"
    IO.println sepLine
    return 1

  IO.println s!"[*] Loaded {allowlist.length} valid allowlist entr(y/ies) from {allowlistPath}."

  let env ←
    try
      importModules #[{module := `Gasm}, {module := `Stdlib}, {module := `Spikes}]
        {} (trustLevel := 0) (loadExts := false)
    catch e =>
      IO.eprintln s!"[!] ERROR: failed to import Gasm/Stdlib/Spikes: {e.toString}"
      IO.eprintln "    Run the canonical full gate from the repo root: `python scripts/run_full_refs_coverage.py --full-repository`"
      IO.Process.exit 1

  let ctx : Core.Context := { fileName := "CheckRefsCoverage", fileMap := default }

  let enumeration ← discoverProjectModules
  let discovered := enumeration.files.map (fun p => (moduleNameOfPath p, p))
  let fileOfModule : Std.HashMap Name System.FilePath :=
    discovered.foldl (init := {}) (fun m (n, p) => m.insert n p)

  let mut candidates ←
    collectCandidates env ctx (fun n i => isCoverageCandidate env n i) (fileOfModule[·]?)

  -- TC15-style module-coverage closure: the baseline import above only sees
  -- whatever Gasm/Stdlib/Spikes transitively `import`. Anything discovered
  -- on disk but not reached that way is loaded standalone, mirroring
  -- Tools/CheckGatesAxioms.lean's identical fix for the identical gap.
  let mut baselineModules : Std.HashSet Name := {}
  for m in env.allImportedModuleNames do
    baselineModules := baselineModules.insert m
  let missing := discovered.filter (fun (m, _) => !baselineModules.contains m)

  -- SUBPROCESS ISOLATION (see this file's header): each `missing` module is
  -- scanned by re-invoking THIS SAME executable as a `--scan-module` worker
  -- in its own fresh OS process, one module at a time, sequentially -- never
  -- batched, never in parallel. Same rationale as
  -- Tools/CheckGatesAxioms.lean: batching would reintroduce the bare-`main`
  -- collision this whole scheme exists to avoid, and running them in-process
  -- (even one `Environment` value at a time, which is what this loop did
  -- before this fix) is exactly what drove this tool's own peak working set
  -- to ~41GB on a clean, contamination-checked measurement.
  let mut unloadable : Array (Name × String) := #[]
  let selfExe ← IO.appPath
  let cwd ← IO.currentDir
  let concurrency ← defaultScanConcurrency
  let workerResults ← runWorkerPool missing concurrency fun (target, targetFile) => do
    let payloadRes ← spawnAndGetResultPayload selfExe cwd #["--scan-module", toString target, targetFile.toString]
    pure (target, targetFile, payloadRes)

  for (target, targetFile, payloadRes) in workerResults do
    match payloadRes with
    | .error spawnErr =>
      unloadable := unloadable.push (target, spawnErr)
    | .ok payload =>
      match parseRefsWorkerResult payload with
      | .error parseErr =>
        unloadable := unloadable.push (target, s!"malformed scan subprocess result: {parseErr}")
      | .ok (.loadFailed loadErr) =>
        unloadable := unloadable.push (target, loadErr)
      | .ok (.scanned cands) =>
        for (fqnS, anchorLine, rangeStart, rangeEnd) in cands do
          candidates := candidates.push {
            fqn := fqnS, module := target, file := targetFile,
            anchorLine := anchorLine, rangeStart := rangeStart, rangeEnd := rangeEnd
          }

  let elapsedImportMs := (← IO.monoMsNow) - startTime

  -- Containment filter is applied per-module across the FULL candidate set
  -- (baseline + every standalone import), so it sees the same picture
  -- regardless of which import produced which candidate.
  let topLevel := dropContained candidates

  -- Group top-level candidates by file so each file is read and scanned
  -- exactly once, regardless of how many declarations it contributes.
  let mut byFile : Std.HashMap System.FilePath (Array DeclCandidate) := {}
  for d in topLevel do
    byFile := byFile.insert d.file ((byFile.getD d.file #[]).push d)

  let mut byKey : Std.HashMap String RefAllowlistEntry := {}
  for e in allowlist do
    let entryModule := moduleNameOfPath (System.FilePath.mk e.file)
    byKey := byKey.insert (matchKey entryModule e.fqn) e

  let mut scanned := 0
  let mut uncited : Array DeclCandidate := #[]
  let mut allowlisted := 0
  let mut matchedKeys : Std.HashSet String := {}

  for (file, decls) in byFile.toList do
    let declLines : Std.HashSet Nat := decls.foldl (init := {}) (fun s d => s.insert d.anchorLine)
    let cited ← scanFileForCitedLines file declLines
    for d in decls do
      scanned := scanned + 1
      if !cited.contains d.anchorLine then
        let key := matchKey d.module d.fqn
        match byKey[key]? with
        | some _ => allowlisted := allowlisted + 1; matchedKeys := matchedKeys.insert key
        | none => uncited := uncited.push d

  let staleEntries := allowlist.filter (fun e =>
    !matchedKeys.contains (matchKey (moduleNameOfPath (System.FilePath.mk e.file)) e.fqn))

  let elapsedMs := (← IO.monoMsNow) - startTime
  let baselineProjectCount := (discovered.filter (fun (m, _) => baselineModules.contains m)).size
  let coveredStandalone := missing.size - unloadable.size

  IO.println ""
  IO.println "--- MODULE COVERAGE (TC15-style closure, mirrors CheckGatesAxioms.lean) ---"
  IO.println s!"[*] {discovered.size} tracked project module(s) under {projectRootDirs} are built by a"
  IO.println s!"    declared lakefile.toml target ({enumeration.libRoots} [[lean_lib]] root(s), \
{enumeration.exeRoots} [[lean_exe]] root(s))."
  IO.println s!"[*] {baselineProjectCount} reachable via the baseline Gasm/Stdlib/Spikes import graph;"
  IO.println s!"    {coveredStandalone} more loaded standalone to close the blind spot."
  IO.println s!"[*] Total in scope: {baselineProjectCount + coveredStandalone} / {discovered.size} in the build closure."
  IO.println s!"[*] Import phase: {elapsedImportMs}ms."
  -- See CheckGatesAxioms.lean's identical block: a tracked module no declared
  -- target reaches is never compiled, so no `.olean` exists for this tool to
  -- scan and a bare exit 1 here would name no cause. `check_orphan_modules.py`
  -- owns that defect class and names the exact fix.
  if !enumeration.unbuilt.isEmpty then
    IO.println ""
    IO.println s!"[*] {enumeration.unbuilt.size} tracked project module(s) are reached by NO declared"
    IO.println "    lakefile.toml root, so nothing compiles them and this gate cannot scan them:"
    for p in enumeration.unbuilt do
      IO.println s!"    - {p}"
    IO.println "    Not a failure here -- `python scripts/check_orphan_modules.py` owns this class."

  IO.println ""
  IO.println "--- SCAN RESULT ---"
  IO.println s!"[*] {candidates.size} candidate declaration(s) before containment filtering;"
  IO.println s!"    {topLevel.size} genuinely top-level (compiler-synthesized companions excluded --"
  IO.println "    see this file's own header for the containment/API-based exclusion rationale)."
  IO.println s!"[*] Scanned {scanned} top-level declaration(s); {allowlisted} uncited-but-allowlisted,"
  IO.println s!"    {uncited.size} uncited with no matching entry."

  let mut failed := false

  -- lakefile.toml and the tracked tree disagreeing about what exists would
  -- silently shrink the build closure and narrow this gate's scope -- a hard
  -- failure, same discipline as CheckGatesAxioms.lean's identical block.
  if !enumeration.errors.isEmpty then
    failed := true
    IO.println ""
    IO.println s!"[!] FAILED: {enumeration.errors.size} lakefile.toml build-root error(s) -- the"
    IO.println "    declared targets and the tracked tree disagree about what exists:"
    for e in enumeration.errors do
      IO.println s!"    - {e}"

  if !unloadable.isEmpty then
    failed := true
    IO.println ""
    IO.println s!"[!] FAILED: {unloadable.size} module(s) found on disk but could not be loaded"
    IO.println "    into any Environment -- build the project (`lake build`) first:"
    for (m, err) in unloadable do
      IO.println s!"    - {m}: {err}"

  if uncited.size > 0 then
    failed := true
    IO.println ""
    IO.println s!"[!] FAILED: {uncited.size} declaration(s) have no preceding `REF:` citation"
    IO.println "    (Law 1 violation: Invention) and no matching scripts/ref_allowlist.txt entry:"
    for d in uncited.toList do
      IO.println s!"    - {d.file}:{d.anchorLine}: {d.module}::{d.fqn}"

  if !staleEntries.isEmpty then
    failed := true
    IO.println ""
    IO.println s!"[!] FAILED: {staleEntries.length} scripts/ref_allowlist.txt entr(y/ies) matched no"
    IO.println "    uncited declaration in this scan (stale; prune or fix the fqn):"
    for e in staleEntries do
      IO.println s!"    - ref_allowlist.txt:{e.lineNum} {e.file}::{e.declName}::{e.fqn}"

  if !failed then
    IO.println "[+] Every reportable declaration in scope carries a `REF:` citation (directly, or"
    IO.println "    via an honest scripts/ref_allowlist.txt entry), and every allowlist entry"
    IO.println "    matched a real finding."

  IO.println ""
  IO.println s!"[*] Wall time: {elapsedMs}ms."
  IO.println sepLine
  return if failed then 1 else 0

/-- CLI entry point. `--scan-module <dotted name> <file path>` is an
internal, undocumented mode: it is how `runGate` re-invokes THIS SAME
executable as a standalone-scan worker subprocess (see this file's header's
SUBPROCESS ISOLATION section) and is never meant to be typed by a human.
Any other argument list (including none) runs the gate itself, exactly as
before this fix. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def main (args : List String) : IO UInt32 :=
  match args with
  | ["--scan-module", modStr, fileStr] => runScanWorker (nameOfDotted modStr) (System.FilePath.mk fileStr)
  | _ => runGate
