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
Tools/GateSubprocess.lean); `runGate` invokes three sequential, short-lived
umbrella workers for `Gasm`, `Stdlib`, and `Spikes`, then per-module
standalone workers for whatever those import closures did not reach (the
same TC15 module-coverage gap and fix as CheckGatesAxioms.lean). The driver
statically imports none of those roots, so building the gate does not build
or elaborate their combined closure. `Tools/` itself is excluded from scope, matching
`isProjectModule`'s existing Gasm/Stdlib/Spikes-only namespace scope -- this file's own
declarations are therefore not gated by itself, though they still carry
`REF:` citations as a matter of ordinary code quality.

SUBPROCESS ISOLATION (same underlying fix as Tools/CheckGatesAxioms.lean's):
the driver never owns a repository `Environment`. Each umbrella is imported
by a sequential `--scan-root` worker that exits before the next starts, and
each module outside those closures uses a `--scan-module` worker. This tool
originally scanned each of the ~33
disk-discovered-but-not-baseline modules with a per-module standalone
`importModules` call INSIDE ITS OWN LOOP, all in this one process. That is
exactly the pattern that drove Tools/CheckGatesAxioms.lean's memory to
~49GB and broke CI on both platforms before ITS fix; a contamination-checked
measurement of this tool's own pre-fix binary (`Get-CimInstance` filtered to
this process's own tree) confirmed the identical failure mode here too: a
single process climbing to ~41GB working set over the run. The current split
also prevents a nominal `lake build check_refs_coverage_full` from compiling
the combined repository closure inside this verifier's own Lean process. The
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
hide). The parent applies the containment and source-citation scans to every
candidate returned by a worker; uncited declarations have no exception path.

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
import Lake.Build.Trace
import Lake.Build.Common
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

/-- What a `--scan-root` or `--scan-module` worker process reported, once its one
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
  | scanned (modules : Array Name) (candidates : Array DeclCandidate)

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
    let modulesJ ← j.getObjVal? "modules"
    let modulesArr ← modulesJ.getArr?
    let modules ← modulesArr.mapM fun item => do
      let moduleS ← item.getStr?
      pure (nameOfDotted moduleS)
    let cands ← candsArr.mapM fun item => do
      let fqnJ ← item.getObjVal? "fqn"
      let fqnS ← fqnJ.getStr?
      let moduleJ ← item.getObjVal? "module"
      let moduleS ← moduleJ.getStr?
      let fileJ ← item.getObjVal? "file"
      let fileS ← fileJ.getStr?
      let lineJ ← item.getObjVal? "anchorLine"
      let lineN ← lineJ.getNat?
      let rangeStartJ ← item.getObjVal? "rangeStart"
      let rangeStart ← FromJson.fromJson? (α := Position) rangeStartJ
      let rangeEndJ ← item.getObjVal? "rangeEnd"
      let rangeEnd ← FromJson.fromJson? (α := Position) rangeEndJ
      pure {
        fqn := fqnS, module := nameOfDotted moduleS, file := System.FilePath.mk fileS,
        anchorLine := lineN, rangeStart := rangeStart, rangeEnd := rangeEnd
      }
    return .scanned modules cands

private def scanResultJson (modules : Array Name) (cands : Array DeclCandidate) : Json :=
  let modulesJson := modules.map (fun moduleName => (toString moduleName : Json))
  let candsJson := cands.map (fun d => Json.mkObj [
    ("fqn", (d.fqn : Json)),
    ("module", (toString d.module : Json)),
    ("file", (d.file.toString : Json)),
    ("anchorLine", (d.anchorLine : Json)),
    ("rangeStart", Lean.toJson d.rangeStart),
    ("rangeEnd", Lean.toJson d.rangeEnd)
  ])
  Json.mkObj [
    ("ok", (true : Json)), ("modules", Json.arr modulesJson),
    ("candidates", Json.arr candsJson)
  ]

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
why that split matters. Declaration coverage has no exception path: every
reported declaration must carry its own preceding citation. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def runScanWorker (target : Name) (file : System.FilePath) : IO UInt32 := do
  setupSearchPath
  let ctx : Core.Context := { fileName := "CheckRefsCoverage", fileMap := default }
  let result ←
    try
      let env2 ← importModules #[{module := target}] {} (trustLevel := 0) (loadExts := false)
      let cands ← collectCandidates env2 ctx
        (fun n i => isCoverageCandidateForModule env2 n i target) (fun _ => some file)
      pure (scanResultJson #[target] cands)
    catch e =>
      pure (Json.mkObj [("ok", (false : Json)), ("error", (e.toString : Json))])
  IO.println s!"{resultMarker}{result.compress}"
  return 0

/-- Imports one umbrella root in its own short-lived process and returns every project module and
    declaration reached by that root.  Running the three roots sequentially retains the old
    baseline efficiency without accumulating all three environments in the gate driver. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def runRootWorker (target : Name) : IO UInt32 := do
  setupSearchPath
  let ctx : Core.Context := { fileName := "CheckRefsCoverage", fileMap := default }
  let result ←
    try
      let enumeration ← discoverProjectModules
      let discovered := enumeration.files.map (fun p => (moduleNameOfPath p, p))
      let fileOfModule : Std.HashMap Name System.FilePath :=
        discovered.foldl (init := {}) (fun m (n, p) => m.insert n p)
      let env2 ← importModules #[{module := target}] {} (trustLevel := 0) (loadExts := false)
      let cands ← collectCandidates env2 ctx
        (fun n i => isCoverageCandidate env2 n i) (fileOfModule[·]?)
      let modules := env2.allImportedModuleNames.filter (fun n => (fileOfModule[n]?).isSome)
      pure (scanResultJson modules cands)
    catch e =>
      pure (Json.mkObj [("ok", (false : Json)), ("error", (e.toString : Json))])
  IO.println s!"{resultMarker}{result.compress}"
  return 0

private structure AuthorityStat where
  size : Nat
  mtimeSec : Nat
  mtimeNsec : Nat

private structure AuthorityContent where
  path : String
  hash : String
  stat : AuthorityStat

private structure AuthorityModule where
  path : String
  sourceHash : String
  source : AuthorityStat
  oleanPath : String
  oleanHash : String
  olean : AuthorityStat
  tracePath : String
  traceHash : String
  trace : AuthorityStat

private structure AuthorityArtifact where
  path : String
  lakeHash : String
  stat : AuthorityStat

private structure BuildAuthority where
  nonce : String
  workerNonce : String
  leanVersion : String
  gate : AuthorityArtifact
  inputs : Array AuthorityContent
  entries : Array AuthorityModule

private def parseAuthorityStat (json : Json) : Except String AuthorityStat := do
  return {
    size := ← (← json.getObjVal? "size").getNat?
    mtimeSec := ← (← json.getObjVal? "mtimeSec").getNat?
    mtimeNsec := ← (← json.getObjVal? "mtimeNsec").getNat?
  }

private def parseAuthorityContent (json : Json) : Except String AuthorityContent := do
  return {
    path := ← (← json.getObjVal? "path").getStr?
    hash := ← (← json.getObjVal? "hash").getStr?
    stat := ← parseAuthorityStat (← json.getObjVal? "stat")
  }

private def parseAuthorityModule (json : Json) : Except String AuthorityModule := do
  return {
    path := ← (← json.getObjVal? "path").getStr?
    sourceHash := ← (← json.getObjVal? "sourceHash").getStr?
    source := ← parseAuthorityStat (← json.getObjVal? "source")
    oleanPath := ← (← json.getObjVal? "oleanPath").getStr?
    oleanHash := ← (← json.getObjVal? "oleanHash").getStr?
    olean := ← parseAuthorityStat (← json.getObjVal? "olean")
    tracePath := ← (← json.getObjVal? "tracePath").getStr?
    traceHash := ← (← json.getObjVal? "traceHash").getStr?
    trace := ← parseAuthorityStat (← json.getObjVal? "trace")
  }

private def parseAuthorityArtifact (json : Json) : Except String AuthorityArtifact := do
  return {
    path := ← (← json.getObjVal? "path").getStr?
    lakeHash := ← (← json.getObjVal? "lakeHash").getStr?
    stat := ← parseAuthorityStat (← json.getObjVal? "stat")
  }

private def parseBuildAuthority (text : String) : Except String BuildAuthority := do
  let json ← Json.parse text
  let version ← (← json.getObjVal? "version").getNat?
  if version != 3 then throw s!"unsupported authority manifest version {version}"
  let inputsJson ← (← json.getObjVal? "inputs").getArr?
  let entriesJson ← (← json.getObjVal? "entries").getArr?
  return {
    nonce := ← (← json.getObjVal? "nonce").getStr?
    workerNonce := ← (← json.getObjVal? "workerNonce").getStr?
    leanVersion := ← (← json.getObjVal? "leanVersion").getStr?
    gate := ← parseAuthorityArtifact (← json.getObjVal? "gate")
    inputs := ← inputsJson.mapM parseAuthorityContent
    entries := ← entriesJson.mapM parseAuthorityModule
  }

private def fnv1a64File (path : System.FilePath) : IO UInt64 := do
  let bytes ← IO.FS.readBinFile path
  let mut value : UInt64 := 14695981039346656037
  for byte in bytes do
    value := (value ^^^ UInt64.ofNat byte.toNat) * 1099511628211
  return value

private def statMatches (expected : AuthorityStat) (actual : IO.FS.Metadata) : Bool :=
  expected.size == actual.byteSize.toNat &&
    expected.mtimeSec == actual.modified.sec.toNat &&
    expected.mtimeNsec == actual.modified.nsec.toNat

private def canonicalPath (path : System.FilePath) : String :=
  path.toString.replace "\\" "/"

private def expectedOleanPath (source : System.FilePath) : System.FilePath :=
  ".lake" / "build" / "lib" / "lean" / source.withExtension "olean"

private def verifyContent (entry : AuthorityContent) : IO Bool := do
  let path := System.FilePath.mk entry.path
  let metadata ← path.metadata
  if !statMatches entry.stat metadata then return false
  return toString (← fnv1a64File path) == entry.hash

private def authorityStatFor (path : System.FilePath) : IO AuthorityStat := do
  let metadata ← path.metadata
  return {
    size := metadata.byteSize.toNat
    mtimeSec := metadata.modified.sec.toNat
    mtimeNsec := metadata.modified.nsec.toNat
  }

private def traceBindsCurrentSource (tracePath source : System.FilePath) : IO Bool := do
  let traceText ← IO.FS.readFile tracePath
  let metadata ←
    match Lake.BuildMetadata.parse traceText with
    | .ok metadata => pure metadata
    | .error _ => return false
  let expectedPath := canonicalPath (← IO.FS.realPath source)
  let expectedHash := toString (← Lake.computeFileHash source true)
  return metadata.inputs.any fun (caption, value) =>
    canonicalPath (System.FilePath.mk caption) == expectedPath &&
      match value with
      | .str hash => hash == expectedHash
      | _ => false

private def verifyBuildAuthority (expectedNonce : String) (manifest : BuildAuthority) : IO Bool := do
  if manifest.nonce != expectedNonce || manifest.leanVersion != Lean.versionString then
    return false

  let gatePath ← IO.appPath
  if canonicalPath gatePath != manifest.gate.path then return false
  let gateMetadata ← gatePath.metadata
  if !statMatches manifest.gate.stat gateMetadata then return false
  let gateHashPath := System.FilePath.mk (gatePath.toString ++ ".hash")
  let recordedGateHash := (← IO.FS.readFile gateHashPath).trimAscii.toString
  if recordedGateHash != manifest.gate.lakeHash ||
      toString (← Lake.computeBinFileHash gatePath) != manifest.gate.lakeHash then
    return false

  let requiredInputs := #[
    "lakefile.toml", "lake-manifest.json", "lean-toolchain",
    "scripts/run_full_refs_coverage.py", "Tools/CheckRefsCoverage.lean",
    "Tools/GateSubprocess.lean"
  ]
  let inputMap : Std.HashMap String AuthorityContent :=
    manifest.inputs.foldl (init := {}) (fun map entry => map.insert entry.path entry)
  if inputMap.size != manifest.inputs.size || inputMap.size != requiredInputs.size then
    return false
  for path in requiredInputs do
    match inputMap[path]? with
    | none => return false
    | some entry => if !(← verifyContent entry) then return false
  for toolSource in #["Tools/CheckRefsCoverage.lean", "Tools/GateSubprocess.lean"] do
    if gateMetadata.modified < (← (System.FilePath.mk toolSource).metadata).modified then
      return false

  let enumeration ← discoverProjectModules
  let moduleMap : Std.HashMap String AuthorityModule :=
    manifest.entries.foldl (init := {}) (fun map entry => map.insert entry.path entry)
  if moduleMap.size != manifest.entries.size || moduleMap.size != enumeration.files.size then
    return false
  for source in enumeration.files do
    let sourceKey := canonicalPath source
    match moduleMap[sourceKey]? with
    | none => return false
    | some entry =>
      let sourceMetadata ← source.metadata
      let oleanPath := expectedOleanPath source
      let oleanKey := canonicalPath oleanPath
      if entry.oleanPath != oleanKey || !statMatches entry.source sourceMetadata then
        return false
      if toString (← fnv1a64File source) != entry.sourceHash then
        return false
      let oleanMetadata ← oleanPath.metadata
      if !statMatches entry.olean oleanMetadata || oleanMetadata.modified < sourceMetadata.modified then
        return false
      let hashPath := System.FilePath.mk (oleanPath.toString ++ ".hash")
      let recordedHash := (← IO.FS.readFile hashPath).trimAscii.toString
      if recordedHash != entry.oleanHash || toString (← Lake.computeBinFileHash oleanPath) != entry.oleanHash then
        return false
      let tracePath := oleanPath.withExtension "trace"
      if entry.tracePath != canonicalPath tracePath then return false
      let traceMetadata ← tracePath.metadata
      if !statMatches entry.trace traceMetadata ||
          toString (← fnv1a64File tracePath) != entry.traceHash then
        return false
      if !(← traceBindsCurrentSource tracePath source) then return false
  return true

/-- A final, cheap barrier after the content-hash pass.  The full verification above establishes
the content and Lake trace bindings.  This second pass rereads the repository census and every
recorded filesystem identity immediately before success, closing the practical race where an
ordinary editor/build changes an entry already visited by the sequential hash pass.

This is an accidental-concurrency guard, not a security boundary against a hostile process with
the same operating-system account: portable filesystem metadata APIs do not provide an atomic
snapshot of a repository tree. -/
private def verifyModuleBarrier (entries : Array AuthorityModule)
    (files : Array System.FilePath) : IO Bool := do
  try
    let moduleMap : Std.HashMap String AuthorityModule :=
      entries.foldl (init := {}) (fun map entry => map.insert entry.path entry)
    if moduleMap.size != entries.size || moduleMap.size != files.size then return false
    for source in files do
      let sourceKey := canonicalPath source
      let some entry := moduleMap[sourceKey]? | return false
      if !statMatches entry.source (← source.metadata) then return false
      let oleanPath := System.FilePath.mk entry.oleanPath
      if !statMatches entry.olean (← oleanPath.metadata) then return false
      let tracePath := System.FilePath.mk entry.tracePath
      if !statMatches entry.trace (← tracePath.metadata) then return false
      let hashPath := System.FilePath.mk (oleanPath.toString ++ ".hash")
      if (← IO.FS.readFile hashPath).trimAscii.toString != entry.oleanHash then return false
    return true
  catch _ =>
    return false

private def verifyArtifactBarrier (expected : AuthorityArtifact)
    (actualPath : System.FilePath) : IO Bool := do
  try
    if canonicalPath actualPath != expected.path ||
        !statMatches expected.stat (← actualPath.metadata) then
      return false
    let hashPath := System.FilePath.mk (actualPath.toString ++ ".hash")
    return (← IO.FS.readFile hashPath).trimAscii.toString == expected.lakeHash
  catch _ =>
    return false

private def verifyBuildAuthorityBarrier (manifest : BuildAuthority) : IO Bool := do
  try
    let gatePath ← IO.appPath
    if !(← verifyArtifactBarrier manifest.gate gatePath) then return false

    for entry in manifest.inputs do
      if !(← verifyContent entry) then return false

    let enumeration ← discoverProjectModules
    return ← verifyModuleBarrier manifest.entries enumeration.files
  catch _ =>
    return false

private def validAuthorityNonce (nonce : String) : Bool :=
  nonce.length ≥ 32 &&
    nonce.all (fun c => c.isAlphanum || c == '-' || c == '_')

private def consumeFreshBuildAuthority : IO (Option BuildAuthority) := do
  match ← IO.getEnv "GASM_FULL_REFS_BUILD_AUTHORITY" with
  | none =>
    IO.eprintln "[!] REFUSED: raw declaration-coverage execution has no fresh-build authority."
    IO.eprintln "    Use: python scripts/run_full_refs_coverage.py --full-repository"
    return none
  | some nonce =>
    if !validAuthorityNonce nonce then
      IO.eprintln "[!] REFUSED: malformed declaration-coverage build authority."
      return none
    let authorityPath : System.FilePath :=
      ".lake" / "build" / "full_refs_authority" / s!"{nonce}.token"
    try
      let manifestText ← IO.FS.readFile authorityPath
      -- Consume before parsing or verification: malformed, stale, and valid manifests are all
      -- one-attempt capabilities and cannot be repaired in place for a replay.
      IO.FS.removeFile authorityPath
      let manifest ←
        match parseBuildAuthority manifestText with
        | .ok manifest => pure manifest
        | .error error =>
          IO.eprintln s!"[!] REFUSED: malformed declaration-coverage authority manifest: {error}"
          return none
      if !(← verifyBuildAuthority nonce manifest) then
        IO.eprintln "[!] REFUSED: tracked sources, build inputs, toolchain, or olean outputs changed"
        IO.eprintln "    after the full build; rerun the canonical launcher."
        return none
      if !validAuthorityNonce manifest.workerNonce then return none
      return some manifest
    catch _ =>
      IO.eprintln "[!] REFUSED: declaration-coverage build authority is absent or already consumed."
      IO.eprintln "    Use: python scripts/run_full_refs_coverage.py --full-repository"
      return none

private def fnv1a64String (text : String) : UInt64 := Id.run do
  let mut value : UInt64 := 14695981039346656037
  for byte in text.toUTF8 do
    value := (value ^^^ UInt64.ofNat byte.toNat) * 1099511628211
  return value

private def workerAuthorityPath (nonce : String) : System.FilePath :=
  ".lake" / "build" / "full_refs_authority" / s!"{nonce}.worker"

private def issueWorkerAuthority (master payload : String) : IO String := do
  let nonce := s!"{master}_{fnv1a64String payload}"
  let expires := (← IO.monoMsNow) + 300000
  IO.FS.writeFile (workerAuthorityPath nonce) s!"{expires}\n{payload}"
  return nonce

/-- Consume an accidental-invocation capability before doing work.  The marker prevents stale or
mistyped internal CLI use; it is intentionally not presented as hostile same-user authorization.
A crashed parent can leave the exact payload capability usable until its five-minute expiry. -/
private def consumeWorkerAuthority (nonce payload : String) : IO Bool := do
  if !validAuthorityNonce nonce then return false
  let workerPath : System.FilePath :=
    ".lake" / "build" / "full_refs_authority" / s!"{nonce}.worker"
  try
    let contents ← IO.FS.readFile workerPath
    IO.FS.removeFile workerPath
    match contents.splitOn "\n" with
    | [expiresText, authorizedPayload] =>
      match expiresText.toNat? with
      | some expires => return (← IO.monoMsNow) ≤ expires && authorizedPayload == payload
      | none => return false
    | _ => return false
  catch _ =>
    return false

private def removeWorkerAuthority (nonce : String) : IO Unit := do
  try IO.FS.removeFile (workerAuthorityPath nonce) catch _ => pure ()

private def printAuthorityModules : IO UInt32 := do
  let enumeration ← discoverProjectModules
  if !enumeration.errors.isEmpty then
    for error in enumeration.errors do IO.eprintln error
    return 1
  let paths := enumeration.files.map (fun path => (canonicalPath path : Json))
  let lakefileText ← IO.FS.readFile "lakefile.toml"
  let (declaredRoots, rootErrors) := deriveLakeBuildRoots lakefileText
  if !rootErrors.isEmpty then
    for error in rootErrors do IO.eprintln error
    return 1
  let mut rootNames : Array String := #[]
  for root in declaredRoots do
    if !rootNames.contains root.module then rootNames := rootNames.push root.module
  let roots : Array Json := rootNames.map fun (root : String) => (root : Json)
  let plan := Json.mkObj [("sources", Json.arr paths), ("roots", Json.arr roots)]
  IO.println s!"GASM_AUTHORITY_MODULES {plan.compress}"
  return 0

/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def runGate (workerNonce : String) : IO UInt32 := do
  let startTime ← IO.monoMsNow

  setupSearchPath

  IO.println sepLine
  IO.println " gasm Law 1 / Law 3 DECLARATION-COVERAGE Gate Verifier (Tools/CheckRefsCoverage.lean)"
  IO.println sepLine
  IO.println "[*] Enumerates every reportable project declaration from the COMPILED ENVIRONMENT"
  IO.println "    (not source-text pattern matching), then checks each for a preceding `REF:`."

  let enumeration ← discoverProjectModules
  let discovered := enumeration.files.map (fun p => (moduleNameOfPath p, p))
  let mut candidates : Array DeclCandidate := #[]

  -- The three umbrella environments are loaded in separate, sequential workers.  The parent
  -- retains only their compact JSON declaration summaries, so neither building nor running the
  -- driver accumulates the full repository environment. Modules outside those import closures
  -- keep the existing one-module worker path that closes the TC15-style coverage gap.
  let mut unloadable : Array (Name × String) := #[]
  let mut baselineModules : Std.HashSet Name := {}
  let selfExe ← IO.appPath
  let cwd ← IO.currentDir
  for root in #[`Gasm, `Stdlib, `Spikes] do
    let payload := s!"root:{root}"
    let workerToken ← issueWorkerAuthority workerNonce payload
    let payloadRes ← spawnAndGetResultPayload selfExe cwd
      #["--scan-root", workerToken, toString root]
    removeWorkerAuthority workerToken
    match payloadRes with
    | .error spawnErr =>
      IO.eprintln s!"[!] umbrella worker {root} failed; falling back to per-module scans: {spawnErr}"
    | .ok payload =>
      match parseRefsWorkerResult payload with
      | .error parseErr =>
        IO.eprintln s!"[!] umbrella worker {root} returned malformed data; falling back: {parseErr}"
      | .ok (.loadFailed loadErr) =>
        IO.eprintln s!"[!] umbrella worker {root} could not load; falling back: {loadErr}"
      | .ok (.scanned modules cands) =>
        for moduleName in modules do
          baselineModules := baselineModules.insert moduleName
        candidates := candidates ++ cands

  let missing := discovered.filter (fun (moduleName, _) => !baselineModules.contains moduleName)
  let concurrency ← defaultScanConcurrency
  let workerResults ← runWorkerPool missing concurrency fun (target, targetFile) => do
    let workerPayload := s!"module:{target}:{targetFile}"
    let workerToken ← issueWorkerAuthority workerNonce workerPayload
    let payloadRes ← spawnAndGetResultPayload selfExe cwd
      #["--scan-module", workerToken, toString target, targetFile.toString]
    removeWorkerAuthority workerToken
    pure (target, targetFile, payloadRes)

  let mut coveredStandalone := 0
  for (target, _targetFile, payloadRes) in workerResults do
    match payloadRes with
    | .error spawnErr =>
      unloadable := unloadable.push (target, spawnErr)
    | .ok payload =>
      match parseRefsWorkerResult payload with
      | .error parseErr =>
        unloadable := unloadable.push (target, s!"malformed scan subprocess result: {parseErr}")
      | .ok (.loadFailed loadErr) =>
        unloadable := unloadable.push (target, loadErr)
      | .ok (.scanned _ cands) =>
        coveredStandalone := coveredStandalone + 1
        candidates := candidates ++ cands

  let elapsedImportMs := (← IO.monoMsNow) - startTime

  -- Containment filtering remains per module across the full candidate set.
  let topLevel := dropContained candidates

  -- Group top-level candidates by file so each file is read and scanned
  -- exactly once, regardless of how many declarations it contributes.
  let mut byFile : Std.HashMap System.FilePath (Array DeclCandidate) := {}
  for d in topLevel do
    byFile := byFile.insert d.file ((byFile.getD d.file #[]).push d)

  let mut scanned := 0
  let mut uncited : Array DeclCandidate := #[]

  for (file, decls) in byFile.toList do
    let declLines : Std.HashSet Nat := decls.foldl (init := {}) (fun s d => s.insert d.anchorLine)
    let cited ← scanFileForCitedLines file declLines
    for d in decls do
      scanned := scanned + 1
      if !cited.contains d.anchorLine then
        uncited := uncited.push d

  let elapsedMs := (← IO.monoMsNow) - startTime
  let baselineProjectCount :=
    (discovered.filter (fun (moduleName, _) => baselineModules.contains moduleName)).size

  IO.println ""
  IO.println "--- MODULE COVERAGE (TC15-style closure, mirrors CheckGatesAxioms.lean) ---"
  IO.println s!"[*] {discovered.size} tracked project module(s) under {projectRootDirs} are built by a"
  IO.println s!"    declared lakefile.toml target ({enumeration.libRoots} [[lean_lib]] root(s), \
{enumeration.exeRoots} [[lean_exe]] root(s))."
  IO.println s!"[*] {baselineProjectCount} reached through three sequential isolated umbrella workers;"
  IO.println s!"    {coveredStandalone} more loaded in isolated per-module workers."
  IO.println "[*] No process accumulates all three repository environments."
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
  IO.println s!"[*] Scanned {scanned} top-level declaration(s); {uncited.size} uncited."

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
    IO.println "    (Law 1 violation: Invention); declaration coverage has no exception path:"
    for d in uncited.toList do
      IO.println s!"    - {d.file}:{d.anchorLine}: {d.module}::{d.fqn}"

  if !failed then
    IO.println "[+] Every reportable declaration in scope carries a preceding `REF:` citation;"
    IO.println "    declaration coverage has no exception path."

  IO.println ""
  IO.println s!"[*] Wall time: {elapsedMs}ms."
  IO.println sepLine
  return if failed then 1 else 0

/-- CLI entry point. `--scan-root <one-time authority> <dotted name>` and
`--scan-module <one-time authority> <dotted name> <file path>` are internal modes:
they are how `runGate` re-invokes this executable as isolated workers (see
this file's header's SUBPROCESS ISOLATION section) and are never meant to be typed by a human.
Any other argument list (including none) attempts the protected top-level gate. -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
private def runAuthoritySelfTest : IO UInt32 := do
  let authorityDir : System.FilePath := ".lake" / "build" / "full_refs_authority"
  IO.FS.createDirAll authorityDir
  let master := "selftest_authority_nonce_0123456789abcdef"
  let payload := "root:DefinitelyMissing"
  let token ← issueWorkerAuthority master payload
  if !(← consumeWorkerAuthority token payload) then return 1
  if ← consumeWorkerAuthority token payload then return 1

  let mismatch ← issueWorkerAuthority master "root:Expected"
  if ← consumeWorkerAuthority mismatch "root:Wrong" then return 1
  if ← (workerAuthorityPath mismatch).pathExists then return 1

  let expired := s!"{master}_expired"
  IO.FS.writeFile (workerAuthorityPath expired) "0\nroot:Expired"
  if ← consumeWorkerAuthority expired "root:Expired" then return 1
  if ← (workerAuthorityPath expired).pathExists then return 1

  let malformed := s!"{master}_malformed"
  IO.FS.writeFile (workerAuthorityPath malformed) "not-a-worker-capability"
  if ← consumeWorkerAuthority malformed "root:Malformed" then return 1
  if ← (workerAuthorityPath malformed).pathExists then return 1

  if (parseBuildAuthority "{\"version\":2}").isOk then return 1
  if (parseBuildAuthority "{\"version\":3}").isOk then return 1
  if (parseRefsWorkerResult "not-json").isOk then return 1

  let selfExe ← IO.appPath
  let cwd ← IO.currentDir
  let rawOld ← IO.Process.output {
    cmd := selfExe.toString
    args := #["--scan-root", "old-reusable-worker-marker", "Gasm"]
    cwd := some cwd
  }
  if rawOld.exitCode != 2 then return 1
  let rawMalformed ← IO.Process.output {
    cmd := selfExe.toString
    args := #["--scan-module", "malformed", "Gasm.Core.Arch", "Gasm/Core/Arch.lean"]
    cwd := some cwd
  }
  if rawMalformed.exitCode != 2 then return 1

  let topNonce := "selftest_top_authority_0123456789abcdef"
  let topPath := authorityDir / s!"{topNonce}.token"
  IO.FS.writeFile topPath "malformed top-level manifest"
  let malformedTop ← IO.Process.output {
    cmd := selfExe.toString
    cwd := some cwd
    env := #[("GASM_FULL_REFS_BUILD_AUTHORITY", some topNonce)]
  }
  if malformedTop.exitCode != 2 || (← topPath.pathExists) then return 1
  let replayTop ← IO.Process.output {
    cmd := selfExe.toString
    cwd := some cwd
    env := #[("GASM_FULL_REFS_BUILD_AUTHORITY", some topNonce)]
  }
  if replayTop.exitCode != 2 then return 1

  let source := authorityDir / "trace-binding-selftest.lean"
  let trace := authorityDir / "trace-binding-selftest.trace"
  IO.FS.writeFile source "def traceBindingSelfTest : Nat := 1\n"
  let sourcePath ← IO.FS.realPath source
  let sourceHash ← Lake.computeFileHash source true
  let metadata : Lake.BuildMetadata := {
    depHash := sourceHash
    inputs := #[(sourcePath.toString, toJson sourceHash)]
    outputs? := none
    log := {}
    synthetic := false
  }
  IO.FS.writeFile trace (toJson metadata).compress
  if !(← traceBindsCurrentSource trace source) then return 1
  let sourceContent : AuthorityContent := {
    path := source.toString
    hash := toString (← fnv1a64File source)
    stat := ← authorityStatFor source
  }
  if !(← verifyContent sourceContent) then return 1
  IO.FS.writeFile source "def traceBindingSelfTestChanged : Nat := 200\n"
  if ← verifyContent sourceContent then return 1
  if ← traceBindsCurrentSource trace source then return 1

  IO.FS.writeFile source "def traceBindingSelfTest : Nat := 1\n"
  let wrongSource := authorityDir / "trace-binding-wrong-source.lean"
  IO.FS.writeFile wrongSource "def wrongTraceBindingSource : Nat := 1\n"
  if ← traceBindsCurrentSource trace wrongSource then return 1
  IO.FS.writeFile trace "malformed trace"
  if ← traceBindsCurrentSource trace source then return 1
  IO.FS.writeFile trace (toJson metadata).compress

  let olean := authorityDir / "trace-binding-selftest.olean"
  let oleanHashPath := System.FilePath.mk (olean.toString ++ ".hash")
  IO.FS.writeFile olean "synthetic olean"
  IO.FS.writeFile oleanHashPath "synthetic-olean-hash"
  let artifact : AuthorityArtifact := {
    path := canonicalPath olean
    lakeHash := "synthetic-olean-hash"
    stat := ← authorityStatFor olean
  }
  if !(← verifyArtifactBarrier artifact olean) then return 1
  IO.FS.writeFile oleanHashPath "mutated artifact hash"
  if ← verifyArtifactBarrier artifact olean then return 1
  IO.FS.writeFile oleanHashPath "synthetic-olean-hash"
  let mkEntry : IO AuthorityModule := do
    return {
      path := canonicalPath source
      sourceHash := toString (← fnv1a64File source)
      source := ← authorityStatFor source
      oleanPath := canonicalPath olean
      oleanHash := "synthetic-olean-hash"
      olean := ← authorityStatFor olean
      tracePath := canonicalPath trace
      traceHash := toString (← fnv1a64File trace)
      trace := ← authorityStatFor trace
    }
  let entry ← mkEntry
  if !(← verifyModuleBarrier #[entry] #[source]) then return 1
  if ← verifyModuleBarrier #[] #[source] then return 1
  if ← verifyModuleBarrier #[entry] #[] then return 1
  if ← verifyModuleBarrier #[entry, entry] #[source] then return 1
  if ← verifyModuleBarrier #[entry] #[source, wrongSource] then return 1

  IO.FS.writeFile source "source mutation detected by final barrier\n"
  if ← verifyModuleBarrier #[entry] #[source] then return 1
  IO.FS.writeFile source "def traceBindingSelfTest : Nat := 1\n"
  let entry ← mkEntry
  IO.FS.writeFile olean "synthetic olean mutation with a different size"
  if ← verifyModuleBarrier #[entry] #[source] then return 1
  IO.FS.writeFile olean "synthetic olean"
  let entry ← mkEntry
  IO.FS.writeFile trace "synthetic trace mutation with a different size"
  if ← verifyModuleBarrier #[entry] #[source] then return 1

  IO.FS.removeFile source
  IO.FS.removeFile wrongSource
  IO.FS.removeFile trace
  IO.FS.removeFile olean
  IO.FS.removeFile oleanHashPath
  IO.println "full-refs authority self-test passed"
  return 0

/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def main (args : List String) : IO UInt32 :=
  match args with
  | ["--self-test-authority"] => runAuthoritySelfTest
  | ["--list-authority-modules"] => printAuthorityModules
  | ["--scan-root", workerNonce, modStr] => do
    if ← consumeWorkerAuthority workerNonce s!"root:{modStr}" then
      runRootWorker (nameOfDotted modStr)
    else return 2
  | ["--scan-module", workerNonce, modStr, fileStr] => do
    if ← consumeWorkerAuthority workerNonce s!"module:{modStr}:{fileStr}" then
      runScanWorker (nameOfDotted modStr) (System.FilePath.mk fileStr)
    else return 2
  | _ => do
    match ← consumeFreshBuildAuthority with
    | some manifest => do
      let result ← runGate manifest.workerNonce
      if !(← verifyBuildAuthority manifest.nonce manifest) then
        IO.eprintln "[!] REFUSED: repository/build state changed during declaration coverage."
        return 2
      if !(← verifyBuildAuthorityBarrier manifest) then
        IO.eprintln "[!] REFUSED: repository/build state changed during final validation."
        return 2
      return result
    | none => return 2
