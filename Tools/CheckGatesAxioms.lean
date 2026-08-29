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
Tools/CheckGatesAxioms.lean - Law 10 / Pillar 1 axiom-level gate verifier

scripts/check_gates.py is a fast, line-regex pre-check over the .lean
*source text*. It is defense-in-depth, not the gate: it can only recognize
tactic *spellings* it already knows about, and cannot see what the compiled
kernel environment actually recorded.

THIS tool is the load-bearing gate. It imports the whole project (Gasm,
Stdlib, Spikes), walks every *compiled* declaration reachable from that
import closure in the resulting kernel environment, and asks Lean's own
axiom-dependency machinery (`Lean.collectAxioms`, the same walk
`#print axioms` performs) which axioms each declaration depends on. NOTE:
"reachable from the import closure" is narrower than "every declaration in
the repository" -- see isProjectModule's doc comment and docs/REVIEW.md
§4.1.1 for the current coverage gap (tracked as TC15).

WHAT COUNTS AS "NEEDS AN ALLOWLIST ENTRY": not just native-evaluation axioms.
Lean's kernel trusts exactly three axioms as part of ordinary mathematics:
`propext`, `Classical.choice`, `Quot.sound`. ANY other axiom a declaration
depends on -- a native-evaluation axiom, `sorryAx`, or a hand-declared
`axiom` -- is exactly what REVIEW.md's Pillar 1 ("zero sorry, zero
unauthorized axioms") is about, and had NO enforcement anywhere before this
tool. So the gate is: every declaration depending on anything outside that
three-axiom standard set must have a matching scripts/gate_allowlist.txt
entry, whatever the axiom's shape.

Ground truth for the native-evaluation case specifically: on Lean toolchain
v4.33.1, `native_decide` and `decide (native := true)` do NOT share a single
`Lean.ofReduceBool` axiom -- each occurrence synthesizes its own
declaration-local axiom nested under a `_native` sub-namespace, e.g.
`<decl>._native.native_decide.ax_i_j` / `<decl>._native.decide.ax_i_j`
(confirmed empirically via `lean` + `#print axioms` on a probe file). That
distinction is used only to LABEL an offending axiom for the report below;
the gate itself does not special-case it -- any non-standard axiom gates.

ALLOWLIST KEYING: by (originating module, FULLY-QUALIFIED declaration name),
not by bare name (what scripts/check_gates.py's source-text scan uses) and
NOT by fqn alone either. A bare-name key is exploitable:
`namespace Foo.Bar; theorem crc32_empty : ... := by native_decide` would
collide with the real, unrelated `crc32_empty` and pass for free. The
allowlist file's format is:
  <file>::<declaration-name>::<fully-qualified-name>::<category>::<justification>
The 3rd field (fully-qualified name, exactly as Lean's environment prints it,
e.g. `Stdlib.Zlib.crc32_empty`) combined with the 1st field (source file,
converted to the module it names -- see `matchKey`) is what THIS tool
matches against; the 1st and 2nd fields alone are what scripts/check_gates.py
matches against (it only ever sees unqualified source text). Malformed lines
(wrong field count, unknown category, missing justification) are a hard
parse failure here, not a silently-salvaged partial match.

fqn ALONE is not enough (TC15 finding): every project module reachable
before this task's fix happens to use a consistent `namespace` matching its
file, so `fqn` alone was accidentally unique project-wide. 32 modules newly
in scope break that -- every spike `Emit.lean`/`Test.lean` and every fuzzer
CLI declares a bare, unnamespaced top-level `def main`, so `toString name =
"main"` for over a dozen unrelated declarations. See `matchKey`'s doc
comment below for the fix.

SCOPE: a declaration is in scope if it was COMPILED FROM a project module
(`env.getModuleIdxFor?` names a module under `Gasm`/`Stdlib`/`Spikes`), not
if its own *name* happens to look like it lives under one of those
namespaces -- a declaration in a foreign/no namespace inside a project file
is still fully part of the build and must not be invisible to this tool.

COVERAGE (docs/REVIEW.md §4.1.1): the single `importModules #[Gasm, Stdlib,
Spikes]` call in `main` only sees whatever those three umbrella files
transitively `import` -- historically 138 of 170 project modules, with 32
(every `Spikes/*/Emit.lean` and `Spikes/*/Test.lean`, all four fuzzer CLIs
plus their non-CLI engine modules, `NASM.lean`, `RoundtripTests.lean`,
`Stdlib/**/Test.lean`, `GzipFuzzer.lean`) sitting outside every umbrella's
import graph and therefore invisible to the scan. `discoverProjectModules`
below enumerates every TRACKED `.lean` file under `Gasm/`, `Stdlib/`,
`Spikes/` via `git ls-files` -- not via any import closure, so it cannot
inherit the blind spot it exists to catch, and not via a filesystem walk,
which is what used to make this gate go red on an agent's uncommitted
work-in-progress (see `enumerateProjectModules` in
Tools/GateSubprocess.lean), and restricted to what a declared lakefile.toml
target actually builds. `main` then: (1) does
the baseline scan exactly as before; (2) for every enumerated module
NOT in the baseline's `env.allImportedModuleNames`, scans it standalone --
see SUBPROCESS ISOLATION below for how; (3) If any enumerated module
can be loaded into NEITHER the baseline environment NOR standalone -- i.e. a
module `lake build` was asked to compile and whose `.olean` is nevertheless
absent or unreadable -- that is exactly the kind of blind spot this task
closes: the tool FAILS LOUDLY rather than silently omitting it. Corollary:
this gate's completeness depends on a prior full build (`lake build`) having
produced every such module's `.olean` -- consistent with the clean-rebuild contract's "gate
runner does one clean-tree build before sign-off." A module NO declared root
reaches is a different defect (nothing compiles it at all) owned by
`scripts/check_orphan_modules.py`, which names the file, its umbrella and the
exact `import` line; this tool reports those by name and does not fold them
into an exit 1 it cannot explain.

SUBPROCESS ISOLATION (CI resource-exhaustion fix, see docs/CI.md): each of
the 32-ish disk-discovered-but-not-baseline modules is scanned in its OWN,
FRESH **OS PROCESS** -- this same executable, re-invoked as
`check_gates_axioms --scan-module <dotted module name>` (see `runScanWorker`
below) -- one module at a time, sequentially, never in parallel and never
batched together. Two things forced this design, not just the first:

1. WHY STANDALONE AT ALL (unchanged from the original design): many of the
   32 (every CLI/Emit/Test entry point) declare a bare top-level `def main`.
   Lean's own code generator (confirmed by reading
   `Lean.Compiler.LCNF.EmitC.emitMainFnIfNeeded` / `hasMainFn` in the
   toolchain source: it looks up a LOCAL declaration whose `Name` is
   *literally* `` `main`` -- no namespace prefix -- to synthesize the
   process's C `main()`; the LLVM backend's `EmitLLVM.hasMainFn` does the
   same `env.find? \`main`` lookup) requires every `lean_exe` root module to
   carry that exact bare name for the resulting binary to have an entry
   point at all. A namespaced `main` (or a namespaced implementation behind
   an unnamespaced shim -- the shim itself would still collide) is therefore
   not an option: Lake's `lean_exe` convention is not a style choice, it is
   downstream of the compiler's own hardcoded lookup. So two such modules
   can never share one `Environment`; each needs its own.
2. WHY A SEPARATE **PROCESS** AND NOT JUST A FRESH VALUE IN THE SAME PROCESS
   (what this tool did before this fix, and what broke CI): giving each
   module its own `Environment` *value* in a loop, relying on the host
   language's reference counting to free the previous one before importing
   the next, does not bound PEAK memory the way it looks like it should --
   CI's hosted runners (far less RAM than a dev workstation) hit exactly
   this: Windows failed to even read `Init/Prelude.olean` (a file that
   plainly exists) partway through the loop, and Linux's job was killed by
   the runner's own shutdown signal, both consistent with the process
   accumulating memory pressure it never gave back. A subprocess boundary
   hands reclamation to the OS on process exit -- a guarantee refcounting
   inside one long-lived process cannot make. Batch size is fixed at
   exactly 1 module per process on purpose: batching more than one module
   into a single subprocess would import them together into one shared
   `Environment`, which reintroduces the exact bare-`main`-collision problem
   point (1) above exists to dodge, the moment two `main`-declaring modules
   land in the same batch.

The worker (`--scan-module`) always exits 0 and reports success/failure of
ITS import via a `GASM_SCAN_RESULT <json>` line on stdout (parsed by
`parseWorkerResult`) -- this lets the parent tell "the module's `.olean`
genuinely doesn't exist / failed to import" (a real, reportable finding)
apart from "the OS process itself crashed, was killed, or emitted nothing
parseable" (also folded into `unloadable`, since both are exactly the kind
of blind spot this gate refuses to hide). The parent does its own allowlist
matching (`byKey`) against whatever the worker reports; the worker itself
carries no allowlist knowledge.

SHARED PLUMBING: `setupSearchPath`, `resultMarker`, `nameOfDotted`, and the
spawn-a-worker-and-capture-its-result-line step (`spawnAndGetResultPayload`)
now live in Tools/GateSubprocess.lean -- Tools/CheckRefsCoverage.lean (Law
1/3) closes the identical module-coverage gap the identical way, and this
plumbing was byte-for-byte duplicated between the two tools before that file
existed. See Tools/GateSubprocess.lean's own header for why only this much
is shared (each tool's `GASM_SCAN_RESULT` JSON schema stays tool-specific).
-/
import Lean
import Lean.Data.Json
import Gasm
import Stdlib
import Spikes
import Tools.GateSubprocess

open Lean

/-- The only axioms Lean's kernel trusts as part of ordinary, sorry-free,
native-eval-free mathematics. Anything else gates. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
def isStandardAxiom (n : Name) : Bool := standardAxioms.contains n

/-- Does any component of this axiom's `Name` literally read `_native`?
That is exactly the sub-namespace Lean nests a native-evaluation axiom
under, regardless of which tactic spelling produced it. Used only to LABEL
an offending axiom in the report -- not to decide whether it gates (every
non-standard axiom gates, per the module doc above). -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
partial def hasNativeComponent : Name → Bool
  | .anonymous => false
  | .str p s => s == "_native" || hasNativeComponent p
  | .num p _ => hasNativeComponent p

/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
def axiomLabel (n : Name) : String :=
  if n == ``Lean.ofReduceBool || n == ``Lean.ofReduceNat || hasNativeComponent n then
    "native-eval"
  else if n == ``sorryAx then
    "sorry"
  else
    "hand-declared/other"

/-- Is `name`'s ORIGINATING MODULE (not its own namespace-shaped name) one
of the project's? A declaration's module tracks the *file* it was compiled
from, which is what scopes this tool to "gasm's own code" -- unlike a
name-prefix check, it cannot be evaded by declaring something in a foreign
or root namespace inside a project file. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
def isProjectModule (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some idx =>
    match env.allImportedModuleNames[idx.toNat]? with
    | none => false
    | some modName =>
      (`Gasm).isPrefixOf modName || (`Stdlib).isPrefixOf modName || (`Spikes).isPrefixOf modName

/-- Theorems/defs/opaques/hand-declared axioms -- inductives, constructors,
recursors, and quotient constants cannot themselves invoke a tactic or carry
a hand-written axiom dependency. `axiomInfo` is included so a bare
`axiom foo : P` is itself flagged the moment it is declared (it trivially
"depends on" itself), not only once something else comes to cite it --
Pillar 1's "zero unauthorized axioms" is about the declaration, not just its
call sites. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
def isReportableKind : ConstantInfo → Bool
  | .thmInfo _ | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ => true
  | _ => false

/-- Skip Lean-generated auxiliary declarations (any name component starting
with `_`: the `_native.*.ax_i_j` axioms themselves, a struct-field `by ...`
block's synthesized `_proof_1`, ...): not something a human can name and
allowlist. Their axiom dependencies are not lost -- they flow up into
whichever non-internal parent declaration references them, which IS
independently walked and reported. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
def isReportable (env : Environment) (name : Name) (info : ConstantInfo) : Bool :=
  isProjectModule env name && isReportableKind info && !name.isInternal

/-- Is `name`'s originating module EXACTLY `target` (not merely under the
same `Gasm`/`Stdlib`/`Spikes` prefix)? Used when scanning a standalone,
single-module `Environment` (see `discoverProjectModules` below): such an
environment's transitive closure includes every dependency of `target`
too, and those dependencies are already counted by the baseline scan (or
by whichever OTHER standalone import covers them) -- restricting to exact
module identity is what keeps each declaration reported exactly once. -/
/- REF: docs/REVIEW.md#law-10-kernel-checked-gates-the-nativedecide-restriction-exhaustive-finite-domains-only -/
def isExactlyModule (env : Environment) (name : Name) (target : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some idx => env.allImportedModuleNames[idx.toNat]? == some target

/- REF: docs/REVIEW.md#law-10-kernel-checked-gates-the-nativedecide-restriction-exhaustive-finite-domains-only -/
def isReportableForModule (env : Environment) (name : Name) (info : ConstantInfo) (target : Name) : Bool :=
  isExactlyModule env name target && isReportableKind info && !name.isInternal

/-- `name`'s originating module, per the same `env.getModuleIdxFor?` lookup
`isProjectModule`/`isExactlyModule` use. `none` only for a name outside any
imported module (never called on a name that already passed `isReportable`
or `isReportableForModule`, both of which imply `some`). -/
/- REF: docs/REVIEW.md#law-10-kernel-checked-gates-the-nativedecide-restriction-exhaustive-finite-domains-only -/
def originatingModule (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | none => none
  | some idx => env.allImportedModuleNames[idx.toNat]?

/-- TC15 finding: bare-`fqn` allowlist keying (the tool's ORIGINAL design,
per the header doc above) silently assumes `fqn` uniquely identifies a
declaration project-wide. That held for every declaration reachable before
this fix -- all library code, consistently namespaced. It does NOT hold for
the 32 newly-in-scope modules: every spike `Emit.lean`/`Test.lean` and every
fuzzer CLI declares a BARE top-level `def main` with no enclosing
`namespace`, so `toString name = "main"` for a dozen-plus unrelated
declarations across different files. Keying the allowlist by `fqn` alone
would let ONE `main`-keyed entry blanket-authorize every such declaration's
axioms project-wide -- the exact "bare-name key is exploitable" failure
mode this file's own header already calls out for scripts/check_gates.py,
just newly reachable here too. Fix: key by `(originating module, fqn)`,
computing the module side of an allowlist entry from its (already-recorded,
already used by scripts/check_gates.py) `file` field via the same
`moduleNameOfPath` disk enumeration uses -- so the file field, previously
carried only for diagnostics, now also does load-bearing disambiguation. -/
/- REF: docs/REVIEW.md#law-10-kernel-checked-gates-the-nativedecide-restriction-exhaustive-finite-domains-only -/
def matchKey (moduleName : Name) (fqn : String) : String := s!"{moduleName}::{fqn}"

/-- The project's own top-level source roots. `Tools/` (home of this very
checker) is deliberately excluded, matching `isProjectModule`'s existing
Gasm/Stdlib/Spikes-only namespace scope. -/
/- REF: docs/REVIEW.md#law-10-kernel-checked-gates-the-nativedecide-restriction-exhaustive-finite-domains-only -/
def projectRootDirs : List String := ["Gasm", "Stdlib", "Spikes"]

/-- Turns a project-relative `.lean` file path (e.g.
`Gasm/Targets/X86_64/NASM.lean`) into the dotted module `Name` Lean's own
import resolution would assign it (`Gasm.Targets.X86_64.NASM`). Assumes the
`.lean` extension is already present (callers filter on it first). -/
/- REF: docs/REVIEW.md#law-10-kernel-checked-gates-the-nativedecide-restriction-exhaustive-finite-domains-only -/
def moduleNameOfPath (p : System.FilePath) : Name :=
  (p.withExtension "").components.foldl Name.mkStr Name.anonymous

/-- Enumerates every project module the build actually compiles, from the
TRACKED TREE: every tracked `.lean` file under `projectRootDirs` (per
`git ls-files`) that some `lakefile.toml` build root reaches transitively.
This is deliberately independent of the tool's own IMPORT CLOSURE -- it is the
ground truth `main` cross-checks the compiled environment(s) against, so it
cannot itself have the blind spot it exists to catch.

Two defects were fixed here, both in `enumerateProjectModules`
(Tools/GateSubprocess.lean), which see for the full argument:

1. This used to be a `System.FilePath.walkDir` recursion. A walk sees any
   agent's UNCOMMITTED `.lean` too, so one person's open editor reddened this
   gate for everyone -- and reddened it by naming an unloadable module rather
   than the real cause (the 2026-08-28 `CanonicalTableSpec.lean` incident:
   exit 1 and exit 0 an hour apart on the same code).
2. It then took EVERY such file as a module this tool must be able to load.
   That has no notion of what `lake build` was ever asked to compile: it
   counted the `[[lean_exe]]` roots (every `Spikes/*/Emit.lean`,
   `*/Test.lean`, every fuzzer CLI) as outside any declared target when each
   IS one, and it counted a genuine orphan no root reaches as a bare exit 1
   with no named cause.

Neither fix weakens the module-coverage check below: a module in scope that
loads into neither the baseline environment nor a standalone import is still
a hard failure. That is TC15/T2 and it stays load-bearing. -/
/- REF: docs/REVIEW.md#law-10-kernel-checked-gates-the-nativedecide-restriction-exhaustive-finite-domains-only -/
def discoverProjectModules : IO ProjectModuleEnumeration :=
  enumerateProjectModules projectRootDirs

/- REF: docs/REVIEW.md#law-10-kernel-checked-gates-the-nativedecide-restriction-exhaustive-finite-domains-only -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
def sepLine : String :=
  "======================================================================"

/-- One parsed, VALID line of scripts/gate_allowlist.txt. Fields beyond
`fqn`/`category` are carried only for stale-entry / diagnostic reporting. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
structure AllowlistEntry where
  file         : String
  declName     : String
  fqn          : String
  category     : String
  justification : String
  lineNum      : Nat
deriving Inhabited

/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
def validCategories : List String := ["finite-forall", "grandfathered", "axiom-only"]

/-- Splits `s` on `sep`, but merges any parts beyond `maxParts` back into the
final part (so a `::` inside a free-text justification field doesn't get
mistaken for a delimiter). Mirrors scripts/check_gates.py's
`line.split("::", maxParts - 1)`. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
def splitOnMax (s : String) (sep : String) (maxParts : Nat) : List String :=
  let parts := s.splitOn sep
  if parts.length ≤ maxParts then
    parts
  else
    let head := parts.take (maxParts - 1)
    let tail := parts.drop (maxParts - 1)
    head ++ [String.intercalate sep tail]

/-- Parses scripts/gate_allowlist.txt. A malformed line (wrong field count,
unknown category, empty justification) is a HARD parse failure -- it is
reported and the whole run fails, rather than being silently skipped or
partially salvaged. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
def parseAllowlist (contents : String) : List AllowlistEntry × List String := Id.run do
  let mut entries : List AllowlistEntry := []
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
        [s!"gate_allowlist.txt:{lineNum}: expected 5 '::'-delimited fields (file::decl::fqn::category::justification), got {parts.length}: {rawLine}"]
      continue
    let file := parts[0]!.trimAscii.toString
    let declName := parts[1]!.trimAscii.toString
    let fqn := parts[2]!.trimAscii.toString
    let category := parts[3]!.trimAscii.toString.toLower
    let justification := parts[4]!.trimAscii.toString
    if !validCategories.contains category then
      errors := errors ++
        [s!"gate_allowlist.txt:{lineNum}: unknown category '{parts[3]!.trimAscii.toString}' (expected one of {validCategories})"]
      continue
    if fqn.isEmpty then
      errors := errors ++ [s!"gate_allowlist.txt:{lineNum}: missing fully-qualified name (3rd field)"]
      continue
    if justification.isEmpty then
      errors := errors ++ [s!"gate_allowlist.txt:{lineNum}: missing justification"]
      continue
    entries := entries ++ [(⟨file, declName, fqn, category, justification, lineNum⟩ : AllowlistEntry)]
  return (entries, errors)

/-- `declModule` is carried purely for reporting: since 32 modules (TC15)
declare a bare top-level `def main`/`def runTests` with no namespace,
`declName` alone (`main`) is not enough for a human reading the FAILED
report to tell which file is at fault. `declName` and each axiom are kept as
plain `String`s (rather than `Name`): a subprocess-reported offender (see
SUBPROCESS ISOLATION above) only ever HAS strings -- it crossed a process
boundary as JSON -- and printing a `String` looks identical to printing the
`Name` it came from, so there is no need to round-trip either back into a
`Name` just to report them. The axiom's label (`axiomLabel`, "native-eval" /
"sorry" / "hand-declared/other") is computed once, wherever the real `Name`
is still in hand (in-process for the baseline scan, inside the worker
process for a standalone module), and carried alongside the axiom's own
string form from then on. -/
/- REF: docs/REVIEW.md#law-10-kernel-checked-gates-the-nativedecide-restriction-exhaustive-finite-domains-only -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
structure Offender where
  declModule : Name
  declName   : String
  axioms     : Array (String × String)

/-- Run `Lean.collectAxioms` for one declaration against a fixed environment. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
def collectAxiomsFor (env : Environment) (ctx : Core.Context) (name : Name) :
    IO (Array Name) := do
  let coreState : Core.State := { env := env }
  let (axs, _) ← (Lean.collectAxioms (m := Core.CoreM) name).toIO ctx coreState
  return axs

-- `setupSearchPath` and `resultMarker` now live in Tools/GateSubprocess.lean,
-- shared verbatim with Tools/CheckRefsCoverage.lean's identical worker
-- protocol (see that file's header for why only this plumbing, and not the
-- tool-specific WorkerResult JSON schema, is shared).

-- `nameOfDotted` (inverse of `moduleNameOfPath`, used to turn a
-- `--scan-module <name>` CLI argument back into a `Name`) also now lives in
-- Tools/GateSubprocess.lean.

/-- What a `--scan-module` worker process reported, once its one
`GASM_SCAN_RESULT` JSON line has been parsed. `loadFailed` mirrors the old
in-process `catch` arm (the module's own `importModules` failed); the parent
folds it into `unloadable` exactly as before. -/
/- REF: docs/REVIEW.md#law-10-kernel-checked-gates-the-nativedecide-restriction-exhaustive-finite-domains-only -/
inductive WorkerResult where
  | loadFailed (msg : String)
  | scanned (count : Nat) (gated : Array (String × Array (String × String)))

/-- Parses one worker's `GASM_SCAN_RESULT` JSON payload (everything after the
marker). See `runScanWorker` for the shape this is the inverse of. -/
/- REF: docs/REVIEW.md#law-10-kernel-checked-gates-the-nativedecide-restriction-exhaustive-finite-domains-only -/
def parseWorkerResult (payload : String) : Except String WorkerResult := do
  let j ← Json.parse payload
  let okJ ← j.getObjVal? "ok"
  let ok ← okJ.getBool?
  if !ok then
    let errJ ← j.getObjVal? "error"
    let errS ← errJ.getStr?
    return .loadFailed errS
  else
    let scannedJ ← j.getObjVal? "scanned"
    let scannedN ← scannedJ.getNat?
    let gatedJ ← j.getObjVal? "gated"
    let gatedArr ← gatedJ.getArr?
    let gatedItems ← gatedArr.mapM fun item => do
      let declJ ← item.getObjVal? "decl"
      let declS ← declJ.getStr?
      let axJ ← item.getObjVal? "axioms"
      let axArr ← axJ.getArr?
      let axPairs ← axArr.mapM fun ax => do
        let nameJ ← ax.getObjVal? "name"
        let nameS ← nameJ.getStr?
        let labelJ ← ax.getObjVal? "label"
        let labelS ← labelJ.getStr?
        pure (nameS, labelS)
      pure (declS, axPairs)
    return .scanned scannedN gatedItems

/-- The `--scan-module <dotted name>` worker entry point: standalone-imports
EXACTLY ONE module into a fresh `Environment` -- in this fresh OS PROCESS,
never the parent's -- scans only declarations originating in it (mirroring
the old in-process standalone loop this replaces), and prints exactly one
`GASM_SCAN_RESULT <json>` line to stdout. Always exits `0`: whether the
IMPORT itself succeeded or failed is reported IN the JSON (`ok` field), not
via process exit code -- that is what lets the parent tell "this module
genuinely failed to import" (a real finding) apart from "this OS process
itself crashed / was killed / printed nothing parseable" (a missing or
unparseable result line, which the parent treats identically -- both are
exactly the blind spot this whole gate exists to refuse to hide). Carries no
allowlist knowledge; the parent alone does `byKey` matching, so N worker
processes never need N copies of the allowlist parsed into them. -/
/- REF: docs/REVIEW.md#law-10-kernel-checked-gates-the-nativedecide-restriction-exhaustive-finite-domains-only -/
def runScanWorker (target : Name) : IO UInt32 := do
  setupSearchPath
  let ctx : Core.Context := { fileName := "CheckGatesAxioms", fileMap := default }
  let result ←
    try
      let env2 ← importModules #[{module := target}] {} (trustLevel := 0) (loadExts := false)
      let mut scanned : Nat := 0
      let mut gatedItems : Array Json := #[]
      for i in [:env2.header.moduleNames.size] do
        if env2.header.moduleNames[i]! == target then
          if let some md := env2.header.moduleData[i]? then
            for name in md.constNames do
              if let some info := env2.find? name then
                if isReportableKind info && !name.isInternal then
                  scanned := scanned + 1
                  let axs ← collectAxiomsFor env2 ctx name
                  let gatingAxs := axs.filter (fun a => !isStandardAxiom a)
                  if gatingAxs.size > 0 then
                    let axJson := gatingAxs.map (fun a =>
                      Json.mkObj [("name", (toString a : Json)), ("label", (axiomLabel a : Json))])
                    gatedItems := gatedItems.push (Json.mkObj [
                      ("decl", (toString name : Json)), ("axioms", Json.arr axJson)])
          break
      pure (Json.mkObj [("ok", (true : Json)), ("scanned", (scanned : Json)), ("gated", Json.arr gatedItems)])
    catch e =>
      pure (Json.mkObj [("ok", (false : Json)), ("error", (e.toString : Json))])
  IO.println s!"{resultMarker}{result.compress}"
  return 0

/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#law-10-kernel-checked-gates-the-nativedecide-restriction-exhaustive-finite-domains-only -/
def runGate : IO UInt32 := do
  let startTime ← IO.monoMsNow

  setupSearchPath

  let allowlistPath : System.FilePath := "scripts" / "gate_allowlist.txt"
  if !(← allowlistPath.pathExists) then
    IO.eprintln s!"[!] ERROR: {allowlistPath} not found relative to the current directory."
    IO.eprintln "    Run this tool from the repo root, e.g.: `lake exe check_gates_axioms`"
    IO.eprintln "    (a direct binary invocation must also be run from the repo root)."
    return 1
  let allowlistText ← IO.FS.readFile allowlistPath
  let (allowlist, parseErrors) := parseAllowlist allowlistText

  IO.println sepLine
  IO.println " gasm Law 10 / Pillar 1 AXIOM-LEVEL Gate Verifier (Tools/CheckGatesAxioms.lean)"
  IO.println sepLine
  IO.println "[*] This is the load-bearing gate: it reads Lean's own axiom-dependency"
  IO.println "    graph (Lean.collectAxioms, the #print axioms machinery), not source text."
  IO.println "[*] Gates on ANY axiom outside {propext, Classical.choice, Quot.sound}, keyed"
  IO.println "    by fully-qualified declaration name."

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
      IO.eprintln "    Run this tool from the repo root, e.g.: `lake exe check_gates_axioms`"
      IO.Process.exit 1

  let ctx : Core.Context := { fileName := "CheckGatesAxioms", fileMap := default }

  -- (module, fqn) -> AllowlistEntry, for O(1) lookup during the scan. Keyed
  -- by `matchKey` (module-qualified), not `fqn` alone -- see `matchKey`'s
  -- doc comment for why bare-`fqn` keying is unsound now that 32 more
  -- modules (many declaring an unnamespaced `main`) are in scope.
  let mut byKey : Std.HashMap String AllowlistEntry := {}
  for e in allowlist do
    let entryModule := moduleNameOfPath (System.FilePath.mk e.file)
    byKey := byKey.insert (matchKey entryModule e.fqn) e

  let mut scanned := 0
  let mut gated := 0
  let mut compliant := 0
  let mut offenders : Array Offender := #[]
  let mut matchedKeys : Std.HashSet String := {}

  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if (`Gasm).isPrefixOf modName || (`Stdlib).isPrefixOf modName || (`Spikes).isPrefixOf modName then
      if let some md := env.header.moduleData[i]? then
        for name in md.constNames do
          if let some info := env.find? name then
            if isReportableKind info && !name.isInternal then
              scanned := scanned + 1
              let axs ← collectAxiomsFor env ctx name
              let gatingAxs := axs.filter (fun a => !isStandardAxiom a)
              if gatingAxs.size > 0 then
                gated := gated + 1
                let declModule := modName
                let key := matchKey declModule (toString name)
                match byKey[key]? with
                | some _ =>
                  compliant := compliant + 1
                  matchedKeys := matchedKeys.insert key
                | none =>
                  let axiomPairs := gatingAxs.map (fun a => (toString a, axiomLabel a))
                  offenders := offenders.push { declModule := declModule, declName := toString name, axioms := axiomPairs }

  -- docs/REVIEW.md §4.1.1: close the import-closure blind spot. `discovered` is
  -- the on-disk ground truth; `baselineModules` is what the single import
  -- above actually pulled in. Anything in the former but not the latter was,
  -- before this fix, silently invisible to the whole scan above.
  let enumeration ← discoverProjectModules
  let discovered := enumeration.files.map moduleNameOfPath
  let mut baselineModules : Std.HashSet Name := {}
  for m in env.allImportedModuleNames do
    baselineModules := baselineModules.insert m
  let missing := discovered.filter (fun m => !baselineModules.contains m)

  let mut coveredStandalone : Std.HashSet Name := {}
  let mut unloadable : Array (Name × String) := #[]

  -- SUBPROCESS ISOLATION (see this file's header): each `missing` module is
  -- scanned by re-invoking THIS SAME executable as a `--scan-module` worker
  -- in its own fresh OS process, one module at a time, sequentially -- never
  -- batched, never in parallel. See the header doc for why: batching would
  -- reintroduce the bare-`main` collision this whole scheme exists to avoid,
  -- and running them in-process (even one `Environment` value at a time) is
  -- exactly what exhausted memory on CI's hosted runners.
  let selfExe ← IO.appPath
  let cwd ← IO.currentDir
  let concurrency ← defaultScanConcurrency
  let workerResults ← runWorkerPool missing concurrency fun target => do
    let payloadRes ← spawnAndGetResultPayload selfExe cwd #["--scan-module", toString target]
    pure (target, payloadRes)

  for (target, payloadRes) in workerResults do
    match payloadRes with
    | .error spawnErr =>
      unloadable := unloadable.push (target, spawnErr)
    | .ok payload =>
      match parseWorkerResult payload with
      | .error parseErr =>
        unloadable := unloadable.push (target, s!"malformed scan subprocess result: {parseErr}")
      | .ok (.loadFailed loadErr) =>
        unloadable := unloadable.push (target, loadErr)
      | .ok (.scanned scannedN gatedItems) =>
        coveredStandalone := coveredStandalone.insert target
        scanned := scanned + scannedN
        for (declS, axPairs) in gatedItems do
          gated := gated + 1
          let key := matchKey target declS
          match byKey[key]? with
          | some _ =>
            compliant := compliant + 1
            matchedKeys := matchedKeys.insert key
          | none =>
            offenders := offenders.push { declModule := target, declName := declS, axioms := axPairs }

  -- `axiom-only` entries exist purely for this tool (no source-text
  -- occurrence will ever back them); one that matched NOTHING in this scan
  -- is a stale pre-authorization of a name that turned out not to need it
  -- (or never did) -- a hard failure, not a silent no-op.
  let staleAxiomOnly := allowlist.filter (fun e =>
    e.category == "axiom-only" &&
    !matchedKeys.contains (matchKey (moduleNameOfPath (System.FilePath.mk e.file)) e.fqn))

  let elapsedMs := (← IO.monoMsNow) - startTime

  -- `baselineModules` is EVERY module the baseline import pulled in
  -- transitively (Lean core + std included, thousands of entries) -- not a
  -- module count comparable to the 170-module disk headline. The
  -- project-scoped subset of it is what belongs in that comparison.
  let baselineProjectCount := (discovered.filter (fun m => baselineModules.contains m)).size

  IO.println ""
  IO.println "--- MODULE COVERAGE (docs/REVIEW.md §4.1.1) ---"
  IO.println s!"[*] {discovered.size} tracked project module(s) under {projectRootDirs} are built by a"
  IO.println s!"    declared lakefile.toml target ({enumeration.libRoots} [[lean_lib]] root(s), \
{enumeration.exeRoots} [[lean_exe]] root(s))."
  IO.println s!"[*] {baselineProjectCount} reachable via the baseline Gasm/Stdlib/Spikes import graph;"
  IO.println s!"    {coveredStandalone.size} more loaded standalone to close the blind spot."
  IO.println s!"[*] Total in scope: {baselineProjectCount + coveredStandalone.size} / {discovered.size} in the build closure."
  -- A tracked project module NO declared target reaches is not this gate's to
  -- report as a failure: `lake build` never compiles it, so no `.olean` exists
  -- to scan and an exit 1 here would say nothing about why. It IS a real
  -- defect, and `scripts/check_orphan_modules.py` is the gate that owns it --
  -- naming the file, its umbrella, and the exact `import` line to add.
  if !enumeration.unbuilt.isEmpty then
    IO.println ""
    IO.println s!"[*] {enumeration.unbuilt.size} tracked project module(s) are reached by NO declared"
    IO.println "    lakefile.toml root, so nothing compiles them and this gate cannot scan them:"
    for p in enumeration.unbuilt do
      IO.println s!"    - {p}"
    IO.println "    This is NOT reported as a failure here -- `python scripts/check_orphan_modules.py`"
    IO.println "    is the gate that owns this defect class and names the exact fix for each."

  IO.println ""
  IO.println "--- SCAN RESULT ---"
  IO.println s!"[*] Scanned {scanned} reportable project declaration(s) (scoped by originating module)."
  IO.println s!"[*] {gated} depend on a non-standard axiom ({compliant} allowlisted, {offenders.size} NOT)."

  let mut failed := false

  -- lakefile.toml and the tracked tree disagreeing about what exists (an
  -- unparseable target, a declared root with no file) is a hard failure: it
  -- would otherwise shrink the build closure below and silently narrow this
  -- gate's scope, which is the one failure mode a coverage gate must not have.
  if !enumeration.errors.isEmpty then
    failed := true
    IO.println ""
    IO.println s!"[!] FAILED: {enumeration.errors.size} lakefile.toml build-root error(s) -- the"
    IO.println "    declared targets and the tracked tree disagree about what exists:"
    for e in enumeration.errors do
      IO.println s!"    - {e}"

  -- Ground truth (`discovered`, the tracked build closure) says these
  -- modules exist; neither the baseline import nor a standalone import of
  -- each could load them (almost certainly: no `lean_lib`/`lean_exe` root
  -- reaches them, so `lake build` never produced a `.olean` for them at
  -- all). This IS the blind spot Law 10 must not have -- a hard failure,
  -- not a silent skip. Run `lake build` (the whole project, or at least
  -- whichever target roots at the listed module) before re-running this gate.
  if !unloadable.isEmpty then
    failed := true
    IO.println ""
    IO.println s!"[!] FAILED: {unloadable.size} module(s) found on disk but could not be loaded"
    IO.println "    into any Environment (baseline or standalone) -- a blind spot this gate"
    IO.println "    refuses to silently ignore. Build the project (`lake build`) first:"
    for (m, err) in unloadable do
      IO.println s!"    - {m}: {err}"

  if offenders.size > 0 then
    failed := true
    IO.println ""
    IO.println s!"[!] FAILED: {offenders.size} declaration(s) depend on an axiom outside"
    IO.println "    {propext, Classical.choice, Quot.sound} with no matching gate_allowlist.txt"
    IO.println "    entry (matched by module-qualified fully-qualified name):"
    for o in offenders do
      let axiomStrs := o.axioms.toList.map (fun (a, lbl) => s!"{a} [{lbl}]")
      IO.println s!"    - {o.declModule}::{o.declName} -- axiom(s): {String.intercalate ", " axiomStrs}"

  if !staleAxiomOnly.isEmpty then
    failed := true
    IO.println ""
    IO.println s!"[!] FAILED: {staleAxiomOnly.length} `axiom-only` allowlist entr(y/ies) matched no"
    IO.println "    gated declaration in this scan (stale pre-authorization; prune or fix the fqn):"
    for e in staleAxiomOnly do
      IO.println s!"    - gate_allowlist.txt:{e.lineNum} {e.file}::{e.declName}::{e.fqn}"

  if !failed then
    IO.println "[+] Every non-standard-axiom-dependent declaration in scope is allowlisted,"
    IO.println "    and every `axiom-only` entry matched a real finding."

  IO.println ""
  IO.println s!"[*] Wall time: {elapsedMs}ms (includes importing Gasm/Stdlib/Spikes)."
  IO.println sepLine
  return if failed then 1 else 0

/-- CLI entry point. `--scan-module <dotted name>` is an internal, undocumented
mode: it is how `runGate` re-invokes THIS SAME executable as a standalone-scan
worker subprocess (see the header doc's SUBPROCESS ISOLATION section) and is
never meant to be typed by a human. Any other argument list (including none)
runs the gate itself, exactly as before this fix. -/
/- REF: docs/REVIEW.md#law-10-kernel-checked-gates-the-nativedecide-restriction-exhaustive-finite-domains-only -/
def main (args : List String) : IO UInt32 :=
  match args with
  | ["--scan-module", modStr] => runScanWorker (nameOfDotted modStr)
  | _ => runGate
