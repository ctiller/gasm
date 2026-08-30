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
Tools/GateSubprocess.lean - shared per-module standalone-scan subprocess protocol

WHY THIS FILE EXISTS. Tools/CheckGatesAxioms.lean (Law 10) and
Tools/CheckRefsCoverage.lean (Law 1/3) both close the identical TC15 module-
coverage blind spot the same way: `discoverProjectModules` enumerates every
tracked Gasm/Stdlib/Spikes module the build compiles (`enumerateProjectModules`
below), the baseline `importModules #[Gasm, Stdlib, Spikes]` only reaches a
subset of them, and each module NOT in that subset must still be scanned
somehow. Both tools import each such
module standalone, and -- this is the part this file exists for -- both do
it via ONE FRESH OS PROCESS PER MODULE (this same executable, re-invoked as
`--scan-module <dotted name>`), never a fresh `Environment` value inside the
existing long-lived process. See Tools/CheckGatesAxioms.lean's header
("SUBPROCESS ISOLATION") for the full rationale of why a process boundary
(not just a fresh `Environment`) is required: many of these modules declare
a bare top-level `def main` (a `lean_exe` root's process entry point, per
the compiler's own hardcoded `hasMainFn` lookup), so two of them can never
share one `Environment`; and giving each its own `Environment` *value* in one
process does not bound peak memory the way it looks like it should -- that
was CI's actual failure mode (Windows: `Init/Prelude.olean` unreadable
partway through the loop; Linux: job killed by the runner) before
CheckGatesAxioms.lean's fix, and (TC15/T2-equivalent for Law 1/3) exactly
what Tools/CheckRefsCoverage.lean's own in-process loop was still doing
until this file's introduction -- confirmed empirically: a contamination-
checked measurement (`Get-CimInstance` filtered to this process's own tree)
of the pre-fix `check_refs_coverage.exe` peaked at ~41GB working set in a
single process scanning the same 33 standalone modules.

WHAT IS SHARED HERE, AND WHAT DELIBERATELY IS NOT. Only the generic
"spawn one worker subprocess and hand back its one `GASM_SCAN_RESULT` line,
or a description of why there wasn't one" step is shared -- the actual JSON
SCHEMA each tool's worker emits (axiom-gating info for Law 10; declaration-
candidate info for Law 1/3) is entirely tool-specific and stays owned by
each tool's own `WorkerResult`-shaped type and parser. Sharing the schema
too would force one tool's payload shape onto the other for no benefit; what
was genuinely duplicated -- byte-for-byte, before this file existed -- was
the spawn/capture/error-classification plumbing itself, which is what a
project's Law 12 ("duplicated-but-unlinked logic is a defect") is about.
Similarly, `isProjectModule`, `isExactlyModule`, and friends remain
independently defined in each tool (they predate this file, mirrored
intentionally per each tool's own header) -- extracting those too was judged
not worth the extra churn against Tools/CheckGatesAxioms.lean, an already
CI-verified gate, for that task's actual scope. `discoverProjectModules` was
in that list until the enumeration half of it moved here: the two copies had
independently drifted into the same filesystem-walk defect, which is exactly
the Law 12 case ("duplicated-but-unlinked logic is a defect") this file
exists for. Each tool still owns its own `discoverProjectModules`, since the
two need different return shapes (`Name` vs `Name × FilePath`), but both now
get their file list from `enumerateProjectModules` here.

`resultMarker`, `setupSearchPath`, and `nameOfDotted` are included alongside
`spawnAndGetResultPayload` because they are the other pieces every
`--scan-module` worker needs and every parent's spawn loop needs, and were
themselves byte-identical duplicates between the two tools' worker/parent
halves before this file existed.

MODULE ENUMERATION IS ALSO SHARED NOW (`enumerateProjectModules`, below).
Both tools' `discoverProjectModules` used to call
`System.FilePath.walkDir` -- and that, not the subprocess plumbing, turned
out to be the duplicated defect. See that function's own doc comment for why
enumeration is `git ls-files` and never a filesystem walk.
-/
import Lean

open Lean

/-- Appends the project's own build output to the Lean search path. A direct
binary invocation (bypassing `lake exe`, which sets `LEAN_PATH` itself --
including when a gate tool re-invokes itself as a `--scan-module` worker
subprocess, since that re-invocation is necessarily direct) would otherwise
fail to find Gasm/Stdlib/Spikes' oleans. Shared so every gate tool's main
run and every worker subprocess resolve the search path identically. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def setupSearchPath : IO Unit := do
  initSearchPath (← findSysroot)
  let projectLibDir : System.FilePath := "." / ".lake" / "build" / "lib" / "lean"
  if ← projectLibDir.pathExists then
    let sp ← searchPathRef.get
    searchPathRef.set (sp ++ [projectLibDir])

/-- Turns a module's dotted `Name.toString` form (e.g.
`"Spikes.Spike1Hello.Windows.Emit"`) back into a `Name`, the same
`foldl Name.mkStr` construction module-path-to-`Name` conversion uses
elsewhere. Used only to turn a `--scan-module <name>` CLI argument back into
the `Name` `importModules` needs -- never on an arbitrary declaration name,
so the (harmless for module names, which are never `.num`-shaped) inability
to reconstruct numeric `Name` components doesn't matter here. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def nameOfDotted (s : String) : Name :=
  (s.splitOn ".").foldl Name.mkStr Name.anonymous

/-- Marker line prefix a `--scan-module` worker process prints its one JSON
result line under, so the parent can find it even if OTHER stdout noise
(warnings, etc.) happened to be interleaved. Shared literally so the two
tools' parent/worker halves can never drift apart on the marker string. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def resultMarker : String := "GASM_SCAN_RESULT "

/-- Spawns `selfExe` (this same executable, re-invoked) with `args` in `cwd`,
and hands back either the raw `GASM_SCAN_RESULT` JSON payload (everything
after the marker, from the LAST such line in stdout -- tolerating other
stdout noise) or a human-readable description of why there wasn't one.
Always exits with `Except.ok` for a subprocess that ran to completion and
printed a parseable result line; every other case -- the OS could not even
spawn the process, or it exited without printing a recognizable result line
(crashed, was killed, or emitted nothing/garbage) -- is folded into
`Except.error` with an explanatory message, because both are exactly the
kind of blind spot the calling gate refuses to hide (see each tool's own
`unloadable`/`unloadable`-equivalent handling of this result). Deliberately
does NOT parse the payload itself -- that JSON schema is tool-specific (see
this file's header) and stays owned by the caller. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def spawnAndGetResultPayload (selfExe : System.FilePath) (cwd : System.FilePath)
    (args : Array String) : IO (Except String String) := do
  try
    let out ← IO.Process.output { cmd := selfExe.toString, args := args, cwd := some cwd }
    let resultLines := (out.stdout.splitOn "\n").filter (·.startsWith resultMarker)
    match resultLines.getLast? with
    | none =>
      pure (Except.error
        s!"scan subprocess exited {out.exitCode} without a result line (stderr: {out.stderr.trimAscii})")
    | some line =>
      pure (Except.ok ((line.drop resultMarker.length).toString))
  catch e =>
    pure (Except.error s!"failed to spawn scan subprocess: {e.toString}")

/-- Every TRACKED `.lean` file in the repository, as repo-root-relative,
forward-slash paths, exactly as `git ls-files` prints them.

ENUMERATION IS `git ls-files`, NEVER A FILESYSTEM WALK. This is a load-bearing
design property shared with `scripts/check_orphan_modules.py` (see that
script's own docstring for the fuller argument), not a convenience:

1. TRACKED-ONLY IS THE CORRECT SEMANTICS. What both gates that call this are
   actually asserting is a property of the tree CI checks out. A *committed*
   `.lean` with no `.olean` is exactly the blind spot they refuse to hide (a
   reviewed, unbuilt, therefore unverified module -- docs/REVIEW.md §4.1.1). An
   *untracked* `.lean` is an agent mid-edit: not yet claimed to be anything,
   and never present in any CI checkout.

   This distinction is not hypothetical. Both tools walked the filesystem
   until this fix, and on 2026-08-28 `lake exe check_gates_axioms` returned
   exit 1 and exit 0 roughly an hour apart on the same code, because
   `Stdlib/Zlib/CanonicalTableSpec.lean` was one agent's untracked
   work-in-progress during the first run and committed by the second. Both
   runs were correct about what they measured; they measured different trees.
   The failure named an unloadable module rather than the real cause, so the
   reader chases the wrong thing -- and `docs/REVIEW.md` Law 13 records what an unexplained
   red costs: it trains people to stop reading failures.

2. Several agents write to this tree concurrently. A filesystem walk makes any
   one of them's uncommitted scratch file everybody else's red build.

3. This repository contains nested git worktrees under `.claude/worktrees/`,
   each a full copy of the tree. A recursive walk sees every file several
   times over; that previously produced 86 phantom CI failures.

NARROWING ENUMERATION IS NOT WEAKENING THE CHECK. A *tracked* module with no
loadable `.olean` still hard-fails at the call site (both tools' `unloadable`
handling) -- that is TC15/T2 and it stays load-bearing. Only the set of files
considered changes, from "whatever is on disk right now" to "what is
committed".

FAIL-CLOSED: a `git` that cannot be run, a non-zero `git ls-files`, or an
empty result all throw rather than returning `#[]`. An empty enumeration
would make the callers' module-coverage check vacuously green, which is the
one outcome a coverage gate must never produce silently. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def trackedLeanFiles : IO (Array String) := do
  let out ←
    try
      IO.Process.output { cmd := "git", args := #["ls-files", "-z", "--", "*.lean"] }
    catch e =>
      throw (IO.userError s!"could not run `git ls-files` to enumerate project modules: {e.toString}\n\
        This gate enumerates the TRACKED tree (the one CI checks out) and deliberately has no \
        filesystem-walk fallback -- a walk goes red on any agent's uncommitted work-in-progress. \
        Run it from the repo root of a git checkout, with `git` on PATH.")
  if out.exitCode != 0 then
    throw (IO.userError s!"`git ls-files` exited {out.exitCode} while enumerating project modules: {out.stderr}")
  -- `-z` NUL-delimits, so a path containing a quote/space/non-ASCII byte is
  -- never shell-quoted or mangled the way `git ls-files`'s default output
  -- would be. Paths come back forward-slash-separated on every platform;
  -- `System.FilePath.components` normalizes to the platform separator before
  -- splitting, so callers' path->module-name conversion is unaffected.
  let selected := (out.stdout.split (· == '\x00')).toStringList.filter (·.endsWith ".lean")
  if selected.isEmpty then
    throw (IO.userError s!"`git ls-files` reported no tracked .lean files at all -- \
      refusing to report vacuously complete module coverage. Run this gate from the repo root.")
  return selected.toArray

/-- `Gasm/Zlib/Spec.lean` -> `Gasm.Zlib.Spec`. Operates on the forward-slash,
repo-relative form `trackedLeanFiles` returns, so it is platform-independent
(unlike a `System.FilePath.components` round-trip, which normalizes to the
host separator first). Lake's own path<->module mapping. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def dottedModuleOfRelPath (rel : String) : String :=
  (rel.dropEnd ".lean".length).toString.replace "/" "."

/-- One build root declared by `lakefile.toml`, plus which target declared it. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
structure LakeBuildRoot where
  module     : String
  targetKind : String   -- "lean_lib" | "lean_exe"
  targetName : String
deriving Inhabited

/-- Every double-quoted string in a TOML scalar-or-array right-hand side. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def tomlQuotedStrings (s : String) : List String := Id.run do
  let mut out : List String := []
  let mut idx := 0
  for part in s.splitOn "\"" do
    if idx % 2 == 1 then
      out := out ++ [part]
    idx := idx + 1
  return out

/-- One `[[lean_lib]]`/`[[lean_exe]]` array-of-tables entry, as raw key -> raw-RHS
pairs. Deliberately a small hand parser rather than a TOML library: this repo's
`lakefile.toml` is flat and comment-heavy, and the only keys ever read back are
`name`, `roots`, and `root`. Mirrors `scripts/check_orphan_modules.py`'s
`_parse_tables` for the same reasons it gives. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
structure LakeRawTable where
  kind : String
  keys : Array (String × String)
deriving Inhabited

/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def parseLakeTables (text : String) : Array LakeRawTable := Id.run do
  let mut out : Array LakeRawTable := #[]
  let mut cur : Option LakeRawTable := none
  for rawLine in (text.replace "\r\n" "\n").splitOn "\n" do
    let line := rawLine.trimAscii.toString
    if line.startsWith "#" then
      continue
    if line == "[[lean_lib]]" || line == "[[lean_exe]]" then
      if let some t := cur then out := out.push t
      cur := some { kind := if line == "[[lean_lib]]" then "lean_lib" else "lean_exe", keys := #[] }
      continue
    if line.startsWith "[" then
      -- Any other table header (including `[[lean_exe]]`-shaped ones this tool
      -- does not model) ends the current table rather than silently absorbing
      -- its keys.
      if let some t := cur then out := out.push t
      cur := none
      continue
    match cur with
    | none => continue
    | some t =>
      match line.splitOn "=" with
      | k :: v :: rest =>
        let key := k.trimAscii.toString
        if !key.isEmpty then
          cur := some { t with keys := t.keys.push (key, String.intercalate "=" (v :: rest)) }
      | _ => continue
  if let some t := cur then out := out.push t
  return out

/-- Parses `lakefile.toml`'s `[[lean_lib]] roots` and `[[lean_exe]] root`
declarations into the full set of build roots.

NOTHING HERE IS HARDCODED, on purpose, and that is the whole point of this
function: the two gates that call it used to model the build as exactly three
`[[lean_lib]]` umbrellas (`Gasm`/`Stdlib`/`Spikes`) and nothing else. That model
is wrong in both directions. It understates what `lake build` compiles -- a
`[[lean_exe]]` root is a real build root, and Lake produces its `.olean` exactly
as it does for a library umbrella -- so every `Spikes/*/Emit.lean`,
`Spikes/*/Test.lean` and fuzzer CLI looked to those gates like a module outside
any declared target rather than what it is, the root of one. And a hardcoded root
list is this defect one level up: declare a new `[[lean_lib]]` and its whole
subtree would be silently unmodelled forever. Same derivation, same reasons, as
`scripts/check_orphan_modules.py`'s `derive_build_roots`. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def deriveLakeBuildRoots (text : String) : Array LakeBuildRoot × Array String := Id.run do
  let mut roots : Array LakeBuildRoot := #[]
  let mut errors : Array String := #[]
  for t in parseLakeTables text do
    let get (k : String) : Option String := (t.keys.find? (·.1 == k)).map (·.2)
    let name := ((get "name").bind (fun v => (tomlQuotedStrings v).head?)).getD "<unnamed>"
    let rootKey := if t.kind == "lean_lib" then "roots" else "root"
    let declared := ((get rootKey).map tomlQuotedStrings).getD []
    if declared.isEmpty then
      errors := errors.push
        s!"lakefile.toml: [[{t.kind}]] '{name}' declares no parseable `{rootKey}`"
    for m in declared do
      roots := roots.push { module := m, targetKind := t.kind, targetName := name }
  if roots.isEmpty then
    errors := errors.push
      "lakefile.toml: no [[lean_lib]]/[[lean_exe]] roots parsed at all -- refusing to model an \
       empty build (with no roots every module would look unbuilt, and this gate's module-coverage \
       check would be vacuous)"
  return (roots, errors)

/-- The modules `rel` imports.

Lean requires the import section to precede every other command in a file, so
this walks the header and STOPS at the first line that is neither blank, nor a
comment, nor an `import`/`prelude`. That bound is what keeps prose out: this tree
contains doc-comment lines beginning with the word "import" at column 0 (this
very file's neighbours do), and an unbounded sweep would invent import edges out
of them. Block comments (`/- ... -/`, including the Apache-2.0 header every file
opens with) are tracked by nesting depth. Mirrors
`scripts/check_orphan_modules.py`'s `imports_of` exactly. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def importsOfFile (rel : String) : IO (Except String (Array String)) := do
  -- A tracked file absent from the WORKING TREE (deleted but not committed --
  -- routine on a tree several agents write to at once) must not take this gate
  -- down with an uncaught `no such file or directory`. That is precisely the
  -- unexplained red this whole enumeration change exists to remove, and it was
  -- found by this function's own control vector. The index and the working tree
  -- disagreeing about what exists is a real, reportable condition: the caller
  -- folds it into `errors`, which fails closed with the file named.
  let textRes ←
    try
      pure (Except.ok (← IO.FS.readFile (System.FilePath.mk rel)))
    catch e =>
      pure (Except.error e.toString)
  let text ←
    match textRes with
    | .error msg =>
      return .error s!"tracked file '{rel}' is in the index but could not be read from the         working tree ({msg}). This gate derives the build closure from working-tree `import`         edges, so it refuses to guess: commit the deletion, or restore the file."
    | .ok t => pure t
  let mut found : Array String := #[]
  -- `Int`, not `Nat`: a stray `-/` would truncate a `Nat` at zero and silently
  -- shift every subsequent line's comment state.
  let mut depth : Int := 0
  for rawLine in (text.replace "\r\n" "\n").splitOn "\n" do
    let line := rawLine.trimAscii.toString
    let opens : Int := ((line.splitOn "/-").length - 1 : Nat)
    let closes : Int := ((line.splitOn "-/").length - 1 : Nat)
    if depth > 0 then
      depth := depth + opens - closes
      continue
    if line.isEmpty || line.startsWith "--" then
      continue
    if line.startsWith "/-" then
      depth := depth + opens - closes
      continue
    if line == "prelude" then
      continue
    if line.startsWith "import " then
      let rest := (line.drop "import ".length).trimAscii.toString
      let rest := if rest.startsWith "all " then (rest.drop 4).trimAscii.toString else rest
      if !rest.isEmpty && rest.all (fun c => c.isAlphanum || c == '_' || c == '.') then
        found := found.push rest
      continue
    break
  return .ok found

/-- What `enumerateProjectModules` computes: the project modules a declared
`lakefile.toml` target actually builds, and the ones it does not. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
structure ProjectModuleEnumeration where
  /-- Tracked project `.lean` files (under the caller's source roots) that are
  reachable, transitively, from some `lakefile.toml` build root -- i.e. exactly
  the ones `lake build` compiles and therefore the ones this gate can and must
  scan. Repo-relative, forward-slash. -/
  files       : Array System.FilePath
  /-- Tracked project modules reachable from NO declared root. `lake build`
  never compiles these, so no `.olean` exists to scan and the calling gate
  cannot say anything about them -- and must not pretend a bare exit 1 said
  something. `scripts/check_orphan_modules.py` owns this defect class and names
  the file, its umbrella, and the exact `import` line to add. -/
  unbuilt     : Array System.FilePath
  libRoots    : Nat
  exeRoots    : Nat
  errors      : Array String
deriving Inhabited

/-- Enumerates the project modules `lake build` actually compiles.

THE MODEL THIS REPLACES, AND WHY. Both calling gates used to take "every
project `.lean` file that exists" as the set of modules they must be able to
load, and treat any failure to load one as a hard, unexplained failure. That
model has no notion of what the build system was ever asked to compile, which
made it wrong in two directions at once:

- It counted the ~48 modules that are `[[lean_exe]]` roots (or reached only
  through one) as sitting outside every declared target, when each is the root
  of a declared target and is compiled by `lake build` like any other.
- It counted `Gasm/Targets/X86_64/RoundtripGate/DispatchExhaustive.lean` -- a
  genuine orphan that no root reaches, so nothing compiles it -- as a bare
  exit 1 with an empty substantive-violation count beside it. Two gates were
  red at once, neither naming the orphan as the cause.

The closure is therefore derived from EVERY declared target -- both
`[[lean_lib]] roots` and `[[lean_exe]] root` -- over `import` edges among
TRACKED files, which is the same model `scripts/check_orphan_modules.py` uses
and the same one docs/REVIEW.md §4.1.1 call for. Reachability is a transitive graph
walk, not a flat membership test: a module reached via an intermediate import
is correctly in scope.

This does NOT weaken the module-coverage check. Everything the build compiles
stays in `files`, and a module in `files` that loads into neither the baseline
environment nor a standalone import is still a hard failure at the call site --
that is TC15/T2 and it stays load-bearing. What changes is that a module the
build was never asked to compile is reported as such, by name, pointing at the
gate that owns it, instead of being indistinguishable from a real one.

THE ONE BEHAVIOUR CHANGE A REVIEWER MUST SIGN OFF ON. An orphan is owned by
the unconditional orphan-module gate rather than being reported opaquely by
two unrelated compiled-environment gates. It remains a hard failure, named by
the gate that can explain and repair it; no exception mechanism exists.

CONTROL VECTORS (measured against a clean committed checkout -- a git worktree,
never the shared working tree; the throwaway-`GIT_INDEX_FILE` staging technique
is `scripts/check_orphan_modules.py --self-test`'s, so the real index is never
written). These are the properties the two fixes above must jointly preserve,
and each is distinct from the others:

  pristine tree                          both gates exit 0
  UNTRACKED unbuilt module               ignored entirely; both gates exit 0
  TRACKED, imported from `Stdlib.lean`
    (so a declared root reaches it),
    no `.olean`                          both gates exit 1, naming it
                                         -- this is TC15/T2, still load-bearing
  TRACKED but imported by nothing        reported by name as unbuilt; NOT a
                                         failure, both gates exit 0
                                         -- `check_orphan_modules.py` owns it
  reverted                               both gates exit 0 again

Note the third and fourth vectors are the pair that pins the exact boundary
this function draws. "A tracked module with no `.olean` hard-fails" is true
ONLY of a module the build was asked to compile; conflating the two is what
produced the opaque red described above. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def enumerateProjectModules (sourceRoots : List String) : IO ProjectModuleEnumeration := do
  let allFiles ← trackedLeanFiles
  let mut moduleToPath : Std.HashMap String String := {}
  for rel in allFiles do
    moduleToPath := moduleToPath.insert (dottedModuleOfRelPath rel) rel

  let lakefilePath : System.FilePath := "lakefile.toml"
  if !(← lakefilePath.pathExists) then
    throw (IO.userError "lakefile.toml not found -- run this gate from the repo root.")
  let lakefileText ← IO.FS.readFile lakefilePath
  let (roots, rootErrors) := deriveLakeBuildRoots lakefileText
  let mut errors := rootErrors

  -- A declared root with no tracked file is a hard error, not a skipped root:
  -- lakefile.toml and the tree disagree about what exists, and dropping it
  -- would shrink the reachable set and manufacture "unbuilt" modules downstream.
  for r in roots do
    if !moduleToPath.contains r.module then
      errors := errors.push
        s!"lakefile.toml: [[{r.targetKind}]] '{r.targetName}' declares root module \
           '{r.module}', but no tracked file for it exists"

  -- BFS from every declared root over `import` edges among tracked files.
  let mut reached : Std.HashSet String := {}
  let mut frontier : Array String := #[]
  for r in roots do
    if moduleToPath.contains r.module && !reached.contains r.module then
      reached := reached.insert r.module
      frontier := frontier.push r.module
  while !frontier.isEmpty do
    let mut next : Array String := #[]
    for m in frontier do
      match moduleToPath[m]? with
      | none => pure ()
      | some rel =>
        match ← importsOfFile rel with
        | .error msg => errors := errors.push msg
        | .ok imports =>
          for imported in imports do
            if moduleToPath.contains imported && !reached.contains imported then
              reached := reached.insert imported
              next := next.push imported
    frontier := next

  let underSourceRoot (p : String) : Bool :=
    sourceRoots.any (fun r => p == r ++ ".lean" || p.startsWith (r ++ "/"))
  let mut files : Array System.FilePath := #[]
  let mut unbuilt : Array System.FilePath := #[]
  for rel in allFiles do
    if underSourceRoot rel then
      if reached.contains (dottedModuleOfRelPath rel) then
        files := files.push (System.FilePath.mk rel)
      else
        unbuilt := unbuilt.push (System.FilePath.mk rel)

  if files.isEmpty then
    throw (IO.userError s!"no tracked .lean file under {sourceRoots} is reachable from any \
      lakefile.toml build root -- refusing to report vacuously complete module coverage.")

  return {
    files := files, unbuilt := unbuilt,
    libRoots := (roots.filter (·.targetKind == "lean_lib")).size,
    exeRoots := (roots.filter (·.targetKind == "lean_exe")).size,
    errors := errors
  }

/-- Resolves gate subprocess concurrency from `GASM_SCAN_CONCURRENCY` env var, defaulting to 8. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
def defaultScanConcurrency : IO Nat := do
  let envVal ← IO.getEnv "GASM_SCAN_CONCURRENCY"
  pure (envVal.bind String.toNat? |>.getD 8)

/-- Bounded-concurrency worker pool running IO tasks across `items` with at most
`maxConcurrency` workers executing concurrently. Results maintain input ordering. -/
/- REF: docs/REVIEW.md#411-gate-tooling-specification -/
/- REF: docs/REVIEW.md#412-reference-coverage-tooling-specification -/
partial def runWorkerPool {α β : Type} (items : Array α) (maxConcurrency : Nat) (f : α → IO β) : IO (Array β) := do
  if items.isEmpty then
    return #[]
  let indexedItems := items.mapIdx (fun idx item => (idx, item))
  let queueRef ← IO.mkRef indexedItems.toList
  let resultsRef : IO.Ref (Array (Option β)) ← IO.mkRef (Array.replicate items.size (none : Option β))

  let rec worker : IO Unit := do
    let nextItem? ← queueRef.modifyGet fun q =>
      match q with
      | [] => (none, [])
      | x :: xs => (some x, xs)
    match nextItem? with
    | none => pure ()
    | some (idx, item) =>
      let res ← f item
      resultsRef.modify fun (arr : Array (Option β)) => arr.set! idx (some res)
      worker

  let numWorkers := min (max 1 maxConcurrency) items.size
  let tasks ← (List.range numWorkers).mapM fun _ => IO.asTask worker
  for t in tasks do
    let _ ← IO.ofExcept t.get

  let finalResults ← resultsRef.get
  let mut out := #[]
  for opt in finalResults do
    match opt with
    | some v => out := out.push v
    | none => throw (IO.userError "worker pool item missing result")
  return out

