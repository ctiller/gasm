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
coverage blind spot the same way: `discoverProjectModules` walks Gasm/Stdlib/
Spikes ON DISK to find every project module, the baseline `importModules
#[Gasm, Stdlib, Spikes]` only reaches a subset of them, and each module NOT
in that subset must still be scanned somehow. Both tools import each such
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
Similarly, `discoverProjectModules`, `isProjectModule`, `isExactlyModule`,
and friends remain independently defined in each tool (they predate this
file, mirrored intentionally per each tool's own header) -- extracting those
too was judged not worth the extra churn against Tools/CheckGatesAxioms.lean,
an already CI-verified gate, for this task's actual scope.

`resultMarker`, `setupSearchPath`, and `nameOfDotted` are included alongside
`spawnAndGetResultPayload` because they are the other pieces every
`--scan-module` worker needs and every parent's spawn loop needs, and were
themselves byte-identical duplicates between the two tools' worker/parent
halves before this file existed.
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
