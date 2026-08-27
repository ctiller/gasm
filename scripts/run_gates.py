#!/usr/bin/env python3
# Copyright 2026 Craig Tiller
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""
scripts/run_gates.py - gasm gate runner (TC5): the single entry point for every merge gate.

Per docs/REVIEW.md Section 4.1 ("Pillar 1: Mechanical Truth") and Section 4.4 ("Gate 1"), a
PR/merge is only eligible for semantic review once a fixed list of mechanical gates all pass.
Before this script existed, every gate was invoked by hand, per-agent, per-session -- PLAN.md's
Phase-1 tracker states the consequence bluntly: "a gate nothing invokes binds nothing." This
script is the single command that invokes all of them, every time, in the fixed order the
GATE_TABLE below declares (this order is this script's own; it is not required to match, and
does not always match, docs/REVIEW.md Section 4.1's item numbering, which is a checklist, not
an invocation sequence).

FAIL-CLOSED, NOT FAIL-SOFT (the entire point of this task, not a nice-to-have):
Every externally-invoked oracle this pipeline depends on (NASM for encoding_fuzzer, node for
wasm_fuzzer) is detected BEFORE any gate runs. If a FULL run needs an oracle that is missing,
this script ABORTS THE WHOLE RUN with a clearly labeled failure -- it never silently skips
that gate. Two prior incidents motivate this, both already fixed at the harness level (see
Gasm/Targets/X86_64/HardwareHarness.lean:309-340 and Gasm/Targets/Wasm/HostOracle.lean), but
which this *runner* must not reintroduce at the orchestration level: the x86 hardware fuzzer
and the Wasm control-flow fuzzer were each once a silent fail-open no-op when their oracle
could not be reached. "The thing that invokes the oracle checks its own control vectors" is
only half the prevention -- this runner is the other half: it refuses to let a missing oracle
quietly not-run the check that would have caught that class of bug in the first place.

--quick DOES NOT WEAKEN THIS: it is scoped to which gates are SELECTED, never to whether a
selected gate's prerequisite is enforced. Every run -- quick or full -- detects and reports
every prerequisite in NEEDED_BY (a superset spanning the whole gate table), and aborts if a
prerequisite a SELECTED gate needs is missing. A prerequisite that only a SKIPPED (--quick)
gate would have needed is never silently ignored either -- it is reported as an explicit
WAIVED entry, in both the human table and the --json output, so "no error" is never
indistinguishable from "not checked." (This closes a real finding: an earlier revision of
this script computed its `needed` set from only the selected gates, so `--quick --json` on a
machine with neither NASM nor node installed produced a fully green run with no signal
anywhere that either oracle was ever considered.)

DIRECT EXIT-CODE CAPTURE ONLY -- NEVER THROUGH A PIPE (the concrete implementation trap this
task exists to avoid): PLAN.md's "Merge train 2" retro records a self-finding that an earlier
merged-tree verification script "reported tools' exit codes through a pipe (got tail's exit)
-- fail-open reporting." Every gate below is invoked via `subprocess.run([...], shell=False)`
with a Python arg list (never a shell string, never piped through `| tee` / `| tail` / a
pager) so `proc.returncode` IS the invoked process's own exit code, full stop. A gate whose
process could not even be spawned (missing binary, OS error) is reported as ERROR, never as a
default PASS or a silently-absent row.

Modes and their exit codes:
  - Full run (default), everything in GATE_TABLE passes  -> "PASSED",         exit 0
  - Full run, something failed                            -> "FAILED",        exit 1
  - --quick run, every SELECTED gate passes                -> "PASSED_PARTIAL", exit 2
      (never "PASSED"/0 -- --quick is NOT sufficient evidence for merge sign-off, and this
      script makes that mechanically undeniable rather than a comment a reader can miss)
  - --quick run, something (selected) failed               -> "FAILED",        exit 1
  - A required prerequisite is missing                     -> "ABORTED",       exit 3
      (distinguishable from an ordinary gate failure; aborts BEFORE any gate runs)

Usage:
    python scripts/run_gates.py                  # full run (~15-25 min with builds+fuzzers)
    python scripts/run_gates.py --quick           # only the fast gates; exits 2 (PASSED_PARTIAL)
                                                   # on success, never 0 -- NOT SUFFICIENT FOR
                                                   # MERGE SIGN-OFF under any circumstance
    python scripts/run_gates.py --clean           # `lake clean` first (TCB T13, merge-train mode)
    python scripts/run_gates.py --json            # machine-parseable JSON summary on stdout;
                                                   # always includes "mode": "quick"|"full" so a
                                                   # partial run's JSON cannot be mistaken for a
                                                   # full green by a consumer that only checks
                                                   # overall_exit_code == 0
    python scripts/run_gates.py --gzip-count 100  # override gzip_fuzzer's --count (default 25)
    python scripts/run_gates.py --gate-timeout 900  # per-gate wall-clock timeout in seconds
                                                     # (default 1800 = 30 min; a hung gate is
                                                     # killed and reported as TIMEOUT, not left
                                                     # to hang the runner forever)
    python scripts/run_gates.py --self-test       # TCB T4 meta-gate fixture: plants each of 6
                                                   # known defects (sorry / unallowlisted
                                                   # native_decide / broken REF / a broken REF
                                                   # immediately preceding an anonymous instance
                                                   # (the case a regex-based checker used to
                                                   # silently drop) / duplicate heading / an
                                                   # anonymous instance with NO citation at all)
                                                   # into the real tree one at a time, asserts
                                                   # the specific gate it should trip
                                                   # goes red, reverts, and asserts green again.
                                                   # Re-runnable regression test for the gates
                                                   # themselves -- see run_self_test() below.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional

REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_TOOLCHAIN_FILE = REPO_ROOT / "lean-toolchain"
GASM_ROOT_FILE = REPO_ROOT / "Gasm.lean"

# Distinct exit codes so CI (TC6) and humans can tell these apart without re-parsing the
# human-readable table (see module docstring "Modes and their exit codes").
EXIT_OK = 0
EXIT_GATE_FAILED = 1
EXIT_PASSED_PARTIAL = 2
EXIT_PREREQ_ABORT = 3

DEFAULT_GATE_TIMEOUT_S = 1800  # 30 min; generous for wasm_fuzzer's real observed ~5-7 min


# --------------------------------------------------------------------------------------------
# Oracle / toolchain version detection (TCB T9: "node/python/nasm: no version recorded or
# asserted anywhere" -- this is where that gap closes. Every oracle's version string is both
# printed to the console AND carried into the --json summary, so a divergence in gate results
# across two machines/sessions is attributable to an environment drift, not silently
# re-litigated as a model bug.)
# --------------------------------------------------------------------------------------------

def _run_capture(cmd: List[str], cwd: Optional[Path] = None, timeout: float = 30.0):
    """Runs `cmd` directly (no shell, no pipe) and returns (returncode_or_None, combined_output).
    returncode is None only if the executable could not be launched at all (not found / OS
    error) -- that is itself a "prerequisite absent" signal, never conflated with a normal
    non-zero exit."""
    try:
        proc = subprocess.run(
            cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, timeout=timeout,
        )
        return proc.returncode, proc.stdout
    except (FileNotFoundError, OSError) as e:
        return None, str(e)
    except subprocess.TimeoutExpired as e:
        return None, f"timed out after {timeout}s: {e}"


def _extract_semver(s: Optional[str]) -> Optional[str]:
    m = re.search(r"(\d+\.\d+\.\d+)", s or "")
    return m.group(1) if m else None


def detect_python() -> Dict:
    # GzipFuzzer.lean's oracle subprocess invokes a bare "python"/"python3"/"py" command name
    # (via findPythonPath) -- detect exactly that binding, since that's what the actual gate
    # depends on, not necessarily the interpreter running this script (sys.executable).
    exe = shutil.which("python") or shutil.which("python3") or shutil.which("py")
    if not exe:
        return {"name": "python", "found": False, "path": None, "version": None,
                "detail": "no 'python'/'python3'/'py' resolvable on PATH"}
    code, out = _run_capture([exe, "--version"])
    version = (out or "").strip()
    return {"name": "python", "found": code == 0, "path": exe, "version": version,
            "detail": f"resolved to {exe}"}


def detect_lake() -> Dict:
    exe = shutil.which("lake")
    if not exe:
        return {"name": "lake", "found": False, "path": None, "version": None,
                "detail": "'lake' not found on PATH -- required for every gate this runner invokes"}
    code, out = _run_capture([exe, "--version"], cwd=REPO_ROOT)
    return {"name": "lake", "found": code == 0, "path": exe, "version": (out or "").strip(),
            "detail": f"resolved to {exe}"}


def detect_lean() -> Dict:
    """Captures `lean --version` and asserts it matches the lean-toolchain pin (TCB T9's
    'oracle environment versions unpinned' gap, applied to the Lean toolchain itself: elan
    should make these agree automatically via the lean-toolchain override, but this is the
    mechanical check that a drift is caught rather than assumed)."""
    pin_raw = LEAN_TOOLCHAIN_FILE.read_text(encoding="utf-8").strip() if LEAN_TOOLCHAIN_FILE.exists() else None
    pin_version = _extract_semver(pin_raw)
    exe = shutil.which("lean")
    if not exe:
        return {"name": "lean", "found": False, "path": None, "version": None,
                "detail": f"'lean' not found on PATH (lean-toolchain pins {pin_raw!r})",
                "pin_ok": False}
    code, out = _run_capture([exe, "--version"], cwd=REPO_ROOT)
    version_str = (out or "").strip()
    found_version = _extract_semver(version_str)
    pin_ok = pin_version is not None and found_version == pin_version
    detail = f"resolved to {exe}; lean-toolchain pins {pin_raw!r}"
    if not pin_ok:
        detail += f" -- MISMATCH: `lean --version` reports {found_version!r}, pin expects {pin_version!r}"
    return {"name": "lean", "found": (code == 0) and pin_ok, "path": exe, "version": version_str,
            "detail": detail, "pin_ok": pin_ok}


def detect_node() -> Dict:
    exe = shutil.which("node")
    if not exe:
        return {"name": "node", "found": False, "path": None, "version": None,
                "detail": "'node' not found on PATH -- required by wasm_fuzzer's host-engine "
                          "oracle (Gasm/Targets/Wasm/HostOracle.lean)"}
    code, out = _run_capture([exe, "--version"])
    return {"name": "node", "found": code == 0, "path": exe, "version": (out or "").strip(),
            "detail": f"resolved to {exe}"}


def detect_nasm() -> Dict:
    """Mirrors Gasm/Targets/X86_64/NASM.lean's `findNasmPath` resolution order (GASM_NASM
    override -> PATH -> %LOCALAPPDATA%\\bin\\NASM -> Program Files -> Program Files (x86)),
    with one deliberate divergence: if GASM_NASM is explicitly set, this does NOT fall through
    to the next candidate when it fails to invoke. `NASM.lean`'s own `findNasmPath` returns an
    explicit override verbatim without ever invoking it, so a bogus GASM_NASM there would
    silently make the Lean tool use a broken path while THIS detector, if it fell through to a
    PATH/standard-location candidate instead, would report a *different, working* NASM's
    version as if it were the one the gate will actually use -- a false provenance record,
    exactly the class of gap TCB T9 exists to close. An explicit, broken override is reported
    as NOT FOUND (never silently substituted), which is also what actually happens when
    encoding_fuzzer runs.
    Captures and returns the real version banner (TCB T9: NASM.lean fetches `nasm -v` and
    discards the banner today -- this is where that banner actually gets recorded)."""
    override = os.environ.get("GASM_NASM")
    if override:
        code, out = _run_capture([override, "-v"])
        if code == 0:
            banner = (out or "").strip().splitlines()[0] if out else ""
            return {"name": "nasm", "found": True, "path": override, "version": banner,
                    "detail": f"resolved to {override} (via GASM_NASM override)"}
        return {"name": "nasm", "found": False, "path": None, "version": None,
                "detail": f"GASM_NASM={override!r} is set but did not respond to `-v` "
                          f"(returncode={code}); NOT falling through to another candidate -- "
                          "an explicit, broken override must abort, not silently substitute a "
                          "different NASM than the one the gate would actually be told to use."}

    candidates: List[str] = []
    which_nasm = shutil.which("nasm") or shutil.which("nasm.exe")
    if which_nasm:
        candidates.append(which_nasm)
    localappdata = os.environ.get("LOCALAPPDATA")
    if localappdata:
        candidates.append(str(Path(localappdata) / "bin" / "NASM" / "nasm.exe"))
    candidates.append(r"C:\Program Files\NASM\nasm.exe")
    candidates.append(r"C:\Program Files (x86)\NASM\nasm.exe")

    tried = []
    for cand in candidates:
        if cand in tried:
            continue
        tried.append(cand)
        code, out = _run_capture([cand, "-v"])
        if code == 0:
            banner = (out or "").strip().splitlines()[0] if out else ""
            return {"name": "nasm", "found": True, "path": cand, "version": banner,
                    "detail": f"resolved to {cand}"}
    return {"name": "nasm", "found": False, "path": None, "version": None,
            "detail": "NASM not found on PATH, GASM_NASM, or any standard install location "
                      f"(tried: {', '.join(tried) if tried else '<none>'}); required by "
                      "encoding_fuzzer's differential oracle (Gasm/Targets/X86_64/NASM.lean). "
                      "Install NASM or set GASM_NASM to its full path."}


PREREQ_DETECTORS = {
    "python": detect_python,
    "lake": detect_lake,
    "lean": detect_lean,
    "node": detect_node,
    "nasm": detect_nasm,
}


def detect_all_prereqs() -> Dict[str, Dict]:
    return {name: fn() for name, fn in PREREQ_DETECTORS.items()}


# --------------------------------------------------------------------------------------------
# Gate table. Every gate declares the prerequisite TOOL NAMES it needs (must be keys of
# PREREQ_DETECTORS) -- this is the single, load-bearing list the abort decision reads. There is
# deliberately no separate "requires" field that duplicates it: an earlier revision of this
# script had both, only one of which was ever actually read, which is its own kind of
# unenforced-prerequisite trap for a future edit that updates one and not the other.
# --------------------------------------------------------------------------------------------

def build_gate_table(gzip_count: int) -> List[Dict]:
    lake = shutil.which("lake") or "lake"
    py = shutil.which("python") or shutil.which("python3") or shutil.which("py") or "python"
    return [
        {"key": "lake_build", "desc": "lake build",
         "long": "all defaultTargets compile cleanly (a stray `sorry` is only a compiler "
                 "warning here -- lakefile.toml sets no warningAsError -- the actual "
                 "zero-sorry/zero-unauthorized-axiom enforcement is check_gates_axioms below)",
         "cmd": [lake, "build"], "slow": False, "tools": ["lean"]},
        {"key": "check_refs", "desc": "python scripts/check_refs.py",
         "long": "Law 3: citation validity (no Lean parsing -- see docs/REVIEW.md #4.1.2)",
         "cmd": [py, "scripts/check_refs.py"], "slow": False, "tools": ["python"]},
        {"key": "check_refs_coverage", "desc": "lake exe check_refs_coverage",
         "long": "Law 1 LOAD-BEARING declaration-coverage gate -- walks the compiled environment, "
                 "not source text, so no declaration form (anonymous instance, abbrev, initialize, "
                 "...) can hide from it; run from repo root, building it is not running it",
         "cmd": [lake, "exe", "check_refs_coverage"], "slow": False, "tools": ["lean"]},
        {"key": "check_gates", "desc": "python scripts/check_gates.py",
         "long": "Law 10 fast source-level pre-check (defense-in-depth, not the load-bearing gate)",
         "cmd": [py, "scripts/check_gates.py"], "slow": False, "tools": ["python"]},
        {"key": "check_gates_axioms", "desc": "lake exe check_gates_axioms",
         "long": "Law 10 LOAD-BEARING axiom gate -- run from repo root; building it is not running it",
         "cmd": [lake, "exe", "check_gates_axioms"], "slow": False, "tools": ["lean"]},
        {"key": "check_references_offline", "desc": "python scripts/check_references.py --offline",
         "long": "Law 6: reference registry integrity -- every REF: <slug>#<anchor> citation is "
                 "registered in references.json, its cache file's freshly-recomputed sha256 matches "
                 "the recorded pin, and its anchor resolves. Network-free; requires a warm local "
                 "cache at .cache/references/ (populate first with --refresh --slug/--corpus/--all).",
         "cmd": [py, "scripts/check_references.py", "--offline"], "slow": False, "tools": ["python"]},
        {"key": "check_publishable", "desc": "python scripts/check_publishable.py",
         "long": "Pre-flatten publishability gate: zero third-party prose under references/ (owner "
                 "ruling), zero dangling REF: citations into it, zero machine-specific paths, "
                 "Apache-2.0 header coverage (delegates to check_licenses.py)",
         "cmd": [py, "scripts/check_publishable.py"], "slow": False, "tools": ["python"]},
        {"key": "check_licenses", "desc": "python scripts/check_licenses.py",
         "long": "REVIEW.md Sec 4.1 item 5: Apache-2.0 header compliance -- required by Sec 4.1 and "
                 "Sec 4.4 Gate 1, but was never wired into this runner (found and fixed during the "
                 "D23/decision-record-integrity remediation pass; the same 'a gate that exists but "
                 "never runs protects nothing' lesson this project has already learned once for "
                 "check_publishable.py/check_references.py)",
         "cmd": [py, "scripts/check_licenses.py"], "slow": False, "tools": ["python"]},
        {"key": "check_record", "desc": "python scripts/check_record.py",
         "long": "D23/decision-record integrity gate: PLAN.md/docs/adr//docs/tasks/ are the sole "
                 "surviving decision history post-flatten (0035)",
         "cmd": [py, "scripts/check_record.py"], "slow": False, "tools": ["python"]},
        {"key": "check_doc_facade", "desc": "python scripts/check_doc_facade.py",
         "long": "TC21: doc-facade linter -- detects docs/*.md (excluding docs/adr/, docs/tasks/) "
                 "asserting enforcement the tree does not provide: a MUST/is-implemented-shaped "
                 "claim citing a Lean identifier absent from the whole .lean tree, or "
                 "docs/REVIEW.md naming a script/lake-exe gate that is missing or not wired into "
                 "this table (the check_licenses.py-was-never-wired-in shape, found this week)",
         "cmd": [py, "scripts/check_doc_facade.py"], "slow": False, "tools": ["python"]},
        {"key": "test_roundtrip", "desc": "lake exe test_roundtrip",
         "long": "x86-64 decode/encode roundtrip suite (registry gate's ~21 native_decide shards "
                 "are compiled into lake build itself, not re-invoked here)",
         "cmd": [lake, "exe", "test_roundtrip"], "slow": False, "tools": ["lean"]},
        # --- Spike / Stdlib CLI test suites (REVIEW.md Sec 4.1 item 9): defaultTargets builds
        # these; building is not running them (the exact distinction item 4 draws for
        # check_gates_axioms). All fast (seconds), all take no CLI args.
        #
        # Spike 1/2's Windows `Test.lean` does NOT self-generate its binary if missing (unlike
        # Spike 3/4/5's, and unlike every Wasm `Test.lean`) -- it fails with "Could not execute
        # .\hello.exe ... Make sure to run 'lake exe spike1_hello_windows' first", which is
        # exactly the fail-open-shaped trap this task's own docstring warns about: wiring in
        # `test_spike1_windows` without also running its emitter first would have reported a
        # spurious FAIL for a gate this script itself made unrunnable, not a real defect. So the
        # emit step is an explicit, separate gate immediately before its test, not folded
        # silently into the test's own command.
        {"key": "spike1_hello_windows", "desc": "lake exe spike1_hello_windows",
         "long": "emits hello.exe -- prerequisite artifact for test_spike1_windows below",
         "cmd": [lake, "exe", "spike1_hello_windows"], "slow": False, "tools": ["lean"]},
        {"key": "test_spike1_windows", "desc": "lake exe test_spike1_windows",
         "long": "Spike 1 (Hello World) Windows target test",
         "cmd": [lake, "exe", "test_spike1_windows"], "slow": False, "tools": ["lean"]},
        {"key": "test_spike1_wasm", "desc": "lake exe test_spike1_wasm",
         "long": "Spike 1 (Hello World) Wasm target test (in-Lean trace + host runtime; "
                 "exit 2 = no host Wasm runner found, per Law 13(4))",
         "cmd": [lake, "exe", "test_spike1_wasm"], "slow": False, "tools": ["lean"]},
        {"key": "spike2_fibonacci_windows", "desc": "lake exe spike2_fibonacci_windows",
         "long": "emits fib.exe -- prerequisite artifact for test_spike2_windows below",
         "cmd": [lake, "exe", "spike2_fibonacci_windows"], "slow": False, "tools": ["lean"]},
        {"key": "test_spike2_windows", "desc": "lake exe test_spike2_windows",
         "long": "Spike 2 (Fibonacci) Windows target test",
         "cmd": [lake, "exe", "test_spike2_windows"], "slow": False, "tools": ["lean"]},
        {"key": "test_spike2_wasm", "desc": "lake exe test_spike2_wasm",
         "long": "Spike 2 (Fibonacci) Wasm target test (in-Lean trace + host runtime; "
                 "exit 2 = no host Wasm runner found, per Law 13(4))",
         "cmd": [lake, "exe", "test_spike2_wasm"], "slow": False, "tools": ["lean"]},
        {"key": "test_spike3_windows", "desc": "lake exe test_spike3_windows",
         "long": "Spike 3 (Sort Lines) Windows target test",
         "cmd": [lake, "exe", "test_spike3_windows"], "slow": False, "tools": ["lean"]},
        {"key": "test_spike3_wasm", "desc": "lake exe test_spike3_wasm",
         "long": "Spike 3 (Sort Lines) Wasm target test",
         "cmd": [lake, "exe", "test_spike3_wasm"], "slow": False, "tools": ["lean"]},
        {"key": "test_spike4", "desc": "lake exe test_spike4",
         "long": "Spike 4 (HTTP Server) target test",
         "cmd": [lake, "exe", "test_spike4"], "slow": False, "tools": ["lean"]},
        {"key": "test_spike5", "desc": "lake exe test_spike5",
         "long": "Spike 5 (Gzip) target test",
         "cmd": [lake, "exe", "test_spike5"], "slow": False, "tools": ["lean"]},
        {"key": "test_zlib", "desc": "lake exe test_zlib",
         "long": "Stdlib.Zlib unit/roundtrip test suite",
         "cmd": [lake, "exe", "test_zlib"], "slow": False, "tools": ["lean"]},
        {"key": "test_png", "desc": "lake exe test_png",
         "long": "Stdlib.Png unit/roundtrip test suite",
         "cmd": [lake, "exe", "test_png"], "slow": False, "tools": ["lean"]},
        {"key": "test_smolalloc", "desc": "lake exe test_smolalloc",
         "long": "Stdlib.SmolAlloc unit test suite",
         "cmd": [lake, "exe", "test_smolalloc"], "slow": False, "tools": ["lean"]},
        {"key": "perf_fuzzer", "desc": "lake exe perf_fuzzer",
         "long": "x86-64 microarchitectural performance fuzzer",
         "cmd": [lake, "exe", "perf_fuzzer"], "slow": False, "tools": ["lean"]},
        # --- Differential fuzzers (slow; --quick-skippable) ---
        {"key": "x86_fuzzer", "desc": "lake exe x86_fuzzer",
         "long": "hardware-semantics differential fuzzer vs real silicon (mandatory pos/neg control vectors)",
         "cmd": [lake, "exe", "x86_fuzzer"], "slow": True, "tools": ["lean"]},
        {"key": "encoding_fuzzer", "desc": "lake exe encoding_fuzzer",
         "long": "binary-encoding differential fuzzer vs NASM (mandatory pos/neg control vectors)",
         "cmd": [lake, "exe", "encoding_fuzzer"], "slow": True, "tools": ["lean", "nasm"]},
        {"key": "wasm_fuzzer", "desc": "lake exe wasm_fuzzer",
         "long": "Wasm host-semantics differential fuzzer vs node",
         "cmd": [lake, "exe", "wasm_fuzzer"], "slow": True, "tools": ["lean", "node"]},
        {"key": "gzip_fuzzer", "desc": f"lake exe gzip_fuzzer --count {gzip_count}",
         "long": "gzip cross-differential fuzzer vs the python stdlib oracle",
         "cmd": [lake, "exe", "gzip_fuzzer", "--count", str(gzip_count)], "slow": True,
         "tools": ["lean", "python"]},
    ]


def run_one_gate(cmd: List[str], capture: bool, timeout_s: float) -> Dict:
    start = time.monotonic()
    # Flush OUR OWN buffered stdout/stderr before the child can write to the same underlying
    # OS file descriptor (relevant whenever stdout is redirected to a file/pipe rather than a
    # TTY, where Python defaults to block buffering). Without this, our own queued "[GATE] ..."
    # header can flush AFTER the child has already written and advanced the shared file
    # position, silently clobbering the child's inherited-stdout output in the redirected log
    # -- exit codes/timings are unaffected (they never touch this buffer), but a human watching
    # a live log would see nothing from the gate that just ran. This was caught by inspecting
    # this script's own first full non-json run (a gate runner is not exempt from Law 13).
    sys.stdout.flush()
    sys.stderr.flush()
    try:
        if capture:
            proc = subprocess.run(cmd, cwd=REPO_ROOT, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True, timeout=timeout_s)
            output = proc.stdout
            code = proc.returncode
        else:
            # Inherit the parent's stdout/stderr so a human watching a 15-25 minute run sees
            # live progress. `proc.returncode` below is STILL the direct exit code of THIS
            # exact process -- no shell, no pipe, no tee sits between us and it.
            proc = subprocess.run(cmd, cwd=REPO_ROOT, timeout=timeout_s)
            output = None
            code = proc.returncode
        elapsed = time.monotonic() - start
        return {"exit_code": code, "output": output, "wall_time": elapsed,
                "launch_error": None, "timed_out": False}
    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - start
        return {"exit_code": None, "output": None, "wall_time": elapsed,
                "launch_error": None, "timed_out": True}
    except (FileNotFoundError, OSError) as e:
        elapsed = time.monotonic() - start
        return {"exit_code": None, "output": None, "wall_time": elapsed,
                "launch_error": str(e), "timed_out": False}


def fmt_seconds(s: Optional[float]) -> str:
    if s is None:
        return "-"
    m, sec = divmod(s, 60)
    if m >= 1:
        return f"{int(m)}m{sec:04.1f}s"
    return f"{sec:.1f}s"


def print_prereq_table(prereqs: Dict[str, Dict], waived: Optional[List[str]] = None) -> None:
    waived = waived or []
    print("=" * 100)
    print(" ORACLE / TOOLCHAIN VERSIONS (TCB T9 -- recorded so cross-machine drift is attributable)")
    print("=" * 100)
    for name, p in prereqs.items():
        status = "OK" if p["found"] else ("WAIVED" if name in waived else "MISSING")
        version = p.get("version") or "-"
        print(f"  [{status:7}] {name:8} {version}")
        print(f"            {p['detail']}")
        if name in waived and not p["found"]:
            print(f"            (waived: no SELECTED gate in this --quick run needs {name}; "
                  "this is not a pass, it is 'not checked for this run's scope')")
    print("=" * 100)


def print_summary_table(rows: List[Dict]) -> None:
    print("\n" + "=" * 100)
    print(" GATE SUMMARY")
    print("=" * 100)
    print(f"  {'GATE':<28} {'STATUS':<32} {'TOOL/VERSION':<28} {'WALL TIME':>10} {'EXIT':>6}")
    print("  " + "-" * 96)
    for r in rows:
        tool_info = r.get("tool_info", "-")
        wt = fmt_seconds(r["wall_time"])
        exit_disp = r["exit_code"] if r["exit_code"] is not None else "-"
        print(f"  {r['key']:<28} {r['status']:<32} {tool_info:<28} {wt:>10} {str(exit_disp):>6}")
    print("  " + "-" * 96)


def _tool_info_for(g: Dict, prereqs: Dict[str, Dict]) -> str:
    non_lean = [t for t in g["tools"] if t != "lean"]
    if non_lean:
        return ", ".join(f"{t}={prereqs[t].get('version') or '?'}" for t in non_lean)
    return prereqs["lean"].get("version") or "-"


# --------------------------------------------------------------------------------------------
# TCB T4 meta-gate fixture (--self-test): a RE-RUNNABLE regression test for the gates
# themselves. A one-time manual demonstration that a gate CAN go red is not a gate by this
# project's own standard (Law 13(4): a control vector must be checkable again, not a report
# of something that once happened) -- this is what makes T4 an actual, standing gate rather
# than a claim about a gate. Each defect is planted into the REAL tree (the scanners this
# exercises glob over the whole repo, so a defect has to actually be visible to them),
# asserted to turn the SPECIFIC gate it targets red, then reverted and re-asserted green,
# with try/finally cleanup so a crash mid-test cannot leave the tree dirty.
#
# A MUST-BE-TRACKED WRINKLE: scripts/check_gates.py and scripts/check_refs.py now enumerate
# `.lean` files from `git ls-files` rather than a filesystem walk (the fix for the nested-
# worktree phantom-violation bug -- see scripts/check_gates.py's git_tracked_files()). A file
# must be tracked to be checked; that is the correct, intended semantics (an untracked stray
# copy of the tree must never produce a finding), but it means a probe `.lean` file planted by
# `Path.write_text()` alone is now INVISIBLE to those two gates until it is staged -- a
# self-test that doesn't account for this would silently stop testing anything (the exact
# "far worse bug" this task warns about), not merely fail loudly. So every probe below that
# targets check_gates.py/check_refs.py is `git add`-ed immediately after being written (making
# it visible to `git ls-files` exactly the way a real, about-to-be-committed defect would be)
# and `git reset`-ed (unstaged) before deletion in the `finally` block, mirroring the real
# workflow: a defect is checked once it is staged for commit, not while it is still a stray
# untracked file nobody has offered to the gate yet.
# --------------------------------------------------------------------------------------------

def _git_stage(path: Path) -> None:
    """Stage a freshly-planted probe file so `git ls-files`-based enumeration
    (scripts/check_gates.py / scripts/check_refs.py) can see it.

    READ THIS BEFORE REMOVING A CALL TO THIS FUNCTION, OR BEFORE ADDING A NEW
    SELF-TEST CONTROL FOR A GATE THAT ENUMERATES `.lean` FILES: if the probe
    below it is not staged, the probe is invisible to `git ls-files` (it is
    an ordinary untracked file on disk), the targeted gate will find NOTHING
    wrong, `red` will be silently False, and the self-test will report
    `turned_red=False` -- which at least fails loudly. The genuinely dangerous
    failure mode, caught once already while writing this fix, is subtler:
    if the assertion string were ever loosened (e.g. to just `code != 0`)
    while this staging call were missing, the control could report a FALSE
    PASS while having tested nothing at all -- the gate would silently stop
    being exercised, and nobody would know, because a self-test that only
    ever reports green is indistinguishable from a self-test that was never
    wired up. That is a strictly worse bug than the phantom-violation bug
    this whole change fixes: the phantom bug was loud (it failed CI); a
    self-test that quietly tests nothing is invisible until someone goes
    looking. Every control that targets a git-ls-files-enumerated gate MUST
    stage its probe here before invoking that gate, and MUST unstage it (see
    _git_unstage) before deleting it in `finally`."""
    subprocess.run(["git", "add", "--", str(path)], cwd=REPO_ROOT, capture_output=True, timeout=30)


def _git_unstage(path: Path) -> None:
    """Reverse of _git_stage(): unstage the probe before it is deleted, so a
    crash mid-test never leaves it sitting in the index (which would corrupt
    the next `git status`/commit a human or another gate does against this
    tree, and would itself be a second, self-inflicted phantom-file bug)."""
    subprocess.run(["git", "reset", "--", str(path)], cwd=REPO_ROOT, capture_output=True, timeout=30)


def _self_test_broken_ref(py: str) -> Dict:
    probe = REPO_ROOT / "Gasm" / "_TC5SelfTestBrokenRef.lean"
    content = (
        "/- TC5 --self-test scratch fixture (T4). Deleted immediately after this check. -/\n"
        "/- REF: docs/DOES_NOT_EXIST_TC5_SELFTEST.md#nonexistent-section -/\n"
        "def tc5SelfTestBrokenRefProbe : Nat := 0\n"
    )
    try:
        probe.write_text(content, encoding="utf-8")
        _git_stage(probe)  # must be tracked: check_refs.py enumerates via `git ls-files`
        code, out = _run_capture([py, "scripts/check_refs.py"], cwd=REPO_ROOT, timeout=60)
        # check_refs.py's broken-citation report is keyed by (file, line), not by
        # declaration name, since citation validity is no longer coupled to "the
        # declaration that follows" at all (see that script's own module docstring) --
        # so the assertion below checks for the probe's FILE, not its decl name.
        red = code != 0 and "_TC5SelfTestBrokenRef.lean" in (out or "") and "not found" in (out or "")
    finally:
        _git_unstage(probe)
        probe.unlink(missing_ok=True)
    code2, _ = _run_capture([py, "scripts/check_refs.py"], cwd=REPO_ROOT, timeout=60)
    green_after = code2 == 0
    return {"defect": "broken_ref", "gate": "check_refs.py", "turned_red": red,
            "green_after_revert": green_after}


def _self_test_ref_before_anonymous_instance(py: str) -> Dict:
    """The exact defect this task closed: a `REF:` citation sitting directly above an
    anonymous `instance : Foo X where` (no name token at all) used to be silently
    DROPPED by check_refs.py's old declaration-coupled citation collector --
    LEAN_DECL_REGEX required an identifier after the keyword, so an anonymous
    instance never matched, and a citation only survived if it eventually reached a
    RECOGNIZED declaration. This control plants a citation with a deliberately
    nonexistent anchor immediately above an anonymous instance and asserts
    check_refs.py reports it broken -- proving the citation is now actually
    validated rather than silently ignored, which is the whole point of decoupling
    citation collection from declaration-form recognition (see collect_ref_citations'
    own docstring)."""
    probe = REPO_ROOT / "Gasm" / "_TC5SelfTestRefBeforeAnonInstance.lean"
    content = (
        "/- TC5 --self-test scratch fixture (T4). Deleted immediately after this check. -/\n"
        "class Tc5SelfTestRefProbeCls (α : Type) where\n"
        "  bar : α → Nat\n"
        "/- REF: docs/DOES_NOT_EXIST_TC5_SELFTEST.md#nonexistent-section -/\n"
        "instance : Tc5SelfTestRefProbeCls Nat where\n"
        "  bar n := n\n"
    )
    try:
        probe.write_text(content, encoding="utf-8")
        _git_stage(probe)  # must be tracked: check_refs.py enumerates via `git ls-files`
        code, out = _run_capture([py, "scripts/check_refs.py"], cwd=REPO_ROOT, timeout=60)
        red = (code != 0 and "_TC5SelfTestRefBeforeAnonInstance.lean" in (out or "")
               and "not found" in (out or ""))
    finally:
        _git_unstage(probe)
        probe.unlink(missing_ok=True)
    code2, _ = _run_capture([py, "scripts/check_refs.py"], cwd=REPO_ROOT, timeout=60)
    green_after = code2 == 0
    return {"defect": "ref_before_anonymous_instance", "gate": "check_refs.py",
            "turned_red": red, "green_after_revert": green_after}


def _self_test_unallowlisted_native_decide(py: str) -> Dict:
    probe = REPO_ROOT / "Gasm" / "_TC5SelfTestUnallowlisted.lean"
    content = (
        "/- TC5 --self-test scratch fixture (T4). Deleted immediately after this check. -/\n"
        "theorem tc5SelfTestUnallowlistedNativeDecide : (1 : Nat) + 1 = 2 := by native_decide\n"
    )
    try:
        probe.write_text(content, encoding="utf-8")
        _git_stage(probe)  # must be tracked: check_gates.py enumerates via `git ls-files`
        code, out = _run_capture([py, "scripts/check_gates.py"], cwd=REPO_ROOT, timeout=60)
        red = code != 0 and "tc5SelfTestUnallowlistedNativeDecide" in (out or "") and "not allowlisted" in (out or "").lower()
    finally:
        _git_unstage(probe)
        probe.unlink(missing_ok=True)
    code2, _ = _run_capture([py, "scripts/check_gates.py"], cwd=REPO_ROOT, timeout=60)
    green_after = code2 == 0
    return {"defect": "unallowlisted_native_decide", "gate": "check_gates.py", "turned_red": red,
            "green_after_revert": green_after}


def _self_test_duplicate_heading(py: str) -> Dict:
    doc = REPO_ROOT / "docs" / "_tc5_selftest_dup_heading.md"
    probe = REPO_ROOT / "Gasm" / "_TC5SelfTestDupHeading.lean"
    doc_content = (
        "---\ntitle: TC5 --self-test scratch doc (T4). Deleted immediately after this check.\n---\n\n"
        "# TC5 Duplicate Heading Self-Test Probe\n\n"
        "## Overview\n\nFirst occurrence -- slug `overview`.\n\n"
        "## Overview\n\nSecond occurrence (identical title) -- must disambiguate to `overview-1`.\n"
    )
    # A REF guessing a disambiguated anchor that does NOT exist (`overview-2`, when only
    # `overview` and `overview-1` exist) must be reported as broken -- proving check_refs.py's
    # duplicate-heading disambiguation is real, not a silent first-match collision.
    probe_content = (
        "/- TC5 --self-test scratch fixture (T4). Deleted immediately after this check. -/\n"
        "/- REF: docs/_tc5_selftest_dup_heading.md#overview-2 -/\n"
        "def tc5SelfTestDupHeadingProbe : Nat := 0\n"
    )
    try:
        doc.write_text(doc_content, encoding="utf-8")
        probe.write_text(probe_content, encoding="utf-8")
        # check_refs.py's citation scan (collect_ref_citations) enumerates `.lean`
        # files via `git ls-files`; its markdown-section index (collect_markdown_
        # sections) still walks docs/ directly (a directory-scoped glob, never
        # affected by the nested-worktree bug), so only the `.lean` probe needs
        # staging for this control to remain visible to the gate it targets.
        _git_stage(probe)
        code, out = _run_capture([py, "scripts/check_refs.py"], cwd=REPO_ROOT, timeout=60)
        red = code != 0 and "overview-2" in (out or "") and "not found" in (out or "")
    finally:
        _git_unstage(probe)
        doc.unlink(missing_ok=True)
        probe.unlink(missing_ok=True)
    code2, _ = _run_capture([py, "scripts/check_refs.py"], cwd=REPO_ROOT, timeout=60)
    green_after = code2 == 0
    return {"defect": "duplicate_heading", "gate": "check_refs.py", "turned_red": red,
            "green_after_revert": green_after}


def _self_test_planted_sorry(lake: str) -> Dict:
    """One of the two build-requiring controls (see also `_self_test_uncited_anonymous_instance`):
    a stray `sorry` type-checks fine (`lake build` would
    not catch it -- see the gate table's own note on this), so this must run a real build and
    then the axiom-level Lean tool, which is what actually depends on `sorryAx`."""
    probe = REPO_ROOT / "Gasm" / "_TC5SelfTestSorry.lean"
    original_root = GASM_ROOT_FILE.read_text(encoding="utf-8")
    import_line = "import Gasm._TC5SelfTestSorry\n"
    probe_content = (
        "/- TC5 --self-test scratch fixture (T4). Deleted immediately after this check. -/\n"
        "theorem tc5SelfTestPlantedSorry : (1 : Nat) + 1 = 2 := by sorry\n"
    )
    red = False
    build_ok = False
    try:
        probe.write_text(probe_content, encoding="utf-8")
        GASM_ROOT_FILE.write_text(original_root + import_line, encoding="utf-8")
        build_code, _ = _run_capture([lake, "build"], cwd=REPO_ROOT, timeout=600)
        build_ok = build_code == 0
        if build_ok:
            code, out = _run_capture([lake, "exe", "check_gates_axioms"], cwd=REPO_ROOT, timeout=300)
            red = code != 0 and "tc5SelfTestPlantedSorry" in (out or "") and "sorryAx" in (out or "")
    finally:
        GASM_ROOT_FILE.write_text(original_root, encoding="utf-8")
        probe.unlink(missing_ok=True)
    # Rebuild to confirm green again -- also restores .lake/build to a clean state for
    # whatever runs next in the same invocation of this script.
    revert_build_code, _ = _run_capture([lake, "build"], cwd=REPO_ROOT, timeout=600)
    green_after = False
    if revert_build_code == 0:
        revert_code, _ = _run_capture([lake, "exe", "check_gates_axioms"], cwd=REPO_ROOT, timeout=300)
        green_after = revert_code == 0
    return {"defect": "planted_sorry", "gate": "lake exe check_gates_axioms",
            "turned_red": build_ok and red, "green_after_revert": green_after,
            "note": None if build_ok else "lake build itself failed with the probe present (unexpected)"}


def _self_test_uncited_anonymous_instance(lake: str) -> Dict:
    """Plants an anonymous `instance : Foo X where` (no name token at all) with NO
    `REF:` citation whatsoever -- the exact declaration form `LEAN_DECL_REGEX` could
    never see (it required an identifier immediately after the keyword). A stray
    uncited declaration type-checks fine (`lake build` would not catch it, and
    check_refs.py no longer even tries -- Law 1 detection now lives entirely in
    Tools/CheckRefsCoverage.lean), so this control needs a real build and then the
    declaration-coverage Lean tool itself, mirroring `_self_test_planted_sorry`'s
    shape for the axiom gate."""
    probe = REPO_ROOT / "Gasm" / "_TC5SelfTestUncitedInstance.lean"
    original_root = GASM_ROOT_FILE.read_text(encoding="utf-8")
    import_line = "import Gasm._TC5SelfTestUncitedInstance\n"
    probe_content = (
        "/- TC5 --self-test scratch fixture (T4). Deleted immediately after this check. -/\n"
        "structure Tc5SelfTestUncitedFoo where\n"
        "  x : Nat\n"
        "instance : Inhabited Tc5SelfTestUncitedFoo where\n"
        "  default := { x := 0 }\n"
    )
    red = False
    build_ok = False
    try:
        probe.write_text(probe_content, encoding="utf-8")
        GASM_ROOT_FILE.write_text(original_root + import_line, encoding="utf-8")
        build_code, _ = _run_capture([lake, "build"], cwd=REPO_ROOT, timeout=600)
        build_ok = build_code == 0
        if build_ok:
            code, out = _run_capture([lake, "exe", "check_refs_coverage"], cwd=REPO_ROOT, timeout=300)
            red = (code != 0 and "instInhabitedTc5SelfTestUncitedFoo" in (out or "")
                   and "_TC5SelfTestUncitedInstance.lean" in (out or ""))
    finally:
        GASM_ROOT_FILE.write_text(original_root, encoding="utf-8")
        probe.unlink(missing_ok=True)
    # Rebuild to confirm green again -- also restores .lake/build to a clean state for
    # whatever runs next in the same invocation of this script.
    revert_build_code, _ = _run_capture([lake, "build"], cwd=REPO_ROOT, timeout=600)
    green_after = False
    if revert_build_code == 0:
        revert_code, _ = _run_capture([lake, "exe", "check_refs_coverage"], cwd=REPO_ROOT, timeout=300)
        green_after = revert_code == 0
    return {"defect": "uncited_anonymous_instance", "gate": "lake exe check_refs_coverage",
            "turned_red": build_ok and red, "green_after_revert": green_after,
            "note": None if build_ok else "lake build itself failed with the probe present (unexpected)"}


def run_self_test(json_mode: bool) -> int:
    py = shutil.which("python") or shutil.which("python3") or shutil.which("py") or "python"
    lake = shutil.which("lake") or "lake"

    if not json_mode:
        print("#" * 100)
        print("# TCB T4 meta-gate fixture (--self-test): re-runnable planted-defect control vectors")
        print("#" * 100)

    results = []
    for label, fn in [
        ("broken_ref", lambda: _self_test_broken_ref(py)),
        ("ref_before_anonymous_instance", lambda: _self_test_ref_before_anonymous_instance(py)),
        ("unallowlisted_native_decide", lambda: _self_test_unallowlisted_native_decide(py)),
        ("duplicate_heading", lambda: _self_test_duplicate_heading(py)),
        ("planted_sorry", lambda: _self_test_planted_sorry(lake)),
        ("uncited_anonymous_instance", lambda: _self_test_uncited_anonymous_instance(lake)),
    ]:
        if not json_mode:
            print(f"\n[SELF-TEST] {label} ...")
        r = fn()
        results.append(r)
        if not json_mode:
            ok = r["turned_red"] and r["green_after_revert"]
            print(f"  turned_red={r['turned_red']}  green_after_revert={r['green_after_revert']}  "
                  f"-> {'PASS' if ok else 'FAIL'}")

    all_ok = all(r["turned_red"] and r["green_after_revert"] for r in results)
    overall = "PASS" if all_ok else "FAIL"

    if json_mode:
        print(json.dumps({"self_test": overall, "results": results}, indent=2))
    else:
        print("\n" + "=" * 100)
        print(f" SELF-TEST SUMMARY: {overall}")
        for r in results:
            print(f"  - {r['defect']:<32} gate={r['gate']:<28} "
                  f"turned_red={r['turned_red']!s:<6} green_after_revert={r['green_after_revert']!s:<6}")
        print("=" * 100)

    return EXIT_OK if all_ok else EXIT_GATE_FAILED


# --------------------------------------------------------------------------------------------
# Main gate-running orchestration
# --------------------------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(
        description="gasm gate runner (TC5): single entry point for every merge gate.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--quick", action="store_true",
                         help="Select only the fast gates (skip the 4 slow differential "
                              "fuzzers). On success this exits 2 (PASSED_PARTIAL), never 0 -- "
                              "NOT SUFFICIENT EVIDENCE FOR MERGE SIGN-OFF under any circumstance.")
    parser.add_argument("--clean", action="store_true",
                         help="Run `lake clean` before anything else (TCB T13, merge-train mode).")
    parser.add_argument("--json", action="store_true",
                         help="Emit a machine-parseable JSON summary to stdout (for CI/TC6); "
                              "suppresses live-streamed gate output and the human table. Always "
                              "includes a top-level \"mode\" field.")
    parser.add_argument("--gzip-count", type=int, default=25,
                         help="Iteration count passed to gzip_fuzzer's --count flag (default: 25).")
    parser.add_argument("--gate-timeout", type=float, default=DEFAULT_GATE_TIMEOUT_S,
                         help=f"Per-gate wall-clock timeout in seconds (default {DEFAULT_GATE_TIMEOUT_S}). "
                              "A gate that exceeds this is killed and reported as TIMEOUT, not left to "
                              "hang the runner (and any CI invoking it) forever.")
    parser.add_argument("--self-test", action="store_true",
                         help="Run the TCB T4 meta-gate fixture instead of the normal gate "
                              "sequence: plant each of 6 known defects, assert the specific "
                              "gate goes red, revert, assert green again. See run_self_test().")
    args = parser.parse_args()

    if args.self_test:
        return run_self_test(args.json)

    json_mode = args.json
    mode = "quick" if args.quick else "full"

    if not json_mode:
        print("#" * 100)
        print("# gasm gate runner (scripts/run_gates.py) -- TC5")
        print(f"# repo root: {REPO_ROOT}")
        print(f"# mode: {mode.upper()}"
              f"{' (fuzzers + several gates skipped -- NOT sufficient for merge sign-off)' if args.quick else ''}"
              f"{' + CLEAN' if args.clean else ''}")
        print("#" * 100)

    gates = build_gate_table(args.gzip_count)
    selected = [g for g in gates if not (args.quick and g["slow"])]
    selected_keys = {g["key"] for g in selected}

    # --- Phase 0: prerequisite detection -- ALWAYS all 5, ALWAYS reported, regardless of mode
    # or of which gates are selected (M2 fix: detection must never be scoped down by --quick).
    prereqs = detect_all_prereqs()

    # `needed`: tools required by a SELECTED gate -- this is what the abort decision reads.
    # `only_skipped_need`: tools ONLY a skipped (--quick) gate would have needed, so a missing
    # one there is reported as an explicit WAIVED entry rather than silently absent from the
    # abort decision.
    always_required = {"lake", "lean", "python"}
    needed = set(always_required)
    for g in selected:
        needed.update(g["tools"])
    all_tools_in_table = set(always_required)
    for g in gates:
        all_tools_in_table.update(g["tools"])
    only_skipped_need = sorted(all_tools_in_table - needed)
    waived = [t for t in only_skipped_need if not prereqs[t]["found"]]

    if not json_mode:
        print_prereq_table(prereqs, waived=waived)
        if waived:
            print(f"\n[i] WAIVED (not enforced this run, --quick skipped every gate that needs "
                  f"{'them' if len(waived) > 1 else 'it'}): {', '.join(waived)}")

    missing = [name for name in needed if not prereqs[name]["found"]]

    if missing:
        # ABORT THE WHOLE RUN -- never silently skip. This is "abort, not skip", verbatim from
        # TASKS.md's TC5 entry, and the exact demonstration this task's acceptance criteria
        # require for NASM-absent / node-absent.
        rows = []
        for g in gates:
            if g["key"] not in selected_keys:
                status = "SKIPPED (--quick)"
            else:
                needs_missing = [t for t in g["tools"] if t in missing]
                status = f"ABORTED (missing: {', '.join(needs_missing)})" if needs_missing \
                    else "NOT RUN (aborted before start)"
            rows.append({"key": g["key"], "status": status, "exit_code": None,
                         "wall_time": None, "tool_info": "-"})

        if json_mode:
            print(json.dumps({
                "mode": mode,
                "overall_status": "ABORTED",
                "overall_exit_code": EXIT_PREREQ_ABORT,
                "missing_prerequisites": missing,
                "waived_prerequisites": waived,
                "prerequisites": prereqs,
                "gates": rows,
            }, indent=2))
        else:
            print("\n" + "!" * 100)
            print("! ABORT: missing required prerequisite(s) -- " + ", ".join(missing))
            for name in missing:
                print(f"!   - {name}: {prereqs[name]['detail']}")
            print("! The run is aborting NOW, before any gate executes. This is fail-closed by")
            print("! design (D13/Law 13): a missing oracle is never silently skipped.")
            print("!" * 100)
            print_summary_table(rows)
        return EXIT_PREREQ_ABORT

    # --- Phase 1: optional `lake clean` (TCB T13 merge-train mode) ---------------------------
    result_rows: List[Dict] = []
    if args.clean:
        lake = shutil.which("lake") or "lake"
        if not json_mode:
            print("\n[*] --clean: running `lake clean` before the gate sequence...")
        clean_res = run_one_gate([lake, "clean"], capture=json_mode, timeout_s=args.gate_timeout)
        status = "PASS" if clean_res["exit_code"] == 0 else "FAIL"
        result_rows.append({"key": "lake_clean", "status": status,
                             "exit_code": clean_res["exit_code"],
                             "wall_time": clean_res["wall_time"], "tool_info": "-"})
        if clean_res["exit_code"] != 0:
            if not json_mode:
                print("[!] `lake clean` failed -- aborting before the gate sequence "
                      "(a corrupted .lake/build tree makes every downstream result unreliable).")
            for g in gates:
                if any(r["key"] == g["key"] for r in result_rows):
                    continue
                sk = "SKIPPED (--quick)" if g["key"] not in selected_keys else "SKIPPED (lake clean failed)"
                result_rows.append({"key": g["key"], "status": sk,
                                     "exit_code": None, "wall_time": None, "tool_info": "-"})
            if json_mode:
                print(json.dumps({"mode": mode, "overall_status": "FAILED",
                                   "overall_exit_code": EXIT_GATE_FAILED,
                                   "prerequisites": prereqs, "gates": result_rows}, indent=2))
            else:
                print_summary_table(result_rows)
            return EXIT_GATE_FAILED

    # --- Phase 2: run every gate in GATE_TABLE order. Non-selected (--quick) gates get an
    # explicit SKIPPED row -- they are never simply absent from the report. -------------------
    stop_rest = False
    for g in gates:
        if g["key"] not in selected_keys:
            result_rows.append({"key": g["key"], "status": "SKIPPED (--quick)",
                                 "exit_code": None, "wall_time": None, "tool_info": "-"})
            continue

        if stop_rest:
            result_rows.append({"key": g["key"], "status": "SKIPPED (lake build failed)",
                                 "exit_code": None, "wall_time": None, "tool_info": "-"})
            continue

        tool_info = _tool_info_for(g, prereqs)

        if not json_mode:
            print("\n" + "-" * 100)
            print(f"[GATE] {g['desc']}  --  {g['long']}")
            print(f"       $ {' '.join(g['cmd'])}   (cwd={REPO_ROOT})")
            print("-" * 100)

        res = run_one_gate(g["cmd"], capture=json_mode, timeout_s=args.gate_timeout)

        if res["timed_out"]:
            status = f"TIMEOUT (> {args.gate_timeout:.0f}s)"
            exit_code = None
        elif res["launch_error"] is not None:
            status = f"ERROR: could not launch ({res['launch_error']})"
            exit_code = None
        elif res["exit_code"] == 0:
            status = "PASS"
            exit_code = 0
        else:
            status = "FAIL"
            exit_code = res["exit_code"]

        result_rows.append({"key": g["key"], "status": status, "exit_code": exit_code,
                             "wall_time": res["wall_time"], "tool_info": tool_info,
                             "output": res["output"] if json_mode else None})

        if g["key"] == "lake_build" and status != "PASS":
            stop_rest = True
            if not json_mode:
                print("\n[!] `lake build` failed -- every remaining gate depends on a successful "
                      "build (either compiling the checker itself, or the lake exe binaries it "
                      "produces). Skipping the rest rather than running against stale/partial "
                      "binaries.")

    selected_rows = [r for r in result_rows if r["key"] in selected_keys]
    overall_pass = all(r["status"] == "PASS" for r in selected_rows)

    if not overall_pass:
        overall_status = "FAILED"
        overall_exit = EXIT_GATE_FAILED
    elif args.quick:
        overall_status = "PASSED_PARTIAL"
        overall_exit = EXIT_PASSED_PARTIAL
    else:
        overall_status = "PASSED"
        overall_exit = EXIT_OK

    if json_mode:
        print(json.dumps({
            "mode": mode,
            "overall_status": overall_status,
            "overall_exit_code": overall_exit,
            "waived_prerequisites": waived,
            "prerequisites": prereqs,
            "gates": result_rows,
        }, indent=2))
    else:
        print_summary_table(result_rows)
        print(f"\n  OVERALL: {overall_status}  (exit code {overall_exit})")
        if args.quick:
            print("  NOTE: --quick mode. This run's success is PASSED_PARTIAL, not PASSED -- it")
            print("        is NOT sufficient evidence for merge sign-off. Re-run in full mode.")
        print("=" * 100)

    return overall_exit


if __name__ == "__main__":
    sys.exit(main())
