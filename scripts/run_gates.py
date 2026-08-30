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
Before this script existed, every gate was invoked by hand, per-agent, per-session. The
consequence is recorded in `docs/REVIEW.md` Law 13: a gate nothing invokes binds nothing. This
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

DIRECT EXIT-CODE CAPTURE ONLY -- NEVER THROUGH A PIPE (a previously observed implementation trap): an earlier
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
    python scripts/run_gates.py --clean           # `lake clean` first (the clean-rebuild contract, merge-train mode)
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
    python scripts/run_gates.py --self-test       # docs/REVIEW.md Law 13 meta-gate fixture: plants each of 6
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
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from contextlib import nullcontext
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

from lean_process_lease import inherited_lease_environment, lean_process_lease

if sys.stdout.encoding != "utf-8":
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass

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
# Oracle / toolchain version detection (the oracle/toolchain provenance contract: "node/python/nasm: no version recorded or
# asserted anywhere" -- this is where that gap closes. Every oracle's version string is both
# printed to the console AND carried into the --json summary, so a divergence in gate results
# across two machines/sessions is attributable to an environment drift, not silently
# re-litigated as a model bug. docs/REVIEW.md Law 10 extends this to `bv_decide`'s external SAT solver: see
# detect_cadical() below.)
# --------------------------------------------------------------------------------------------

def _run_capture(cmd: List[str], cwd: Optional[Path] = None, timeout: float = 30.0):
    """Runs `cmd` directly (no shell, no pipe) and returns (returncode_or_None, combined_output).
    returncode is None only if the executable could not be launched at all (not found / OS
    error) -- that is itself a "prerequisite absent" signal, never conflated with a normal
    non-zero exit."""
    try:
        proc = subprocess.run(
            cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, encoding="utf-8", errors="replace", timeout=timeout,
        )
        return proc.returncode, proc.stdout
    except (FileNotFoundError, OSError, TimeoutError, ValueError) as e:
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
    """Captures `lean --version` and asserts it matches the lean-toolchain pin (the oracle/toolchain provenance contract's
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
    exactly the class of gap the oracle/toolchain provenance contract exists to close. An explicit, broken override is reported
    as NOT FOUND (never silently substituted), which is also what actually happens when
    encoding_fuzzer runs.
    Captures and returns the real version banner (the oracle/toolchain provenance contract: NASM.lean fetches `nasm -v` and
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
    programfiles = os.environ.get("ProgramFiles")
    if programfiles:
        candidates.append(str(Path(programfiles) / "NASM" / "nasm.exe"))
    programfiles_x86 = os.environ.get("ProgramFiles(x86)")
    if programfiles_x86:
        candidates.append(str(Path(programfiles_x86) / "NASM" / "nasm.exe"))

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


def detect_qemu() -> Dict:
    """Mirrors detect_nasm()'s resolution order, applied to Gasm/Targets/BareMetal/QEMU.lean's
    `findQemuPath`: GASM_QEMU override -> PATH -> standard Windows install location -> standard Linux
    package-manager location (`/usr/bin/qemu-system-x86_64`)."""
    override = os.environ.get("GASM_QEMU")
    if override:
        code, out = _run_capture([override, "--version"])
        if code == 0:
            banner = (out or "").strip().splitlines()[0] if out else ""
            return {"name": "qemu", "found": True, "path": override, "version": banner,
                    "detail": f"resolved to {override} (via GASM_QEMU override)"}
        return {"name": "qemu", "found": False, "path": None, "version": None,
                "detail": f"GASM_QEMU={override!r} is set but did not respond to `--version` "
                          f"(returncode={code}); NOT falling through to another candidate -- "
                          "an explicit, broken override must abort, not silently substitute a "
                          "different QEMU than the one the gate would actually be told to use."}

    candidates: List[str] = []
    which_qemu = shutil.which("qemu-system-x86_64") or shutil.which("qemu-system-x86_64.exe")
    if which_qemu:
        candidates.append(which_qemu)
    programfiles = os.environ.get("ProgramFiles")
    if programfiles:
        candidates.append(str(Path(programfiles) / "qemu" / "qemu-system-x86_64.exe"))
    programfiles_x86 = os.environ.get("ProgramFiles(x86)")
    if programfiles_x86:
        candidates.append(str(Path(programfiles_x86) / "qemu" / "qemu-system-x86_64.exe"))
    candidates.append("/usr/bin/qemu-system-x86_64")
    candidates.append("/usr/local/bin/qemu-system-x86_64")

    tried = []
    for cand in candidates:
        if cand in tried:
            continue
        tried.append(cand)
        code, out = _run_capture([cand, "--version"])
        if code == 0:
            banner = (out or "").strip().splitlines()[0] if out else ""
            return {"name": "qemu", "found": True, "path": cand, "version": banner,
                    "detail": f"resolved to {cand}"}
    return {"name": "qemu", "found": False, "path": None, "version": None,
            "detail": "qemu-system-x86_64 not found on PATH, GASM_QEMU, or any standard install "
                      f"location (tried: {', '.join(tried) if tried else '<none>'}); required by "
                      "test_spike1_baremetal's hardware runner "
                      "(Gasm/Targets/BareMetal/QEMU.lean). Install QEMU or set GASM_QEMU to its "
                      "full path."}


def detect_cadical() -> Dict:
    """Resolves the SAT solver `bv_decide` actually invokes (docs/REVIEW.md Law 10), mirroring Lean's own
    `determineSolver` (`Lean/Meta/Tactic/BVDecide/TacticContext.lean`): prefer `cadical.exe`
    (or `cadical`) shipped in the SAME directory as the running toolchain's own binaries --
    pinned by `lean-toolchain` exactly the way `lean.exe`/`lake.exe` are (T1) -- and fall back
    to a bare `cadical` resolved from PATH, which is UNPINNED BY CONSTRUCTION, only if that
    bundled binary is absent. Recording which of the two was actually used is the point: T14
    found that this disclosure did not exist anywhere before this detector.

    The toolchain's own bin/ directory is asked from the running `lean` itself via
    `lean --print-prefix` rather than assumed from the directory containing
    `shutil.which("lean")`'s result, because on this platform `lean` on PATH commonly resolves
    to an elan shim rather than the toolchain binary directly -- the shim's own directory is
    NOT where `cadical` ships, only the real toolchain prefix's `bin/` is."""
    lean_exe = shutil.which("lean")
    bundled_path: Optional[Path] = None
    if lean_exe:
        code, out = _run_capture([lean_exe, "--print-prefix"])
        if code == 0 and out:
            prefix = out.strip().splitlines()[-1].strip()
            for candidate_name in ("cadical.exe", "cadical"):
                candidate = Path(prefix) / "bin" / candidate_name
                if candidate.exists():
                    bundled_path = candidate
                    break

    if bundled_path is not None:
        code, out = _run_capture([str(bundled_path), "--version"])
        return {"name": "cadical", "found": code == 0, "path": str(bundled_path),
                "version": (out or "").strip(),
                "detail": f"resolved to {bundled_path} -- bundled with the toolchain, pinned "
                          "by lean-toolchain the same way lean.exe/lake.exe are (docs/REVIEW.md Law 10); "
                          "this is the path bv_decide's determineSolver prefers"}

    # Bundled binary absent (or `lean --print-prefix` unavailable): fall back to a bare
    # `cadical` on PATH, exactly as Lean's own determineSolver does -- and exactly as
    # unpinned as that fallback is by construction (docs/REVIEW.md Law 10).
    exe = shutil.which("cadical") or shutil.which("cadical.exe")
    if not exe:
        return {"name": "cadical", "found": False, "path": None, "version": None,
                "detail": "no bundled cadical(.exe) found under the toolchain's own bin/ "
                          "(resolved via `lean --print-prefix`) and no bare 'cadical' "
                          "resolvable on PATH -- required by any bv_decide occurrence (docs/REVIEW.md Law 10)"}
    code, out = _run_capture([exe, "--version"])
    return {"name": "cadical", "found": code == 0, "path": exe, "version": (out or "").strip(),
            "detail": f"resolved to {exe} via PATH -- the bundled toolchain binary was not "
                      "found under bin/; this fallback is UNPINNED BY CONSTRUCTION (docs/REVIEW.md Law 10)"}


def detect_qemu_system_aarch64() -> Dict:
    override = os.environ.get("GASM_QEMU_AARCH64")
    if override:
        code, out = _run_capture([override, "--version"])
        if code == 0:
            banner = (out or "").strip().splitlines()[0] if out else ""
            return {"name": "qemu_system_aarch64", "found": True, "path": override, "version": banner,
                    "detail": f"resolved to {override} (via GASM_QEMU_AARCH64 override)"}
        return {"name": "qemu_system_aarch64", "found": False, "path": None, "version": None,
                "detail": f"GASM_QEMU_AARCH64={override!r} is set but did not respond to `--version` (returncode={code})" }

    candidates: List[str] = []
    which_qemu = shutil.which("qemu-system-aarch64") or shutil.which("qemu-system-aarch64.exe")
    if which_qemu:
        candidates.append(which_qemu)
    programfiles = os.environ.get("ProgramFiles")
    if programfiles:
        candidates.append(str(Path(programfiles) / "qemu" / "qemu-system-aarch64.exe"))
    programfiles_x86 = os.environ.get("ProgramFiles(x86)")
    if programfiles_x86:
        candidates.append(str(Path(programfiles_x86) / "qemu" / "qemu-system-aarch64.exe"))
    candidates.append("/usr/bin/qemu-system-aarch64")
    candidates.append("/usr/local/bin/qemu-system-aarch64")
    candidates.append("/usr/bin/qemu-system-aarch64")

    tried = []
    for cand in candidates:
        if cand in tried:
            continue
        tried.append(cand)
        code, out = _run_capture([cand, "--version"])
        if code == 0:
            banner = (out or "").strip().splitlines()[0] if out else ""
            return {"name": "qemu_system_aarch64", "found": True, "path": cand, "version": banner,
                    "detail": f"resolved to {cand}"}
    return {"name": "qemu_system_aarch64", "found": False, "path": None, "version": None,
            "detail": "qemu-system-aarch64 not found on PATH or GASM_QEMU_AARCH64"}


def detect_qemu_user_aarch64() -> Dict:
    override = os.environ.get("GASM_QEMU_USER_AARCH64")
    if override:
        code, out = _run_capture([override, "--version"])
        if code == 0:
            banner = (out or "").strip().splitlines()[0] if out else ""
            return {"name": "qemu_user_aarch64", "found": True, "path": override, "version": banner,
                    "detail": f"resolved to {override} (via GASM_QEMU_USER_AARCH64 override)"}
        return {"name": "qemu_user_aarch64", "found": False, "path": None, "version": None,
                "detail": f"GASM_QEMU_USER_AARCH64={override!r} is set but did not respond to `--version` (returncode={code})" }

    candidates: List[str] = []
    which_qemu = shutil.which("qemu-aarch64") or shutil.which("qemu-aarch64.exe")
    if which_qemu:
        candidates.append(which_qemu)
    candidates.append("/usr/bin/qemu-aarch64")

    tried = []
    for cand in candidates:
        if cand in tried:
            continue
        tried.append(cand)
        code, out = _run_capture([cand, "--version"])
        if code == 0:
            banner = (out or "").strip().splitlines()[0] if out else ""
            return {"name": "qemu_user_aarch64", "found": True, "path": cand, "version": banner,
                    "detail": f"resolved to {cand}"}
    return {"name": "qemu_user_aarch64", "found": False, "path": None, "version": None,
            "detail": "qemu-aarch64 not found on PATH or GASM_QEMU_USER_AARCH64"}


def detect_llvm_mc() -> Dict:
    override = os.environ.get("GASM_LLVM_MC")
    if override:
        code, out = _run_capture([override, "--version"])
        if code == 0:
            banner = (out or "").strip().splitlines()[0] if out else ""
            return {"name": "llvm_mc", "found": True, "path": override, "version": banner,
                    "detail": f"resolved to {override} (via GASM_LLVM_MC override)"}
        return {"name": "llvm_mc", "found": False, "path": None, "version": None,
                "detail": f"GASM_LLVM_MC={override!r} is set but did not respond to `--version` (returncode={code})" }

    candidates = ["llvm-mc-19", "llvm-mc"]
    tried = []
    for cand in candidates:
        exe = shutil.which(cand)
        if exe:
            tried.append(exe)
            code, out = _run_capture([exe, "--version"])
            if code == 0:
                banner = (out or "").strip().splitlines()[0] if out else ""
                return {"name": "llvm_mc", "found": True, "path": exe, "version": banner,
                        "detail": f"resolved to {exe}"}
    return {"name": "llvm_mc", "found": False, "path": None, "version": None,
            "detail": "llvm-mc-19 or llvm-mc not found on PATH or GASM_LLVM_MC"}


PREREQ_DETECTORS = {
    "python": detect_python,
    "lake": detect_lake,
    "lean": detect_lean,
    "node": detect_node,
    "nasm": detect_nasm,
    "qemu": detect_qemu,
    "qemu_system_aarch64": detect_qemu_system_aarch64,
    "qemu_user_aarch64": detect_qemu_user_aarch64,
    "llvm_mc": detect_llvm_mc,
    "cadical": detect_cadical,
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
        {"key": "lake_build", "desc": "python scripts/build_full.py",
         "group": "build",
         "long": "all defaultTargets compile cleanly (a stray `sorry` is only a compiler "
                 "warning here -- lakefile.toml sets no warningAsError -- the actual "
                 "zero-sorry/zero-unauthorized-axiom enforcement is check_gates_axioms below)",
         "cmd": [py, "scripts/build_full.py"], "slow": False,
         "tools": ["python", "lean"], "depends_on": []},
        {"key": "check_refs", "desc": "python scripts/check_refs.py",
         "group": "linters",
         "long": "Law 3: citation validity (no Lean parsing -- see docs/REVIEW.md #4.1.2)",
         "cmd": [py, "scripts/check_refs.py"], "slow": False, "tools": ["python"], "depends_on": []},
        {"key": "check_full_refs_gate_wiring",
         "desc": "python scripts/check_full_refs_gate_wiring.py",
         "group": "linters",
         "long": "prevents tests, runners, and workflows from bypassing the explicit "
                 "full-repository declaration-coverage launcher",
         "cmd": [py, "scripts/check_full_refs_gate_wiring.py"], "slow": False,
         "tools": ["python"], "depends_on": []},
        {"key": "check_no_exception_ledgers",
         "desc": "python scripts/check_no_exception_ledgers.py",
         "group": "linters",
         "long": "ratchet: retired gate exception ledgers and parser wiring cannot be reintroduced; "
                 "the shrinking Law-10 debt ledger is the sole temporary exception",
         "cmd": [py, "scripts/check_no_exception_ledgers.py"], "slow": False,
         "tools": ["python"], "depends_on": []},
        {"key": "check_refs_coverage", "desc": "python scripts/run_full_refs_coverage.py --full-repository",
         "group": "proofs",
         "long": "Law 1 LOAD-BEARING declaration-coverage gate -- walks the compiled environment, "
                 "not source text, so no declaration form (anonymous instance, abbrev, initialize, "
                 "...) can hide from it; run from repo root, building it is not running it",
         "cmd": [py, "scripts/run_full_refs_coverage.py", "--full-repository"], "slow": False,
         "tools": ["python", "lean"], "depends_on": ["lake_build"]},
        {"key": "check_gates", "desc": "python scripts/check_gates.py",
         "group": "linters",
         "long": "Law 10 fast source-level pre-check (defense-in-depth, not the load-bearing gate)",
         "cmd": [py, "scripts/check_gates.py"], "slow": False, "tools": ["python"], "depends_on": []},
        {"key": "check_gates_axioms", "desc": "lake exe check_gates_axioms",
         "group": "proofs",
         "long": "Law 10 LOAD-BEARING axiom gate -- run from repo root; building it is not running it",
         "cmd": [lake, "exe", "check_gates_axioms"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "check_references_offline", "desc": "python scripts/check_references.py --offline",
         "group": "linters",
         "long": "Law 6: reference registry integrity -- every REF: <slug>#<anchor> citation is "
                 "registered in references.json, its cache file's freshly-recomputed sha256 matches "
                 "the recorded pin, and its anchor resolves. Network-free; requires a warm local "
                 "cache at .cache/references/ (populate first with --refresh --slug/--corpus/--all).",
         "cmd": [py, "scripts/check_references.py", "--offline"], "slow": False, "tools": ["python"], "depends_on": []},
        {"key": "check_publishable", "desc": "python scripts/check_publishable.py",
         "group": "linters",
         "long": "Pre-flatten publishability gate: zero third-party prose under references/ (owner "
                 "ruling), zero dangling REF: citations into it, zero machine-specific paths, "
                 "Apache-2.0 header coverage (delegates to check_licenses.py)",
         "cmd": [py, "scripts/check_publishable.py"], "slow": False, "tools": ["python"], "depends_on": []},
        {"key": "check_licenses", "desc": "python scripts/check_licenses.py",
         "group": "linters",
         "long": "REVIEW.md Sec 4.1 item 5: Apache-2.0 header compliance -- required by Sec 4.1 and "
                 "Sec 4.4 Gate 1, but was never wired into this runner (found and fixed during the "
                 "documentation-integrity remediation pass; the same 'a gate that exists but "
                 "never runs protects nothing' lesson this project has already learned once for "
                 "check_publishable.py/check_references.py)",
         "cmd": [py, "scripts/check_licenses.py"], "slow": False, "tools": ["python"], "depends_on": []},
        {"key": "check_doc_facade", "desc": "python scripts/check_doc_facade.py",
         "group": "linters",
         "long": "Doc-facade linter -- detects governed docs/*.md "
                 "asserting enforcement the tree does not provide: a MUST/is-implemented-shaped "
                 "claim citing a Lean identifier absent from the whole .lean tree, or "
                 "docs/REVIEW.md naming a script/lake-exe gate that is missing or not wired into "
                 "this table (the check_licenses.py-was-never-wired-in shape, found this week)",
         "cmd": [py, "scripts/check_doc_facade.py"], "slow": False, "tools": ["python"], "depends_on": []},
        {"key": "check_orphan_modules", "desc": "python scripts/check_orphan_modules.py",
         "group": "linters",
         "long": "Law 13 ratchet: every tracked .lean file must be reachable, transitively, from "
                 "a root lakefile.toml declares. An orphan is a committed file that `lake build` "
                 "never compiles, so no proof, `sorry` or axiom inside it is checked by anything "
                 "-- including by check_gates_axioms above, whose environment walk only sees the "
                 "umbrella closure. Three shipped instances of this class (d5c1171, 7414099, "
                 "Stdlib/Zlib/CanonicalTableSpec.lean) are what made it a gate; the script's "
                 "module docstring has the full specification, including why the roots are "
                 "derived from lakefile.toml rather than hardcoded and why enumeration is "
                 "`git ls-files` rather than a filesystem walk. Needs no build.",
         "cmd": [py, "scripts/check_orphan_modules.py"], "slow": False, "tools": ["python"], "depends_on": []},
        {"key": "check_instructions_umbrella", "desc": "python scripts/check_instructions_umbrella.py",
         "group": "linters",
         "long": "B3: Gasm/Targets/X86_64/Instructions.lean umbrella completeness. That file is a "
                 "hand-maintained 'true umbrella' whose import list is the ONLY reason Registry.lean's "
                 "build-time environment audit can see an instruction family at all -- Lean's "
                 "environment walk sees the current file's import graph, not every .lean Lake happens "
                 "to compile -- so an Instructions/<Foo>.lean declaring an X86_64Instruction instance "
                 "but missing from that list is invisible to the audit rather than flagged by it. "
                 "Wired in here (and into .github/workflows/ci.yml) as a follow-up to "
                 "the build-performance follow-up recorded in docs/TARGETS/X86_64.md: the script "
                 "existed and nothing invoked it, the identical shape as "
                 "the check_licenses.py finding recorded two entries above. That note gave the "
                 "script's missing mutation test as the reason it stayed unwired, so wiring it came "
                 "with one: `--self-test` plants a real unimported family file (asserts red, names "
                 "it, reverts, asserts green) plus a negative control that an un-imported "
                 "NON-family file is correctly ignored. Measured 0.5s; needs no build (pure "
                 "filesystem-vs-import-list diff).",
         "cmd": [py, "scripts/check_instructions_umbrella.py"], "slow": False, "tools": ["python"], "depends_on": []},
        {"key": "test_roundtrip", "desc": "lake exe test_roundtrip",
         "group": "proofs",
         "long": "x86-64 decode/encode roundtrip suite (registry gate's ~21 native_decide shards "
                 "are compiled into lake build itself, not re-invoked here)",
         "cmd": [lake, "exe", "test_roundtrip"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "check_x86_obligations", "desc": "lake exe check_x86_obligations",
         "group": "proofs",
         "long": "P4/P5 unified x86-64 instruction obligation gate -- LOAD-BEARING "
                 "honesty check on top of Instructions/Base.lean's mandatory validationOracle/"
                 "costProvenance fields (field PRESENCE is compile-time and enforced by lake build "
                 "itself; this walks the compiled registry and checks field HONESTY: toUops "
                 "non-empty, a .silicon claim agrees with canFuzzHardware and clears a fuzz-vector "
                 "vacuity floor, every reason string clears a minimum length, and every .optedOut "
                 "instance has a matching, justified scripts/x86_obligation_allowlist.txt entry). "
                 "Run from the repo root; building it is not running it, the same distinction item "
                 "4 draws for check_gates_axioms. See Tools/CheckX86Obligations.lean's own module "
                 "docstring for the full specification.",
         "cmd": [lake, "exe", "check_x86_obligations"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "check_aarch64_obligations", "desc": "lake exe check_aarch64_obligations",
         "group": "proofs",
         "long": "AArch64 instruction obligation gate enforcing honesty constraints on validationOracle "
                 "and costProvenance fields.",
         "cmd": [lake, "exe", "check_aarch64_obligations"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
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
         "group": "spikes",
         "long": "emits hello.exe -- prerequisite artifact for test_spike1_windows below",
         "cmd": [lake, "exe", "spike1_hello_windows"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "test_spike1_windows", "desc": "lake exe test_spike1_windows",
         "group": "spikes",
         "long": "Spike 1 (Hello World) Windows target test",
         "cmd": [lake, "exe", "test_spike1_windows"], "slow": False, "tools": ["lean"], "depends_on": ["spike1_hello_windows"]},
        {"key": "test_spike1_wasm", "desc": "lake exe test_spike1_wasm",
         "group": "spikes",
         "long": "Spike 1 (Hello World) Wasm target test (in-Lean trace + host runtime; "
                 "exit 2 = no host Wasm runner found, per Law 13(4))",
         "cmd": [lake, "exe", "test_spike1_wasm"], "slow": False, "tools": ["lean"], "allow_skip_code_2": True, "depends_on": ["lake_build"]},
        {"key": "spike1_hello_baremetal", "desc": "lake exe spike1_hello_baremetal",
         "group": "spikes",
         "long": "emits spike1_hello_baremetal.elf -- prerequisite artifact for test_spike1_baremetal below",
         "cmd": [lake, "exe", "spike1_hello_baremetal"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "test_spike1_baremetal", "desc": "lake exe test_spike1_baremetal",
         "group": "spikes",
         "long": "Spike 1 (Hello World) Bare Metal target test (in-Lean trace + QEMU execution); "
                 "requires the qemu prerequisite (see detect_qemu()) so a missing QEMU aborts "
                 "this run rather than being reported as an ordinary gate FAIL indistinguishable "
                 "from a real verification defect -- consistent with how nasm/node are enforced "
                 "for encoding_fuzzer/wasm_fuzzer above.",
         "cmd": [lake, "exe", "test_spike1_baremetal"], "slow": False, "tools": ["lean", "qemu"], "depends_on": ["spike1_hello_baremetal"]},
        {"key": "spike1_hello_aarch64_baremetal", "desc": "lake exe spike1_hello_aarch64_baremetal",
         "group": "spikes",
         "long": "emits spike1_hello_aarch64_baremetal.elf -- prerequisite artifact for test_spike1_aarch64_baremetal below",
         "cmd": [lake, "exe", "spike1_hello_aarch64_baremetal"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "test_spike1_aarch64_baremetal", "desc": "lake exe test_spike1_aarch64_baremetal",
         "group": "spikes",
         "long": "Spike 1 (Hello World) AArch64 Bare Metal target test (in-Lean trace + QEMU execution); "
                 "requires the qemu_system_aarch64 prerequisite.",
         "cmd": [lake, "exe", "test_spike1_aarch64_baremetal"], "slow": False, "tools": ["lean", "qemu_system_aarch64"], "depends_on": ["spike1_hello_aarch64_baremetal"]},
        {"key": "spike1_hello_aarch64_linux", "desc": "lake exe spike1_hello_aarch64_linux",
         "group": "spikes",
         "long": "emits spike1_hello_aarch64_linux -- prerequisite artifact for test_spike1_aarch64_linux below",
         "cmd": [lake, "exe", "spike1_hello_aarch64_linux"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "test_spike1_aarch64_linux", "desc": "lake exe test_spike1_aarch64_linux",
         "group": "spikes",
         "long": "Spike 1 (Hello World) AArch64 Linux target test (in-Lean trace + QEMU user execution; "
                 "requires the lean prerequisite; qemu-aarch64 run if available, skipped if not).",
         "cmd": [lake, "exe", "test_spike1_aarch64_linux"], "slow": False, "tools": ["lean"], "allow_skip_code_2": True, "depends_on": ["spike1_hello_aarch64_linux"]},
        {"key": "spike2_fibonacci_windows", "desc": "lake exe spike2_fibonacci_windows",
         "group": "spikes",
         "long": "emits fib.exe -- prerequisite artifact for test_spike2_windows below",
         "cmd": [lake, "exe", "spike2_fibonacci_windows"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "test_spike2_windows", "desc": "lake exe test_spike2_windows",
         "group": "spikes",
         "long": "Spike 2 (Fibonacci) Windows target test",
         "cmd": [lake, "exe", "test_spike2_windows"], "slow": False, "tools": ["lean"], "depends_on": ["spike2_fibonacci_windows"]},
        {"key": "test_spike2_wasm", "desc": "lake exe test_spike2_wasm",
         "group": "spikes",
         "long": "Spike 2 (Fibonacci) Wasm target test (in-Lean trace + host runtime; "
                 "exit 2 = no host Wasm runner found, per Law 13(4))",
         "cmd": [lake, "exe", "test_spike2_wasm"], "slow": False, "tools": ["lean"], "allow_skip_code_2": True, "depends_on": ["lake_build"]},
        {"key": "test_spike3_windows", "desc": "lake exe test_spike3_windows",
         "group": "spikes",
         "long": "Spike 3 (Sort Lines) Windows target test",
         "cmd": [lake, "exe", "test_spike3_windows"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "test_spike3_wasm", "desc": "lake exe test_spike3_wasm",
         "group": "spikes",
         "long": "Spike 3 (Sort Lines) Wasm target test (in-Lean trace + host runtime; "
                 "exit 2 = no host Wasm runner found, per Law 13(4))",
         "cmd": [lake, "exe", "test_spike3_wasm"], "slow": False, "tools": ["lean"], "allow_skip_code_2": True, "depends_on": ["lake_build"]},
        {"key": "test_spike4", "desc": "lake exe test_spike4",
         "group": "spikes",
         "long": "Spike 4 (HTTP Server) target test",
         "cmd": [lake, "exe", "test_spike4"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "test_spike5", "desc": "lake exe test_spike5",
         "group": "spikes",
         "long": "Spike 5 (Gzip) target test",
         "cmd": [lake, "exe", "test_spike5"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "test_zlib", "desc": "lake exe test_zlib",
         "group": "spikes",
         "long": "Stdlib.Zlib unit/roundtrip test suite",
         "cmd": [lake, "exe", "test_zlib"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "test_png", "desc": "lake exe test_png",
         "group": "spikes",
         "long": "Stdlib.Png unit/roundtrip test suite",
         "cmd": [lake, "exe", "test_png"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "test_smolalloc", "desc": "lake exe test_smolalloc",
         "group": "spikes",
         "long": "Stdlib.SmolAlloc unit test suite",
         "cmd": [lake, "exe", "test_smolalloc"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "perf_fuzzer", "desc": "lake exe perf_fuzzer",
         "group": "fuzzers",
         "long": "x86-64 microarchitectural performance fuzzer",
         "cmd": [lake, "exe", "perf_fuzzer"], "slow": False, "tools": ["lean"], "depends_on": ["lake_build"]},
        # --- Differential fuzzers (slow; --quick-skippable) ---
        {"key": "x86_fuzzer", "desc": "lake exe x86_fuzzer",
         "group": "fuzzers",
         "long": "hardware-semantics differential fuzzer vs real silicon (mandatory pos/neg control vectors)",
         "cmd": [lake, "exe", "x86_fuzzer"], "slow": True, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "encoding_fuzzer", "desc": "lake exe encoding_fuzzer",
         "group": "fuzzers",
         "long": "binary-encoding differential fuzzer vs NASM (mandatory pos/neg control vectors)",
         "cmd": [lake, "exe", "encoding_fuzzer"], "slow": True, "tools": ["lean", "nasm"], "depends_on": ["lake_build"]},
        {"key": "wasm_fuzzer", "desc": "lake exe wasm_fuzzer",
         "group": "fuzzers",
         "long": "Wasm host-semantics differential fuzzer vs node",
         "cmd": [lake, "exe", "wasm_fuzzer"], "slow": True, "tools": ["lean", "node"], "depends_on": ["lake_build"]},
        {"key": "gzip_fuzzer", "desc": f"lake exe gzip_fuzzer --count {gzip_count}",
         "group": "fuzzers",
         "long": "gzip cross-differential fuzzer vs the python stdlib oracle",
         "cmd": [lake, "exe", "gzip_fuzzer", "--count", str(gzip_count)], "slow": True,
         "tools": ["lean", "python"], "depends_on": ["lake_build"]},
        {"key": "png_stability_fuzzer", "desc": "lake exe png_stability_fuzzer",
         "group": "fuzzers",
         "long": "PNG parser-stability fuzzer: parse b = r1 -> parse (write r1) = r2 -> r1 = r2. "
                 "No external oracle (unlike every fuzzer above) -- structured-mutation-generated "
                 "bytes only, self-checked against this codebase's own writer. The fuzzer's own "
                 "introduction found a genuine, pre-existing gap (parseIhdr did not validate "
                 "bitDepth against the standard PNG value set {1,2,4,8,16} or against colorType, "
                 "so unpackScanlinesToRGBA8's depth dispatch silently dropped pixel data for e.g. "
                 "bitDepth=0, or for bitDepth=16 paired with colorType=indexed); parseIhdr now "
                 "validates every (bitDepth, colorType) pair against RFC 2083 Sec 4.1.1's legality "
                 "table (png-rfc2083#section-4.1.1) and unpackScanlinesToRGBA8's dispatch is total "
                 "(an unhandled depth/colorType combination is an explicit .unsupportedBitDepth "
                 "error, not a silent no-op), so this gate now passes.",
         "cmd": [lake, "exe", "png_stability_fuzzer"], "slow": True, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "x86_stability_fuzzer", "desc": "lake exe x86_stability_fuzzer",
         "group": "fuzzers",
         "long": "x86-64 decoder/encoder parser-stability fuzzer: decode b = r1 -> decode "
                 "(encode r1) = r2 -> r1 = r2. No external oracle (complements encoding_fuzzer's "
                 "NASM oracle and x86_fuzzer's silicon oracle, neither of which cover every "
                 "encodable form) -- structured mutation of a valid encoding only.",
         "cmd": [lake, "exe", "x86_stability_fuzzer"], "slow": True, "tools": ["lean"], "depends_on": ["lake_build"]},
        {"key": "elf_stability_fuzzer", "desc": "lake exe elf_stability_fuzzer",
         "group": "fuzzers",
         "long": "ELF64 parser-stability fuzzer: parse b = r1 -> parse (write r1) = r2 -> r1 = r2 "
                 "(phrased as parse (write p) = p against an already-parsed p; see "
                 "Spikes/Common/ElfStabilityFuzzer.lean's header for why the two are equivalent). "
                 "No external oracle -- checks Gasm/Targets/ELF/Parser.lean (this project's first "
                 "ELF64 reader) against every real Linux Spike's actually-emitted binary plus "
                 "structured-mutation-generated bytes from the real writer, "
                 "Gasm.Targets.Linux.emitELF64Executable.",
         "cmd": [lake, "exe", "elf_stability_fuzzer"], "slow": True, "tools": ["lean"], "depends_on": ["lake_build"]},
    ]


def resolve_gate_cmd(cmd: List[str]) -> List[str]:
    """If cmd is [lake, 'exe', target, ...], and .lake/build/bin/target[.exe] exists,
    invokes the binary directly. This avoids Lake internal lock file contention
    when multiple gates execute concurrently in parallel."""
    if len(cmd) >= 3 and Path(cmd[0]).name.lower().startswith("lake") and cmd[1] == "exe":
        target = cmd[2]
        bin_dir = REPO_ROOT / ".lake" / "build" / "bin"
        candidate_exe = bin_dir / f"{target}.exe"
        candidate_bin = bin_dir / target
        if candidate_exe.is_file():
            return [str(candidate_exe)] + cmd[3:]
        elif candidate_bin.is_file():
            return [str(candidate_bin)] + cmd[3:]
    return cmd


def run_one_gate(cmd: List[str], capture: bool, timeout_s: float,
                 needs_lean_lease: bool = False) -> Dict:
    eff_cmd = resolve_gate_cmd(cmd)
    start = time.monotonic()
    sys.stdout.flush()
    sys.stderr.flush()
    try:
        lease = lean_process_lease() if needs_lean_lease else nullcontext()
        with lease:
            child_env = inherited_lease_environment() if needs_lean_lease else None
            if capture:
                proc = subprocess.run(eff_cmd, cwd=REPO_ROOT, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, text=True,
                                       encoding="utf-8", errors="replace", timeout=timeout_s,
                                       env=child_env)
                output = proc.stdout
                code = proc.returncode
            else:
                # Inherit the parent's stdout/stderr so a human watching a 15-25 minute run sees
                # live progress. `proc.returncode` below is STILL the direct exit code of THIS
                # exact process -- no shell, no pipe, no tee sits between us and it.
                proc = subprocess.run(eff_cmd, cwd=REPO_ROOT, timeout=timeout_s, env=child_env)
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
    print(" ORACLE / TOOLCHAIN VERSIONS (the oracle/toolchain provenance and Law 10 contracts -- recorded so cross-machine drift is attributable)")
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


def automatic_parallel_jobs(selected: List[Dict], cpu_count: Optional[int] = None) -> int:
    """Memory-safe worker default; the global lease additionally serializes Lean child trees."""
    if any(g.get("group") == "proofs" for g in selected):
        return 1
    available_cpus = cpu_count if cpu_count is not None else (os.cpu_count() or 1)
    return min(2, max(1, available_cpus))


# --------------------------------------------------------------------------------------------
# docs/REVIEW.md Law 13 meta-gate fixture (--self-test): a RE-RUNNABLE regression test for the gates
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
        _git_stage(probe)
        build_code, _ = _run_capture([lake, "build"], cwd=REPO_ROOT, timeout=600)
        build_ok = build_code == 0
        if build_ok:
            code, out = _run_capture([lake, "exe", "check_gates_axioms"], cwd=REPO_ROOT, timeout=300)
            red = code != 0 and "tc5SelfTestPlantedSorry" in (out or "") and "sorryAx" in (out or "")
    finally:
        _git_unstage(probe)
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
        _git_stage(probe)
        build_code, _ = _run_capture([lake, "build"], cwd=REPO_ROOT, timeout=600)
        build_ok = build_code == 0
        if build_ok:
            code, out = _run_capture(
                [sys.executable, "scripts/run_full_refs_coverage.py", "--full-repository"],
                cwd=REPO_ROOT, timeout=300)
            red = (code != 0 and "instInhabitedTc5SelfTestUncitedFoo" in (out or "")
                   and "_TC5SelfTestUncitedInstance.lean" in (out or ""))
    finally:
        _git_unstage(probe)
        GASM_ROOT_FILE.write_text(original_root, encoding="utf-8")
        probe.unlink(missing_ok=True)
    # Rebuild to confirm green again -- also restores .lake/build to a clean state for
    # whatever runs next in the same invocation of this script.
    revert_build_code, _ = _run_capture([lake, "build"], cwd=REPO_ROOT, timeout=600)
    green_after = False
    if revert_build_code == 0:
        revert_code, _ = _run_capture(
            [sys.executable, "scripts/run_full_refs_coverage.py", "--full-repository"],
            cwd=REPO_ROOT, timeout=300)
        green_after = revert_code == 0
    return {"defect": "uncited_anonymous_instance",
            "gate": "python scripts/run_full_refs_coverage.py --full-repository",
            "turned_red": build_ok and red, "green_after_revert": green_after,
            "note": None if build_ok else "lake build itself failed with the probe present (unexpected)"}


def run_self_test(json_mode: bool) -> int:
    py = shutil.which("python") or shutil.which("python3") or shutil.which("py") or "python"
    lake = shutil.which("lake") or "lake"

    if not json_mode:
        print("#" * 100)
        print("# docs/REVIEW.md Law 13 meta-gate fixture (--self-test): re-runnable planted-defect control vectors")
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
                         help="Run `lake clean` before anything else (the clean-rebuild contract, merge-train mode).")
    parser.add_argument("--json", action="store_true",
                         help="Emit a machine-parseable JSON summary to stdout (for CI/TC6); "
                              "suppresses live-streamed gate output and the human table. Always "
                              "includes a top-level \"mode\" field.")
    parser.add_argument("--gzip-count", type=int, default=25,
                         help="Iteration count passed to gzip_fuzzer's --count flag (default: 25).")
    parser.add_argument("--group", action="append", default=[],
                         help="Select one or more gate groups (e.g. build, linters, proofs, spikes, fuzzers; can be repeated or comma-separated).")
    parser.add_argument("--gate", action="append", default=[],
                         help="Select one or more specific gates by key (can be repeated).")
    parser.add_argument("--shard", type=str, default=None,
                         help="Shard index and total (e.g. 1/4, 2/4) to distribute gates across parallel runners.")
    parser.add_argument("-j", "--jobs", type=int, default=None,
                         help="Explicit worker count. Lean/Lake trees remain globally serialized; "
                              "a large value can still pressure the host with non-Lean tools.")
    parser.add_argument("--parallel", action="store_true",
                         help="Run independent gates concurrently. Automatic limit: proofs=1, "
                              "other selections<=2. Use --jobs for an explicit override.")
    parser.add_argument("--list-groups", action="store_true",
                         help="List all available gate groups and their gates, then exit.")
    parser.add_argument("--gate-timeout", type=float, default=DEFAULT_GATE_TIMEOUT_S,
                         help=f"Per-gate wall-clock timeout in seconds (default {DEFAULT_GATE_TIMEOUT_S}). "
                              "A gate that exceeds this is killed and reported as TIMEOUT, not left to "
                              "hang the runner (and any CI invoking it) forever.")
    parser.add_argument("--self-test", action="store_true",
                         help="Run the docs/REVIEW.md Law 13 meta-gate fixture instead of the normal gate "
                              "sequence: plant each of 6 known defects, assert the specific "
                              "gate goes red, revert, assert green again. See run_self_test().")
    args = parser.parse_args()

    if args.self_test:
        return run_self_test(args.json)

    gates = build_gate_table(args.gzip_count)

    if args.list_groups:
        groups: Dict[str, List[str]] = {}
        for g in gates:
            grp = g.get("group", "other")
            groups.setdefault(grp, []).append(g["key"])
        print("Available gate groups:")
        for grp, keys in sorted(groups.items()):
            print(f"  {grp:<12} ({len(keys)} gates): {', '.join(keys)}")
        return EXIT_OK

    json_mode = args.json
    mode = "quick" if args.quick else "full"

    GROUP_ALIASES = {
        "lint": "linters",
        "linter": "linters",
        "proof": "proofs",
        "spike": "spikes",
        "test": "spikes",
        "tests": "spikes",
        "fuzzer": "fuzzers",
    }
    valid_groups = {g.get("group") for g in gates if g.get("group")}

    requested_groups: Set[str] = set()
    if args.group:
        for g_arg in args.group:
            for item in g_arg.split(","):
                norm = item.strip().lower()
                norm = GROUP_ALIASES.get(norm, norm)
                if norm:
                    requested_groups.add(norm)
        unknown = requested_groups - valid_groups
        if unknown:
            sys.stderr.write(f"Unknown gate group(s): {', '.join(sorted(unknown))}. Valid groups: {', '.join(sorted(valid_groups))}\n")
            return EXIT_PREREQ_ABORT

    # Filter pipeline: groups -> quick -> specific gates -> shard
    selected = list(gates)
    if requested_groups:
        selected = [g for g in selected if g.get("group") in requested_groups]
    if args.quick:
        selected = [g for g in selected if not g["slow"]]
    if args.gate:
        selected = [g for g in selected if g["key"] in args.gate]
    if args.shard:
        parts = args.shard.split("/")
        if len(parts) == 2 and parts[0].isdigit() and parts[1].isdigit():
            k, n = int(parts[0]), int(parts[1])
            if 1 <= k <= n:
                selected = [g for i, g in enumerate(selected) if i % n == (k - 1)]
            else:
                sys.stderr.write(f"Invalid shard: {args.shard} (index must be between 1 and total)\n")
                return EXIT_PREREQ_ABORT
        else:
            sys.stderr.write(f"Invalid shard format: {args.shard} (expected K/N, e.g. 1/4)\n")
            return EXIT_PREREQ_ABORT

    selected_keys = {g["key"] for g in selected}

    if args.jobs is not None and args.jobs < 1:
        sys.stderr.write("--jobs must be at least 1\n")
        return EXIT_PREREQ_ABORT
    if args.jobs is not None:
        jobs = args.jobs
    elif args.parallel:
        # Proof executables can each import or scan a repository-sized environment. Running them
        # together has exhausted Windows system commit in practice. Other groups retain bounded
        # concurrency without turning CPU count into an unbounded memory multiplier.
        jobs = automatic_parallel_jobs(selected)
    else:
        jobs = 1

    if not json_mode:
        if args.jobs is not None and args.jobs > 2:
            print(f"WARNING: explicit --jobs={args.jobs} overrides the automatic worker cap. "
                  "Lean/Lake trees remain globally serialized, but other tools can still "
                  "consume substantial resources.")
        elif args.parallel and args.jobs is None:
            reason = "proof gates are memory-heavy" if jobs == 1 else "automatic memory-safe cap"
            print(f"[*] Parallel worker limit: {jobs} ({reason})")
        print("#" * 100)
        print("# gasm gate runner (scripts/run_gates.py) -- TC5")
        print(f"# repo root: {REPO_ROOT}")
        print(f"# mode: {mode.upper()}"
              f"{' (fuzzers + several gates skipped -- NOT sufficient for merge sign-off)' if args.quick else ''}"
              f"{f' [GROUPS: {', '.join(sorted(requested_groups))}]' if requested_groups else ''}"
              f"{f' [SHARD {args.shard}]' if args.shard else ''}"
              f"{f' [GATES: {', '.join(args.gate)}]' if args.gate else ''}"
              f"{f' [JOBS: {jobs}]' if jobs > 1 else ''}"
              f"{' + CLEAN' if args.clean else ''}")
        print("#" * 100)

    # --- Phase 0: prerequisite detection -- ALWAYS all, ALWAYS reported, regardless of mode
    prereqs = detect_all_prereqs()

    needed: Set[str] = set()
    for g in selected:
        needed.update(g["tools"])
    all_tools_in_table: Set[str] = set()
    for g in gates:
        all_tools_in_table.update(g["tools"])
    only_skipped_need = sorted(all_tools_in_table - needed)
    waived = [t for t in only_skipped_need if not prereqs[t]["found"]]

    if not json_mode:
        print_prereq_table(prereqs, waived=waived)
        if waived:
            print(f"\n[i] WAIVED (not enforced this run, no selected gate needs "
                  f"{'them' if len(waived) > 1 else 'it'}): {', '.join(waived)}")

    missing = [name for name in needed if not prereqs[name]["found"]]

    if missing:
        # ABORT THE WHOLE RUN -- fail-closed
        rows = []
        for g in gates:
            if g["key"] not in selected_keys:
                if requested_groups and g.get("group") not in requested_groups:
                    status = "SKIPPED (--group)"
                elif args.quick and g["slow"]:
                    status = "SKIPPED (--quick)"
                elif args.gate and g["key"] not in args.gate:
                    status = "SKIPPED (--gate)"
                elif args.shard:
                    status = "SKIPPED (--shard)"
                else:
                    status = "SKIPPED"
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
            print("! design (docs/REVIEW.md Law 13): a missing oracle is never silently skipped.")
            print("!" * 100)
            print_summary_table(rows)
        return EXIT_PREREQ_ABORT

    # --- Phase 1: optional `lake clean` (clean-rebuild merge-train mode) ---------------------
    clean_row = None
    if args.clean:
        lake = shutil.which("lake") or "lake"
        if not json_mode:
            print("\n[*] --clean: running `lake clean` before the gate sequence...")
        clean_res = run_one_gate([lake, "clean"], capture=json_mode,
                                 timeout_s=args.gate_timeout, needs_lean_lease=True)
        status = "PASS" if clean_res["exit_code"] == 0 else "FAIL"
        clean_row = {"key": "lake_clean", "status": status,
                     "exit_code": clean_res["exit_code"],
                     "wall_time": clean_res["wall_time"], "tool_info": "-"}
        if clean_res["exit_code"] != 0:
            if not json_mode:
                print("[!] `lake clean` failed -- aborting before the gate sequence "
                      "(a corrupted .lake/build tree makes every downstream result unreliable).")
            rows = [clean_row]
            for g in gates:
                rows.append({"key": g["key"], "status": "SKIPPED (lake clean failed)",
                             "exit_code": None, "wall_time": None, "tool_info": "-"})
            if json_mode:
                print(json.dumps({"mode": mode, "overall_status": "FAILED",
                                   "overall_exit_code": EXIT_GATE_FAILED,
                                   "prerequisites": prereqs, "gates": rows}, indent=2))
            else:
                print_summary_table(rows)
            return EXIT_GATE_FAILED

    # --- Phase 2: Execute selected gates (parallel if jobs > 1, sequential if jobs == 1) ---
    result_map: Dict[str, Dict] = {}

    if jobs > 1:
        if not json_mode:
            print(f"\n[*] Running {len(selected)} selected gates in parallel (max {jobs} concurrent workers)...")
        pending_gates = {g["key"]: g for g in selected}
        in_flight: Dict = {}

        with ThreadPoolExecutor(max_workers=jobs) as executor:
            while pending_gates or in_flight:
                # Find all gates that are ready to schedule
                ready = []
                failed_or_skipped_keys = {
                    k for k, v in result_map.items() if v["status"] != "PASS"
                }
                passed_keys = {
                    k for k, v in result_map.items() if v["status"] == "PASS"
                }

                for key, g in list(pending_gates.items()):
                    eff_deps = [d for d in g.get("depends_on", []) if d in selected_keys]
                    blocked_by = [d for d in eff_deps if d in failed_or_skipped_keys]
                    if blocked_by:
                        del pending_gates[key]
                        reason = f"SKIPPED (dependency '{blocked_by[0]}' failed)"
                        tool_info = _tool_info_for(g, prereqs)
                        result_map[key] = {
                            "key": key, "status": reason, "exit_code": None,
                            "wall_time": None, "tool_info": tool_info, "output": None
                        }
                        if not json_mode:
                            print(f"  [SKIP   ] {key:<28} -- dependency '{blocked_by[0]}' failed")
                        continue

                    if all(d in passed_keys for d in eff_deps):
                        ready.append(g)

                for g in ready:
                    key = g["key"]
                    del pending_gates[key]
                    if not json_mode:
                        print(f"  [START  ] {key:<28} ($ {' '.join(g['cmd'])})")
                    fut = executor.submit(
                        run_one_gate, g["cmd"], True, args.gate_timeout, "lean" in g["tools"]
                    )
                    in_flight[fut] = g

                if in_flight:
                    done, _ = wait(in_flight.keys(), return_when=FIRST_COMPLETED)
                    for fut in done:
                        g = in_flight.pop(fut)
                        key = g["key"]
                        tool_info = _tool_info_for(g, prereqs)
                        res = fut.result()
                        if res["timed_out"]:
                            status = f"TIMEOUT (> {args.gate_timeout:.0f}s)"
                            exit_code = None
                        elif res["launch_error"] is not None:
                            status = f"ERROR: could not launch ({res['launch_error']})"
                            exit_code = None
                        elif res["exit_code"] == 0:
                            status = "PASS"
                            exit_code = 0
                        elif res["exit_code"] == 2 and g.get("allow_skip_code_2", False):
                            status = "SKIPPED (runner not available)"
                            exit_code = 2
                        else:
                            status = "FAIL"
                            exit_code = res["exit_code"]

                        result_map[key] = {
                            "key": key, "status": status, "exit_code": exit_code,
                            "wall_time": res["wall_time"], "tool_info": tool_info,
                            "output": res["output"]
                        }
                        if not json_mode:
                            wt_str = fmt_seconds(res["wall_time"])
                            status_tag = f"[{status:<7}]"
                            print(f"  {status_tag} {key:<28} ({wt_str})")
                            if status not in ("PASS", "SKIPPED (runner not available)") and res["output"]:
                                print(f"\n--- Output from {key} ---")
                                print(res["output"].rstrip())
                                print("-" * 40 + "\n")
    else:
        for g in selected:
            key = g["key"]
            eff_deps = [d for d in g.get("depends_on", []) if d in selected_keys]
            if any(result_map.get(d, {}).get("status") not in ("PASS", "SKIPPED (runner not available)") for d in eff_deps):
                failed_dep = [d for d in eff_deps if result_map.get(d, {}).get("status") not in ("PASS", "SKIPPED (runner not available)")][0]
                result_map[key] = {
                    "key": key, "status": f"SKIPPED (dependency '{failed_dep}' failed)",
                    "exit_code": None, "wall_time": None,
                    "tool_info": _tool_info_for(g, prereqs), "output": None
                }
                continue

            tool_info = _tool_info_for(g, prereqs)
            if not json_mode:
                print("\n" + "-" * 100)
                print(f"[GATE] {g['desc']}  --  {g['long']}")
                print(f"       $ {' '.join(g['cmd'])}   (cwd={REPO_ROOT})")
                print("-" * 100)

            res = run_one_gate(g["cmd"], capture=json_mode, timeout_s=args.gate_timeout,
                               needs_lean_lease="lean" in g["tools"])
            if res["timed_out"]:
                status = f"TIMEOUT (> {args.gate_timeout:.0f}s)"
                exit_code = None
            elif res["launch_error"] is not None:
                status = f"ERROR: could not launch ({res['launch_error']})"
                exit_code = None
            elif res["exit_code"] == 0:
                status = "PASS"
                exit_code = 0
            elif res["exit_code"] == 2 and g.get("allow_skip_code_2", False):
                status = "SKIPPED (runner not available)"
                exit_code = 2
            else:
                status = "FAIL"
                exit_code = res["exit_code"]

            result_map[key] = {
                "key": key, "status": status, "exit_code": exit_code,
                "wall_time": res["wall_time"], "tool_info": tool_info,
                "output": res["output"] if json_mode else None
            }

    result_rows: List[Dict] = []
    if clean_row is not None:
        result_rows.append(clean_row)

    for g in gates:
        k = g["key"]
        if k in result_map:
            result_rows.append(result_map[k])
        else:
            if requested_groups and g.get("group") not in requested_groups:
                sk_reason = "SKIPPED (--group)"
            elif args.quick and g["slow"]:
                sk_reason = "SKIPPED (--quick)"
            elif args.gate and k not in args.gate:
                sk_reason = "SKIPPED (--gate)"
            elif args.shard:
                sk_reason = "SKIPPED (--shard)"
            else:
                sk_reason = "SKIPPED"
            result_rows.append({
                "key": k, "status": sk_reason, "exit_code": None,
                "wall_time": None, "tool_info": "-"
            })

    selected_rows = [r for r in result_rows if r["key"] in selected_keys]
    overall_pass = (len(selected_rows) > 0) and all(r["status"] in ("PASS", "SKIPPED (runner not available)") for r in selected_rows)

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

