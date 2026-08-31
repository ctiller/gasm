#!/usr/bin/env python3
# Copyright 2026 Google LLC
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
tests/e2e/harness.py - End-to-End Test Harness & Framework for x86-64 GPR Support in gasm.

Provides core execution context, prerequisite detection, NASM golden oracle assembly,
Lean file inspection, process execution, and standardized reporting with fail-honest
exit code semantics:
  - Exit 0: All tests PASSED.
  - Exit 1: One or more tests FAILED or ERROR.
  - Exit 2: Tests SKIPPED due to missing host runner/oracle and all other tests PASSED.
"""

import enum
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple, Union

SCRIPTS_DIR = Path(__file__).resolve().parents[2] / "scripts"
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

try:
    from lean_process_lease import inherited_lease_environment, lean_process_lease
except ImportError:
    # Fallback if scripts/lean_process_lease.py cannot be imported
    def lean_process_lease():
        import contextlib
        return contextlib.nullcontext()

    def inherited_lease_environment():
        return {}


class TestStatus(enum.Enum):
    PASS = "PASS"
    FAIL = "FAIL"
    SKIP = "SKIP"
    ERROR = "ERROR"


@dataclass
class TestResult:
    test_id: str
    name: str
    tier: int
    milestone: str
    feature_id: int
    status: TestStatus
    message: str = ""
    duration_s: float = 0.0
    detail: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {
            "test_id": self.test_id,
            "name": self.name,
            "tier": self.tier,
            "milestone": self.milestone,
            "feature_id": self.feature_id,
            "status": self.status.value,
            "message": self.message,
            "duration_s": round(self.duration_s, 4),
            "detail": self.detail,
        }


class ExecutionContext:
    """Manages paths, external tools, process spawning, and binary artifact inspections."""

    def __init__(self, repo_root: Optional[Path] = None):
        if repo_root is None:
            self.repo_root = Path(__file__).resolve().parent.parent.parent
        else:
            self.repo_root = Path(repo_root).resolve()

        self.python_exe = shutil.which("python3") or shutil.which("python") or "python"
        self.lake_exe = shutil.which("lake")
        self.lean_exe = shutil.which("lean")
        self.nasm_exe = self._detect_nasm()
        self._cached_files: Dict[str, str] = {}

    def _detect_nasm(self) -> Optional[str]:
        env_override = os.environ.get("GASM_NASM")
        if env_override and shutil.which(env_override):
            return env_override
        candidates = [
            shutil.which("nasm"),
            shutil.which("nasm.exe"),
            "/usr/bin/nasm",
            "/usr/local/bin/nasm",
        ]
        for c in candidates:
            if c and os.path.exists(c):
                return c
        return None

    def read_repo_file(self, rel_path: Union[str, Path]) -> Optional[str]:
        """Reads a file relative to repo_root with caching."""
        key = str(rel_path)
        if key in self._cached_files:
            return self._cached_files[key]
        full_path = self.repo_root / rel_path
        if not full_path.is_file():
            return None
        try:
            content = full_path.read_text(encoding="utf-8", errors="replace")
            self._cached_files[key] = content
            return content
        except Exception:
            return None

    def file_exists(self, rel_path: Union[str, Path]) -> bool:
        return (self.repo_root / rel_path).is_file()

    def check_file_contains(
        self, rel_path: Union[str, Path], required_tokens: List[str]
    ) -> Tuple[bool, List[str]]:
        """Checks if all required tokens exist in the specified relative file."""
        content = self.read_repo_file(rel_path)
        if content is None:
            return False, [f"File not found: {rel_path}"]
        missing = [t for t in required_tokens if t not in content]
        return len(missing) == 0, missing

    def check_file_regex(
        self, rel_path: Union[str, Path], pattern: str, flags: int = 0
    ) -> Tuple[bool, Optional[str]]:
        """Checks if regex pattern matches in the specified relative file."""
        content = self.read_repo_file(rel_path)
        if content is None:
            return False, f"File not found: {rel_path}"
        m = re.search(pattern, content, flags)
        if m:
            return True, m.group(0)
        return False, f"Pattern not found: {pattern}"

    def assemble_nasm(self, asm_code: str) -> Tuple[bool, bytes, str]:
        """
        Assembles x86-64 assembly string into raw binary bytes using NASM golden oracle.
        Automatically prepends 'BITS 64\\nDEFAULT REL\\n' if not present.
        """
        if not self.nasm_exe:
            return False, b"", "NASM executable not found on PATH or GASM_NASM"

        header = "BITS 64\nDEFAULT REL\n"
        full_asm = header + asm_code if "BITS" not in asm_code.upper() else asm_code

        with tempfile.NamedTemporaryFile(suffix=".asm", delete=False, mode="w", encoding="utf-8") as f_asm:
            f_asm.write(full_asm)
            asm_path = Path(f_asm.name)

        bin_path = asm_path.with_suffix(".bin")
        try:
            cmd = [self.nasm_exe, "-f", "bin", str(asm_path), "-o", str(bin_path)]
            proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=10.0)
            if proc.returncode != 0:
                return False, b"", f"NASM assembly failed: {proc.stderr.strip()}"
            if not bin_path.exists():
                return False, b"", "NASM exited 0 but binary output file was not created"
            raw_bytes = bin_path.read_bytes()
            return True, raw_bytes, ""
        except subprocess.TimeoutExpired:
            return False, b"", "NASM assembly timed out after 10s"
        except Exception as e:
            return False, b"", f"NASM invocation error: {e}"
        finally:
            if asm_path.exists():
                asm_path.unlink()
            if bin_path.exists():
                bin_path.unlink()

    def run_cmd(
        self,
        cmd: List[str],
        timeout: float = 60.0,
        cwd: Optional[Path] = None,
        env: Optional[Dict[str, str]] = None,
    ) -> Tuple[Optional[int], str, str]:
        """Runs a subprocess directly (no shell, no pipe) returning (returncode, stdout, stderr)."""
        run_env = os.environ.copy()
        if env:
            run_env.update(env)
        work_dir = cwd or self.repo_root
        try:
            executable = Path(cmd[0]).name.lower()
            needs_lean_lease = executable in {"lake", "lake.exe", "lean", "lean.exe"}
            if needs_lean_lease:
                with lean_process_lease():
                    run_env.update(inherited_lease_environment())
                    proc = subprocess.run(
                        cmd,
                        cwd=work_dir,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        text=True,
                        timeout=timeout,
                        env=run_env,
                    )
            else:
                proc = subprocess.run(
                    cmd,
                    cwd=work_dir,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    timeout=timeout,
                    env=run_env,
                )
            return proc.returncode, proc.stdout, proc.stderr
        except FileNotFoundError as e:
            return None, "", f"Executable not found: {e}"
        except subprocess.TimeoutExpired as e:
            return None, "", f"Command timed out after {timeout}s: {e}"
        except (OSError, TimeoutError, ValueError) as e:
            return None, "", f"Execution error: {e}"

    def run_lean_target(self, target: str, timeout: float = 120.0) -> Tuple[Optional[int], str, str]:
        """Runs a Lake executable target."""
        if not self.lake_exe:
            return None, "", "Lake not found on PATH"
        return self.run_cmd([self.lake_exe, "exe", target], timeout=timeout)


class TestCase:
    """Base class for all opaque-box E2E test cases."""

    def __init__(
        self,
        test_id: str,
        name: str,
        tier: int,
        milestone: str,
        feature_id: int,
        description: str = "",
    ):
        self.test_id = test_id
        self.name = name
        self.tier = tier
        self.milestone = milestone
        self.feature_id = feature_id
        self.description = description

    def run(self, ctx: ExecutionContext) -> TestResult:
        raise NotImplementedError("Subclasses must implement run()")
