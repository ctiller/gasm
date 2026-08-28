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
tests/e2e/harness.py - End-to-End Test Harness & Framework for AArch64 QEMU Support in gasm.

Provides core execution context, prerequisite detection, ELF verification, process execution,
and standardized reporting with fail-honest exit code semantics:
  - Exit 0: All tests PASSED.
  - Exit 1: One or more tests FAILED.
  - Exit 2: Tests SKIPPED due to missing host runner (e.g. QEMU) and all other tests PASSED.
"""

import enum
import os
import re
import shutil
import struct
import subprocess
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any


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

        self.python_exe = sys_exe = shutil.which("python3") or shutil.which("python") or "python"
        self.lake_exe = shutil.which("lake")
        self.lean_exe = shutil.which("lean")

        # QEMU System Runner for AArch64 Bare Metal
        self.qemu_system = self._detect_qemu_system()

        # QEMU User Runner for AArch64 Linux
        self.qemu_user = self._detect_qemu_user()

        # LLVM-MC for Differential Encoding
        self.llvm_mc = self._detect_llvm_mc()

    def _detect_qemu_system(self) -> Optional[str]:
        env_override = os.environ.get("GASM_QEMU_AARCH64")
        if env_override and shutil.which(env_override):
            return env_override
        candidates = [
            shutil.which("qemu-system-aarch64"),
            shutil.which("qemu-system-aarch64.exe"),
            "/usr/bin/qemu-system-aarch64",
            "/usr/local/bin/qemu-system-aarch64",
            r"C:\Program Files\qemu\qemu-system-aarch64.exe",
        ]
        for c in candidates:
            if c and os.path.exists(c):
                return c
        return None

    def _detect_qemu_user(self) -> Optional[str]:
        env_override = os.environ.get("GASM_QEMU_USER_AARCH64")
        if env_override and shutil.which(env_override):
            return env_override
        candidates = [
            shutil.which("qemu-aarch64"),
            shutil.which("qemu-aarch64-static"),
            shutil.which("qemu-aarch64.exe"),
            "/usr/bin/qemu-aarch64",
            "/usr/bin/qemu-aarch64-static",
            "/usr/local/bin/qemu-aarch64",
        ]
        for c in candidates:
            if c and os.path.exists(c):
                return c
        return None

    def _detect_llvm_mc(self) -> Optional[str]:
        env_override = os.environ.get("GASM_LLVM_MC")
        if env_override and shutil.which(env_override):
            return env_override
        candidates = [
            shutil.which("llvm-mc-19"),
            shutil.which("llvm-mc"),
            shutil.which("llvm-mc.exe"),
            "/usr/bin/llvm-mc-19",
            "/usr/bin/llvm-mc",
            "/usr/local/bin/llvm-mc",
        ]
        for c in candidates:
            if c and os.path.exists(c):
                return c
        return None

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
        except Exception as e:
            return None, "", f"Execution error: {e}"

    def run_lean_target(self, target: str, timeout: float = 120.0) -> Tuple[Optional[int], str, str]:
        """Runs a Lake executable target."""
        if not self.lake_exe:
            return None, "", "Lake not found on PATH"
        return self.run_cmd([self.lake_exe, "exe", target], timeout=timeout)

    def validate_elf64_aarch64(self, file_path: Path) -> Tuple[bool, str]:
        """
        Validates an AArch64 ELF64 binary header according to ELF and ARM specifications:
          - EI_MAG: 0x7F 'E' 'L' 'F'
          - EI_CLASS: 2 (64-bit)
          - EI_DATA: 1 (2's complement, little endian)
          - EI_VERSION: 1 (EV_CURRENT)
          - EI_OSABI: 0 (System V) or 3 (Linux)
          - e_type: 2 (ET_EXEC)
          - e_machine: 183 (EM_AARCH64 = 0x00B7)
          - e_version: 1
          - e_entry: > 0
        """
        if not file_path.exists():
            return False, f"File does not exist: {file_path}"
        try:
            with open(file_path, "rb") as f:
                header = f.read(64)
            if len(header) < 64:
                return False, f"File too small for ELF64 header: {len(header)} bytes"

            # Check magic
            if header[0:4] != b"\x7fELF":
                return False, f"Invalid ELF magic: {header[0:4]!r}"
            ei_class = header[4]
            if ei_class != 2:
                return False, f"Invalid ELF class (expected 2 for 64-bit, got {ei_class})"
            ei_data = header[5]
            if ei_data != 1:
                return False, f"Invalid ELF data encoding (expected 1 for little-endian, got {ei_data})"
            ei_version = header[6]
            if ei_version != 1:
                return False, f"Invalid ELF version (expected 1, got {ei_version})"

            # Unpack e_type (2 bytes), e_machine (2 bytes), e_version (4 bytes), e_entry (8 bytes)
            e_type, e_machine, e_version, e_entry = struct.unpack("<HHIQ", header[16:32])
            if e_type != 2:
                return False, f"Invalid e_type (expected 2 for ET_EXEC, got {e_type})"
            if e_machine != 183:  # EM_AARCH64 = 0x00B7 = 183
                return False, f"Invalid e_machine (expected 183 for EM_AARCH64, got {e_machine})"
            if e_version != 1:
                return False, f"Invalid e_version (expected 1, got {e_version})"
            if e_entry == 0:
                return False, "Invalid e_entry (entry point address is 0)"

            return True, f"Valid AArch64 ELF64 executable: e_entry=0x{e_entry:016x}, e_machine=EM_AARCH64(183)"
        except Exception as e:
            return False, f"Error parsing ELF header: {e}"


class TestCase:
    """Base class for all opaque-box E2E test cases."""

    def __init__(
        self,
        test_id: str,
        name: str,
        tier: int,
        milestone: str,
        feature_id: int,
        description: str,
    ):
        self.test_id = test_id
        self.name = name
        self.tier = tier
        self.milestone = milestone
        self.feature_id = feature_id
        self.description = description

    def run(self, ctx: ExecutionContext) -> TestResult:
        raise NotImplementedError
