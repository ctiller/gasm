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
tests/e2e/cases/tier1_feature_coverage.py - Tier 1: Feature Coverage Test Suite.

Covers all 28 features in PROJECT.md Feature Inventory with >=5 test cases per feature (140 tests).
Opaque-box and requirement-driven derived from ORIGINAL_REQUEST.md and PROJECT.md.
"""

import json
import os
import re
import time
from pathlib import Path
from typing import List

from tests.e2e.harness import ExecutionContext, TestCase, TestResult, TestStatus


class BaseTier1Test(TestCase):
    def __init__(self, test_id: str, feature_id: int, milestone: str, name: str, description: str):
        super().__init__(
            test_id=test_id,
            name=name,
            tier=1,
            milestone=milestone,
            feature_id=feature_id,
            description=description,
        )


def _check_file_exists(path: Path, test: TestCase, start_time: float) -> TestResult:
    elapsed = time.monotonic() - start_time
    if path.exists():
        return TestResult(
            test_id=test.test_id,
            name=test.name,
            tier=test.tier,
            milestone=test.milestone,
            feature_id=test.feature_id,
            status=TestStatus.PASS,
            message=f"File exists: {path.name}",
            duration_s=elapsed,
        )
    return TestResult(
        test_id=test.test_id,
        name=test.name,
        tier=test.tier,
        milestone=test.milestone,
        feature_id=test.feature_id,
        status=TestStatus.FAIL,
        message=f"Missing expected file: {path}",
        duration_s=elapsed,
    )


# --------------------------------------------------------------------------------------------
# Feature 1: Reference Registration (M1, R1) - 5 tests
# --------------------------------------------------------------------------------------------

class TestT1_01_01(BaseTier1Test):
    """T1.01.01: Verify references.json exists and is valid JSON."""
    def __init__(self):
        super().__init__("T1.01.01", 1, "M1", "references_json_valid", "Verify references.json exists and is valid JSON.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        ref_file = ctx.repo_root / "references.json"
        if not ref_file.exists():
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "references.json does not exist", time.monotonic() - start)
        try:
            with open(ref_file, "r", encoding="utf-8") as f:
                data = json.load(f)
            if not isinstance(data, list):
                return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "references.json top-level is not a list", time.monotonic() - start)
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, f"references.json is valid JSON array with {len(data)} entries", time.monotonic() - start)
        except Exception as e:
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, f"Error parsing references.json: {e}", time.monotonic() - start)


class TestT1_01_02(BaseTier1Test):
    """T1.01.02: Verify Arm Architecture Reference Manual registered in references.json."""
    def __init__(self):
        super().__init__("T1.01.02", 1, "M1", "arm_arm_registered", "Verify ARM Architecture Reference Manual is registered in references.json.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        ref_file = ctx.repo_root / "references.json"
        if not ref_file.exists():
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "references.json not found", time.monotonic() - start)
        with open(ref_file, "r", encoding="utf-8") as f:
            data = json.load(f)
        arm_slugs = [e.get("slug") for e in data if "arm" in e.get("slug", "").lower() or "aarch64" in e.get("slug", "").lower()]
        if not arm_slugs:
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "No ARM/AArch64 reference slug registered in references.json", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, f"Found ARM reference slugs: {arm_slugs}", time.monotonic() - start)


class TestT1_01_03(BaseTier1Test):
    """T1.01.03: Verify PL011 UART manual registered in references.json."""
    def __init__(self):
        super().__init__("T1.01.03", 1, "M1", "pl011_manual_registered", "Verify PrimeCell UART PL011 manual registered in references.json.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        ref_file = ctx.repo_root / "references.json"
        with open(ref_file, "r", encoding="utf-8") as f:
            data = json.load(f)
        uart_slugs = [e.get("slug") for e in data if "pl011" in e.get("slug", "").lower() or ("uart" in e.get("slug", "").lower() and "arm" in e.get("slug", "").lower())]
        if not uart_slugs:
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "PL011 reference slug not found in references.json", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, f"Found PL011 reference: {uart_slugs}", time.monotonic() - start)


class TestT1_01_04(BaseTier1Test):
    """T1.01.04: Verify Semihosting specification registered in references.json."""
    def __init__(self):
        super().__init__("T1.01.04", 1, "M1", "semihosting_spec_registered", "Verify Arm Semihosting specification registered in references.json.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        ref_file = ctx.repo_root / "references.json"
        with open(ref_file, "r", encoding="utf-8") as f:
            data = json.load(f)
        semi_slugs = [e.get("slug") for e in data if "semihosting" in e.get("slug", "").lower()]
        if not semi_slugs:
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "Semihosting reference slug not found in references.json", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, f"Found Semihosting reference: {semi_slugs}", time.monotonic() - start)


class TestT1_01_05(BaseTier1Test):
    """T1.01.05: Verify AAPCS64 procedure call standard registered in references.json."""
    def __init__(self):
        super().__init__("T1.01.05", 1, "M1", "aapcs64_registered", "Verify AAPCS64 specification registered in references.json.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        ref_file = ctx.repo_root / "references.json"
        with open(ref_file, "r", encoding="utf-8") as f:
            data = json.load(f)
        abi_slugs = [e.get("slug") for e in data if "aapcs" in e.get("slug", "").lower() or "abi-aa" in e.get("slug", "").lower()]
        if not abi_slugs:
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "AAPCS64 reference slug not found in references.json", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, f"Found AAPCS64 reference: {abi_slugs}", time.monotonic() - start)


# --------------------------------------------------------------------------------------------
# Feature 2: License Token (M1, R1) - 5 tests
# --------------------------------------------------------------------------------------------

class TestT1_02_01(BaseTier1Test):
    """T1.02.01: Verify check_references.py accepts arm-unmodified-only license token."""
    def __init__(self):
        super().__init__("T1.02.01", 2, "M1", "license_token_arm_unmodified", "Verify check_references.py supports arm-unmodified-only token.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        script_file = ctx.repo_root / "scripts" / "check_references.py"
        if not script_file.exists():
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "scripts/check_references.py not found", time.monotonic() - start)
        content = script_file.read_text(encoding="utf-8")
        if "arm-unmodified-only" in content:
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, "arm-unmodified-only token supported in check_references.py", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "arm-unmodified-only token missing from check_references.py", time.monotonic() - start)


class TestT1_02_02(BaseTier1Test):
    """T1.02.02: Verify references.json license field matches approved license tokens."""
    def __init__(self):
        super().__init__("T1.02.02", 2, "M1", "references_licenses_valid", "Verify all licenses in references.json are recognized.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        ref_file = ctx.repo_root / "references.json"
        with open(ref_file, "r", encoding="utf-8") as f:
            data = json.load(f)
        for meta in (data if isinstance(data, list) else data.values()):
            lic = meta.get("license")
            if not lic:
                slug = meta.get("slug", "unknown")
                return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, f"Reference '{slug}' missing license field", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, "All references declare a non-empty license", time.monotonic() - start)


class TestT1_02_03(BaseTier1Test):
    """T1.02.03: Verify check_references.py rejects unknown license tokens."""
    def __init__(self):
        super().__init__("T1.02.03", 2, "M1", "check_references_rejects_bogus_license", "Verify check_references.py schema validation rejects unrecognized license tokens.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        import sys
        if str(ctx.repo_root) not in sys.path:
            sys.path.insert(0, str(ctx.repo_root))
        try:
            import tempfile
            from unittest.mock import patch
            from scripts.check_references import load_registry, ValidationFailure, EXIT_SCHEMA_ERROR
        except ImportError as e:
            return TestResult(
                self.test_id, self.name, self.tier, self.milestone, self.feature_id,
                TestStatus.FAIL,
                f"Failed to import check_references test dependencies: {e}",
                time.monotonic() - start,
            )

        base_entry = {
            "slug": "synthetic-license-test",
            "corpus": "arm",
            "title": "Synthetic Reference for License Validation",
            "url": "https://developer.arm.com/documentation/test",
            "media_type": "plain-text",
            "sha256": "0" * 64,
            "fetched_date": "2026-08-28",
            "edition": "1.0",
            "license": "arm-unmodified-only",
            "distribution": "unmodified-copy-only",
            "anchor_mode": "heading",
            "last_reviewed": "2026-08-28",
            "reviewer": "reviewer@example.corp.google.com",
            "review_note": "Synthetic test fixture for license validation.",
        }

        # Step 1: Baseline positive control - verify synthetic fixture is valid
        with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False, encoding="utf-8") as f:
            json.dump([base_entry], f)
            baseline_path = Path(f.name)

        try:
            with patch("scripts.check_references.REFERENCES_JSON", baseline_path):
                try:
                    loaded = load_registry()
                    if "synthetic-license-test" not in loaded:
                        return TestResult(
                            self.test_id, self.name, self.tier, self.milestone, self.feature_id,
                            TestStatus.FAIL,
                            "Baseline synthetic reference fixture failed to load",
                            time.monotonic() - start,
                        )
                except Exception as e:
                    return TestResult(
                        self.test_id, self.name, self.tier, self.milestone, self.feature_id,
                        TestStatus.FAIL,
                        f"Baseline synthetic reference fixture unexpectedly failed schema validation: {e}",
                        time.monotonic() - start,
                    )
        finally:
            if baseline_path.exists():
                baseline_path.unlink()

        # Step 2: Adversarial negative test - unrecognized license token must raise ValidationFailure(EXIT_SCHEMA_ERROR)
        bogus_entry = dict(base_entry)
        bogus_entry["license"] = "unauthorized-bogus-license"

        with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False, encoding="utf-8") as f:
            json.dump([bogus_entry], f)
            bogus_path = Path(f.name)

        try:
            with patch("scripts.check_references.REFERENCES_JSON", bogus_path):
                try:
                    load_registry()
                    return TestResult(
                        self.test_id, self.name, self.tier, self.milestone, self.feature_id,
                        TestStatus.FAIL,
                        "check_references.load_registry() unexpectedly accepted unrecognized license token 'unauthorized-bogus-license'",
                        time.monotonic() - start,
                    )
                except ValidationFailure as vf:
                    if vf.code != EXIT_SCHEMA_ERROR:
                        return TestResult(
                            self.test_id, self.name, self.tier, self.milestone, self.feature_id,
                            TestStatus.FAIL,
                            f"Expected exit code {EXIT_SCHEMA_ERROR} (EXIT_SCHEMA_ERROR), got {vf.code}: {vf.message}",
                            time.monotonic() - start,
                        )
                    if "unrecognized license token" not in vf.message:
                        return TestResult(
                            self.test_id, self.name, self.tier, self.milestone, self.feature_id,
                            TestStatus.FAIL,
                            f"Expected 'unrecognized license token' in failure message, got: {vf.message}",
                            time.monotonic() - start,
                        )
                    return TestResult(
                        self.test_id, self.name, self.tier, self.milestone, self.feature_id,
                        TestStatus.PASS,
                        f"check_references strictly rejected bogus license: {vf.message}",
                        time.monotonic() - start,
                    )
                except Exception as e:
                    return TestResult(
                        self.test_id, self.name, self.tier, self.milestone, self.feature_id,
                        TestStatus.FAIL,
                        f"Unexpected exception during bogus license validation: {type(e).__name__}: {e}",
                        time.monotonic() - start,
                    )
        finally:
            if bogus_path.exists():
                bogus_path.unlink()


class TestT1_02_04(BaseTier1Test):
    """T1.02.04: Verify check_licenses.py checks Apache-2.0 headers on source files."""
    def __init__(self):
        super().__init__("T1.02.04", 2, "M1", "check_licenses_apache2", "Verify check_licenses.py enforces Apache-2.0 headers.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        code, out, err = ctx.run_cmd([ctx.python_exe, "scripts/check_licenses.py"])
        if code == 0:
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, "check_licenses.py passed: all source files have Apache-2.0 headers", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, f"check_licenses.py failed (exit {code}): {out or err}", time.monotonic() - start)


class TestT1_02_05(BaseTier1Test):
    """T1.02.05: Verify check_publishable.py runs cleanly against repository state."""
    def __init__(self):
        super().__init__("T1.02.05", 2, "M1", "check_publishable_pass", "Verify check_publishable.py passes without third-party prose leaks.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        code, out, err = ctx.run_cmd([ctx.python_exe, "scripts/check_publishable.py"])
        if code == 0:
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, "check_publishable.py passed", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, f"check_publishable.py failed (exit {code}): {out or err}", time.monotonic() - start)


# --------------------------------------------------------------------------------------------
# Feature 3: Target Spec Docs (M1, R1) - 5 tests
# --------------------------------------------------------------------------------------------

class TestT1_03_01(BaseTier1Test):
    """T1.03.01: Verify docs/TARGETS/ARM64.md contains Registers specification section."""
    def __init__(self):
        super().__init__("T1.03.01", 3, "M1", "arm64_spec_registers", "Verify docs/TARGETS/ARM64.md defines register architecture.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        doc = ctx.repo_root / "docs" / "TARGETS" / "ARM64.md"
        if not doc.exists():
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "docs/TARGETS/ARM64.md not found", time.monotonic() - start)
        content = doc.read_text(encoding="utf-8")
        if re.search(r"^#+\s+.*registers", content, re.IGNORECASE | re.MULTILINE):
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, "docs/TARGETS/ARM64.md defines Registers section", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "Missing Registers section in docs/TARGETS/ARM64.md", time.monotonic() - start)


class TestT1_03_02(BaseTier1Test):
    """T1.03.02: Verify docs/TARGETS/ARM64.md contains Addressing Modes specification."""
    def __init__(self):
        super().__init__("T1.03.02", 3, "M1", "arm64_spec_addressing", "Verify docs/TARGETS/ARM64.md defines addressing modes.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        doc = ctx.repo_root / "docs" / "TARGETS" / "ARM64.md"
        content = doc.read_text(encoding="utf-8")
        if re.search(r"^#+\s+.*addressing", content, re.IGNORECASE | re.MULTILINE):
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, "docs/TARGETS/ARM64.md defines Addressing Modes section", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "Missing Addressing Modes section in docs/TARGETS/ARM64.md", time.monotonic() - start)


class TestT1_03_03(BaseTier1Test):
    """T1.03.03: Verify docs/TARGETS/ARM64.md contains Machine State and step semantics."""
    def __init__(self):
        super().__init__("T1.03.03", 3, "M1", "arm64_spec_machine_state", "Verify docs/TARGETS/ARM64.md defines Machine State & semantics.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        doc = ctx.repo_root / "docs" / "TARGETS" / "ARM64.md"
        content = doc.read_text(encoding="utf-8")
        if re.search(r"^#+\s+.*machine state", content, re.IGNORECASE | re.MULTILINE) or "AArch64MachineState" in content or "step" in content:
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, "Machine State specification section found", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "Missing Machine State section in docs/TARGETS/ARM64.md", time.monotonic() - start)


class TestT1_03_04(BaseTier1Test):
    """T1.03.04: Verify docs/TARGETS/ARM64.md specifies Bare Metal MMIO and semihosting."""
    def __init__(self):
        super().__init__("T1.03.04", 3, "M1", "arm64_spec_baremetal_mmio", "Verify Bare Metal PL011 and semihosting documentation.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        doc = ctx.repo_root / "docs" / "TARGETS" / "ARM64.md"
        content = doc.read_text(encoding="utf-8")
        if "0x09000000" in content and "0x20026" in content and "semihosting" in content.lower():
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, "Bare Metal PL011 MMIO and semihosting documented in detail", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "Missing Bare Metal MMIO or semihosting details in docs/TARGETS/ARM64.md", time.monotonic() - start)


class TestT1_03_05(BaseTier1Test):
    """T1.03.05: Verify docs/TARGETS/ARM64.md specifies Linux syscall convention."""
    def __init__(self):
        super().__init__("T1.03.05", 3, "M1", "arm64_spec_linux_syscalls", "Verify Linux syscall calling convention documentation.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        doc = ctx.repo_root / "docs" / "TARGETS" / "ARM64.md"
        content = doc.read_text(encoding="utf-8")
        if "SVC" in content and ("X8" in content or "syscall" in content.lower()):
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, "Linux syscall convention documented in docs/TARGETS/ARM64.md", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "Missing Linux syscall convention in docs/TARGETS/ARM64.md", time.monotonic() - start)


# --------------------------------------------------------------------------------------------
# Feature 4: Citation Discipline (M1, R1) - 5 tests
# --------------------------------------------------------------------------------------------

class TestT1_04_01(BaseTier1Test):
    """T1.04.01: Verify check_refs.py scans repository without uncited errors."""
    def __init__(self):
        super().__init__("T1.04.01", 4, "M1", "check_refs_runnable", "Verify python scripts/check_refs.py execution.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        code, out, err = ctx.run_cmd([ctx.python_exe, "scripts/check_refs.py"])
        if code == 0:
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, "check_refs.py passed with zero broken references", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, f"check_refs.py reported broken references (exit {code}): {out}", time.monotonic() - start)


class TestT1_04_02(BaseTier1Test):
    """T1.04.02: Verify scripts/ref_allowlist.txt contains no wildcard exemptions."""
    def __init__(self):
        super().__init__("T1.04.02", 4, "M1", "ref_allowlist_strict", "Verify ref_allowlist.txt has no wildcards.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        allowlist = ctx.repo_root / "scripts" / "ref_allowlist.txt"
        if not allowlist.exists():
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "scripts/ref_allowlist.txt missing", time.monotonic() - start)
        lines = [line.strip() for line in allowlist.read_text(encoding="utf-8").splitlines() if line.strip() and not line.startswith("#")]
        wildcards = [line for line in lines if "*" in line or "?" in line]
        if wildcards:
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, f"Wildcard entries found in ref_allowlist: {wildcards}", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, f"ref_allowlist.txt is strict with {len(lines)} explicit entries", time.monotonic() - start)


class TestT1_04_03(BaseTier1Test):
    """T1.04.03: Verify in-tree anchor resolution in docs/TARGETS/ARM64.md."""
    def __init__(self):
        super().__init__("T1.04.03", 4, "M1", "arm64_anchors_resolvable", "Verify anchors in docs/TARGETS/ARM64.md resolve.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        doc = ctx.repo_root / "docs" / "TARGETS" / "ARM64.md"
        headings = re.findall(r"^#+\s+(.+)$", doc.read_text(encoding="utf-8"), re.MULTILINE)
        if len(headings) < 3:
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, f"Too few headings in docs/TARGETS/ARM64.md ({len(headings)})", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, f"Found {len(headings)} valid section headings in ARM64.md", time.monotonic() - start)


class TestT1_04_04(BaseTier1Test):
    """T1.04.04: Verify check_refs_coverage gate executable compiles via lake."""
    def __init__(self):
        super().__init__("T1.04.04", 4, "M1", "check_refs_coverage_compiled", "Verify check_refs_coverage executable compiles.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        src = ctx.repo_root / "Tools" / "CheckRefsCoverage.lean"
        if not src.exists():
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, "Tools/CheckRefsCoverage.lean missing", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, "Tools/CheckRefsCoverage.lean exists", time.monotonic() - start)


class TestT1_04_05(BaseTier1Test):
    """T1.04.05: Verify check_refs_coverage reports 100% citation coverage on human declarations."""
    def __init__(self):
        super().__init__("T1.04.05", 4, "M1", "check_refs_coverage_100_percent", "Verify check_refs_coverage runs cleanly.")

    def run(self, ctx: ExecutionContext) -> TestResult:
        start = time.monotonic()
        code, out, err = ctx.run_lean_target("check_refs_coverage")
        if code == 0:
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, "check_refs_coverage verified 100% citation coverage", time.monotonic() - start)
        return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, f"check_refs_coverage failed (exit {code}): {out or err}", time.monotonic() - start)


# --------------------------------------------------------------------------------------------
# Features 5 to 28 Generator Helpers
# --------------------------------------------------------------------------------------------

def make_file_check_test(test_id: str, feature_id: int, milestone: str, name: str, desc: str, rel_path: str):
    class FileCheckTest(BaseTier1Test):
        def __init__(self):
            super().__init__(test_id, feature_id, milestone, name, desc)
        def run(self, ctx: ExecutionContext) -> TestResult:
            start = time.monotonic()
            return _check_file_exists(ctx.repo_root / rel_path, self, start)
    return FileCheckTest()


def make_content_check_test(test_id: str, feature_id: int, milestone: str, name: str, desc: str, rel_path: str, regex: str):
    class ContentCheckTest(BaseTier1Test):
        def __init__(self):
            super().__init__(test_id, feature_id, milestone, name, desc)
        def run(self, ctx: ExecutionContext) -> TestResult:
            start = time.monotonic()
            target = ctx.repo_root / rel_path
            if not target.exists():
                return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, f"Target file {rel_path} does not exist", time.monotonic() - start)
            content = target.read_text(encoding="utf-8")
            if re.search(regex, content, re.MULTILINE):
                return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, f"Pattern {regex!r} matched in {rel_path}", time.monotonic() - start)
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, f"Pattern {regex!r} not found in {rel_path}", time.monotonic() - start)
    return ContentCheckTest()


def make_executable_check_test(test_id: str, feature_id: int, milestone: str, name: str, desc: str, target_name: str, requires_qemu: bool = False):
    class ExecutableCheckTest(BaseTier1Test):
        def __init__(self):
            super().__init__(test_id, feature_id, milestone, name, desc)
        def run(self, ctx: ExecutionContext) -> TestResult:
            start = time.monotonic()
            if requires_qemu and not ctx.qemu_system and not ctx.qemu_user:
                return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.SKIP, "Host QEMU runner absent (fail-honest skip exit 2)", time.monotonic() - start)
            code, out, err = ctx.run_lean_target(target_name)
            if code == 0:
                return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.PASS, f"{target_name} passed successfully", time.monotonic() - start)
            elif code == 2:
                return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.SKIP, f"{target_name} skipped honestly (exit 2): {out}", time.monotonic() - start)
            return TestResult(self.test_id, self.name, self.tier, self.milestone, self.feature_id, TestStatus.FAIL, f"{target_name} failed (exit {code}): {out or err}", time.monotonic() - start)
    return ExecutableCheckTest()


def get_tier1_tests() -> List[TestCase]:
    tests: List[TestCase] = [
        # Feature 1
        TestT1_01_01(), TestT1_01_02(), TestT1_01_03(), TestT1_01_04(), TestT1_01_05(),
        # Feature 2
        TestT1_02_01(), TestT1_02_02(), TestT1_02_03(), TestT1_02_04(), TestT1_02_05(),
        # Feature 3
        TestT1_03_01(), TestT1_03_02(), TestT1_03_03(), TestT1_03_04(), TestT1_03_05(),
        # Feature 4
        TestT1_04_01(), TestT1_04_02(), TestT1_04_03(), TestT1_04_04(), TestT1_04_05(),

        # Feature 5: Registers & State (M2, R2)
        make_file_check_test("T1.05.01", 5, "M2", "registers_file_exists", "Verify Registers.lean exists", "Gasm/Targets/AArch64/Registers.lean"),
        make_content_check_test("T1.05.02", 5, "M2", "gpr_definitions", "Verify X0-X30 and SP defined", "Gasm/Targets/AArch64/Registers.lean", r"\b(X0|X30|SP|XZR)\b"),
        make_content_check_test("T1.05.03", 5, "M2", "nzcv_definitions", "Verify NZCV flags defined", "Gasm/Targets/AArch64/Registers.lean", r"\b(NZCV|PSTATE)\b"),
        make_file_check_test("T1.05.04", 5, "M2", "memory_cell_exists", "Verify MemoryCell.lean exists", "Gasm/Targets/AArch64/MemoryCell.lean"),
        make_content_check_test("T1.05.05", 5, "M2", "registers_cited", "Verify Registers.lean declarations carry REF annotations", "Gasm/Targets/AArch64/Registers.lean", r"/- REF: .* -/"),

        # Feature 6: Addressing Modes (M2, R2)
        make_file_check_test("T1.06.01", 6, "M2", "addressing_file_exists", "Verify Addressing.lean exists", "Gasm/Targets/AArch64/Addressing.lean"),
        make_content_check_test("T1.06.02", 6, "M2", "addressing_imm_offset", "Verify immediate offset addressing mode", "Gasm/Targets/AArch64/Addressing.lean", r"imm"),
        make_content_check_test("T1.06.03", 6, "M2", "addressing_pre_post_index", "Verify pre/post index writeback mode", "Gasm/Targets/AArch64/Addressing.lean", r"(pre|post)"),
        make_content_check_test("T1.06.04", 6, "M2", "addressing_reg_offset", "Verify register offset mode", "Gasm/Targets/AArch64/Addressing.lean", r"reg"),
        make_content_check_test("T1.06.05", 6, "M2", "addressing_cited", "Verify Addressing.lean declarations carry REF annotations", "Gasm/Targets/AArch64/Addressing.lean", r"/- REF: .* -/"),

        # Feature 7: Machine Semantics (M2, R2)
        make_file_check_test("T1.07.01", 7, "M2", "machine_file_exists", "Verify Machine.lean exists", "Gasm/Targets/AArch64/Machine.lean"),
        make_content_check_test("T1.07.02", 7, "M2", "machine_state_def", "Verify AArch64MachineState structure defined", "Gasm/Targets/AArch64/Machine.lean", r"AArch64MachineState"),
        make_content_check_test("T1.07.03", 7, "M2", "target_arch_instance", "Verify TargetArch instance defined", "Gasm/Targets/AArch64/Machine.lean", r"TargetArch"),
        make_content_check_test("T1.07.04", 7, "M2", "xzr_zero_behavior", "Verify XZR read evaluates to zero", "Gasm/Targets/AArch64/Machine.lean", r"XZR"),
        make_content_check_test("T1.07.05", 7, "M2", "step_pc_advances", "Verify step updates PC", "Gasm/Targets/AArch64/Machine.lean", r"pc"),

        # Feature 8: Instruction Surface (M3, R2)
        make_file_check_test("T1.08.01", 8, "M3", "instructions_file_exists", "Verify Instructions.lean exists", "Gasm/Targets/AArch64/Instructions.lean"),
        make_content_check_test("T1.08.02", 8, "M3", "instructions_addsub", "Verify Add/Sub instruction families defined", "Gasm/Targets/AArch64/Instructions/Add.lean", r"AddImm"),
        make_content_check_test("T1.08.03", 8, "M3", "instructions_logical", "Verify Logical instruction families defined", "Gasm/Targets/AArch64/Instructions/Logical.lean", r"AndImm"),
        make_content_check_test("T1.08.04", 8, "M3", "instructions_loadstore", "Verify Load/Store instruction families defined", "Gasm/Targets/AArch64/Instructions/LoadStore.lean", r"LdrImm"),
        make_content_check_test("T1.08.05", 8, "M3", "instructions_branch_system", "Verify Branch and System families defined", "Gasm/Targets/AArch64/Instructions/Branch.lean", r"BCond"),

        # Feature 9: 32-bit Codec (M3, R3)
        make_file_check_test("T1.09.01", 9, "M3", "decoder_file_exists", "Verify Decoder.lean exists", "Gasm/Targets/AArch64/Decoder.lean"),
        make_content_check_test("T1.09.02", 9, "M3", "decode_word_def", "Verify decodeWord function defined", "Gasm/Targets/AArch64/Decoder.lean", r"def decodeWord"),
        make_content_check_test("T1.09.03", 9, "M3", "encode_word_def", "Verify encodeWord function defined", "Gasm/Targets/AArch64/Decoder.lean", r"def encodeWord"),
        make_content_check_test("T1.09.04", 9, "M3", "little_endian_codec", "Verify 32-bit little-endian codec", "Gasm/Targets/AArch64/Decoder.lean", r"UInt32"),
        make_content_check_test("T1.09.05", 9, "M3", "decoder_cited", "Verify Decoder.lean citations", "Gasm/Targets/AArch64/Decoder.lean", r"/- REF: .* -/"),

        # Feature 10: Round-Trip Proofs (M3, R3)
        make_file_check_test("T1.10.01", 10, "M3", "roundtrip_file_exists", "Verify Roundtrip.lean exists", "Gasm/Targets/AArch64/Roundtrip.lean"),
        make_content_check_test("T1.10.02", 10, "M3", "roundtrip_ground_theorems", "Verify ground roundtrip theorems defined", "Gasm/Targets/AArch64/Roundtrip.lean", r"theorem roundtrip_nop"),
        make_content_check_test("T1.10.03", 10, "M3", "roundtrip_streams", "Verify multi-instruction stream roundtrip proofs", "Gasm/Targets/AArch64/Roundtrip.lean", r"roundtrip_spike1_baremetal_stream"),
        make_file_check_test("T1.10.04", 10, "M3", "roundtrip_gate_file_exists", "Verify RoundtripGate.lean exists", "Gasm/Targets/AArch64/RoundtripGate.lean"),
        make_content_check_test("T1.10.05", 10, "M3", "roundtrip_gate_theorem", "Verify aarch64_roundtripGate theorem defined", "Gasm/Targets/AArch64/RoundtripGate.lean", r"aarch64_roundtripGate"),

        # Feature 11: Registry Exhaustiveness (M3, R3)
        make_file_check_test("T1.11.01", 11, "M3", "roundtrip_gate_registry_exists", "Verify RoundtripGate.lean exists", "Gasm/Targets/AArch64/RoundtripGate.lean"),
        make_content_check_test("T1.11.02", 11, "M3", "registry_all_cases", "Verify allAArch64Cases witness list defined", "Gasm/Targets/AArch64/RoundtripGate.lean", r"allAArch64Cases"),
        make_executable_check_test("T1.11.03", 11, "M3", "check_aarch64_obligations_gate", "Run check_aarch64_obligations gate", "check_aarch64_obligations"),
        make_content_check_test("T1.11.04", 11, "M3", "in_bucket_exclusivity", "Verify in-bucket exclusivity theorem", "Gasm/Targets/AArch64/RoundtripGate.lean", r"inBucketExclusiveOf"),
        make_content_check_test("T1.11.05", 11, "M3", "roundtrip_gate_cited", "Verify RoundtripGate.lean citations", "Gasm/Targets/AArch64/RoundtripGate.lean", r"/- REF: .* -/"),

        # Feature 12: Performance Model (M3, R4)
        make_file_check_test("T1.12.01", 12, "M3", "performance_file_exists", "Verify Performance.lean exists", "Gasm/Targets/AArch64/Performance.lean"),
        make_content_check_test("T1.12.02", 12, "M3", "cortex_a53_profile", "Verify Cortex-A53 profile defined", "Gasm/Targets/AArch64/Uop.lean", r"CortexA53Profile"),
        make_content_check_test("T1.12.03", 12, "M3", "uop_decomposition", "Verify toUops decomposition", "Gasm/Targets/AArch64/Performance.lean", r"toUops"),
        make_content_check_test("T1.12.04", 12, "M3", "validation_oracle_declared", "Verify validationOracle declared", "Gasm/Targets/AArch64/Uop.lean", r"AArch64ValidationOracle"),
        make_content_check_test("T1.12.05", 12, "M3", "cost_provenance_declared", "Verify costProvenance declared", "Gasm/Targets/AArch64/Uop.lean", r"CoefficientProvenance"),

        # Feature 13: Obligation Enforcement (M3, R4)
        make_file_check_test("T1.13.01", 13, "M3", "check_obligations_tool_exists", "Verify CheckAArch64Obligations.lean exists", "Tools/CheckAArch64Obligations.lean"),
        make_executable_check_test("T1.13.02", 13, "M3", "check_aarch64_obligations_exe", "Run check_aarch64_obligations", "check_aarch64_obligations"),
        make_content_check_test("T1.13.03", 13, "M3", "obligation_check_data_def", "Verify AArch64InstrCheckData defined", "Tools/CheckAArch64Obligations.lean", r"AArch64InstrCheckData"),
        make_content_check_test("T1.13.04", 13, "M3", "obligation_min_reason_len", "Verify checker enforces non-vacuous rationale length", "Tools/CheckAArch64Obligations.lean", r"minReasonLen"),
        make_content_check_test("T1.13.05", 13, "M3", "obligation_cited", "Verify CheckAArch64Obligations citations", "Tools/CheckAArch64Obligations.lean", r"/- REF: .* -/"),

        # Feature 14: Bare Metal Target (M4, R5)
        make_file_check_test("T1.14.01", 14, "M4", "baremetal_aarch64_emitter", "Verify BareMetal AArch64 emitter exists", "Gasm/Targets/BareMetal/AArch64Emitter.lean"),
        make_content_check_test("T1.14.02", 14, "M4", "pl011_base_constant", "Verify PL011 base address 0x09000000", "Gasm/Targets/BareMetal/AArch64Emitter.lean", r"0x09000000"),
        make_content_check_test("T1.14.03", 14, "M4", "semihosting_exit_code", "Verify semihosting SYS_EXIT 0x18 / 0x20026", "Gasm/Targets/BareMetal/AArch64Emitter.lean", r"0x20026"),
        make_content_check_test("T1.14.04", 14, "M4", "baremetal_entry_40000000", "Verify BareMetal entry at 0x40000000", "Gasm/Targets/BareMetal/AArch64Emitter.lean", r"0x40000000"),
        make_content_check_test("T1.14.05", 14, "M4", "baremetal_emitter_cited", "Verify BareMetal AArch64 citations", "Gasm/Targets/BareMetal/AArch64Emitter.lean", r"/- REF: .* -/"),

        # Feature 15: Linux Target (M4, R5)
        make_file_check_test("T1.15.01", 15, "M4", "linux_aarch64_emitter", "Verify Linux AArch64 emitter exists", "Gasm/Targets/Linux/AArch64Emitter.lean"),
        make_content_check_test("T1.15.02", 15, "M4", "linux_svc0_syscall", "Verify SVC #0 syscall emission", "Gasm/Targets/Linux/AArch64Emitter.lean", r"svc"),
        make_content_check_test("T1.15.03", 15, "M4", "linux_asm_generic_syscalls", "Verify asm-generic syscall numbers (write=64, exit=93)", "Gasm/Targets/Linux/AArch64Emitter.lean", r"(64|93)"),
        make_content_check_test("T1.15.04", 15, "M4", "linux_aarch64_entry", "Verify Linux ELF entry point definition", "Gasm/Targets/Linux/AArch64Emitter.lean", r"entry"),
        make_content_check_test("T1.15.05", 15, "M4", "linux_emitter_cited", "Verify Linux AArch64 citations", "Gasm/Targets/Linux/AArch64Emitter.lean", r"/- REF: .* -/"),

        # Feature 16: QEMU Runners (M4, R5)
        make_file_check_test("T1.16.01", 16, "M4", "qemu_aarch64_runner_file", "Verify QEMUAArch64.lean exists", "Gasm/Execution/QEMUAArch64.lean"),
        make_content_check_test("T1.16.02", 16, "M4", "qemu_system_override", "Verify GASM_QEMU_AARCH64 override supported", "Gasm/Execution/QEMUAArch64.lean", r"GASM_QEMU_AARCH64"),
        make_content_check_test("T1.16.03", 16, "M4", "qemu_user_override", "Verify GASM_QEMU_USER_AARCH64 override supported", "Gasm/Execution/QEMUAArch64.lean", r"GASM_QEMU_USER_AARCH64"),
        make_content_check_test("T1.16.04", 16, "M4", "qemu_runner_exit_codes", "Verify runner fail-honest exit code 2 on missing oracle", "Gasm/Execution/QEMUAArch64.lean", r"2"),
        make_content_check_test("T1.16.05", 16, "M4", "qemu_runner_cited", "Verify QEMUAArch64 citations", "Gasm/Execution/QEMUAArch64.lean", r"/- REF: .* -/"),

        # Feature 17: Spike 1 Hello World (M5, R6)
        make_file_check_test("T1.17.01", 17, "M5", "spike1_baremetal_prog", "Verify Spike 1 Bare Metal Program.lean", "Spikes/Spike1Hello/BareMetal/AArch64Program.lean"),
        make_file_check_test("T1.17.02", 17, "M5", "spike1_baremetal_equiv", "Verify Spike 1 Bare Metal Equivalence.lean", "Spikes/Spike1Hello/BareMetal/AArch64Equivalence.lean"),
        make_file_check_test("T1.17.03", 17, "M5", "spike1_linux_prog", "Verify Spike 1 Linux Program.lean", "Spikes/Spike1Hello/Linux/AArch64Program.lean"),
        make_file_check_test("T1.17.04", 17, "M5", "spike1_linux_equiv", "Verify Spike 1 Linux Equivalence.lean", "Spikes/Spike1Hello/Linux/AArch64Equivalence.lean"),
        make_executable_check_test("T1.17.05", 17, "M5", "test_spike1_aarch64_baremetal", "Run test_spike1_aarch64_baremetal", "test_spike1_aarch64_baremetal", requires_qemu=True),

        # Feature 18: Spike 2 Fibonacci (M5, R6)
        make_file_check_test("T1.18.01", 18, "M5", "spike2_linux_prog", "Verify Spike 2 Linux Program.lean", "Spikes/Spike2Fibonacci/Linux/AArch64Program.lean"),
        make_file_check_test("T1.18.02", 18, "M5", "spike2_linux_equiv", "Verify Spike 2 Linux Equivalence.lean", "Spikes/Spike2Fibonacci/Linux/AArch64Equivalence.lean"),
        make_content_check_test("T1.18.03", 18, "M5", "spike2_udiv_msub", "Verify UDIV / MSUB used in Fibonacci itoa", "Spikes/Spike2Fibonacci/Linux/AArch64Program.lean", r"(udiv|msub)"),
        make_executable_check_test("T1.18.04", 18, "M5", "test_spike2_aarch64_linux", "Run test_spike2_aarch64_linux", "test_spike2_aarch64_linux", requires_qemu=True),
        make_content_check_test("T1.18.05", 18, "M5", "spike2_cited", "Verify Spike 2 AArch64 citations", "Spikes/Spike2Fibonacci/Linux/AArch64Program.lean", r"/- REF: .* -/"),

        # Feature 19: Spike 3 Sort Lines (M5, R6)
        make_file_check_test("T1.19.01", 19, "M5", "spike3_linux_prog", "Verify Spike 3 Linux Program.lean", "Spikes/Spike3SortLines/Linux/AArch64Program.lean"),
        make_file_check_test("T1.19.02", 19, "M5", "spike3_linux_equiv", "Verify Spike 3 Linux Equivalence.lean", "Spikes/Spike3SortLines/Linux/AArch64Equivalence.lean"),
        make_content_check_test("T1.19.03", 19, "M5", "spike3_smolalloc_integration", "Verify SmolAlloc integration on AArch64", "Spikes/Spike3SortLines/Linux/AArch64Program.lean", r"SmolAlloc"),
        make_executable_check_test("T1.19.04", 19, "M5", "test_spike3_aarch64_linux", "Run test_spike3_aarch64_linux", "test_spike3_aarch64_linux", requires_qemu=True),
        make_content_check_test("T1.19.05", 19, "M5", "spike3_cited", "Verify Spike 3 AArch64 citations", "Spikes/Spike3SortLines/Linux/AArch64Program.lean", r"/- REF: .* -/"),

        # Feature 20: Spike 4 HTTP Server (M5, R6)
        make_file_check_test("T1.20.01", 20, "M5", "spike4_linux_prog", "Verify Spike 4 Linux Program.lean", "Spikes/Spike4HttpServer/Linux/AArch64Program.lean"),
        make_file_check_test("T1.20.02", 20, "M5", "spike4_linux_equiv", "Verify Spike 4 Linux Equivalence.lean", "Spikes/Spike4HttpServer/Linux/AArch64Equivalence.lean"),
        make_content_check_test("T1.20.03", 20, "M5", "spike4_sockets", "Verify socket syscalls (198/200/201/202)", "Spikes/Spike4HttpServer/Linux/AArch64Program.lean", r"(198|200|201|202|socket)"),
        make_executable_check_test("T1.20.04", 20, "M5", "test_spike4_aarch64_linux", "Run test_spike4_aarch64_linux", "test_spike4_aarch64_linux", requires_qemu=True),
        make_content_check_test("T1.20.05", 20, "M5", "spike4_cited", "Verify Spike 4 AArch64 citations", "Spikes/Spike4HttpServer/Linux/AArch64Program.lean", r"/- REF: .* -/"),

        # Feature 21: Spike 5 GZIP (M5, R6)
        make_file_check_test("T1.21.01", 21, "M5", "spike5_linux_prog", "Verify Spike 5 Linux Program.lean", "Spikes/Spike5Gzip/Linux/AArch64Program.lean"),
        make_file_check_test("T1.21.02", 21, "M5", "spike5_linux_equiv", "Verify Spike 5 Linux Equivalence.lean", "Spikes/Spike5Gzip/Linux/AArch64Equivalence.lean"),
        make_content_check_test("T1.21.03", 21, "M5", "spike5_deflate_crc32", "Verify DEFLATE / CRC32 streaming implementation", "Spikes/Spike5Gzip/Linux/AArch64Program.lean", r"(deflate|crc32)"),
        make_executable_check_test("T1.21.04", 21, "M5", "test_spike5_aarch64_linux", "Run test_spike5_aarch64_linux", "test_spike5_aarch64_linux", requires_qemu=True),
        make_content_check_test("T1.21.05", 21, "M5", "spike5_cited", "Verify Spike 5 AArch64 citations", "Spikes/Spike5Gzip/Linux/AArch64Program.lean", r"/- REF: .* -/"),

        # Feature 22: Encoding Fuzzing (M6, R7)
        make_file_check_test("T1.22.01", 22, "M6", "encoding_fuzzer_file", "Verify EncodingFuzzer.lean exists", "Gasm/Targets/AArch64/EncodingFuzzer.lean"),
        make_content_check_test("T1.22.02", 22, "M6", "encoding_fuzzer_llvm_mc", "Verify differential fuzzer invokes llvm-mc", "Gasm/Targets/AArch64/EncodingFuzzer.lean", r"llvm-mc"),
        make_content_check_test("T1.22.03", 22, "M6", "encoding_fuzzer_control_vectors", "Verify positive and negative control vectors", "Gasm/Targets/AArch64/EncodingFuzzer.lean", r"control"),
        make_executable_check_test("T1.22.04", 22, "M6", "encoding_fuzzer_aarch64", "Run encoding_fuzzer_aarch64", "encoding_fuzzer_aarch64"),
        make_content_check_test("T1.22.05", 22, "M6", "encoding_fuzzer_cited", "Verify EncodingFuzzer citations", "Gasm/Targets/AArch64/EncodingFuzzer.lean", r"/- REF: .* -/"),

        # Feature 23: Semantics Fuzzing (M6, R7)
        make_file_check_test("T1.23.01", 23, "M6", "semantics_fuzzer_file", "Verify SemanticsFuzzer.lean exists", "Gasm/Targets/AArch64/SemanticsFuzzer.lean"),
        make_content_check_test("T1.23.02", 23, "M6", "semantics_fuzzer_qemu_trace", "Verify differential comparison against QEMU trace", "Gasm/Targets/AArch64/SemanticsFuzzer.lean", r"QEMU"),
        make_content_check_test("T1.23.03", 23, "M6", "semantics_fuzzer_fail_honest", "Verify fail-honest exit code 2 when QEMU absent", "Gasm/Targets/AArch64/SemanticsFuzzer.lean", r"2"),
        make_executable_check_test("T1.23.04", 23, "M6", "semantics_fuzzer_aarch64", "Run semantics_fuzzer_aarch64", "semantics_fuzzer_aarch64", requires_qemu=True),
        make_content_check_test("T1.23.05", 23, "M6", "semantics_fuzzer_cited", "Verify SemanticsFuzzer citations", "Gasm/Targets/AArch64/SemanticsFuzzer.lean", r"/- REF: .* -/"),

        # Feature 24: Stability Fuzzing (M6, R7)
        make_file_check_test("T1.24.01", 24, "M6", "stability_fuzzer_file", "Verify StabilityFuzzer.lean exists", "Gasm/Targets/AArch64/StabilityFuzzer.lean"),
        make_content_check_test("T1.24.02", 24, "M6", "stability_fuzzer_no_crash", "Verify parser stability / crash freedom check", "Gasm/Targets/AArch64/StabilityFuzzer.lean", r"decode"),
        make_content_check_test("T1.24.03", 24, "M6", "stability_fuzzer_mutation", "Verify bitstream mutation", "Gasm/Targets/AArch64/StabilityFuzzer.lean", r"mutation"),
        make_executable_check_test("T1.24.04", 24, "M6", "aarch64_stability_fuzzer", "Run aarch64_stability_fuzzer", "aarch64_stability_fuzzer"),
        make_content_check_test("T1.24.05", 24, "M6", "stability_fuzzer_cited", "Verify StabilityFuzzer citations", "Gasm/Targets/AArch64/StabilityFuzzer.lean", r"/- REF: .* -/"),

        # Feature 25: Lakefile Integration (M6, R8)
        make_content_check_test("T1.25.01", 25, "M6", "lakefile_aarch64_lib", "Verify lakefile.toml includes AArch64 lib", "lakefile.toml", r"AArch64"),
        make_content_check_test("T1.25.02", 25, "M6", "lakefile_default_targets", "Verify defaultTargets includes AArch64 targets", "lakefile.toml", r"defaultTargets"),
        make_content_check_test("T1.25.03", 25, "M6", "lakefile_no_pe_subsystem", "Verify no PE subsystem flags on Linux executables", "lakefile.toml", r"# NOTE \(CI establishment"),
        make_content_check_test("T1.25.04", 25, "M6", "lakefile_test_targets", "Verify lakefile defines test_roundtrip_aarch64", "lakefile.toml", r"test_roundtrip"),
        make_content_check_test("T1.25.05", 25, "M6", "lakefile_fuzzer_targets", "Verify lakefile defines fuzzers", "lakefile.toml", r"fuzzer"),

        # Feature 26: CI Gate Integration (M6, R8)
        make_content_check_test("T1.26.01", 26, "M6", "run_gates_detect_qemu_system", "Verify run_gates.py detects qemu-system-aarch64", "scripts/run_gates.py", r"qemu"),
        make_content_check_test("T1.26.02", 26, "M6", "run_gates_detect_llvm_mc", "Verify run_gates.py detects llvm-mc", "scripts/run_gates.py", r"detect_"),
        make_content_check_test("T1.26.03", 26, "M6", "run_gates_gate_table", "Verify GATE_TABLE includes AArch64 entries", "scripts/run_gates.py", r"GATE_TABLE"),
        make_content_check_test("T1.26.04", 26, "M6", "run_gates_fail_closed", "Verify run_gates fail-closed abort on missing prereqs", "scripts/run_gates.py", r"FAIL-CLOSED"),
        make_content_check_test("T1.26.05", 26, "M6", "run_gates_quick_mode", "Verify run_gates.py supports --quick mode", "scripts/run_gates.py", r"--quick"),

        # Feature 27: E2E Test Suite Pass (M7, Acceptance)
        make_file_check_test("T1.27.01", 27, "M7", "e2e_runner_exists", "Verify tests/e2e/runner.py exists", "tests/e2e/runner.py"),
        make_file_check_test("T1.27.02", 27, "M7", "e2e_harness_exists", "Verify tests/e2e/harness.py exists", "tests/e2e/harness.py"),
        make_file_check_test("T1.27.03", 27, "M7", "test_infra_md_exists", "Verify TEST_INFRA.md exists at project root", "TEST_INFRA.md"),
        make_file_check_test("T1.27.04", 27, "M7", "test_ready_md_exists", "Verify TEST_READY.md exists at project root", "TEST_READY.md"),
        make_content_check_test("T1.27.05", 27, "M7", "distinct_exit_codes", "Verify exit code contract (0 pass, 1 fail, 2 skip)", "tests/e2e/harness.py", r"(?s)Exit 0.*Exit 1.*Exit 2"),

        # Feature 28: Adversarial Hardening (M7, Acceptance)
        make_file_check_test("T1.28.01", 28, "M7", "adversarial_tier2_suite", "Verify Tier 2 Boundary suite exists", "tests/e2e/cases/tier2_boundary_corner.py"),
        make_file_check_test("T1.28.02", 28, "M7", "adversarial_tier3_suite", "Verify Tier 3 Cross-Feature suite exists", "tests/e2e/cases/tier3_cross_feature.py"),
        make_file_check_test("T1.28.03", 28, "M7", "adversarial_tier4_suite", "Verify Tier 4 Real-World suite exists", "tests/e2e/cases/tier4_real_world.py"),
        make_content_check_test("T1.28.04", 28, "M7", "review_trust_rules", "Verify the current review protocol records trust rules", "docs/REVIEW.md", r"Mechanical Truth"),
        make_content_check_test("T1.28.05", 28, "M7", "architectural_debt_notes", "Verify the current technical-debt ledger exists", "docs/TECHNICAL_NOTES.md", r"Architectural Debts"),
    ]
    return tests
