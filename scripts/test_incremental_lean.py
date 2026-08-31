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

"""Unit and live mutation controls for scripts/run_incremental_lean.py."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "run_incremental_lean.py"
SPEC = importlib.util.spec_from_file_location("run_incremental_lean", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def pair_writer_helper(arguments: list[str]) -> int:
    """Subprocess side of the deterministic two-writer publication control."""

    lock_path, temporary, target, started, acquired, between, release = map(Path, arguments)
    started.write_text("started\n", encoding="utf-8")
    with MODULE.cache_lock(lock_path, timeout=10.0):
        acquired.write_text("acquired\n", encoding="utf-8")
        callback = None
        if str(between) != "-":
            def pause_between_replaces() -> None:
                between.write_text("between\n", encoding="utf-8")
                deadline = time.monotonic() + 10.0
                while not release.is_file() and time.monotonic() < deadline:
                    time.sleep(0.01)
                if not release.is_file():
                    raise TimeoutError("timed out waiting between pair replaces")
            callback = pause_between_replaces
        MODULE.publish_snapshot_pair(
            temporary,
            MODULE.dependency_companion(temporary),
            target,
            between_replaces=callback,
        )
    return 0


class IncrementalLeanTests(unittest.TestCase):
    def test_import_prefix_excludes_body(self) -> None:
        first = b"/- license -/\nimport Init\n\nprivate theorem a : True := by trivial\n"
        second = b"/- license -/\nimport Init\n\nprivate theorem b : False := by trivial\n"
        self.assertEqual(MODULE.source_import_prefix(first), MODULE.source_import_prefix(second))
        self.assertEqual(MODULE.source_import_prefix(first), b"/- license -/\nimport Init\n")

    def test_import_prefix_tracks_visibility_and_order(self) -> None:
        first = b"public import Init\nmeta import Lean\n\ndef x := 1\n"
        second = b"meta import Lean\npublic import Init\n\ndef x := 1\n"
        self.assertNotEqual(MODULE.source_import_prefix(first), MODULE.source_import_prefix(second))

    def test_only_resource_and_diagnostic_arguments_are_accepted(self) -> None:
        MODULE.validate_lean_arguments(
            ["-M", "4096", "--timeout=200000", "-j", "1", "--profile", "--stats"]
        )
        forbidden = [
            "--incr-load=untrusted.snapshot",
            "--setup=mutable.json",
            "--plugin=mutable.so",
            "--load-dynlib=mutable.so",
            "-R",
            "-D",
            "-o",
            "--stdin",
        ]
        for argument in forbidden:
            with self.subTest(argument=argument), self.assertRaises(MODULE.PreparationError):
                MODULE.validate_lean_arguments([argument])

    def test_dependency_discovery_receives_the_same_accepted_arguments(self) -> None:
        with mock.patch.object(MODULE, "run_capture", return_value="") as capture:
            output, dependencies = MODULE.dependency_paths(
                "Example.lean", ["-M", "4096", "--profile"]
            )
        self.assertEqual(output, "")
        self.assertEqual(dependencies, [])
        capture.assert_called_once_with(
            ["lake", "env", "lean", "-M", "4096", "--profile", "--deps", "Example.lean"]
        )

    def test_lock_serializes_two_writers_and_keeps_pair_coherent(self) -> None:
        with tempfile.TemporaryDirectory(prefix="gasm-incremental-pair-") as raw_temp:
            temp = Path(raw_temp)
            lock_path = temp / ".pair.lock"
            target = temp / "pair.snapshot"
            first = temp / "first.tmp"
            first_deps = MODULE.dependency_companion(first)
            second = temp / "second.tmp"
            second_deps = MODULE.dependency_companion(second)
            first.write_bytes(b"first-snapshot")
            first_deps.write_bytes(b"first-dependencies")
            second.write_bytes(b"second-snapshot")
            second_deps.write_bytes(b"second-dependencies")

            first_started = temp / "first-started"
            first_acquired = temp / "first-acquired"
            between_replaces = temp / "between-replaces"
            release_first = temp / "release-first"
            second_started = temp / "second-started"
            second_acquired = temp / "second-acquired"

            def launch_writer(
                temporary: Path,
                started: Path,
                acquired: Path,
                between: Path | str,
                release: Path | str,
            ) -> subprocess.Popen[str]:
                return subprocess.Popen(
                    [
                        sys.executable,
                        str(Path(__file__).resolve()),
                        "--pair-writer-helper",
                        str(lock_path),
                        str(temporary),
                        str(target),
                        str(started),
                        str(acquired),
                        str(between),
                        str(release),
                    ],
                    cwd=REPO_ROOT,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                )

            def wait_for(path: Path) -> None:
                deadline = time.monotonic() + 10.0
                while not path.is_file() and time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertTrue(path.is_file(), f"timed out waiting for {path.name}")

            first_process = launch_writer(
                first, first_started, first_acquired, between_replaces, release_first
            )
            wait_for(between_replaces)
            second_process = launch_writer(second, second_started, second_acquired, "-", "-")
            wait_for(second_started)
            self.assertFalse(second_acquired.is_file())
            time.sleep(0.1)
            self.assertFalse(second_acquired.is_file())
            release_first.write_text("release\n", encoding="utf-8")

            first_stdout, first_stderr = first_process.communicate(timeout=10.0)
            second_stdout, second_stderr = second_process.communicate(timeout=10.0)
            self.assertEqual(first_process.returncode, 0, first_stdout + first_stderr)
            self.assertEqual(second_process.returncode, 0, second_stdout + second_stderr)
            self.assertTrue(second_acquired.is_file())
            self.assertTrue(MODULE.validate_snapshot_pair(target))
            self.assertEqual(target.read_bytes(), b"second-snapshot")
            self.assertEqual(
                MODULE.dependency_companion(target).read_bytes(), b"second-dependencies"
            )

    def test_mixed_or_incomplete_pair_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory(prefix="gasm-incremental-corrupt-") as raw_temp:
            temp = Path(raw_temp)
            target = temp / "pair.snapshot"
            source = temp / "source.tmp"
            source_deps = MODULE.dependency_companion(source)
            source.write_bytes(b"snapshot")
            source_deps.write_bytes(b"dependencies")
            MODULE.publish_snapshot_pair(source, source_deps, target)
            self.assertTrue(MODULE.validate_snapshot_pair(target))

            MODULE.dependency_companion(target).write_bytes(b"different-generation")
            with self.assertRaises(MODULE.PreparationError):
                MODULE.validate_snapshot_pair(target)

            MODULE.manifest_companion(target).unlink()
            with self.assertRaises(MODULE.PreparationError):
                MODULE.validate_snapshot_pair(target)

    def test_live_snapshot_rechecks_changed_body(self) -> None:
        with tempfile.TemporaryDirectory(prefix="gasm-incremental-lean-") as raw_temp:
            temp = Path(raw_temp)
            source = temp / "SnapshotMutation.lean"
            cache = temp / "cache"
            source.write_text("import Init\n\nprivate theorem probe : False := by trivial\n", encoding="utf-8")
            command = [sys.executable, str(SCRIPT), "--cache-dir", str(cache), str(source)]

            first = subprocess.run(command, cwd=REPO_ROOT, text=True, capture_output=True)
            self.assertNotEqual(first.returncode, 0)
            self.assertIn("mode=save", first.stderr)
            snapshots = list(cache.glob("*.snapshot"))
            self.assertEqual(len(snapshots), 1)
            self.assertGreater(snapshots[0].stat().st_size, 0)
            self.assertGreater(MODULE.dependency_companion(snapshots[0]).stat().st_size, 0)
            self.assertGreater(MODULE.manifest_companion(snapshots[0]).stat().st_size, 0)

            second = subprocess.run(command, cwd=REPO_ROOT, text=True, capture_output=True)
            self.assertNotEqual(second.returncode, 0)
            self.assertIn("mode=load", second.stderr)

            source.write_text(
                "import Init\n\ndef snapshotValue : Nat := 1\n"
                "private theorem probe : snapshotValue = 1 := by rfl\n",
                encoding="utf-8",
            )
            third = subprocess.run(command, cwd=REPO_ROOT, text=True, capture_output=True)
            self.assertEqual(third.returncode, 0, third.stdout + third.stderr)
            self.assertIn("mode=load", third.stderr)

            source.write_text(
                "import Init\n\ndef snapshotValue : Nat := 2\n"
                "private theorem probe : snapshotValue = 1 := by rfl\n",
                encoding="utf-8",
            )
            downstream = subprocess.run(command, cwd=REPO_ROOT, text=True, capture_output=True)
            self.assertNotEqual(downstream.returncode, 0)
            self.assertIn("mode=load", downstream.stderr)

            source.write_text(
                "import Init\n\ndef snapshotValue : Nat := 2\n"
                "private theorem probe : snapshotValue = 2 := by rfl\n",
                encoding="utf-8",
            )
            repaired = subprocess.run(command, cwd=REPO_ROOT, text=True, capture_output=True)
            self.assertEqual(repaired.returncode, 0, repaired.stdout + repaired.stderr)
            self.assertIn("mode=load", repaired.stderr)

            source.write_text(
                "import Lean\n\n#check Lean.Name\nprivate theorem probe : True := by trivial\n",
                encoding="utf-8",
            )
            fourth = subprocess.run(command, cwd=REPO_ROOT, text=True, capture_output=True)
            self.assertEqual(fourth.returncode, 0, fourth.stdout + fourth.stderr)
            self.assertIn("mode=save", fourth.stderr)
            self.assertEqual(len(list(cache.glob("*.snapshot"))), 1)

            snapshot = list(cache.glob("*.snapshot"))[0]
            MODULE.dependency_companion(snapshot).write_bytes(b"corrupt generation")
            corrupt = subprocess.run(command, cwd=REPO_ROOT, text=True, capture_output=True)
            self.assertEqual(corrupt.returncode, 2)
            self.assertIn("failed integrity validation", corrupt.stderr)

            refresh_command = [
                sys.executable,
                str(SCRIPT),
                "--refresh",
                "--cache-dir",
                str(cache),
                str(source),
            ]
            refreshed = subprocess.run(
                refresh_command, cwd=REPO_ROOT, text=True, capture_output=True
            )
            self.assertEqual(refreshed.returncode, 0, refreshed.stdout + refreshed.stderr)
            self.assertIn("mode=refresh", refreshed.stderr)
            self.assertTrue(MODULE.validate_snapshot_pair(snapshot))


if __name__ == "__main__":
    if sys.argv[1:2] == ["--pair-writer-helper"]:
        raise SystemExit(pair_writer_helper(sys.argv[2:]))
    unittest.main()
