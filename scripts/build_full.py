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

"""Memory-bounded authoritative build of every Lake default target.

Lake starts independent target closures concurrently. In this repository, the three large
libraries and proof-gate roots can each make several multi-GiB Lean processes runnable at once.
This launcher preserves the exact ``defaultTargets`` set but builds its roots sequentially, then
asks Lake to prove that the complete default closure needs no further work.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tomllib

from lean_process_lease import inherited_lease_environment, lean_process_lease


REPO_ROOT = Path(__file__).resolve().parent.parent
LAKEFILE = REPO_ROOT / "lakefile.toml"
NORMALIZATION_BATCH_SIZE_ENV = "GASM_LEAN_NORMALIZATION_BATCH_SIZE"
MAX_AUTOMATIC_NORMALIZATION_BATCH_SIZE = 16


def default_targets() -> list[str]:
    config = tomllib.loads(LAKEFILE.read_text(encoding="utf-8"))
    targets = config.get("defaultTargets")
    if not isinstance(targets, list) or not targets or not all(
        isinstance(target, str) and target for target in targets
    ):
        raise ValueError("lakefile.toml must declare a non-empty string defaultTargets list")
    if len(set(targets)) != len(targets):
        raise ValueError("lakefile.toml defaultTargets contains duplicates")
    return targets


def build_plan(lake: str, targets: list[str]) -> list[list[str]]:
    phases = [[lake, "build", target] for target in targets]
    # This final check is load-bearing: it detects target drift and proves that the same bare
    # default closure is current without starting another build wave.
    return [*phases, [lake, "--no-build", "build"]]


def module_source(module: str) -> Path:
    return REPO_ROOT / f"{module.replace('.', '/')}.lean"


def local_import_order(root: str) -> list[str]:
    """Return the local source closure in dependency-first order."""
    ordered: list[str] = []
    visited: set[str] = set()
    visiting: set[str] = set()

    def visit(module: str) -> None:
        source = module_source(module)
        if not source.is_file() or module in visited:
            return
        if module in visiting:
            raise ValueError(f"local Lean import cycle involving {module}")
        visiting.add(module)
        for line in source.read_text(encoding="utf-8").splitlines():
            stripped = line.strip()
            if stripped.startswith("import "):
                for imported in stripped.removeprefix("import ").split():
                    visit(imported)
        visiting.remove(module)
        visited.add(module)
        ordered.append(module)

    visit(root)
    return ordered


def normalization_batches(
    lake: str, targets: list[str], batch_size: int
) -> list[list[str]]:
    """Prebuild local default-target source closures in bounded topological waves."""
    modules: list[str] = []
    scheduled: set[str] = set()
    for target in targets:
        for module in local_import_order(target):
            if module not in scheduled:
                modules.append(module)
                scheduled.add(module)
    return [
        [lake, "build", *modules[index:index + batch_size]]
        for index in range(0, len(modules), batch_size)
    ]


def normalization_batch_size() -> int:
    raw = os.environ.get(NORMALIZATION_BATCH_SIZE_ENV)
    if raw is None:
        try:
            total_bytes = os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES")
        except (AttributeError, OSError, ValueError):
            from lean_process_lease import windows_commit_status

            status = windows_commit_status()
            total_bytes = status.total_physical_bytes if status is not None else 8 * 1024**3
        # Cold Gasm profiling observes roughly 1.5 GiB RSS per sibling Lean process. Budget
        # 1.8 GiB per wave member and cap at 16 even on large hosts so desktop/CI headroom remains.
        return max(
            1,
            min(
                MAX_AUTOMATIC_NORMALIZATION_BATCH_SIZE,
                total_bytes // (18 * 1024**3 // 10),
            ),
        )
    try:
        value = int(raw)
    except ValueError as error:
        raise ValueError(f"{NORMALIZATION_BATCH_SIZE_ENV} must be an integer") from error
    if value < 1:
        raise ValueError(f"{NORMALIZATION_BATCH_SIZE_ENV} must be at least 1")
    return value


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build every Lake default target sequentially, then verify the full closure."
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="print the deterministic phase order without running Lake",
    )
    args = parser.parse_args(argv)

    lake = shutil.which("lake") or "lake"
    try:
        targets = default_targets()
        batch_size = normalization_batch_size()
        normalization = normalization_batches(lake, targets, batch_size)
    except (OSError, tomllib.TOMLDecodeError, ValueError) as error:
        print(f"full build configuration error: {error}", file=sys.stderr)
        return 2

    plan = [*normalization, *build_plan(lake, targets)]
    print("Authoritative memory-bounded full build")
    print(f"Default targets ({len(targets)}), in declared order: {', '.join(targets)}")
    print(
        f"Local Lean normalization: {sum(len(command) - 2 for command in normalization)} "
        f"closure modules in {len(normalization)} wave(s), at most {batch_size} per wave"
    )
    if args.dry_run:
        for index, command in enumerate(plan, start=1):
            if index <= len(normalization):
                label = f"normalize {index}/{len(normalization)}"
            elif index == len(plan):
                label = "closure check"
            else:
                phase = index - len(normalization)
                label = f"phase {phase}/{len(targets)}"
            print(f"[{label}] {subprocess.list2cmdline(command)}", flush=True)
        return 0

    try:
        with lean_process_lease():
            for index, command in enumerate(plan, start=1):
                if index <= len(normalization):
                    label = f"normalize {index}/{len(normalization)}"
                elif index == len(plan):
                    label = "closure check"
                else:
                    phase = index - len(normalization)
                    label = f"phase {phase}/{len(targets)}"
                print(f"[{label}] {subprocess.list2cmdline(command)}", flush=True)
                result = subprocess.run(
                    command,
                    cwd=REPO_ROOT,
                    check=False,
                    env=inherited_lease_environment(),
                )
                if result.returncode != 0:
                    print(f"full build stopped: {label} exited {result.returncode}", file=sys.stderr)
                    return result.returncode
    except (OSError, TimeoutError, ValueError) as error:
        print(f"full build lease failed: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
