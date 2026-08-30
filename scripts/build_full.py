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
from pathlib import Path
import shutil
import subprocess
import sys
import tomllib

from lean_process_lease import inherited_lease_environment, lean_process_lease


REPO_ROOT = Path(__file__).resolve().parent.parent
LAKEFILE = REPO_ROOT / "lakefile.toml"


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
    except (OSError, tomllib.TOMLDecodeError, ValueError) as error:
        print(f"full build configuration error: {error}", file=sys.stderr)
        return 2

    plan = build_plan(lake, targets)
    print("Authoritative memory-bounded full build")
    print(f"Default targets ({len(targets)}), in declared order: {', '.join(targets)}")
    if args.dry_run:
        for index, command in enumerate(plan, start=1):
            label = "closure check" if index == len(plan) else f"phase {index}/{len(targets)}"
            print(f"[{label}] {subprocess.list2cmdline(command)}", flush=True)
        return 0

    try:
        with lean_process_lease():
            for index, command in enumerate(plan, start=1):
                label = "closure check" if index == len(plan) else f"phase {index}/{len(targets)}"
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
