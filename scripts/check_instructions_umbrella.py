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

"""Require Instructions.lean to reach every recursively nested instruction-directory module.

The compiled x86 registry audit can inspect every form of instance declaration -- anonymous,
named, parameterized, parenthesized, or `@[instance] def` -- but only after the module containing
that declaration enters its import environment. Source-level classification of "family files"
recreates the blind spot: any declaration syntax the classifier misses can be hidden by omitting
the same file from the umbrella.

This gate therefore does no declaration parsing. Every `Instructions/**/*.lean` file, including
shared infrastructure, must be reachable through the local import graph rooted at
`Instructions.lean`, and every local import must name a file on disk. A future infrastructure
module pays one cheap import edge rather than becoming a new syntax/exclusion case. Compiled
registry and proof audits own semantic classification after this gate makes the complete directory
visible.

Usage:
    python scripts/check_instructions_umbrella.py
    python scripts/check_instructions_umbrella.py --json
    python scripts/check_instructions_umbrella.py --self-test
"""

import argparse
import json
import re
import sys
import tomllib
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
INSTRUCTIONS_DIR = REPO_ROOT / "Gasm" / "Targets" / "X86_64" / "Instructions"
UMBRELLA_FILE = REPO_ROOT / "Gasm" / "Targets" / "X86_64" / "Instructions.lean"
IMPORT_PREFIX = "Gasm.Targets.X86_64.Instructions."
CONTROL_MODULE = "Gasm.Targets.X86_64.InstructionCensusControls"
CONTROL_TARGET = "X86InstructionCensusControls"


def modules_on_disk() -> set[str]:
    if not INSTRUCTIONS_DIR.is_dir():
        raise FileNotFoundError(INSTRUCTIONS_DIR)
    return {
        ".".join(path.relative_to(INSTRUCTIONS_DIR).with_suffix("").parts)
        for path in INSTRUCTIONS_DIR.rglob("*.lean")
    }


def module_path(name: str) -> Path:
    return (INSTRUCTIONS_DIR.joinpath(*name.split("."))).with_suffix(".lean")


def local_imports(path: Path) -> set[str]:
    if not path.is_file():
        raise FileNotFoundError(path)
    imported: set[str] = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        match = re.match(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$", line)
        if not match:
            continue
        module = match.group(1)
        if module.startswith(IMPORT_PREFIX):
            imported.add(module[len(IMPORT_PREFIX):])
    return imported


def compute() -> dict[str, object]:
    modules = modules_on_disk()
    graph = {name: local_imports(module_path(name)) for name in modules}
    roots = local_imports(UMBRELLA_FILE)
    reachable: set[str] = set()
    frontier = list(roots)
    while frontier:
        module = frontier.pop()
        if module in reachable:
            continue
        reachable.add(module)
        frontier.extend(graph.get(module, set()))
    referenced = roots | set().union(*graph.values()) if graph else roots
    lake_config = tomllib.loads((REPO_ROOT / "lakefile.toml").read_text(encoding="utf-8"))
    control_targets = [
        library for library in lake_config.get("lean_lib", [])
        if library.get("name") == CONTROL_TARGET
    ]
    control_target_exact = (
        len(control_targets) == 1 and
        control_targets[0].get("roots") == [CONTROL_MODULE]
    )
    control_default = CONTROL_TARGET in lake_config.get("defaultTargets", [])
    control_importers: list[str] = []
    exact_import = re.compile(rf"^\s*import\s+{re.escape(CONTROL_MODULE)}\s*$", re.MULTILINE)
    for source_root in ("Gasm", "Spikes", "Stdlib"):
        for path in (REPO_ROOT / source_root).rglob("*.lean"):
            if path == REPO_ROOT / "Gasm/Targets/X86_64/InstructionCensusControls.lean":
                continue
            if exact_import.search(path.read_text(encoding="utf-8")):
                control_importers.append(path.relative_to(REPO_ROOT).as_posix())
    for facade in (REPO_ROOT / "Gasm.lean", REPO_ROOT / "Spikes.lean", REPO_ROOT / "Stdlib.lean"):
        if facade.is_file() and exact_import.search(facade.read_text(encoding="utf-8")):
            control_importers.append(facade.relative_to(REPO_ROOT).as_posix())
    return {
        "modules": len(modules),
        "missing_from_umbrella": sorted(modules - reachable),
        "stale_in_umbrella": sorted(referenced - modules),
        "control_target_exact": control_target_exact,
        "control_default_target": control_default,
        "control_library_importers": sorted(control_importers),
    }


def result_exit_code(result: dict[str, object]) -> int:
    return 1 if (
        result["missing_from_umbrella"] or result["stale_in_umbrella"] or
        not result["control_target_exact"] or not result["control_default_target"] or
        result["control_library_importers"]
    ) else 0


def print_report(result: dict[str, object]) -> None:
    if result_exit_code(result) == 0:
        print(
            f"OK: Instructions.lean reaches all {result['modules']} Instructions/**/*.lean "
            "modules through local imports; hostile census controls are a default gate-only root "
            "and absent from library import closures."
        )
        return
    print("Instructions.lean umbrella completeness check FAILED.", file=sys.stderr)
    if result["missing_from_umbrella"]:
        print(
            "  Modules on disk but absent from the umbrella (therefore invisible to compiled "
            f"registry audits): {result['missing_from_umbrella']}",
            file=sys.stderr,
        )
    if result["stale_in_umbrella"]:
        print(
            f"  Umbrella imports with no file on disk: {result['stale_in_umbrella']}",
            file=sys.stderr,
        )
    if not result["control_target_exact"] or not result["control_default_target"]:
        print(
            "  InstructionCensusControls must be the exact X86InstructionCensusControls lean_lib "
            "root and a Lake default target run by the authoritative build gate.",
            file=sys.stderr,
        )
    if result["control_library_importers"]:
        print(
            "  Hostile census control leaked into library imports: "
            f"{result['control_library_importers']}",
            file=sys.stderr,
        )


SELF_TEST_MODULES = {
    "_UmbrellaInfrastructure": "def umbrellaInfrastructureHelper : Nat := 0\n",
    "_UmbrellaNested.Hidden": "def nestedUmbrellaInfrastructureHelper : Nat := 0\n",
}


def run_self_test(json_mode: bool) -> int:
    paths = [module_path(name) for name in SELF_TEST_MODULES]
    if any(path.exists() for path in paths):
        collisions = [str(path) for path in paths if path.exists()]
        print(f"self-test scratch path already exists: {collisions}", file=sys.stderr)
        return 1
    red_exit = None
    red = False
    try:
        for name, content in SELF_TEST_MODULES.items():
            path = module_path(name)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
        red_result = compute()
        expected = sorted(SELF_TEST_MODULES)
        red = red_result["missing_from_umbrella"] == expected
        red_exit = result_exit_code(red_result)
    finally:
        for path in paths:
            path.unlink(missing_ok=True)
        nested_dir = INSTRUCTIONS_DIR / "_UmbrellaNested"
        if nested_dir.is_dir() and not any(nested_dir.iterdir()):
            nested_dir.rmdir()
    green_result = compute()
    green = result_exit_code(green_result) == 0
    result = {
        "planted_modules": sorted(SELF_TEST_MODULES),
        "red_exit_code": red_exit,
        "named_exactly": red,
        "green_after_revert": green,
        "passed": red and red_exit == 1 and green,
    }
    if json_mode:
        print(json.dumps({"self_test": "PASS" if result["passed"] else "FAIL", **result}, indent=2))
    else:
        print("# Instructions umbrella recursive planted controls")
        print(f"  top-level and nested modules named exactly: {result['named_exactly']}")
        print(f"  red exit code: {result['red_exit_code']}")
        print(f"  green after revert: {result['green_after_revert']}")
        print(f"SELF-TEST: {'PASS' if result['passed'] else 'FAIL'}")
    return 0 if result["passed"] else 1


def main() -> int:
    parser = argparse.ArgumentParser(description="Instructions.lean exact umbrella completeness")
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    parser.add_argument("--self-test", action="store_true", help="run planted form controls")
    args = parser.parse_args()
    if args.self_test:
        return run_self_test(args.json)
    try:
        result = compute()
    except FileNotFoundError as error:
        print(f"Instructions.lean umbrella completeness check FAILED: {error}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps({**result, "exit_code": result_exit_code(result)}, indent=2))
    else:
        print_report(result)
    return result_exit_code(result)


if __name__ == "__main__":
    sys.exit(main())
