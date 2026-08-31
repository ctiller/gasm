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

"""Close the x86 instruction-family proof-pipeline wiring gap.

`check_instructions_umbrella.py` proves that every instruction family on disk is visible to
Lean's registry audit.  Visibility alone is not the whole onboarding contract: each family also
needs a local round-trip proof shard, inclusion in the hot-path round-trip aggregator and
registry population, a global-dispatch reachability theorem, and a memory-frame proof shard.
Those surfaces are deliberately sharded for build performance, but their import lists are
necessarily hand maintained.

This gate derives the family set from the same structural fact as the umbrella gate -- a file
declares an `X86_64Instruction` instance -- and checks the rest of that pipeline against it.  It
checks wiring and the presence of the established proof declarations; Lean still checks the
proof terms and `MemoryFrameAudit.lean` still checks per-instruction frame coverage.  This script
does not certify instruction semantics, target fidelity, memory-model admission, or
`VerifiedProgram` authority.

Usage:
    python scripts/check_x86_family_pipeline.py
    python scripts/check_x86_family_pipeline.py --json
    python scripts/check_x86_family_pipeline.py --self-test
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
INSTANCE_DECL_RE = re.compile(
    r"^\s*instance(?:\s+(?:[A-Za-z_][A-Za-z0-9_']*|«[^»]+»))?\s*:\s*"
    r"X86_64Instruction\s+([A-Za-z0-9_.]+)\b",
    re.MULTILINE,
)
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$", re.MULTILINE)

INSTRUCTION_PREFIX = "Gasm.Targets.X86_64.Instructions."
ROUNDTRIP_PREFIX = "Gasm.Targets.X86_64.RoundtripGate."
MEMORY_FRAME_PREFIX = "Gasm.Targets.X86_64.MemoryFrame."

ROUNDTRIP_INFRA = {"Common", "DispatchExhaustive"}
MEMORY_FRAME_INFRA = {"Common", "NegativeControl"}


def strip_lean_comments(text: str) -> str:
    """Remove nested block comments and line comments while preserving newlines."""
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(text):
        pair = text[i:i + 2]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                i += 2
            elif pair == "-/":
                block_depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if not in_string and pair == "/-":
            block_depth = 1
            i += 2
            continue
        if not in_string and pair == "--":
            end = text.find("\n", i + 2)
            if end == -1:
                break
            out.append("\n")
            i = end + 1
            continue
        ch = text[i]
        out.append(ch)
        if ch == '"' and (i == 0 or text[i - 1] != "\\"):
            in_string = not in_string
        i += 1
    return "".join(out)


def read_code(path: Path) -> str:
    if not path.is_file():
        raise FileNotFoundError(path)
    return strip_lean_comments(path.read_text(encoding="utf-8"))


def imports_with_prefix(path: Path, prefix: str) -> set[str]:
    return {
        module[len(prefix):]
        for module in IMPORT_RE.findall(read_code(path))
        if module.startswith(prefix)
    }


def lower_first(name: str) -> str:
    return name[:1].lower() + name[1:]


def family_files(root: Path) -> set[str]:
    directory = root / "Gasm" / "Targets" / "X86_64" / "Instructions"
    if not directory.is_dir():
        raise FileNotFoundError(directory)
    families: set[str] = set()
    for path in directory.glob("*.lean"):
        instance_targets = INSTANCE_DECL_RE.findall(read_code(path))
        # Base.lean registers the open existential carrier so generic consumers can store
        # heterogeneous instructions.  It deliberately has no cases and is not a decoder family;
        # every concrete instruction instance is.  Key this exception to the semantic wrapper
        # type rather than to a filename/exclusion list.
        if any(target != "AnyX86_64Instruction" for target in instance_targets):
            families.add(path.stem)
    return families


def shard_files(directory: Path, infrastructure: set[str]) -> set[str]:
    if not directory.is_dir():
        raise FileNotFoundError(directory)
    return {path.stem for path in directory.glob("*.lean")} - infrastructure


def declaration_present(code: str, kind: str, name: str) -> bool:
    return bool(re.search(rf"^\s*{kind}\s+{re.escape(name)}\b", code, re.MULTILINE))


def theorem_signature_present(code: str, name: str, proposition: str) -> bool:
    compact = " ".join(code.split())
    return f"theorem {name} : {proposition} :=" in compact


def registry_sections(code: str) -> tuple[str, str]:
    population = re.search(
        r"\bdef\s+allEncodableInstructions\b.*?:=.*?(?=\bdef\s+expectedInstructionTypes\b)",
        code,
        re.DOTALL,
    )
    counts = re.search(
        r"\blet\s+familyCounts\b.*?:=.*?\[(.*?)]\s*\blet\s+empties\b",
        code,
        re.DOTALL,
    )
    return (population.group(0) if population else "", counts.group(1) if counts else "")


def occurrence_count(code: str, identifier: str) -> int:
    return len(re.findall(rf"\b{re.escape(identifier)}\b", code))


def compute(root: Path = REPO_ROOT) -> dict[str, object]:
    x86 = root / "Gasm" / "Targets" / "X86_64"
    families = family_files(root)
    roundtrip_dir = x86 / "RoundtripGate"
    memory_frame_dir = x86 / "MemoryFrame"

    roundtrip_shards = shard_files(roundtrip_dir, ROUNDTRIP_INFRA)
    frame_shards = shard_files(memory_frame_dir, MEMORY_FRAME_INFRA)
    roundtrip_imports = imports_with_prefix(x86 / "RoundtripGate.lean", ROUNDTRIP_PREFIX)
    dispatch_imports = imports_with_prefix(
        roundtrip_dir / "DispatchExhaustive.lean", ROUNDTRIP_PREFIX
    )
    frame_imports = imports_with_prefix(x86 / "MemoryFrame.lean", MEMORY_FRAME_PREFIX)

    roundtrip_imports -= ROUNDTRIP_INFRA
    dispatch_imports -= ROUNDTRIP_INFRA
    frame_imports -= MEMORY_FRAME_INFRA

    missing_roundtrip_declarations: dict[str, list[str]] = {}
    missing_dispatch_theorems: list[str] = []
    dispatch_code = read_code(roundtrip_dir / "DispatchExhaustive.lean")
    for family in sorted(families & roundtrip_shards):
        stem = lower_first(family)
        code = read_code(roundtrip_dir / f"{family}.lean")
        required = [
            ("def", f"{stem}FamilyCases"),
            ("theorem", f"{stem}Family_inBucketExclusive"),
        ]
        missing = [name for kind, name in required if not declaration_present(code, kind, name)]
        roundtrip_name = f"{stem}Family_roundtripGate"
        roundtrip_prop = f"{stem}FamilyCases.all (decodesOk {stem}TryDecode) = true"
        if not theorem_signature_present(code, roundtrip_name, roundtrip_prop):
            missing.append(roundtrip_name)
        if missing:
            missing_roundtrip_declarations[family] = missing
        dispatch_name = f"{stem}Family_dispatchReachable"
        dispatch_prop = f"{stem}FamilyCases.all (decodesOk decodeX86_64Instr) = true"
        if not theorem_signature_present(dispatch_code, dispatch_name, dispatch_prop):
            missing_dispatch_theorems.append(dispatch_name)

    registry_code = read_code(x86 / "Registry.lean")
    population, counts = registry_sections(registry_code)
    missing_registry_population: list[str] = []
    duplicate_registry_population: list[str] = []
    missing_registry_counts: list[str] = []
    duplicate_registry_counts: list[str] = []
    for family in sorted(families):
        cases = f"{lower_first(family)}FamilyCases"
        population_count = occurrence_count(population, cases)
        counts_count = occurrence_count(counts, cases)
        if population_count == 0:
            missing_registry_population.append(cases)
        elif population_count > 1:
            duplicate_registry_population.append(cases)
        if counts_count == 0:
            missing_registry_counts.append(cases)
        elif counts_count > 1:
            duplicate_registry_counts.append(cases)

    return {
        "families": sorted(families),
        "family_count": len(families),
        "missing_roundtrip_shards": sorted(families - roundtrip_shards),
        "orphan_roundtrip_shards": sorted(roundtrip_shards - families),
        "missing_roundtrip_imports": sorted(families - roundtrip_imports),
        "stale_roundtrip_imports": sorted(roundtrip_imports - families),
        "missing_roundtrip_declarations": missing_roundtrip_declarations,
        "missing_dispatch_imports": sorted(families - dispatch_imports),
        "stale_dispatch_imports": sorted(dispatch_imports - families),
        "missing_dispatch_theorems": missing_dispatch_theorems,
        "missing_memory_frame_shards": sorted(families - frame_shards),
        "orphan_memory_frame_shards": sorted(frame_shards - families),
        "missing_memory_frame_imports": sorted(families - frame_imports),
        "stale_memory_frame_imports": sorted(frame_imports - families),
        "missing_registry_population": missing_registry_population,
        "duplicate_registry_population": duplicate_registry_population,
        "missing_registry_counts": missing_registry_counts,
        "duplicate_registry_counts": duplicate_registry_counts,
    }


def failures(result: dict[str, object]) -> dict[str, object]:
    ignored = {"families", "family_count"}
    return {key: value for key, value in result.items() if key not in ignored and value}


def print_report(result: dict[str, object]) -> None:
    failed = failures(result)
    if not failed:
        print(
            "OK: all "
            f"{result['family_count']} x86 instruction families have complete round-trip, "
            "global-dispatch, registry-population, and memory-frame pipeline wiring."
        )
        return
    print("x86 instruction-family pipeline check FAILED.", file=sys.stderr)
    for key, value in failed.items():
        print(f"  {key}: {value}", file=sys.stderr)


def write_fixture(root: Path) -> None:
    x86 = root / "Gasm" / "Targets" / "X86_64"
    instructions = x86 / "Instructions"
    roundtrip = x86 / "RoundtripGate"
    frame = x86 / "MemoryFrame"
    for directory in (instructions, roundtrip, frame):
        directory.mkdir(parents=True, exist_ok=True)

    (instructions / "Foo.lean").write_text(
        "structure FooInstr where\n  value : Nat\n\n"
        "instance fooInstruction : X86_64Instruction FooInstr where\n",
        encoding="utf-8",
    )
    (instructions / "Helper.lean").write_text(
        "def helperOnly : Nat := 0\n", encoding="utf-8"
    )
    (roundtrip / "Foo.lean").write_text(
        "def fooFamilyCases : List Nat := []\n"
        "theorem fooFamily_roundtripGate : "
        "fooFamilyCases.all (decodesOk fooTryDecode) = true := by trivial\n"
        "theorem fooFamily_inBucketExclusive : True := by trivial\n",
        encoding="utf-8",
    )
    (roundtrip / "Common.lean").write_text("def common : Nat := 0\n", encoding="utf-8")
    (roundtrip / "DispatchExhaustive.lean").write_text(
        "import Gasm.Targets.X86_64.RoundtripGate.Foo\n"
        "theorem fooFamily_dispatchReachable : "
        "fooFamilyCases.all (decodesOk decodeX86_64Instr) = true := by trivial\n",
        encoding="utf-8",
    )
    (frame / "Foo.lean").write_text("theorem fooFrame : True := by trivial\n", encoding="utf-8")
    (frame / "Common.lean").write_text("def common : Nat := 0\n", encoding="utf-8")
    (x86 / "RoundtripGate.lean").write_text(
        "import Gasm.Targets.X86_64.RoundtripGate.Common\n"
        "import Gasm.Targets.X86_64.RoundtripGate.Foo\n",
        encoding="utf-8",
    )
    (x86 / "MemoryFrame.lean").write_text(
        "import Gasm.Targets.X86_64.MemoryFrame.Common\n"
        "import Gasm.Targets.X86_64.MemoryFrame.Foo\n",
        encoding="utf-8",
    )
    (x86 / "Registry.lean").write_text(
        "def allEncodableInstructions : List Nat := fooFamilyCases\n"
        "def expectedInstructionTypes : List Nat := []\n"
        "run_cmd do\n"
        "  let familyCounts : List (String × Nat) := [(\"foo\", fooFamilyCases.length)]\n"
        "  let empties := familyCounts\n",
        encoding="utf-8",
    )


def replace_once(path: Path, old: str, new: str = "") -> None:
    text = path.read_text(encoding="utf-8")
    if text.count(old) != 1:
        raise RuntimeError(f"self-test mutation expected one occurrence in {path}: {old!r}")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")


def run_self_test(json_mode: bool) -> int:
    vectors: list[tuple[str, str]] = [
        ("missing_roundtrip_shard", "missing_roundtrip_shards"),
        ("missing_roundtrip_import", "missing_roundtrip_imports"),
        ("wrong_roundtrip_signature", "missing_roundtrip_declarations"),
        ("missing_dispatch_import", "missing_dispatch_imports"),
        ("wrong_dispatch_signature", "missing_dispatch_theorems"),
        ("missing_memory_frame_shard", "missing_memory_frame_shards"),
        ("missing_memory_frame_import", "missing_memory_frame_imports"),
        ("missing_registry_population", "missing_registry_population"),
        ("missing_registry_count", "missing_registry_counts"),
    ]
    results: list[dict[str, object]] = []
    with tempfile.TemporaryDirectory(prefix="gasm-x86-family-pipeline-") as temp:
        root = Path(temp)
        for vector, expected_key in vectors:
            write_fixture(root)
            x86 = root / "Gasm" / "Targets" / "X86_64"
            if vector == "missing_roundtrip_shard":
                (x86 / "RoundtripGate" / "Foo.lean").unlink()
            elif vector == "missing_roundtrip_import":
                replace_once(
                    x86 / "RoundtripGate.lean",
                    "import Gasm.Targets.X86_64.RoundtripGate.Foo\n",
                )
            elif vector == "wrong_roundtrip_signature":
                replace_once(
                    x86 / "RoundtripGate" / "Foo.lean",
                    "fooFamilyCases.all (decodesOk fooTryDecode) = true",
                    "True",
                )
            elif vector == "missing_dispatch_import":
                replace_once(
                    x86 / "RoundtripGate" / "DispatchExhaustive.lean",
                    "import Gasm.Targets.X86_64.RoundtripGate.Foo\n",
                )
            elif vector == "wrong_dispatch_signature":
                replace_once(
                    x86 / "RoundtripGate" / "DispatchExhaustive.lean",
                    "fooFamilyCases.all (decodesOk decodeX86_64Instr) = true",
                    "True",
                )
            elif vector == "missing_memory_frame_shard":
                (x86 / "MemoryFrame" / "Foo.lean").unlink()
            elif vector == "missing_memory_frame_import":
                replace_once(
                    x86 / "MemoryFrame.lean",
                    "import Gasm.Targets.X86_64.MemoryFrame.Foo\n",
                )
            elif vector == "missing_registry_population":
                replace_once(x86 / "Registry.lean", "fooFamilyCases\n", "[]\n")
            elif vector == "missing_registry_count":
                replace_once(
                    x86 / "Registry.lean",
                    "[(\"foo\", fooFamilyCases.length)]",
                    "[]",
                )
            result = compute(root)
            red = expected_key in failures(result)
            write_fixture(root)
            green = not failures(compute(root))
            results.append(
                {
                    "vector": vector,
                    "expected_failure": expected_key,
                    "turned_red": red,
                    "green_after_revert": green,
                    "passed": red and green,
                }
            )

    all_ok = all(bool(result["passed"]) for result in results)
    if json_mode:
        print(json.dumps({"self_test": "PASS" if all_ok else "FAIL", "results": results}, indent=2))
    else:
        print("# x86 family-pipeline planted-defect controls")
        for result in results:
            status = "PASS" if result["passed"] else "FAIL"
            print(
                f"  {result['vector']:<30} {status} "
                f"(expected {result['expected_failure']})"
            )
        print(f"SELF-TEST: {'PASS' if all_ok else 'FAIL'}")
    return 0 if all_ok else 1


def main() -> int:
    parser = argparse.ArgumentParser(description="x86 instruction-family pipeline wiring gate")
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    parser.add_argument(
        "--self-test", action="store_true", help="run planted-defect controls in a temp tree"
    )
    args = parser.parse_args()
    if args.self_test:
        return run_self_test(args.json)
    try:
        result = compute()
    except (FileNotFoundError, RuntimeError) as error:
        print(f"x86 instruction-family pipeline check FAILED: {error}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps({**result, "exit_code": 1 if failures(result) else 0}, indent=2))
    else:
        print_report(result)
    return 1 if failures(result) else 0


if __name__ == "__main__":
    sys.exit(main())
