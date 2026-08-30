# Copyright 2026 Craig Tiller
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Keep whole-program proof authority singular and legacy-free.

Lean checks the proof fields of `Gasm.Core.Platform.VerifiedProgram`; this
small source ratchet checks the architectural fact that there is exactly one
declaration with that authority name and that retired target-specific program
and environment-loader APIs cannot return as compatibility debt.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
CANONICAL_FILE = "Gasm/Core/Platform.lean"
DECLARATION_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?P<modifiers>(?:(?:private|protected|noncomputable|partial|scoped|unsafe)\s+)*)"
    r"(?P<kind>structure|class|inductive|abbrev|def|opaque)\s+"
    r"(?P<name>[A-Za-z0-9_.<>]+)\b"
)
RETIRED_IDENTIFIERS = {
    "VerifiedLinuxProgram",
    "VerifiedWindowsProgram",
    "VerifiedWasmProgram",
    "VerifiedAArch64LinuxProgram",
    "EnvironmentLoader",
    "LinuxEnvironmentLoader",
}


def tracked_lean_files() -> list[str]:
    result = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.lean"], cwd=REPO_ROOT,
        capture_output=True, check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.decode("utf-8", errors="replace"))
    return [p for p in result.stdout.decode("utf-8").split("\0") if p]


def strip_comments(text: str) -> str:
    """Remove nested Lean comments while retaining strings and line shape."""
    out: list[str] = []
    depth = 0
    i = 0
    in_string = False
    while i < len(text):
        if depth == 0 and text[i] == '"':
            in_string = not in_string
            out.append(" ")
            i += 1
        elif in_string:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif not in_string and text.startswith("/-", i):
            depth += 1
            out.extend("  ")
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            out.extend("  ")
            i += 2
        elif depth > 0:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif not in_string and text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                out.extend(" " * (len(text) - i))
                break
            out.extend(" " * (end - i))
            i = end
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def findings(files: dict[str, str]) -> list[str]:
    problems: list[str] = []
    canonical_count = 0
    for rel, raw in files.items():
        text = strip_comments(raw)
        for match in DECLARATION_RE.finditer(text):
            name = match.group("name")
            short_name = name.rsplit(".", 1)[-1]
            if not re.fullmatch(r"Verified[A-Za-z0-9_]*Program", short_name):
                continue
            canonical = (
                rel == CANONICAL_FILE
                and match.group("kind") == "structure"
                and not match.group("modifiers").strip()
                and name == "VerifiedProgram"
            )
            if canonical:
                canonical_count += 1
            else:
                problems.append(f"{rel}: parallel whole-program authority declaration `{name}`")
        for identifier in sorted(RETIRED_IDENTIFIERS):
            if re.search(rf"\b{re.escape(identifier)}\b", text):
                problems.append(f"{rel}: retired verification API `{identifier}`")
    if canonical_count != 1:
        problems.append(
            f"{CANONICAL_FILE}: expected exactly one canonical `structure VerifiedProgram`, "
            f"found {canonical_count}"
        )
    return sorted(problems)


def self_test() -> int:
    good = {
        CANONICAL_FILE: "structure VerifiedProgram (P : Type) where\n  sound : True\n",
        "Gasm/Other.lean": "/- VerifiedLinuxProgram -/\ndef helper := 1\n",
    }
    duplicate = dict(good, **{"Gasm/Duplicate.lean": "structure VerifiedProgram where\n"})
    legacy = dict(good, **{"Spikes/Old.lean": "def x : VerifiedLinuxProgram := by trivial\n"})
    modified = dict(good, **{"Gasm/Modified.lean": "private structure VerifiedFooProgram where\n"})
    qualified = dict(good, **{"Gasm/Qualified.lean": "noncomputable def Foo.VerifiedBarProgram := 1\n"})
    attributed = dict(good, **{"Gasm/Attributed.lean": "@[irreducible] def Foo.VerifiedBazProgram := 1\n"})
    opaque = dict(good, **{"Gasm/Opaque.lean": "opaque VerifiedOpaqueProgram : Type\n"})
    shadow = dict(good)
    shadow[CANONICAL_FILE] += "def VerifiedProgram := 1\n"
    passed = all([
        not findings(good),
        bool(findings(duplicate)),
        bool(findings(legacy)),
        bool(findings(modified)),
        bool(findings(qualified)),
        bool(findings(attributed)),
        bool(findings(opaque)),
        bool(findings(shadow)),
    ])
    print(f"verification-authority synthetic controls: {'PASS' if passed else 'FAIL'}")
    return 0 if passed else 1


def main() -> int:
    parser = argparse.ArgumentParser(description="Enforce the sole VerifiedProgram authority")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    files = {
        rel: (REPO_ROOT / rel).read_text(encoding="utf-8")
        for rel in tracked_lean_files()
    }
    problems = findings(files)
    for problem in problems:
        print(f"[!] {problem}")
    if problems:
        print(f"[!] verification authority gate failed with {len(problems)} finding(s)")
        return 1
    print("[+] sole VerifiedProgram authority and legacy-free API confirmed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
