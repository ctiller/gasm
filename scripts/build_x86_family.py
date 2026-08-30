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

"""Build the fast correctness frontier for one x86-64 instruction family.

This is an inner-loop command, not a replacement for ``python scripts/build_full.py`` or the
full repository gates.  It checks the edited instruction module and the core
consumers that catch local encoding, decoding, semantics, frame, and oracle
breakage without pulling the registry-derived whole-library tail into every
edit cycle.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import sys

from lean_process_lease import inherited_lease_environment, lean_process_lease


ROOT = Path(__file__).resolve().parents[1]


def targets_for(family: str) -> list[str]:
    family_source = ROOT / "Gasm" / "Targets" / "X86_64" / "Instructions" / f"{family}.lean"
    frame_source = ROOT / "Gasm" / "Targets" / "X86_64" / "MemoryFrame" / f"{family}.lean"
    gate_source = ROOT / "Gasm" / "Targets" / "X86_64" / "RoundtripGate" / f"{family}.lean"
    missing = [path.relative_to(ROOT) for path in (family_source, frame_source, gate_source)
               if not path.is_file()]
    if missing:
        rendered = ", ".join(str(path) for path in missing)
        raise ValueError(f"unknown or incomplete x86 family {family!r}; missing: {rendered}")

    prefix = "Gasm.Targets.X86_64"
    return [
        f"{prefix}.Instructions.{family}",
        f"{prefix}.Assembler",
        f"{prefix}.Decoder",
        f"{prefix}.Fuzzer",
        f"{prefix}.Instructions",
        f"{prefix}.MacroAssembler",
        f"{prefix}.MemoryFrame.{family}",
        f"{prefix}.PerfHardwareFuzzer",
        f"{prefix}.RoundtripGate.{family}",
    ]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("family", help="case-sensitive module name, for example Add or Jcc")
    parser.add_argument(
        "--print-only",
        action="store_true",
        help="print the lake command without executing it",
    )
    args = parser.parse_args()

    try:
        targets = targets_for(args.family)
    except ValueError as error:
        parser.error(str(error))

    command = ["lake", "build", *targets]
    print("FAST PARTIAL x86 family build (run `python scripts/build_full.py` before review):",
          flush=True)
    print(" ".join(command), flush=True)
    if args.print_only:
        return 0
    try:
        with lean_process_lease():
            return subprocess.run(
                command, cwd=ROOT, check=False, env=inherited_lease_environment()
            ).returncode
    except (OSError, TimeoutError, ValueError) as error:
        print(f"x86 family build lease failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
