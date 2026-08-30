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

"""Cheap mutation controls for the protected full declaration-coverage launcher."""

from __future__ import annotations

import contextlib
import io
import os
from pathlib import Path
import sys
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_full_refs_coverage as launcher


class Result:
    def __init__(self, returncode: int = 0) -> None:
        self.returncode = returncode


def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> int:
    with mock.patch.dict(os.environ, {launcher.OPT_IN_ENV: ""}, clear=False):
        with contextlib.redirect_stderr(io.StringIO()):
            check(launcher.main([]) == 2, "accidental invocation did not refuse")

    try:
        with contextlib.redirect_stderr(io.StringIO()):
            launcher.main(["--full-repository", "--", "--scan-root"])
    except SystemExit as error:
        check(error.code == 2, "reserved argument forwarding did not fail in argparse")
    else:
        raise AssertionError("reserved argument forwarding was accepted")

    # `--print-command` must be usable in a clean checkout: make any binary lookup fatal.
    with mock.patch.object(
        launcher, "gate_executable_path", side_effect=AssertionError("binary lookup in print mode")
    ):
        with contextlib.redirect_stdout(io.StringIO()) as output:
            check(
                launcher.main(["--full-repository", "--print-command"]) == 0,
                "clean print-command failed",
            )
        rendered = output.getvalue()
        check("check_refs_coverage_full" in rendered, "print-command omitted protected target")
        check("+Gasm:olean" in rendered, "print-command omitted declared root build")

    calls: list[list[str]] = []

    def fake_run(command: list[str], **_: object) -> Result:
        calls.append(list(command))
        return Result()

    class FakeLease:
        def __enter__(self) -> None:
            return None

        def __exit__(self, *_: object) -> None:
            return None

    with mock.patch.object(launcher, "lean_process_lease", return_value=FakeLease()):
        with mock.patch.object(launcher.subprocess, "run", side_effect=fake_run):
            check(launcher.main(["--self-test-authority"]) == 0, "authority self-test path failed")
    check(len(calls) == 2, "authority self-test did not build then execute")
    check(calls[1][-1] == "--self-test-authority", "authority self-test argument was not forwarded")

    print("full-refs launcher self-test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
