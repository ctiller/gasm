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

"""Measure one leased process tree without repeatedly enumerating all host processes."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import threading
import time

try:
    import psutil
except ImportError:  # local measurement tool; CI/build paths do not depend on psutil
    psutil = None

from lean_process_lease import inherited_lease_environment, lean_process_lease


BUILT_JOB_RE = re.compile(r"(?m)^(?:✔|⚠) \[[0-9]+/[0-9]+\] Built ")


def terminate_tree(root) -> None:
    if psutil is None:
        return
    try:
        descendants = root.children(recursive=True)
    except psutil.Error:
        descendants = []
    for process in reversed(descendants):
        try:
            process.terminate()
        except psutil.Error:
            pass
    try:
        root.terminate()
    except psutil.Error:
        pass
    _, alive = psutil.wait_procs([*descendants, root], timeout=5)
    for process in alive:
        try:
            process.kill()
        except psutil.Error:
            pass


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sample-ms", type=int, default=500)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("a command is required after --")
    if args.sample_ms < 50:
        parser.error("--sample-ms must be at least 50")
    if psutil is None:
        print("measurement requires the local Python package 'psutil'", file=sys.stderr)
        return 2

    output_parts: list[str] = []
    peak_rss = 0
    peak_snapshot: list[tuple[int, int, str]] = []
    process_peaks: dict[int, tuple[int, str]] = {}
    root = None
    start = time.monotonic()
    try:
        with lean_process_lease():
            child = subprocess.Popen(
                command,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                encoding="utf-8",
                errors="replace",
                env=inherited_lease_environment(),
            )
            root = psutil.Process(child.pid)

            def copy_output() -> None:
                assert child.stdout is not None
                for line in child.stdout:
                    output_parts.append(line)
                    print(line, end="", flush=True)

            reader = threading.Thread(target=copy_output, daemon=True)
            reader.start()
            while child.poll() is None:
                processes = [root]
                try:
                    processes.extend(root.children(recursive=True))
                except psutil.Error:
                    pass
                sample_rss = 0
                sample_processes: list[tuple[int, int, str]] = []
                for process in processes:
                    try:
                        rss = process.memory_info().rss
                        previous = process_peaks.get(process.pid)
                        if previous is None:
                            command_line = " ".join(process.cmdline()) or process.name()
                            label = " ".join(command_line.split())[:300]
                        else:
                            label = previous[1]
                        if previous is None or rss > previous[0]:
                            process_peaks[process.pid] = (rss, label)
                        sample_processes.append((rss, process.pid, label))
                        sample_rss += rss
                    except psutil.Error:
                        pass
                if sample_rss > peak_rss:
                    peak_rss = sample_rss
                    peak_snapshot = sorted(sample_processes, reverse=True)[:8]
                time.sleep(args.sample_ms / 1000)
            reader.join(timeout=5)
            exit_code = child.returncode
    except (KeyboardInterrupt, OSError, TimeoutError, ValueError) as error:
        if root is not None:
            terminate_tree(root)
        print(f"measurement aborted and process tree cleaned up: {error}", file=sys.stderr)
        return 2

    elapsed = time.monotonic() - start
    combined = "".join(output_parts)
    built_jobs = len(BUILT_JOB_RE.findall(combined))
    print(
        f"MEASURE seconds={elapsed:.3f} peak_mib={peak_rss / 1024**2:.1f} "
        f"built_jobs={built_jobs} sample_ms={args.sample_ms} exit={exit_code}"
    )
    for rss, pid, label in peak_snapshot:
        print(
            f"MEASURE_AT_AGGREGATE_PEAK pid={pid} rss_mib={rss / 1024**2:.1f} "
            f"command={label}"
        )
    for pid, (rss, label) in sorted(
        process_peaks.items(), key=lambda item: item[1][0], reverse=True
    )[:8]:
        print(
            f"MEASURE_PROCESS_PEAK pid={pid} rss_mib={rss / 1024**2:.1f} command={label}"
        )
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
