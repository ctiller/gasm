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

"""
Dual-Direction Cross-Differential GZIP & GUNZIP Binary Fuzzer
Oracle: Python standard library gzip & zlib modules.

Cross-checks BOTH native binaries with live dynamic piped stdin:
1. Direction A: Dynamic stdin -> spike5_gzip.exe -> Python gzip.decompress -> assert == stdin
2. Direction B: Dynamic stdin -> Python gzip.compress -> spike5_gunzip.exe -> assert == stdin
3. Direction C: Dynamic stdin -> spike5_gzip.exe -> spike5_gunzip.exe -> assert == stdin
"""

import gzip
import os
import random
import subprocess
import sys
import tempfile

from lean_process_lease import inherited_lease_environment, lean_process_lease

def test_spike5_binaries(count: int = 50):
    # 1. Emit spike5_gzip.exe and spike5_gunzip.exe from verified contracts
    print("[*] Emitting spike5_gzip.exe and spike5_gunzip.exe from Lean verified contracts...")
    with lean_process_lease():
        child_env = inherited_lease_environment()
        res1 = subprocess.run(
            ["lake", "exe", "spike5_gzip_windows"], capture_output=True, text=True,
            env=child_env,
        )
        if res1.returncode != 0:
            print(f"[-] Failed to emit spike5_gzip.exe: {res1.stderr}")
            sys.exit(1)

        res2 = subprocess.run(
            ["lake", "exe", "spike5_gunzip_windows"], capture_output=True, text=True,
            env=child_env,
        )
        if res2.returncode != 0:
            print(f"[-] Failed to emit spike5_gunzip.exe: {res2.stderr}")
            sys.exit(1)

    gzip_exe = os.path.abspath("spike5_gzip.exe")
    gunzip_exe = os.path.abspath("spike5_gunzip.exe")

    if not os.path.exists(gzip_exe):
        print(f"[-] Error: {gzip_exe} was not produced!")
        sys.exit(1)
    if not os.path.exists(gunzip_exe):
        print(f"[-] Error: {gunzip_exe} was not produced!")
        sys.exit(1)

    print(f"[+] Verified native binaries produced:\n    Compressor:   {gzip_exe}\n    Decompressor: {gunzip_exe}")
    print(f"[+] Starting Dual-Direction Cross-Differential Fuzzing ({count} randomized vectors)...")

    num_random_tests = count
    test_cases = [
        b"",
        b"A",
        b"Hello, World!",
        b"A" * 100,
        b"A" * 251,
        b"A" * 500,
        b"abcdef" * 50,
        b"The quick brown fox jumps over the lazy dog.\n" * 20,
        b"hello world! " * 80,
        bytes(range(256)),
        bytes([i % 10 for i in range(1000)]),
    ]

    random.seed(0xDEADBEEF)
    for i in range(num_random_tests):
        size = random.choice([0, 1, 2, 5, 15, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192])
        mode = random.choice([0, 1, 2, 3, 4])
        if mode == 0:
            test_cases.append(b"A" * size)
        elif mode == 1:
            pattern = os.urandom(random.randint(2, 8))
            test_cases.append((pattern * (size // len(pattern) + 1))[:size])
        elif mode == 2:
            test_cases.append(bytes([(x % 26 + 65) for x in range(size)]))
        elif mode == 3:
            test_cases.append(bytes([(x & 0xFF) for x in range(size)]))
        else:
            test_cases.append(os.urandom(size))

    print(f"[*] Testing {len(test_cases)} dynamic test vectors across all 3 execution paths...")

    for idx, data in enumerate(test_cases):
        # -------------------------------------------------------------
        # Path 1: Native GZIP -> Python gunzip oracle
        # -------------------------------------------------------------
        proc_comp = subprocess.run([gzip_exe], input=data, capture_output=True)
        if proc_comp.returncode != 0:
            print(f"[-] [Path 1] Test {idx} (size {len(data)}) failed: {gzip_exe} returned code {proc_comp.returncode}")
            sys.exit(1)
        comp_output = proc_comp.stdout

        # Assert size reduction on repetitive strings (both single-byte and multi-byte patterns)
        if len(data) >= 100:
            # Check if repetitive (single-character, small character set, or periodic pattern)
            is_repetitive = (
                len(set(data)) <= 2 or
                data == (data[:6] * (len(data) // 6 + 1))[:len(data)] or
                data == (data[:13] * (len(data) // 13 + 1))[:len(data)] or
                data == (data[:44] * (len(data) // 44 + 1))[:len(data)]
            )
            if is_repetitive:
                assert len(comp_output) < len(data), (
                    f"Compression failure: {len(data)} repetitive bytes did not get shorter! "
                    f"(Compressed size: {len(comp_output)})"
                )

        try:
            decomp_by_py = gzip.decompress(comp_output)
            assert decomp_by_py == data, f"Path 1 mismatch on test {idx}!"
        except Exception as e:
            print(f"[-] [Path 1] Test {idx} (size {len(data)}) failed: Python gunzip rejected output: {e}")
            sys.exit(1)

        # -------------------------------------------------------------
        # Path 2A: Python Stored Block GZIP -> Native GUNZIP
        # -------------------------------------------------------------
        py_stored = gzip.compress(data, compresslevel=0, mtime=0)
        proc_decomp_stored = subprocess.run([gunzip_exe], input=py_stored, capture_output=True)
        if proc_decomp_stored.returncode != 0:
            print(f"[-] [Path 2A] Test {idx} (size {len(data)}) failed: {gunzip_exe} returned code {proc_decomp_stored.returncode}")
            sys.exit(1)
        assert proc_decomp_stored.stdout == data, f"Path 2A mismatch on test {idx}!"

        # -------------------------------------------------------------
        # Path 2B: Python Real Fixed Huffman Compressed GZIP -> Native GUNZIP
        # -------------------------------------------------------------
        import zlib
        comp_obj = zlib.compressobj(wbits=31, strategy=zlib.Z_FIXED)
        py_huff = comp_obj.compress(data) + comp_obj.flush()
        proc_decomp_huff = subprocess.run([gunzip_exe], input=py_huff, capture_output=True)
        if proc_decomp_huff.returncode != 0:
            print(f"[-] [Path 2B] Test {idx} (size {len(data)}) failed: {gunzip_exe} returned code {proc_decomp_huff.returncode}")
            sys.exit(1)
        assert proc_decomp_huff.stdout == data, f"Path 2B mismatch on test {idx}!"

        # -------------------------------------------------------------
        # Path 2C: Standard Python Dynamic Huffman Compressed GZIP -> Native GUNZIP
        # -------------------------------------------------------------
        py_dynamic = gzip.compress(data, mtime=0)
        proc_decomp_dyn = subprocess.run([gunzip_exe], input=py_dynamic, capture_output=True)
        if proc_decomp_dyn.returncode != 0:
            print(f"[-] [Path 2C] Test {idx} (size {len(data)}) failed: {gunzip_exe} returned code {proc_decomp_dyn.returncode}")
            sys.exit(1)
        assert proc_decomp_dyn.stdout == data, f"Path 2C mismatch on test {idx}!"

        # -------------------------------------------------------------
        # Path 3: Native GZIP -> Native GUNZIP Full Roundtrip
        # -------------------------------------------------------------
        proc_roundtrip = subprocess.run([gunzip_exe], input=comp_output, capture_output=True)
        if proc_roundtrip.returncode != 0:
            print(f"[-] [Path 3] Test {idx} (size {len(data)}) failed: {gunzip_exe} returned code {proc_roundtrip.returncode}")
            sys.exit(1)
        assert proc_roundtrip.stdout == data, f"Path 3 roundtrip mismatch on test {idx}!"

    print(f"[+] SUCCESS: All {len(test_cases)} vectors verified bidirectional across:")
    print(f"    1. Native GZIP                  -> Python gunzip  (100% MATCH)")
    print(f"    2A. Python gzip (Stored Block)  -> Native GUNZIP  (100% MATCH)")
    print(f"    2B. Python gzip (Fixed Huffman) -> Native GUNZIP  (100% MATCH)")
    print(f"    2C. Python gzip (Dynamic Trees) -> Native GUNZIP  (100% MATCH)")
    print(f"    3. Native GZIP                  -> Native GUNZIP  (100% MATCH)")

def main():
    print("=" * 80)
    print(" GASM Dual-Direction GZIP / GUNZIP Live Native Binary Differential Fuzzer")
    print("=" * 80)

    test_spike5_binaries(50)

    print("\n[+] [In-Process Fuzzer] Running Lean GzipFuzzer CLI...")
    cmd = ["lake", "exe", "gzip_fuzzer", "--count", "100"]
    with lean_process_lease():
        subprocess.run(cmd, check=True, env=inherited_lease_environment())

    print("\n" + "=" * 80)
    print(" ALL DUAL-DIRECTION LIVE NATIVE BINARY AND IN-LEAN FUZZER CHECKS PASSED (100% SUCCESS)")
    print("=" * 80)

if __name__ == "__main__":
    main()
