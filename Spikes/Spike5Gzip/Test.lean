/-
Copyright 2026 Craig Tiller

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Lean
import Gasm.Core.Verification
import Gasm.Effects.Inject
import Gasm.Effects.Trace
import Gasm.Targets.WASI.ABI
import Spikes.Spike5Gzip.Spec
import Spikes.Spike5Gzip.Equivalence

open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.WASI
open Spikes.Spike5Gzip
open Stdlib.Zlib

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- CLI Test Target for Dual-Target Spike 5 GZIP/GUNZIP Utility (x86_64 Windows & WebAssembly). -/
def main : IO UInt32 := do
  IO.println "[*] ==================================================================="
  IO.println "[*] SPIKE 5: Dual-Target GZIP / GUNZIP Verification Suite"
  IO.println "[*] ==================================================================="

  -- 1. Verify VerifiedProgram Windows Contract & Binary Emission
  IO.println "[*] [1/6] Verifying x86_64 Windows VerifiedProgram Contract..."
  let winExeBytes ← IO.ofExcept (emitVerifiedProgram spike5WindowsVerifiedProgram)
  let winExePath := "spike5_gzip.exe"
  IO.FS.writeBinFile winExePath winExeBytes
  IO.println s!"[+] Windows PE32+ binary generated: {winExePath} ({winExeBytes.size} bytes)"

  -- 2. Verify universal VerifiedProgram contracts and binary emission
  IO.println "[*] [2/6] Verifying x86_64 Linux VerifiedProgram Contracts..."
  let linuxGzipBytes ← IO.ofExcept (emitVerifiedProgram spike5LinuxVerifiedProgram)
  let linuxGunzipBytes ← IO.ofExcept (emitVerifiedProgram spike5GunzipLinuxVerifiedProgram)
  let linuxGzipPath := "spike5_gzip_linux"
  let linuxGunzipPath := "spike5_gunzip_linux"
  IO.FS.writeBinFile linuxGzipPath linuxGzipBytes
  IO.FS.writeBinFile linuxGunzipPath linuxGunzipBytes
  IO.println s!"[+] Linux ELF64 GZIP binary generated: {linuxGzipPath} ({linuxGzipBytes.size} bytes)"
  IO.println s!"[+] Linux ELF64 GUNZIP binary generated: {linuxGunzipPath} ({linuxGunzipBytes.size} bytes)"

  -- 3. Verify WebAssembly universal VerifiedProgram contract and emission
  IO.println "[*] [3/6] Verifying WebAssembly VerifiedProgram Contract..."
  let wasmBytes ← IO.ofExcept (emitVerifiedProgram spike5WasmVerifiedProgram)
  let wasmPath := "spike5_gzip.wasm"
  IO.FS.writeBinFile wasmPath wasmBytes
  IO.println s!"[+] WebAssembly binary generated: {wasmPath} ({wasmBytes.size} bytes)"

  -- 4. Demonstrate both outcomes of the fold-backed streaming contract used
  -- by the emitted VerifiedProgram.
  IO.println "[*] [4/6] Demonstrating fallible-fold streaming outcomes..."
  match compressAll bufferedStreamingZlibCapability spike5AllocationScope canonicalSampleData with
  | .success compressed _ =>
      IO.println s!"    ✓ Accepted: {canonicalSampleData.size} bytes -> {compressed.size} bytes"
  | .rejected _ _ =>
      IO.println "[!] FAIL: compression unexpectedly rejected"
      return 1
  | .resourceExhausted _ =>
      IO.println "[!] FAIL: normal-capacity compression exhausted its scope"
      return 1

  let zeroScope : AllocationScope := { capacity := 0 }
  match compressAll bufferedStreamingZlibCapability zeroScope canonicalSampleData with
  | .resourceExhausted finalScope =>
      if finalScope = zeroScope then
        IO.println "    ✓ Refused: zero-capacity scope produced exact resourceExhausted outcome"
      else
        IO.println "[!] FAIL: refusal did not preserve the exact failed allocation scope"
        return 1
  | .success _ _ =>
      IO.println "[!] FAIL: zero-capacity compression unexpectedly succeeded"
      return 1
  | .rejected _ _ =>
      IO.println "[!] FAIL: zero-capacity compression returned the wrong refusal kind"
      return 1

  -- The imported contracts carry universal trace equivalence for both
  -- directions on all three targets; elaboration of this executable is the proof gate.
  IO.println "    ✓ Six universal streaming trace contracts elaborated."

  -- 4. Verify GZIP Roundtrip on Multiple Inputs
  IO.println "[*] [5/6] Verifying GZIP / GUNZIP Invertibility & Checksum Invariants..."
  let repeatedStr := (String.pushn "" 'A' 500) ++ (String.pushn "" 'B' 500)
  let inputs : List (String × ByteArray) := [
    ("Empty Data", ByteArray.empty),
    ("Sample Canonical Data", canonicalSampleData),
    ("Short String", "Hello gzip world!".toUTF8),
    ("Repetitive Pattern", repeatedStr.toUTF8)
  ]

  for (label, data) in inputs do
    let compressed := compressData data
    match decompressData compressed with
    | Except.ok uncompressed =>
      if uncompressed == data then
        IO.println s!"    ✓ [{label}]: {data.size} bytes -> {compressed.size} bytes -> {uncompressed.size} bytes (Verified)"
      else
        IO.println s!"    [!] [{label}]: Payload mismatch!"
        return 1
    | Except.error err =>
      IO.println s!"    [!] [{label}]: Decompression failed: {err}"
      return 1

  -- Mandatory Assertion: Repetitive string gets significantly shorter after compression
  let repeatingAs := (String.pushn "" 'a' 251).toUTF8
  let compressedAs := compressData repeatingAs
  if compressedAs.size >= repeatingAs.size then
    IO.println s!"[!] FAIL: Repetitive 'a'*251 did not get shorter! ({repeatingAs.size} -> {compressedAs.size})"
    return 1
  IO.println s!"    ✓ Verified Compression: 251 bytes of repetitive 'a' -> {compressedAs.size} bytes ({100 - (compressedAs.size * 100 / repeatingAs.size)}% size reduction)"

  -- 5. Verify CLI Flag Parsing
  IO.println "[*] [6/6] Verifying CLI Flag Parsing..."
  if parseGzipFlags ["-d", "file.gz"] != GzipMode.Decompress then
    IO.println "[!] FAIL: -d flag parsing"
    return 1
  if parseGzipFlags ["--decompress", "file.gz"] != GzipMode.Decompress then
    IO.println "[!] FAIL: --decompress flag parsing"
    return 1
  if parseGzipFlags ["file.txt"] != GzipMode.Compress then
    IO.println "[!] FAIL: default compress mode parsing"
    return 1
  IO.println "    ✓ CLI Flag Parsing verified."

  IO.println "[*] ==================================================================="
  IO.println "[+] ALL SPIKE 5 DUAL-TARGET GZIP / GUNZIP VERIFICATION CHECKS PASSED!"
  IO.println "[*] ==================================================================="
  return 0
