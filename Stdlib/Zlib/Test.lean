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
import Stdlib.Zlib.CRC32
import Stdlib.Zlib.Adler32
import Stdlib.Zlib.Huffman
import Stdlib.Zlib.Deflate
import Stdlib.Zlib.Spec
import Stdlib.Zlib.Gzip
import Stdlib.Zlib.Equivalence

namespace Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#61-checksum-invariance-theorems -/
/-- Test runner verifying CRC-32 against standard IEEE 802.3 test vectors. -/
def testCrc32 : IO Unit := do
  IO.println "[+] Testing CRC-32 Checksum Engine..."
  let emptyCrc := crc32 ByteArray.empty
  if emptyCrc != 0 then throw (IO.userError s!"Empty CRC failed: expected 0, got {emptyCrc}")
  -- Standard IEEE 802.3 test vector "123456789" -> 0xCBF43926 (3421780262)
  let testVec := "123456789".toUTF8
  let testCrc := crc32 testVec
  if testCrc != 0xCBF43926 then
    throw (IO.userError s!"CRC-32 vector failed: expected 0xCBF43926, got {testCrc}")
  IO.println "    ✓ CRC-32 standard test vector passed (0xCBF43926)."

/- REF: docs/STDLIB_ZLIB.md#61-checksum-invariance-theorems -/
/-- Test runner verifying Adler-32 against standard RFC 1950 test vectors. -/
def testAdler32 : IO Unit := do
  IO.println "[+] Testing Adler-32 Checksum Engine..."
  let emptyAdler := adler32 ByteArray.empty
  if emptyAdler != 1 then throw (IO.userError s!"Empty Adler failed: expected 1, got {emptyAdler}")
  -- Standard RFC 1950 test vector "123456789" -> 0x091E01DE (152961502)
  let testVec := "123456789".toUTF8
  let testAdler := adler32 testVec
  if testAdler != 0x091E01DE then
    throw (IO.userError s!"Adler-32 vector failed: expected 0x091E01DE, got {testAdler}")
  -- "Wikipedia" -> 0x11E60398
  let wikiAdler := adler32 "Wikipedia".toUTF8
  if wikiAdler != 0x11E60398 then
    throw (IO.userError s!"Adler-32 'Wikipedia' vector failed: expected 0x11E60398, got {wikiAdler}")
  IO.println "    ✓ Adler-32 standard test vectors passed (0x091E01DE, 0x11E60398)."

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Test runner verifying DEFLATE / INFLATE compression and decompression roundtrips. -/
def testDeflate : IO Unit := do
  IO.println "[+] Testing RFC 1951 DEFLATE & INFLATE Engine..."
  -- Test 1: Empty payload
  let emptyDeflated := compress ByteArray.empty
  let emptyInflated ← match decompress emptyDeflated with
    | Except.ok res => pure res
    | Except.error e => throw (IO.userError s!"Empty DEFLATE decomp error: {repr e}")
  if emptyInflated.size != 0 then throw (IO.userError "Empty DEFLATE roundtrip mismatch")

  -- Test 2: Binary pattern 0..255
  let mut pattern := ByteArray.empty
  for i in [0:256] do
    pattern := pattern.push i.toUInt8
  let patternDeflated := compress pattern
  let patternInflated ← match decompress patternDeflated with
    | Except.ok res => pure res
    | Except.error e => throw (IO.userError s!"Pattern DEFLATE decomp error: {repr e}")
  if patternInflated != pattern then throw (IO.userError "Binary pattern DEFLATE roundtrip mismatch")

  -- Test 3: Large text payload
  let text := ("The quick brown fox jumps over the lazy dog. " ++
               "gasm is a formally verified multi-target assembly synthesis engine.\n").toUTF8
  let textDeflated := compress text
  let textInflated ← match decompress textDeflated with
    | Except.ok res => pure res
    | Except.error e => throw (IO.userError s!"Text DEFLATE decomp error: {repr e}")
  if textInflated != text then throw (IO.userError "Text DEFLATE roundtrip mismatch")

  IO.println "    ✓ RFC 1951 DEFLATE roundtrips passed (Empty, Binary, Text)."

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Test runner verifying the dynamic-Huffman (BTYPE=10) encode path is genuinely chosen
    and decoded: asserts the exact-bit-cost heuristic picks the dynamic block on a
    dynamic-favorable vector (so `decodeDynamicTables` is actually exercised, not
    vacuously skipped), picks the fixed block on a fixed-favorable vector, and that both
    roundtrip through the fully general `decompress`. -/
def testDynamicHuffman : IO Unit := do
  IO.println "[+] Testing RFC 1951 Dynamic Huffman (BTYPE=10) Encode/Decode Path..."
  -- A skewed-alphabet repetitive vector: dynamic tables beat the fixed code here.
  let mut skewed := ByteArray.empty
  for i in [0:4096] do
    skewed := skewed.push ((i % 17).toUInt8)
  let (usedDyn, dynStream) := compressPlan skewed
  if !usedDyn then
    throw (IO.userError "Dynamic-favorable vector did not select the dynamic-Huffman block — decodeDynamicTables would go unexercised (vacuity)")
  let dynInflated ← match decompress dynStream with
    | Except.ok res => pure res
    | Except.error e => throw (IO.userError s!"Dynamic block DEFLATE decomp error: {repr e}")
  if dynInflated != skewed then throw (IO.userError "Dynamic block DEFLATE roundtrip mismatch")
  -- A tiny vector: the ~dozens-of-bytes dynamic header can never win; fixed must be chosen.
  let tiny := "Hi".toUTF8
  let (usedDynTiny, tinyStream) := compressPlan tiny
  if usedDynTiny then
    throw (IO.userError "Tiny vector unexpectedly selected the dynamic-Huffman block")
  let tinyInflated ← match decompress tinyStream with
    | Except.ok res => pure res
    | Except.error e => throw (IO.userError s!"Fixed block DEFLATE decomp error: {repr e}")
  if tinyInflated != tiny then throw (IO.userError "Fixed block DEFLATE roundtrip mismatch")
  IO.println s!"    ✓ Dynamic-Huffman block chosen ({dynStream.size} bytes for 4096) and decoded; fixed path preserved."

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Test runner verifying RFC 1950 ZLIB container roundtrips with Adler-32 validation. -/
def testZlibContainer : IO Unit := do
  IO.println "[+] Testing RFC 1950 ZLIB Container & Adler-32 Verification..."
  let payload := "Formally verified ZLIB container roundtrip with Adler-32 check.".toUTF8
  let compressed := zlibCompress payload
  let decompressed ← match zlibDecompress compressed with
    | .ok res => pure res
    | .error e => throw (IO.userError s!"ZLIB container decompress failed: {e}")
  if decompressed != payload then throw (IO.userError "ZLIB container payload mismatch")
  IO.println "    ✓ RFC 1950 ZLIB container roundtrip verified."

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Test runner verifying RFC 1952 GZIP container roundtrips with CRC-32 & ISIZE validation. -/
def testGzipContainer : IO Unit := do
  IO.println "[+] Testing RFC 1952 GZIP Container & CRC-32 / ISIZE Verification..."
  let payload := "Formally verified GZIP container roundtrip with CRC-32 and ISIZE check.".toUTF8
  let compressed := gzipCompress payload
  let decompressed ← match gzipDecompress compressed with
    | .ok res => pure res
    | .error e => throw (IO.userError s!"GZIP container decompress failed: {e}")
  if decompressed != payload then throw (IO.userError "GZIP container payload mismatch")
  IO.println "    ✓ RFC 1952 GZIP container roundtrip verified."

end Stdlib.Zlib

open Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#6-formal-theorems-15-roundtrip-soundness -/
def main : IO UInt32 := do
  IO.println "======================================================================"
  IO.println " Stdlib.Zlib Test Suite (RFC 1950, RFC 1951, RFC 1952)"
  IO.println "======================================================================"
  try
    testCrc32
    testAdler32
    testDeflate
    testDynamicHuffman
    testZlibContainer
    testGzipContainer
    IO.println "\n[+] ALL STDLIB.ZLIB TESTS PASSED (100% SUCCESS)."
    return 0
  catch e =>
    IO.println s!"\n[!] TEST FAILED: {e}"
    return 1
