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
import Stdlib.Zlib.Deflate
import Stdlib.Zlib.Gzip

namespace Stdlib.Gzip

open Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Canonical in-memory GZIP (RFC 1952) compression. -/
def compress (data : ByteArray) : ByteArray :=
  gzipCompress data

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Canonical in-memory GZIP (RFC 1952) decompression with CRC-32 and ISIZE validation. -/
def decompress (bytes : ByteArray) : Except String ByteArray :=
  gzipDecompress bytes

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Compresses a source file to a destination .gz file. -/
def compressFile (srcPath dstPath : String) : IO Unit := do
  let srcBytes ← IO.FS.readBinFile srcPath
  let gzBytes := compress srcBytes
  IO.FS.writeBinFile dstPath gzBytes

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Decompresses a .gz file to a destination uncompressed file. -/
def decompressFile (srcPath dstPath : String) : IO (Except String Unit) := do
  let gzBytes ← IO.FS.readBinFile srcPath
  match decompress gzBytes with
  | .ok uncompressed =>
    IO.FS.writeBinFile dstPath uncompressed
    pure (.ok ())
  | .error err =>
    pure (.error err)

end Stdlib.Gzip
