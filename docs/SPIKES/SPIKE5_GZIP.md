# Spike 5: Dual-Target GZIP / GUNZIP Utility (x86_64 Windows & WebAssembly)

Spike 5 establishes the formal verified lowering and execution of a **GZIP / GUNZIP compression and decompression utility** (`Spikes.Spike5Gzip`) co-developed across two distinct machine targets using `Stdlib.Zlib`:
1. **x86_64 Windows (`.exe`)**: Native PE32+ console binary linking with `kernel32.dll` for streaming file and console I/O (`ReadFile`, `WriteFile`, `GetStdHandle`).
2. **WebAssembly (`.wasm`)**: Standard WebAssembly MVP binary module operating over linear memory with WASI system calls (`fd_read`, `fd_write`, `proc_exit`).

Both implementations satisfy identical high-level mathematical specifications and constructive semantic trace equivalence proofs.

---

## 1. High-Level Architecture & GZIP State Machine

```mermaid
graph TD
    Input["Input Data Stream (File / Stdin)"] --> Mode{"Mode: Compress or Decompress?"}
    
    Mode -->|Compress (gzip)| GzipEnc["Gzip Header Builder (ID1=0x1F, ID2=0x8B, CM=8)"]
    GzipEnc --> Deflate["Stdlib.Zlib.Deflate (RFC 1951)"]
    Deflate --> CrcEnc["Compute CRC-32 & Uncompressed Size (ISIZE)"]
    CrcEnc --> OutEnc["Write GZIP Stream (.gz / stdout)"]
    
    Mode -->|Decompress (gunzip)| GzipDec["Parse & Validate Gzip Header (ID1, ID2, CM, FLG)"]
    GzipDec --> Inflate["Stdlib.Zlib.Inflate (RFC 1951)"]
    Inflate --> CrcDec["Verify CRC-32 Checksum & ISIZE Trailer"]
    CrcDec --> OutDec["Write Decompressed Stream (File / stdout)"]
```

### 1.1 Supported RFC 1952 Specification Subset
- **Magic Identification**:
  - `ID1 = 0x1F`, `ID2 = 0x8B`.
- **Compression Method**:
  - `CM = 8` (DEFLATE).
- **Header Flags (`FLG`)**:
  - `FTEXT` (bit 0): Optional text hint.
  - `FHCRC` (bit 1): Header CRC16 (validated if present).
  - `FEXTRA` (bit 2): Extra fields (parsed and skipped).
  - `FNAME` (bit 3): Original filename string (zero-terminated).
  - `FCOMMENT` (bit 4): Comment string (zero-terminated).
- **Trailer Validation**:
  - `CRC32` (4 bytes little-endian): CRC-32 of the uncompressed data.
  - `ISIZE` (4 bytes little-endian): Size of the uncompressed input modulo $2^{32}$.

---

## 2. Monadic Specification & CLI State Machine

**Status** (corrected 2026-08-28): this section used to transcribe `GzipMode`, `GzipConfig` and
the three signatures below verbatim from the tree. That is Law 12's unlinked twin — a second
encoding of one fact, adding no information because it *was* the code — and it had already
drifted: the transcribed `gzipPipelineMonadic` carried a `[MonadFileSystem m]` constraint the
real definition has never had, and the prose described it as "parameterized over file system and
console effects". It is console effects only. The declarations are cited rather than copied now,
so that drift cannot recur.

The CLI's operating mode and configuration are `GzipMode` and `GzipConfig`
(`Spikes/Spike5Gzip/Spec.lean:34` and `:41`). `GzipMode` is a two-constructor enum,
`Compress`/`Decompress`, selected from CLI flags by `parseGzipFlags` (`:48`), which recognizes
`-d`, `--decompress`, `-dc` and `-cd`. `GzipConfig` carries the mode plus a `keepSource` flag and
a compression `level`. Both derive `DecidableEq`/`Repr`/`Inhabited` — that is what lets the
spike's equivalence theorems decide trace equality.

### 2.1 Pure Transformation Functions
The pure layer is `Stdlib.Zlib`'s, not the spike's: `gzipCompress : ByteArray → ByteArray`
(`Stdlib/Zlib/Gzip.lean:25`) and `gzipDecompress : ByteArray → Except String ByteArray` (`:102`).
Compression is total; decompression is fallible, and that `Except` is the whole error surface §3
disciplines. `gzipCompressStored` (`:61`) is a third entry point emitting stored (uncompressed)
DEFLATE blocks; it currently has no call site.

### 2.2 End-to-End Monadic Pipeline
`gzipPipelineMonadic` (`Spikes/Spike5Gzip/Spec.lean:67`) is parameterized over **console effects
only** — its constraints are `[Monad m] [MonadConsole m]`. It takes a `GzipMode` and an input
`ByteArray`, returns `m (Except String ByteArray)`, and emits a progress line through
`MonadConsole` on each branch. File I/O is not part of this pipeline: the targets feed it bytes
their own entry points have already read.

---

## 3. Linear Resource Discipline & Error Handling

1. **Stream Validation**: Fail-fast error propagation on corrupted GZIP headers, invalid compression methods, DEFLATE stream errors, or CRC32/ISIZE mismatches.
2. **Buffer Invariants**: Linear buffer memory allocation through `Stdlib.SmolAlloc` with explicit deallocation upon pipeline termination.
3. **Zero Resource Leaks**: All opened file handles or temporary stream buffers are guaranteed to be discharged along both success and error paths.

---

## 4. Dual-Target Architectural Realization

### 4.1 x86_64 Windows (`kernel32.dll`)
- PE32+ binary with `.idata` importing `GetStdHandle`, `ReadFile`, `WriteFile`, and `ExitProcess`.
- Command line argument parsing for `-d` / `--decompress` flag.
- Heap buffer allocation via `Stdlib.SmolAlloc.Windows`.

### 4.2 WebAssembly WASI (`wasi_snapshot_preview1`)
- WASI imports: `fd_read`, `fd_write`, `proc_exit`.
- Memory operations in WASM linear memory with `Stdlib.SmolAlloc.Wasm`.
- Byte-level stream decoding and verification in pure WebAssembly instructions.

---

## 5. Semantic Trace Equivalence & Verification Contract

The lowering theorems for both Windows x86_64 (`spike5_windows_gzip_trace_equivalence`,
`Spikes/Spike5Gzip/Equivalence.lean:70`) and WebAssembly (`spike5_wasm_gzip_trace_equivalence`,
`:84`) prove constructive trace equivalence between each target's lowering and the high-level
pure specification. Those two theorems are real, discharged constructively with zero `sorry`,
and exercised in the automated test suites.

**Status** (corrected 2026-08-28): this section previously displayed, as the specification those
lowerings are equivalent *to*, a block reading `theorem gzip_roundtrip_soundness (data :
ByteArray) : gzipDecompress (gzipCompress data) = .ok data`, described as "discharged
constructively with zero `sorry`". **That theorem has never existed in the tree.** Trace
equivalence between a lowering and a specification is a different claim from soundness of the
specification itself, and only the former is proved here. The universal GZIP-container roundtrip
is an open PA16 obligation (L9, itself downstream of L7's dynamic branch); what exists today is
`gzip_roundtrip_soundness_inst` — a `native_decide` check over one string literal — plus, at the
DEFLATE layer, the genuinely universal `emitFixedBlock_roundtrip_soundness` and the conditional
`compress_roundtrip_of_fixed_choice`. See `docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems`
and `docs/PA16_CODEC_SOUNDNESS.md` §9.
