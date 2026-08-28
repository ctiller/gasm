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

```lean
inductive GzipMode where
  | Compress
  | Decompress
  deriving DecidableEq, Repr, Inhabited

structure GzipConfig where
  mode       : GzipMode := .Compress
  keepSource : Bool     := true
  level      : Nat      := 6
  deriving DecidableEq, Repr, Inhabited
```

### 2.1 Pure Transformation Functions
```lean
def gzipCompress (input : ByteArray) : ByteArray
def gzipDecompress (input : ByteArray) : Except String ByteArray
```

### 2.2 End-to-End Monadic Pipeline
Parameterized over file system and console effects (`MonadFileSystem`, `MonadConsole`):
```lean
def gzipPipelineMonadic (m : Type → Type) [Monad m] [MonadFileSystem m] [MonadConsole m]
    (mode : GzipMode) (input : ByteArray) : m (Except String ByteArray)
```

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
