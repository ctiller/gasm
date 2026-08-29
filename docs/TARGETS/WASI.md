# WASI Snapshot Preview 1 Specification & ABI Contracts

This document defines the WASI (WebAssembly System Interface) Snapshot Preview 1 ABI contracts, system call signatures, memory layouts, and capability conventions used in `gasm`.

WASI host calls and Wasm execution semantics are one realization of the abstract placements in
[Composable Boundary ABI Contexts](../ABI_CONTEXT.md). Library requirements remain independent of
WASI: a realization may provide them through explicit parameters or typed capability/import-table
slots, and must model finite memory growth and its explicit failure outcome.

---

## 1. WASI Snapshot Preview 1 Architecture

WASI Snapshot Preview 1 provides POSIX-like system calls as host WebAssembly imports under the module name `"wasi_snapshot_preview1"`.

All WASI functions return an `errno` value (`i32`) where `0` indicates success (`__WASI_ERRNO_SUCCESS`).

---

## 2. Syscall Signatures

### 2.1 `fd_write`
Writes data to a file descriptor from an array of I/O vectors.

- **Import Name**: `"wasi_snapshot_preview1"."fd_write"`
- **Signature**: `(param i32 i32 i32 i32) (result i32)`
- **Parameters**:
  1. `fd : i32`: The file descriptor (e.g. `1` for stdout, `2` for stderr).
  2. `iovs_ptr : i32`: Memory offset of array of `__wasi_ciovec_t` structures.
  3. `iovs_len : i32`: Number of `__wasi_ciovec_t` structures in array.
  4. `nwritten_ptr : i32`: Memory offset where the number of bytes written (`i32`) will be stored.
- **Return**: `errno : i32` (0 on success).

### 2.2 `proc_exit`
Terminates the execution of the process.

- **Import Name**: `"wasi_snapshot_preview1"."proc_exit"`
- **Signature**: `(param i32)`
- **Parameters**:
  1. `rval : i32`: The exit code returned by the process.
- **Return**: None (noreturn / trap execution).

### 2.3 The `sock_*` calls Spike 4 imports are **self-authored, not WASI Preview 1**

**Status** (added 2026-08-28): §2.1 and §2.2 above are the *only* two calls this document
describes from the real specification, and they are the only two `gasm` uses that WASI Preview 1
actually defines. `Spikes/Spike4HttpServer/Wasm/Program.lean` imports **five further functions —
`sock_listen`, `sock_accept`, `sock_recv`, `sock_send`, `sock_close` — from the module name
`"wasi_snapshot_preview1"`, and this repository invented all five.** They are recorded here
because seven `REF:` citations in that file point at §2 for exactly these declarations
(`sockListenType` and its siblings, `Wasm/Program.lean:50`–`:68`), and until this subsection
existed those citations resolved to a section that did not mention them. `check_refs.py`
validated the anchor and passed; the anchor existed, the justification did not.

What is actually true of the five, checked against the Preview 1 API:

| Import | In WASI Preview 1? | This repository's version |
| :-- | :-- | :-- |
| `sock_listen` | **No.** Not in Preview 1 in any form; listening sockets are outside its capability model, which can only *accept* on a pre-opened descriptor supplied by the host | `(param i32) (result i32)` — takes a port and returns a descriptor |
| `sock_accept` | Name exists in later Preview 1 revisions | **Signature differs.** The real call is `(fd, flags, result_ptr) -> errno`; this one is `(param i32) (result i32)`, returning the descriptor directly |
| `sock_recv` | Name exists | **Signature differs.** The real call takes an `iovec` array and writes flags and a byte count through out-pointers; this one is `(param i32 i32 i32) (result i32)` over a flat buffer |
| `sock_send` | Name exists | **Signature differs**, in the same way as `sock_recv` |
| `sock_close` | **No.** Preview 1 closes descriptors with `fd_close` | `(param i32) (result i32)` |

**This is a Law 4 departure and is recorded as one.** Law 4 forbids authoring ad-hoc
approximations of external specifications; five invented imports presented under the real
module name are exactly that. The invention is nonetheless load-bearing for the spike, so it is
disclosed rather than hidden: Spike 4's Wasm target is a *dual-target lowering exercise against a
socket model this project defined*, not a program that runs on a conforming WASI runtime.
`spike4_http.wasm` will fail to instantiate on any host that implements Preview 1 as specified,
because four of its six imports do not exist there and the fifth has a different type.

**What this does and does not cost the spike's results.** It does not weaken the trace-equivalence
theorems in `Spikes/Spike4HttpServer/Equivalence.lean`: those relate the lowering to
`Spec.lean`'s model, and both sides use this same socket vocabulary consistently, so the
equivalence is a real statement about a real pair of artifacts. What it costs is the *external*
claim — the theorems say nothing about behaviour under a conforming runtime, and no result here
transfers to one. Read
`docs/SPIKES/SPIKE4_HTTP_SERVER.md#4-semantic-trace-equivalence-verifiedprogram-contract`
for the parallel limitation on the theorems' domain.

**The honest routes out**, neither taken here: vendor an authoritative socket specification that
these signatures can cite (WASIX or `wasi-sockets`/Preview 2 define real listening-socket APIs,
and Law 4 wants the text imported, not paraphrased), or rename the imports to a module name this
project owns so they stop claiming to be `wasi_snapshot_preview1`. The second is cheap and
removes the false claim without needing a vendored corpus. Either is a change to
`Spikes/Spike4HttpServer/Wasm/Program.lean` and belongs to that spike's owner, not to this
document.

---

## 3. Data Structures & Memory Layout

### 3.1 `__wasi_ciovec_t` Structure
Represents a contiguous scatter/gather I/O buffer:

| Field | Type | Offset | Size | Description |
| :--- | :--- | :--- | :--- | :--- |
| `buf` | `i32` (`*const u8`) | +0 | 4 bytes | Linear memory pointer to the byte buffer. |
| `buf_len` | `i32` (`size_t`) | +4 | 4 bytes | Length of the byte buffer in bytes. |

Total size: **8 bytes**, aligned to 4 bytes.

---

## 4. Standard Error Codes (`__wasi_errno_t`)

| Name | Value | Description |
| :--- | :--- | :--- |
| `SUCCESS` | 0 | No error occurred. |
| `EBADF` | 8 | Bad file descriptor. |
| `EFAULT` | 21 | Bad address in linear memory. |
| `EINVAL` | 28 | Invalid argument. |
| `EIO` | 29 | Input/output error. |
