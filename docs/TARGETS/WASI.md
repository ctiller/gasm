# WASI Snapshot Preview 1 Specification & ABI Contracts

This document defines the WASI (WebAssembly System Interface) Snapshot Preview 1 ABI contracts, system call signatures, memory layouts, and capability conventions used in `gasm`.

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
