---
id: N8
title: Fix Spike 4 HTTP Server stack buffer overflow and uninitialized memory read
status: ready
blocked_on: ""
after: [N3]
related: [N4, N5]
bar: ""
track: networking
priority: 8.5
priority_set: 2026-08-28T00:06:33Z
design: inline
design_review: waived-mechanical
date: 2026-08-28
---

# N8: Fix Spike 4 HTTP Server stack buffer overflow and uninitialized memory read

## Context

Sourced from the 2026-08-28 comprehensive codebase security audit.
An adversarial inspection of `Spikes/Spike4HttpServer/Windows/Program.lean` uncovered three concrete memory safety and protocol parsing defects in the lowered x86-64 assembly implementation that are currently masked by pointwise equivalence proofs:

1. **Stack Buffer Overflow into WSADATA**:
   In `spike4SymbolicProgram` (`Spikes/Spike4HttpServer/Windows/Program.lean:80-90`), the stack layout allocates a 520-byte stack frame:
   - `[RSP + 0x00..0x1F]` : shadow space (32 bytes)
   - `[RSP + 0x20..0x27]` : server socket descriptor (8 bytes)
   - `[RSP + 0x28..0x2F]` : client socket descriptor (8 bytes)
   - `[RSP + 0x30..0x3F]` : `sockaddr_in` buffer (16 bytes)
   - `[RSP + 0x40..0x4F]` : HTTP request recv buffer (**16 bytes allocated**)
   - `[RSP + 0x50..0x1E8]` : WSADATA buffer (408 bytes)
   
   However, step 8 (`lines 130-136`) invokes `recv`:
   ```lean
   instr (mov_reg64_mem64_disp .rcx .rsp 0x28),
   instr (lea_rsp .rdx 0x40),
   instr (mov_r32 .r8d 128),
   instr (xor_r32 .r9d .r9d),
   call_import "recv",
   ```
   Passing `len = 128` to `recv` with destination buffer `RSP + 0x40` allows up to 128 bytes to be written into a 16-byte slot. Any standard HTTP request (even the canonical sample `GET / HTTP/1.1\r\nHost: localhost\r\n\r\n`, which is 37 bytes) overflows the 16-byte buffer and overwrites `RSP + 0x50` through `RSP + 0x65`, directly corrupting the stack memory reserved for `WSADATA`.

2. **Uninitialized Memory Read on Short Reads / EOF**:
   In step 9 (`lines 137-145`), immediately following `recv`:
   ```lean
   instr (lea_rsp .rsi (0x40 + 4)),
   instr (mov_reg64_mem64_disp .rax .rsi 0),
   instr (mov_r64_imm64 .rdx 0xFFFFFFFFFF),
   instr (and_r64 .rax .rdx),
   instr (mov_r64_imm64 .rcx 0x746174732F), -- "/stat"
   instr (cmp_r64 .rax .rcx),
   je_label "send_status",
   ```
   The program unconditionally loads 8 bytes from `RSP + 0x44` without inspecting the return value of `recv` (`RAX`). If `recv` returned fewer than 5 bytes, returned 0 (client closed socket gracefully), or returned -1 (`SOCKET_ERROR`), `spike4SymbolicProgram` executes branch comparisons against uninitialized stack bytes and proceeds to call `send` rather than closing the connection or handling the error.

3. **Prefix Route Truncation**:
   The check for `/status` masks 5 bytes (`0xFFFFFFFFFF`) and tests against `0x746174732F` (`"/stat"`), omitting the final `"us"`. Any request path prefixed with `/stat` (e.g., `GET /static`, `GET /status_check`) erroneously matches and serves the 200 OK Status response.

### Why this evaded detection
The equivalence theorem in `Spikes/Spike4HttpServer/Equivalence.lean` evaluates `spike4_windows_root_trace_equivalence` using `native_decide` against the single pre-packaged input `["GET / HTTP/1.1\r\nHost: localhost\r\n\r\n"]`. In the simulated machine environment of `Win32API.lean`:
- `recvHook` writes exactly the pre-configured string without faulting on stack boundaries.
- `WSADATA` is never read after `WSAStartup`.
Therefore, the stack overflow and short-read bugs are completely invisible to the in-Lean evaluator, but constitute immediate memory safety and crash vulnerabilities on real Windows hardware.

## Deliverables & acceptance criteria

- **Stack Layout Resize**: Expand the stack allocation for the recv buffer in `spike4SymbolicProgram` to at least 256 bytes, adjusting stack frame offsets and frame sizing so `RSP` remains 16-byte aligned and `WSADATA` is not corrupted.
- **Recv Length Validation**: Check `RAX` after `recv`. If `RAX <= 0` (error or EOF), branch to connection teardown (`closesocket` + loop back to `accept`), avoiding uninitialized memory reads.
- **Full Path Verification**: Update route comparison logic to verify the full 7-character string `"/status"` rather than truncating at 5 characters `"/stat"`.
- **Negative Control & Differential Test**: Add a test in `Spikes/Spike4HttpServer/Test.lean` that submits requests of variable sizes (e.g. 1 byte, 15 bytes, 37 bytes, 120 bytes) to demonstrate that the buffer overflow and uninitialized memory read conditions do not crash or corrupt stack state.
- `lake build` and `scripts/run_gates.py --quick` pass cleanly.

## Pointers

- `Spikes/Spike4HttpServer/Windows/Program.lean:80-160` (stack frame allocation and `recv` call).
- `Spikes/Spike4HttpServer/Equivalence.lean:65-75` (pointwise trace definitions).
- `docs/tasks/N3-real-socket-model.md` and `docs/tasks/N4-socket-e2e-spike4.md` (sibling socket tasks).
- `MODEL_DEBT.md` §B3 (memory model lack of faulting).

## Notes

- 2026-08-28: Task created following comprehensive codebase security audit finding stack buffer overflow at `Spikes/Spike4HttpServer/Windows/Program.lean:133`.
