---
id: N3
title: Real socket model (WinSock semantics vs invented hooks)
status: ready
blocked_on: ""
after: [N2]
related: []
bar: ""
track: networking
priority: 7.5
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# N3: Real socket model — replace invented hooks with harness-validated WinSock semantics

## Context

`TASKS.md`'s line for this task: "real socket model: replace invented hooks with harness-validated
WinSock semantics (blocking, WSA errors, graceful close); drop or legitimize WASI sock_* — after:
N2." This task depends on N2 (`OS1`) because N2 builds the handle table, error-code model, and the
differential-harness machinery this task reuses for sockets specifically — WinSock handles are
Win32 handles, `WSAGetLastError` follows the same `GetLastError` pattern N2 establishes, and the
harness architecture (native companion, `Except`-typed outcomes, control vectors) N2 builds is the
same one this task extends to blocking socket calls.

### C5 — sockets are wholly invented (quoting MODEL_DEBT verbatim)

`MODEL_DEBT.md` §C5, quoted in full:

> Sockets are wholly invented. `socket`→100, `accept`→101, `bind`/`listen`/`WSAStartup`→0
> (`Win32API.lean:146-182`); `recv` delivers an entire queued request in one call and never
> short-reads or blocks (lines 186-203); `send` always sends everything. No `WSAGetLastError`, no
> `WSAEWOULDBLOCK`, no graceful-close (`0`) vs `SOCKET_ERROR` (`-1`) distinction, no blocking
> semantics. `acceptHook` on an empty queue sets `rip := 0` to terminate the program (lines
> 176-178) — an invention with no Win32 counterpart. Nothing opens a real socket against an
> emitted binary (PLAN Phase 6 concurs).

Every one of these is grep-confirmed against `Gasm/Targets/Windows/Win32API.lean` at time of
writing:

- **`socketHook`** (`:152-156`) ignores every input register and unconditionally sets
  `RAX := 100`. Real `socket()` returns an OS-allocated descriptor and can fail
  (`INVALID_SOCKET`, `-1`, with a real `WSAGetLastError` code) if the address family/type/protocol
  combination is invalid or resources are exhausted — none of which this hook can express, because
  it never inspects its arguments.
- **`acceptHook`** (`:174-182`) is the most severe invention in the file: on an empty
  `incomingRequests` queue, it sets `rip := 0` (line 177) — **this is not a `SOCKET_ERROR` return,
  not a `WSAEWOULDBLOCK`, not a blocking wait; it is a direct manipulation of the instruction
  pointer that halts program execution outright**, with, in TASKS.md's and MODEL_DEBT's words, "no
  Win32 counterpart at all." A real blocking `accept()` call on a listening socket with no pending
  connection simply blocks the calling thread until a connection arrives or the socket is closed
  — it never terminates the calling program.
- **`recvHook`** (`:186-203`) delivers an entire queued request string in a single call
  (`bytes := req.toUTF8`, `count := bytes.size` at lines 194-195) and can never short-read (return
  fewer bytes than requested with more remaining) or block (wait when no data is queued at all —
  on an empty queue it returns `0`, which in real WinSock means "peer performed a graceful
  close," not "no data yet"). This conflates "nothing available, would block" with "connection
  closed" — two semantically opposite outcomes collapsed onto the same return value.
- **`sendHook`** (`:207-213`) always sends the full requested length (`s'.rax := len.toUInt64` at
  line 212) — no partial send, no `SOCKET_ERROR`, no backpressure.
- **`bindHook`**, **`listenHook`**, **`wsaStartupHook`** (`:146-149`, `:160-163`, `:167-170`)
  ignore their inputs entirely and unconditionally return `0` (success) — no invalid-address,
  already-bound, or already-listening failure paths.
- No `WSAGetLastError` exists anywhere in the file; no hook ever returns `SOCKET_ERROR` (`-1`); no
  code path distinguishes "peer closed gracefully" (`recv` returns `0`) from "socket error"
  (`recv` returns `-1` + a `WSAGetLastError` code) from "would block" (`WSAEWOULDBLOCK` under
  non-blocking mode).

**This task's core deliverable is to replace every one of these with harness-validated real
WinSock semantics** — blocking behavior, the full success/graceful-close/error three-way
distinction on `recv`, real `WSAGetLastError` codes, and short reads/writes on sockets exactly as
N2 closed the equivalent gap for `ReadFile`/`WriteFile`.

### The parallel invention on the Wasm/WASI side — C8, and why this is a "drop or legitimize" decision

`TASKS.md`'s line names a second, independent action for this task: "drop or legitimize WASI
sock_*". This refers to `MODEL_DEBT.md` §C8, quoted (the relevant clause):

> WASI: `errno` is always 0, and `sock_*` are non-existent syscalls. ... `sock_listen/accept/
> recv/send/close` (lines 129-171) are **not WASI preview1 functions with these signatures** —
> preview1 has no `sock_listen`, and its `sock_recv`/`sock_send` are iovec-based and
> errno-returning.

Grep-confirmed directly against `Gasm/Targets/WASI/ABI.lean`: `sock_listen` (`:129-132`),
`sock_accept` (`:134-141`), `sock_recv` (`:143-157`), `sock_send` (`:159-166`), `sock_close`
(`:168-171`) exist as host-call dispatch arms taking flat `i32` arguments and returning a single
`i32` (a socket descriptor, or a byte count) directly on the value stack — mirroring the Win32
Winsock hooks' calling convention, not WASI's. Real WASI preview1 (per
`references/wasi/preview1.md`, already vendored per C8's note that "this debt is
ingestion-ready") has **no `sock_listen` at all**, and its actual socket-adjacent functions
(`sock_recv`/`sock_send`, where they exist in preview1 extensions) are iovec-based (they take a
pointer to a vector of `{ptr, len}` buffer descriptors, matching `fd_read`/`fd_write`'s existing
iovec convention in this same file) and return a WASI `errno` value rather than an ad-hoc
sentinel. Concretely, `sock_recv` here (`:143-157`) pops three flat `i32`s (`_sock`, `buf_ptr`,
`max_len`) and returns a byte count directly, matching neither preview1's real signature nor its
error-reporting convention (`fd_read`'s own hook in this file, at `:79+`, does follow the correct
`errno`-returning iovec convention — `sock_*` breaks with the very pattern the file establishes
two functions earlier). This means any Wasm module compiled to import these `sock_*` names is
importing symbols that **do not exist in any real WASI implementation** — no production Wasm
runtime (Wasmtime, WasmEdge, Node's experimental WASI, wasmtime-py) can load and run such a module,
so the host-oracle differential validation this project relies on for every other Wasm surface
(`docs/VISION.md` §3.2 — "Wasm semantics vs. production engines") structurally cannot validate
these five functions; they have been running exclusively against gasm's own interpreter.

Craig's framing (from the assignment context, worth stating explicitly in this task): this is "the
same invented-import-surface defect class `GRAPHICS_PREBUILD_AUDIT.md` separately flags for a
fabricated Wasm+Vulkan target" — i.e. this is not a one-off Windows-side bug, it is a recurring
failure mode of inventing a plausible-looking foreign-API surface without checking it against the
real spec, and it recurs on the Wasm target independently of the Windows socket work. This task
must choose one of two outcomes for `sock_*`, not default silently to the current state:

1. **Legitimize**: redefine the surface as genuine, iovec-based, errno-returning functions
   matching either real WASI preview1 (if such functions exist there) or a documented,
   Law-4-ingested non-preview1 extension (e.g. WASI-sockets / `wasi-sockets` proposal, if the
   project chooses to target it) — with the choice and its justification written into
   `docs/TARGETS/WASI.md`.
2. **Drop**: remove `sock_*` from `Gasm/Targets/WASI/ABI.lean` entirely, and either demote or
   redesign Spike4's Wasm variant (`Spikes/Spike4HttpServer/Wasm/`) so it does not depend on a
   fictional import surface — deferring Wasm-side networking to whatever real mechanism WASI
   preview1/preview2 actually offers, on spike demand (Law 5/D7), rather than inventing one now.

### Governing laws

`docs/REVIEW.md` Law 5 (stop-and-design — new socket-model surface), Law 9 (read-binder mandate —
`recv` is exactly a `read` in Law 9's sense: "every monadic input operation... `recv`... binds an
arbitrary result... proven correct for any returned `ByteArray`... including partial reads, empty
reads, and EOF" — the current `recvHook`'s single-shot delivery is precisely the kind of
maximal-read shape Law 9 prohibits proving anything meaningful against), Law 13(4) (control-vector
discipline, reused from N1/N2's harness architecture). `docs/VISION.md` §3.2 (differential
validation against the real OS) and §1 (web/gRPC servers class: "threading and async I/O;
protocol causality" — this task is the socket-semantics foundation that class needs).

## Deliverables & acceptance criteria

- **Blocking `accept`/`recv`/`send` exercised against a real WinSock server/client pair** via the
  harness N1 scoped and N2 built out — extended here to sockets specifically. This directly
  replaces `acceptHook`'s empty-queue `rip := 0` termination with harness-measured real blocking
  behavior (or, if the model chooses to represent blocking as a documented approximation rather
  than true OS-thread blocking, that choice must be stated and justified against what the harness
  actually measured — not silently reintroduced as an invention).
- **The three-way `recv` distinction restored**: success-with-data, graceful-close (`0` bytes,
  peer closed), and error (`SOCKET_ERROR` / `-1` + a real `WSAGetLastError` code) must be three
  observably distinct outcomes, matching real WinSock — not collapsed as they are today.
- **Short reads/writes on sockets**: `recv` must be able to return fewer bytes than requested with
  more data pending (the same class of fix N2 delivers for `ReadFile`, applied to sockets); `send`
  must be able to partially send.
- **Real `WSAGetLastError` codes** for the socket-specific failure modes current and near-term
  spikes need (at minimum: `WSAEWOULDBLOCK`, connection-reset, invalid-socket) — scoped per
  Law 5/D7 to demonstrated need, following N1's precedent for scoping C3.
- **`socket`/`bind`/`listen`/`WSAStartup` given real failure paths** where a differential harness
  run can actually produce one (e.g. `bind` to an already-bound address, `listen` on an unbound
  socket) — not merely documented as theoretically possible.
- **The WASI `sock_*` decision, made explicitly and recorded**: either (a) legitimized as a real,
  iovec-based, errno-returning surface matching a named real spec (preview1 or a documented
  extension), with `docs/TARGETS/WASI.md` updated accordingly and Spike4's Wasm variant updated to
  match the corrected ABI; or (b) dropped from `Gasm/Targets/WASI/ABI.lean` entirely, with
  Spike4's Wasm dependency on it resolved (demoted, redesigned, or deferred) rather than left
  silently broken. Whichever path is chosen, it must be justified in the consolidated design doc
  against `references/wasi/preview1.md` (already vendored) — not asserted without checking the
  reference.
- **Harness-validated, per Law 13(4)**: mandatory positive control (a known-good
  `socket`/`bind`/`listen`/`accept`/`recv`/`send`/`closesocket` sequence against a real loopback
  TCP connection, shown to succeed with the expected byte counts) and negative control (a
  deliberately invalid call — e.g. `recv` on a closed socket, `bind` to an in-use port — shown to
  be rejected with the correct WinSock error) before any differential comparison result counts,
  following `HardwareHarness.lean`'s pattern (`:281` `Except`-typed batch runner, `:309-340`
  control-pair-before-any-result-counts). `Except`-typed outcomes throughout — a harness that
  cannot open a real socket (no network stack, firewall block) must fail the run, never no-op.
- Since this is new model/contract surface replacing wholesale invention, it is Law-5-class:
  `status` should progress `ready → designing → design-review → implementing → done`, and a
  fresh-agent design review is required before implementation dispatch — not waived. The
  consolidated design should extend `docs/TARGETS/WINDOWS.md` (WinSock section) and
  `docs/TARGETS/WASI.md` (the `sock_*` decision).

## Pointers

- `Gasm/Targets/Windows/Win32API.lean:146-149` (`wsaStartupHook` — returns 0 unconditionally),
  `:152-156` (`socketHook` — constant 100), `:159-163` (`bindHook` — constant 0), `:166-170`
  (`listenHook` — constant 0), `:174-182` (`acceptHook` — the `rip := 0` invention at line 177),
  `:186-203` (`recvHook` — single-shot delivery, no short-read/block, `0` on empty queue conflates
  "would block" with "graceful close"), `:207-213` (`sendHook` — always full length), `:217-221`
  (`closesocketHook`), `:224-228` (`wsaCleanupHook`).
- `Gasm/Targets/WASI/ABI.lean:129-132` (`sock_listen`), `:134-141` (`sock_accept`), `:143-157`
  (`sock_recv` — flat i32 args/return, not iovec-based), `:159-166` (`sock_send`), `:168-171`
  (`sock_close`); compare against `:79+` (`fd_read` — the correct iovec/errno-returning WASI
  convention this file establishes and then breaks for `sock_*`) and `references/wasi/preview1.md`
  (vendored — the ground truth to check the legitimize/drop decision against).
- `docs/tasks/N2-os1-readfile-writefile-model.md` — the direct prerequisite; this task reuses
  N2's handle table, error-code model, and harness architecture for sockets.
- `MODEL_DEBT.md` §C5 (sockets wholly invented — quoted in full above) and §C8 (WASI errno/sock_*
  — quoted above), TOP-10 table (C5/C8 are part of the OS-gap class items 1 and 8 name).
- `GRAPHICS_PREBUILD_AUDIT.md` — the sibling finding for the fabricated Wasm+Vulkan target; cite
  as the same invented-import-surface defect class recurring on a different target.
- `PLAN.md` Phase 6 "Spike repair & next spikes" — "Spike4: no test opens a real socket against
  the emitted binaries. Add end-to-end exercise (and for Wasm, note sock_* imports are invented
  non-WASI extensions)" — the concrete gap this task and N4 jointly close.
- `Gasm/Targets/X86_64/HardwareHarness.lean:281`, `:309-340` — the control-vector architecture to
  reuse (see N2's Pointers section for the same citation with fuller context).
- `docs/VISION.md` §1 (web/gRPC servers class — protocol causality), §3.2 (differential validation
  mandate).
- `docs/REVIEW.md` Law 5, Law 9 (read-binder — `recv` is a `read`), Law 13(4).

## Notes

- 2026-08-27: priority 7.5 — real socket model is the next load-bearing step in the owner's explicitly-prioritized networking buildout, after N2 lands the OS-level read/write model it depends on.

_(none yet — first entries append here as work begins; this is Law-5-class networking-model work
— consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch.)_
