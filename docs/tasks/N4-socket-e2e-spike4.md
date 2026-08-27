---
id: N4
title: End-to-end socket exercise of Spike4 binaries
status: ready
blocked_on: ""
after: [N3]
related: []
bar: ""
track: networking
priority: 7.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# N4: End-to-end socket exercise of Spike4 binaries

## Context

`TASKS.md`'s line for this task: "end-to-end socket exercise of Spike4 binaries — after: N3." This
task closes a gap `PLAN.md` states plainly in its Phase 6 "Spike repair & next spikes" section:

> Spike4: no test opens a real socket against the emitted binaries. Add end-to-end exercise (and
> for Wasm, note sock_* imports are invented non-WASI extensions).

This is verified directly by reading `Spikes/Spike4HttpServer/Test.lean` in full: the CLI does
four things — (1) emits the Windows PE32+ binary via `emitVerifiedExecutable` and writes it to
disk (`spike4_http.exe`), (2) emits the Wasm binary/WAT text via `emitVerifiedWasmBinary`/
`emitVerifiedWasmText` and writes both to disk, (3) checks in-Lean trace equality
(`windowsTraceRoot == modelTraceRoot`, etc. — three routes, all compared against
`Spikes.Spike4HttpServer.Equivalence`'s pre-computed traces), and (4) calls `handleRawRequest`
directly in-process against three hardcoded request strings (`rootReq`, `statusReq`,
`notFoundReq`) and string-compares the result to `formatResponse (routeRequest ...)`. **At no
point does the test open a socket, start either emitted binary as a running process, connect to
it over TCP/localhost, or send bytes across a real OS network stack to it.** The `.exe` and
`.wasm` files are written to disk and never executed. Everything that looks like "the server
responding to a request" is actually pure in-Lean function application
(`handleRawRequest`/`routeRequest`) — the emitted binaries' actual behavior when run as OS
processes accepting real connections is completely unexercised.

This matters because it is exactly the gap N3's real socket model creates the *possibility* of
closing: N3 replaces `acceptHook`/`recvHook`/`sendHook`'s inventions with harness-validated real
WinSock semantics, but N3's scope is the *model* (what a hook does when the interceptor fires
inside gasm's own execution engine). N4 is the separate, necessary step of proving the **emitted
artifact itself**, run as a standalone OS process under a real socket stack, behaves the way the
model says it should — end-to-end, PE-on-disk to TCP-connection-in, response-out. Without N4, N3's
model correctness says nothing about whether `spike4_http.exe` run by `cmd.exe` and connected to
via a real client socket actually serves an HTTP response.

### Governing laws

`docs/REVIEW.md` Law 9 (the socket-facing side of the anti-pointwise law: three hardcoded request
strings compared to three hardcoded expected outputs is a pointwise/domain-shrinking check in
the same family Law 9 prohibits for `VerifiedProgram` contracts — even though this task's
deliverable is a test-infrastructure exercise rather than a proof, the same anti-pointwise
discipline should shape how many/what kind of real requests the end-to-end exercise sends,
rather than settling for one more hardcoded triple at the process boundary instead of the
function boundary). Law 13(4) (control-vector discipline — this is exactly the "harness that
interacts with the world" class: a real running process and a real socket connection to it).
`docs/VISION.md` §1 (web/gRPC servers: "threading and async I/O; protocol causality") and §3.2
(differential validation — this is validation of the *emitted artifact*, distinct from and
complementary to N3's validation of the *model*).

## Deliverables & acceptance criteria

- **A real end-to-end test harness**: launch `spike4_http.exe` (Windows target) as an actual child
  process, open a real TCP socket connection to it on the port it listens on, send real HTTP/1.1
  request bytes over that socket, read the real response bytes back, and compare against the
  expected response — replacing the current in-process `handleRawRequest` call with an actual
  client/server exchange across a real OS socket.
- **The same for the Wasm target**, run under whatever Wasm host/runtime Spike4's Wasm variant
  targets (per N3's resolution of the WASI `sock_*` legitimize-or-drop decision — if `sock_*` was
  dropped rather than legitimized, this deliverable's Wasm half is scoped to whatever real
  networking mechanism replaced it, and that scoping must be stated explicitly rather than
  silently skipped).
- **Coverage across the three existing routes** (`/`, `/status`, `/unknown` → 404) at minimum,
  exercised as real requests over the real socket connection — not reduced back to a single
  hardcoded vector at the process boundary (Law 9's anti-pointwise spirit, applied to test
  design even though this is not itself a proof obligation).
- **At least one exercise of a request arriving in multiple TCP segments** (a request split across
  two or more `send()` calls on the client side, or throttled to force the server's `recv()` to be
  called more than once) — this is the concrete, artifact-level analogue of C1/N2's short-read
  closure and N3's short-recv closure; an end-to-end exercise that only ever sends one
  single-`recv()`-sized request would not actually test what N2/N3 built.
- **Positive and negative control vectors (Law 13(4))**: a known-good request/response pair
  proven to round-trip correctly over the real socket, and a deliberately malformed or oversized
  request proven to be handled (rejected or correctly error-responded, not silently hung or
  crashed) — before the exercise's results are trusted as validating anything. `Except`-typed
  outcomes: if the child process fails to start, the port is unavailable, or the socket connection
  cannot be established, the run must fail loudly, never silently skip the exercise and report
  success.
- **Process lifecycle handled correctly**: the child process must be reliably terminated at the
  end of the test run (no orphaned listening processes across test runs — a known failure mode
  in this codebase's other harnesses per `TCB.md`'s findings about temp-file/process cleanup in
  sibling fuzzers).
- Since this is genuinely new verification-exercise surface (proving an emitted binary's real
  process/socket behavior for the first time, not merely a mechanical test addition), it warrants
  a real design review before implementation rather than being waived as mechanical — state this
  reasoning explicitly rather than defaulting either way: it is Law-5-adjacent because it is
  establishing the pattern (process launch + real socket harness) that N5's reverification and any
  future networked spike will reuse, so getting its control-vector discipline and lifecycle
  handling right the first time is worth a fresh-agent look before code, per the same
  cheaper-before-code logic the graphics pre-build audit demonstrated. `status` should progress
  `ready → designing → design-review → implementing → done`.

## Pointers

- `Spikes/Spike4HttpServer/Test.lean` (full file, 92 lines) — the current test entry point;
  sections [1/4]/[2/4] emit the binaries to disk and never run them; section [3/4] compares
  pre-computed in-Lean traces; section [4/4] calls `handleRawRequest` in-process on three
  hardcoded strings (`rootReq`/`statusReq`/`notFoundReq`, lines 60-62) — this is the exact
  pointwise, no-real-socket gap this task closes.
  `Spikes/Spike4HttpServer/Windows/Emit.lean`, `Windows/Program.lean` — the Windows binary this
  task must launch as a real process.
  `Spikes/Spike4HttpServer/Wasm/Emit.lean`, `Wasm/Program.lean` — the Wasm binary this task must
  run under a real host.
- `docs/tasks/N3-real-socket-model.md` — the direct prerequisite; this task's harness exercises
  the socket semantics N3 fixes, and depends on N3's resolution of the WASI `sock_*` question for
  its Wasm half.
- `PLAN.md` Phase 6 "Spike repair & next spikes" — "Spike4: no test opens a real socket against
  the emitted binaries" (quoted above) — the exact gap this task's title names.
- `Gasm/Targets/X86_64/HardwareHarness.lean:281`, `:309-340` — the control-vector architecture
  (`Except`-typed outcomes, mandatory positive+negative controls before any result counts) this
  task's process/socket harness should follow the same discipline as.
- `docs/VISION.md` §1 (web/gRPC servers class), §3.2 (differential validation of the emitted
  artifact, distinct from model validation).
- `docs/REVIEW.md` Law 9 (anti-pointwise spirit applied to test design), Law 13(4) (control-vector
  discipline).

## Notes

- 2026-08-27: priority 7.0 — end-to-end socket exercise of Spike4 is the first real differential validation of the socket model N3 builds.

_(none yet — first entries append here as work begins; this is Law-5-class networking-model work
— consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch.)_
