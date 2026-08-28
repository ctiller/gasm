---
id: N2
title: "OS1: ReadFile/WriteFile/handle model rebuild vs real OS"
status: ready
blocked_on: ""
after: [N1]
related: []
bar: ""
track: networking
priority: 9.3
priority_set: 2026-08-28T02:00:00Z
design: ""
design_review: ""
date: 2026-08-27
---

# N2: OS1 — ReadFile/WriteFile/handle model rebuild vs real OS

**Alias note:** `TASKS.md` names this task `N2` and annotates it `*(alias OS1 — referenced by
PA5/PA6)*`. Every other task and doc in this project that says "OS1" — including
`PLAN.md` Phase 4's `read`-as-binder item, and `TASKS.md`'s own `PA5` line ("needs OS1 (short
reads) for the input-event model") and `PA6` line ("after: PA5, OS1") — means **this task**.
There is no separate OS1 file; this is it. A fresh agent picking up PA5 or PA6 and looking for
"OS1" should land here.

## Context

This task is where `N1`'s Win32 differential harness design gets **implemented**: the harness
architecture N1 specifies (native companion invoking real `ReadFile`/`WriteFile`/`VirtualAlloc`
under controlled conditions, `Except`-typed outcomes, mandatory positive+negative controls) is
built for real, and the fix it enables lands in `Gasm/Targets/Windows/Win32API.lean`.

### Why this is "the single most load-bearing OS gap" — quoting MODEL_DEBT verbatim

`MODEL_DEBT.md` §C1 states the reasoning this task exists to resolve, in its own words:

> Given "`read` as the universal binder" (Law 9 / PLAN Phase 4), this is the single most
> load-bearing OS gap: a `∀ read-result` contract proven against a model that can only produce
> maximal reads proves nothing about chunk-robustness. **The Win32 differential harness must pin
> this first.**

`docs/REVIEW.md` Law 9 is the enforcement mechanism this unblocks: "every monadic input operation
in a specification (`readFile`, `recv`, `accept`, console reads — all forms of `read`) binds an
arbitrary result, and the verification contract MUST be parametric in that result: the
continuation after a read is proven correct for **any** returned `ByteArray`... Contracts that
pin a read's result to a concrete vector are unrepresentable as verified." Today's `readFileHook`
(`Gasm/Targets/Windows/Win32API.lean:85-104`) cannot even produce the inputs such a proof would
need to quantify over: it computes `count := min maxLen avail` (line 90) and unconditionally sets
`RAX := 1` (success) at line 94. The handle value in `RCX` is never read anywhere in the hook body
— there is no branch on handle type at all. Structurally, this hook can only express "return
everything requested or everything available, and always succeed." It cannot express: a pipe
delivering 7 bytes when 4096 were requested with more data arriving later; console line-buffered
reads (one line per call, CRLF, Ctrl-Z EOF); or a broken pipe (`FALSE` return +
`ERROR_BROKEN_PIPE`). Any Phase-4 contract of the shape "∀ read-result, prove X" proven against
this hook is vacuously true for every read-result the hook can actually produce, which is exactly
one shape (maximal, successful) — the theorem says nothing about chunk-robustness because
chunk-robustness was never exercised.

### C2 — WriteFile short-writes and the stdout/stderr collapse

`MODEL_DEBT.md` §C2, quoted: "`WriteFile` never short-writes, and ignores the handle.
`writeFileHook` (`Win32API.lean:108-122`) always writes all `R8` bytes, always succeeds, and
always emits `ConsoleEvent.out` — so **stdout and stderr are indistinguishable**, which also
breaks the two-stream observation algebra `SYSTEM_EFFECTS.md` §6.1 depends on. Compounding this,
`getStdHandleHook` (`Win32API.lean:75-79`) returns handle `1` for *both* `STD_INPUT_HANDLE` and
`STD_OUTPUT_HANDLE`. There is no handle table and no lifecycle." Grep-confirmed directly:
`getStdHandleHook` (`:74-81`) maps `0xFFFFFFF6` (STD_INPUT, -10) and `0xFFFFFFF5` (STD_OUTPUT,
-11) both to handle `1`; only `0xFFFFFFF4` (STD_ERROR, -12) gets `2`. `writeFileHook`
unconditionally emits `Inject.inject (ConsoleEvent.out text)` (line 122) regardless of which
handle was used to call it — there is no code path that could ever produce `ConsoleEvent.err`.
`docs/SYSTEM_EFFECTS.md` §6.1's coalescing table treats `ConsoleEvent.out`/`.err` as two distinct
streams with independent concatenation congruence; with only one handle value and one event
constructor reachable, that distinction is currently unrealizable by any program this target can
emit.

### C4 — VirtualAlloc is a constant

`MODEL_DEBT.md` §C4: "`VirtualAlloc` is a constant. `virtualAllocHook` (`Win32API.lean:132-135`)
returns `0x20000000` regardless of size, address, or protection flags — **two allocations return
the same pointer**. `virtualFreeHook` always returns 1 and tracks nothing.
`Zlib/Windows.lean`'s fixed 8 MB/8 MB split rests on this." Grep-confirmed: `virtualAllocHook`
(`:132-135`) ignores every input register and sets `RAX := 0x20000000` unconditionally;
`virtualFreeHook` (`:138-142`) ignores its inputs and always returns 1. A real allocator must
track live regions, return distinct addresses per call, and respect protection flags — none of
which the current hook can represent even in principle, since it discards its arguments before
computing anything.

### The TCB T6 connection — this is where the IAT/loader fix lands

`TCB.md` §T6, quoted in full:

> `findIatIndex` keys on a slot containing its own address — a convention `loadMemory`
> manufactures; **the real loader writes the resolved VA.** 4KB-boundary assumption; positional
> dispatch skipping index 6 (per-DLL null terminator, stride reimplemented ×3); `| _ => none`
> fail-open default. Every trace proof is conditioned on a false premise about the OS; binaries
> work because interception never happens in reality. Fix: Win32 differential harness dumps the
> real post-load IAT and diffs vs synthesized; re-key interception on resolved VA.

Grep-confirmed directly against `Win32API.lean`: `findIatIndex` (`:247-251`) treats an address as
an IAT slot iff `s.read64 addr == addr` — i.e. the 8 bytes stored at that memory location equal
the address of the location itself. This is a convention `loadMemory` (`:277-303+`) manufactures
purely for gasm's own synthetic loader (it writes each IAT slot's own address into itself as a
sentinel so `findIatIndex` can recognize it later) — it is not how any real Windows loader
behaves. The real PE loader resolves each import at load time and writes the **target function's
actual virtual address** into the IAT slot; nothing about a real IAT slot's contents identifies it
as an IAT slot, and nothing about a real resolved import VA equals its own slot's address. This
means: "every trace proof is conditioned on a false premise about the OS" (TCB's words) —
`Win32API.lean`'s interception mechanism only works because gasm's own loader colludes with its
own interceptor; a gasm-emitted PE run under the *real* Windows loader would have its IAT slots
overwritten with real function pointers, and `findIatIndex`'s self-referential check would never
fire, so none of the Win32 hooks would ever be invoked — the emitted binary's behavior under a
real loader is completely unvalidated by anything in the current model. Two further oddities TCB
and N1 both flag, independently grep-confirmed: the dispatch `match` at `:255-273` jumps from
`some 5` (`virtualFreeHook`) directly to `some 7` (`wsaStartupHook`) with **no `some 6` arm at
all** — index 6 is silently unreachable, no comment explains why; and `iatBase := (addr >>> 12)
<<< 12` (`:250`) assumes the IAT begins exactly on a 4 KB page boundary, an assumption never
validated against a real PE layout.

N1's design doc specifies *what* the harness must measure (dump the real post-load IAT from an
actual Windows process running a gasm-emitted PE, diff it against gasm's synthesized IAT) and
*what* re-keying requires of `findIatIndex`/`loadMemory` operationally. **This task (N2) is where
that measurement harness actually gets built and where the fix — re-keying interception on the
resolved VA the harness measures, rather than gasm's self-referential slot convention — lands in
`findIatIndex` and `loadMemory`.**

### Governing laws

`docs/REVIEW.md` Law 5 (stop-and-design — this task only proceeds because N1's design exists and
has cleared review); Law 9 (the read-binder mandate this task's C1 fix directly serves); Law 13(4)
(control-vector discipline: this is exactly the harness-touches-the-world class Law 13(4)
describes — proof is not available, so mandatory positive+negative controls are the substitute).
`docs/VISION.md` §3.2 (the differential-validation obligation N1/N2 jointly discharge) and §3.3
(demand-driven growth — scope error paths/handle lifecycle to what current and near-term spikes
need, per N1's own scoping of C3, not the full Win32 surface).

## Deliverables & acceptance criteria

- **The native harness itself, built per N1's design**: a Windows test companion that invokes
  real `ReadFile`, `WriteFile`, `VirtualAlloc`/`VirtualFree`, and `GetLastError` under controlled
  conditions (pipes, console, files, invalid handles) and captures return values, error codes,
  buffer contents, and byte counts for comparison against the model's hook outputs for matching
  inputs.
- **`readFileHook` rebuilt to close C1**: must be able to express short reads (fewer bytes
  returned than requested, with more available later), console line-buffered semantics (CRLF,
  Ctrl-Z EOF), and the broken-pipe failure (`FALSE` + `ERROR_BROKEN_PIPE`) — replacing the current
  `count := min maxLen avail`-always-succeeds shape. The handle value in `RCX` must actually be
  read and must gate behavior (pipe vs console vs invalid handle are observably different).
- **`writeFileHook` rebuilt to close C2**: must be able to express short writes, and must emit
  `ConsoleEvent.out` vs `.err` based on which handle was actually written to — which requires
  `getStdHandleHook`/the handle table (below) to first make stdin/stdout/stderr distinguishable.
- **A real handle table**: distinct handle values for stdin/stdout/stderr and for any
  file/pipe handles a current or near-term spike opens; an open/close lifecycle; invalid-handle
  behavior (a closed or never-opened handle used in a subsequent call must fail observably, not
  silently succeed).
- **`GetLastError`/`SetLastError` semantics** and the specific error codes N1 scoped as in-demand
  (broken pipe, invalid handle, out of memory) — per N1's Law-5/D7 scoping, not the full Win32
  error-code universe.
- **`virtualAllocHook` rebuilt to close C4**: a real allocator that tracks live regions and
  returns distinct addresses per call (at minimum: two allocations never alias); `virtualFreeHook`
  actually tracks what it releases rather than unconditionally returning success.
- **TCB T6 fix**: `findIatIndex`/`loadMemory` re-keyed on the resolved VA the harness measures
  (per N1's operational spec for "dump the real post-load IAT"), replacing the self-referential
  `s.read64 addr == addr` convention. The index-6 dispatch gap and the 4 KB-boundary assumption
  in `iatBase` must be resolved or explicitly justified as part of this fix — not left as silent
  gaps in the rekeyed table.
- **Control-vector discipline (Law 13(4))**, following `HardwareHarness.lean`'s pattern
  (`Gasm/Targets/X86_64/HardwareHarness.lean:281` — `runHardwareBatch`'s `Except String (List
  HardwareExecutionResult)` signature so a missing/unrunnable oracle cannot silently synthesize a
  passing result; `:309-340` — the mandatory positive-control (a known-good call proven to
  succeed) and negative-control (a deliberately invalid call — e.g. `div rbx` with `rbx=0` —
  proven to be *detected* as faulted) pair, run before any fuzz vector counts, with the run
  aborting on any control failure). N2's OS-level harness needs the direct analogue: a known-good
  `ReadFile`/`WriteFile`/`VirtualAlloc` call must be shown to succeed with the expected observable
  result, AND a deliberately invalid call (bad handle, oversized buffer, write to a closed handle)
  must be shown to be rejected/erred as Windows actually rejects it — before any differential
  comparison result is trusted. `Except`-typed outcomes throughout: a harness that cannot run
  (not on Windows, required privilege absent) must fail the run, never no-op.
- Since this task rebuilds real model surface (a differential API contract, not a mechanical
  fix), it is Law-5-class: `status` should progress `ready → designing → design-review →
  implementing → done`, and a fresh-agent design review is required before implementation
  dispatch — not waived. The consolidated design should extend `docs/TARGETS/WINDOWS.md` (or
  N1's chosen design-doc location) with the concrete hook rewrites, handle-table shape, and
  error-code set this task commits to building.

## Pointers

- `Gasm/Targets/Windows/Win32API.lean:74-81` (`getStdHandleHook` — both STD_INPUT/STD_OUTPUT map
  to handle `1`, only STD_ERROR gets `2`), `:85-104` (`readFileHook` — C1: `count := min maxLen
  avail` at line 90, `RAX := 1` unconditional at line 94, `RCX`/handle never read), `:108-122`
  (`writeFileHook` — C2: full-length write always, `ConsoleEvent.out` unconditional at line 122),
  `:132-135` (`virtualAllocHook` — C4: constant `0x20000000`), `:138-142` (`virtualFreeHook` —
  always returns 1, tracks nothing), `:247-251` (`findIatIndex` — TCB T6: `s.read64 addr == addr`
  self-referential convention), `:255-273` (the IAT dispatch table — confirm the `some 5` →
  `some 7` jump with no `some 6` arm), `:277-303+` (`loadMemory` — the synthetic IAT-slot
  self-address convention TCB T6 flags).
- `Gasm/Targets/X86_64/HardwareHarness.lean:281` (`runHardwareBatch`'s `Except`-typed signature —
  the control-vector architecture to mirror at the OS-API level) and `:309-340`
  (`hardwareOracleSanityCheck` or equivalent — the mandatory positive/negative control pair,
  aborting on any control failure; note the specific positive control is `mov rax, 0xC0FFEE1234`
  checked against the real register value, and the negative control is `div rbx` with `rbx=0`
  checked for `faulted := true`).
- `docs/tasks/N1-win32-harness-design.md` — the direct prerequisite; this task's whole
  implementation surface is scoped by what N1's design specifies. Read it first.
- `MODEL_DEBT.md` §C1 (short reads — quoted above), §C2 (WriteFile/handle collapse — quoted
  above), §C3 (no error model), §C4 (VirtualAlloc constant — quoted above), §C6 (IAT/loader
  convention), and the TOP-10 table items 1 and 8 (both name this class of gap).
- `TCB.md` §T6 (IAT/loader convention — quoted in full above) and the RANKED TOP 8 table entry 6.
- `docs/VISION.md` §3.2 (differential-validation obligation), §3.3 (demand-driven growth/scoping).
- `docs/SYSTEM_EFFECTS.md` §6.1 (the console `.out`/`.err` two-stream coalescing algebra this
  task's C2 fix must make realizable).
- `docs/REVIEW.md` Law 5 (stop-and-design), Law 9 (read-binder mandate), Law 13(4) (control-vector
  discipline).
- `Stdlib/Zlib/Windows.lean` — the fixed 8 MB/8 MB `VirtualAlloc` scratch split that currently
  rests on the invented constant this task replaces; a real allocator changes what that code can
  assume about allocation addresses.

## Notes

- 2026-08-27: priority 9.0 — MODEL_DEBT top-10 #1: 'read as the universal binder' is unsound without this — a ∀-read-result contract proven against today's always-maximal-read hook is vacuous; also closes TCB T6 (IAT/loader convention, ranked #6).
- 2026-08-27 (oracle-debt audit, `docs/ORACLE_DEBT.md` Part 6): priority raised 9.0 → 9.3. Already
  near the top of the frontier; nudged further since it now doubly gates the oracle-debt chain
  (PA5 → PA6 → PA8/PA17) the owner has named top priority, on top of its original networking-track
  rationale.

_(none yet — first entries append here as work begins; this is Law-5-class networking-model work
— consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch.)_
