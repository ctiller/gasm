---
id: N1
title: Win32 API differential harness design doc
status: designing
blocked_on: ""
after: []
related: []
bar: ""
track: networking
priority: 9.0
priority_set: 2026-08-27T18:25:47Z
design: "docs/TARGETS/WIN32_DIFFERENTIAL_HARNESS.md"
design_review: "needs-rework 2026-08-27"
date: 2026-08-27
---

# N1: Win32 API differential harness design doc

## Context

This task's own deliverable **is** a Law-5 design doc — it exists because `docs/REVIEW.md` Law 5
requires that any API contract not yet fully designed in `docs/` must stop implementation cold
until the design is authored and reviewed, and the entire Windows Win32 model
(`Gasm/Targets/Windows/Win32API.lean`) currently has real code and zero validation against the
real OS. `docs/VISION.md` §3.2 states the obligation this task exists to satisfy directly:

> Windows API models vs. the real OS: every modeled Win32 contract (`ReadFile`, `WriteFile`,
> `VirtualAlloc`, sockets, ...) must be exercised by a native harness that invokes the real API
> and compares observable behavior against the model's state-transition hooks — the same
> discipline the ISA models already follow.

"The same discipline the ISA models already follow" means: symmetric with
`Gasm/Targets/X86_64/HardwareHarness.lean` — that harness invokes real silicon and diffs registers
against the model; this design must specify the OS-level equivalent, invoking real Win32 APIs and
diffing observable state-transitions (memory writes, return values, emitted events) against
`Win32API.lean`'s hooks. Reuse that harness's hard-won control-vector architecture rather than
reinventing it: mandatory positive AND negative controls before any result counts (Law 13(4)),
`Except`-typed outcomes so a missing OS/API surface cannot be silently synthesized as a passing
result (the exact class of bug that made the x86 hardware fuzzer a silent no-op for a full review
cycle, per PLAN.md's Phase-1 history), and — per D13's TCB policy — a differential harness is
mandatory for every OS surface trusted but not proven, which is the entire Win32 model as it
stands today.

### Why this doc must pin C1 (short reads) first — `TASKS.md`'s explicit ordering

`TASKS.md`'s own line for this task states the priority order: "pins C1 short-reads FIRST, error
paths, handle table." This is not arbitrary sequencing — it's because `MODEL_DEBT.md`'s **C1**
entry identifies `ReadFile`'s short-read gap as "the single most load-bearing OS gap" in the whole
ledger, for a specific downstream reason:

> Given "`read` as the universal binder" (Law 9 / PLAN Phase 4), this is the single most
> load-bearing OS gap: a `∀ read-result` contract proven against a model that can only produce
> maximal reads proves nothing about chunk-robustness. **The Win32 differential harness must pin
> this first.**

Concretely, verified by reading `Win32API.lean` directly: `readFileHook` (`:85-104`) computes
`count := min maxLen avail` and always sets `RAX := 1` (success) — it can only ever return as many
bytes as were requested or as are available, **and it always succeeds**. It cannot express a real
pipe delivering 7 bytes when 4096 were requested with more data still arriving; console
line-buffering (one line per call, CRLF, Ctrl-Z EOF); a broken pipe (`FALSE` +
`ERROR_BROKEN_PIPE`); or any handle-type-dependent behavior at all — **the handle value in `RCX`
is never read by the hook.** Because Law 9's enforcement mechanism ("`read` is the universal
binder") requires every `∀ (env : Environment)` contract to be proven correct for *any* returned
byte array — any length, any chunking, partial reads, empty reads, EOF — a model that structurally
cannot produce anything but a maximal read makes every such Phase-4 contract statement vacuous by
construction, in the same way an untested `Environment` field would (see `TCB.md` T12 / this
conversion's TC18 file for the sibling `Environment`-dead-fields finding). This design doc's C1
section is therefore not "one item in a list" — it is the item that makes or breaks whether Phase
4's whole `read`-as-binder plan is buildable on real OS behavior at all.

### The rest of the gap this harness must close

Verified directly against `Win32API.lean` at time of writing (grep-confirmed line numbers below):

- **C2 — `WriteFile` never short-writes, and stdout/stderr are indistinguishable.**
  `writeFileHook` (`:108-122`) always writes the full requested length and always emits
  `ConsoleEvent.out` — never `.err`. Compounding this, `getStdHandleHook` (`:74-81`) maps **both**
  `STD_INPUT_HANDLE` (`-10`/`0xFFFFFFF6`) and `STD_OUTPUT_HANDLE` (`-11`/`0xFFFFFFF5`) to the same
  handle value `1` (only `STD_ERROR_HANDLE` gets `2`) — there is no real handle table, so nothing
  downstream can distinguish stdin from stdout even in principle. This directly breaks the
  two-stream observation algebra `docs/SYSTEM_EFFECTS.md` §6.1 depends on (console `.out`/`.err`
  are supposed to be distinct coalescing streams).
- **C3 — no error model whatsoever.** No `GetLastError`/`SetLastError`, no error codes; every
  hook in the file succeeds unconditionally. `references/windows/` has only 6 thin pages
  (`readfile.md` is 28 lines but does mention `GetLastError` and pipe/console sequential
  semantics — the reference material to design against exists, thinly).
- **C4 — `VirtualAlloc` is a constant.** `virtualAllocHook` (`:132-135`) returns the literal
  `0x20000000` regardless of size, address, or protection flags — two allocations return the same
  pointer. `Stdlib/Zlib/Windows.lean`'s fixed 8 MB/8 MB scratch split rests on this invented
  constant.
- **C5 — sockets are wholly invented.** `socketHook`→`100`, `acceptHook`→`101`,
  `bindHook`/`listenHook`/`wsaStartupHook`→`0` (`:145-182`, grep-confirmed); `recvHook` delivers an
  entire queued request in one call and can never short-read or block; `sendHook` always sends
  everything. **`acceptHook` on an empty request queue sets `rip := 0` to terminate the program**
  (`:176-178`) — an invention with no Win32 counterpart at all, not even an approximation of real
  blocking-accept behavior.
- **TCB T6 — the IAT interception convention is keyed on gasm's own emitter, not on OS behavior.**
  `findIatIndex` (`:247-251`) identifies which Win32 function is being called by checking whether
  the 8 bytes at the call target **equal the call target's own address** — a convention
  `loadMemory` (`:277+`) manufactures for its own synthetic loader, not anything the real Windows
  loader does (the real loader writes the resolved function VA into that slot). `TCB.md` T6's
  exact words: "Every trace proof is conditioned on a false premise about the OS; binaries work
  because interception never happens in reality." Two additional, independently grep-confirmed
  oddities in the same dispatch table (`:255-273`): positional dispatch skips **index 6** with no
  comment (the `match` jumps from `some 5` directly to `some 7`), and `iatBase := (addr >>> 12) <<<
  12` assumes the IAT begins exactly at a 4 KB boundary. TCB's proposed fix belongs in this design:
  **the harness must dump the real post-load IAT from an actual Windows process loading one of
  gasm's own emitted PEs, and diff it against gasm's synthesized IAT** — this is the concrete
  "invokes the real API and compares observable behavior" instance for the loader itself, not just
  for individual hook functions. Re-keying interception on the resolved VA (what the harness
  measures) rather than gasm's self-referential slot convention is the fix N2/N3 will implement
  once this design specifies exactly what the harness measures and how.

## Deliverables & acceptance criteria

This task's deliverable is the design doc itself — a new `docs/TARGETS/` file (or a substantial
new section of `docs/TARGETS/WINDOWS.md`, whichever the implementing agent judges cleaner given
existing structure) specifying, at minimum:

- **Harness architecture**, symmetric with `HardwareHarness.lean`: a native (Windows) test
  companion that invokes real `ReadFile`/`WriteFile`/`VirtualAlloc`/`VirtualFree`/WinSock calls
  under controlled conditions and captures their observable results (return values, error codes,
  buffer contents, timing-independent state) for comparison against `Win32API.lean`'s hook outputs
  for the same inputs.
- **C1 pinned first, explicitly**: the design's short-read section must cover pipe delivery of
  partial data (fewer bytes than requested, more arriving later), console line-buffered reads
  (CRLF handling, Ctrl-Z EOF), and the broken-pipe case (`FALSE` return + `ERROR_BROKEN_PIPE`) —
  and must specify how the harness represents "read result" so that it can, in a follow-up task
  (N2), replace `readFileHook`'s `min(requested, available)`-always-succeeds shape with something
  that can express all of these outcomes.
- **A handle-table design**: real handle values, real distinctness between stdin/stdout/stderr
  (closing C2), and a lifecycle (open/close, invalid-handle behavior) — not the current "handle 1
  for two different standard streams" collapse.
- **An error-path model**: at minimum `GetLastError`/`SetLastError` semantics and the specific
  error codes this project's spikes are likely to need (broken pipe, invalid handle, out of
  memory) — closing C3 to the extent the demand-driven growth principle (D7/Law 5) justifies for
  currently-planned spikes, not the full Win32 error-code universe.
- **Socket harness scope**: how blocking `accept`/`recv`/`send` will be exercised against a real
  WinSock server/client pair, replacing the `acceptHook` empty-queue `rip := 0` invention with
  harness-measured behavior — this section directly feeds N3 (real socket model).
- **The IAT/loader re-keying plan** (TCB T6): specify exactly what "dump the real post-load IAT"
  means operationally (a minimal real Windows process loading a gasm-emitted PE, read back via a
  debugger API or a small native helper), what it should be diffed against, and what "re-key
  interception on resolved VA" requires of `findIatIndex`/`loadMemory` — this design output feeds
  N2's implementation directly.
- **Control-vector discipline carried over from `HardwareHarness.lean`**: `Except`-typed outcomes
  (no synthesizable "it worked" result when a real API call couldn't be made — e.g. running
  outside Windows, or a required privilege absent), and mandatory positive + negative controls
  (a known-good call must be shown to succeed; a deliberately invalid call — bad handle, oversized
  buffer — must be shown to be rejected, before any comparison result is trusted).
- Since this design doc's subject is new model surface (a differential API contract), it is
  Law-5-class: this task's own `status` should progress `ready → designing → design-review →
  done` (there is no separate "implementing" stage for a design-only deliverable, or it collapses
  into "designing"), and it must **not** be marked done until a fresh-agent design review has
  evaluated it against `docs/VISION.md` §3.2/3.3, the C1–C5 gaps above, and TCB T6 — waiving that
  review is not appropriate here, since the doc directly gates N2/N3/N4/N5's implementation and,
  transitively, PA5/PA6 (which need OS1/N2's short-read model for their input-event design).

## Pointers

- `Gasm/Targets/Windows/Win32API.lean:74-81` (`getStdHandleHook` — both STD_INPUT/STD_OUTPUT map
  to handle `1`), `:85-104` (`readFileHook` — C1), `:108-122` (`writeFileHook` — C2), `:132-135`
  (`virtualAllocHook` — C4), `:145-228` (WinSock hooks incl. `acceptHook`'s `rip := 0` at
  `:176-178` — C5), `:247-251` (`findIatIndex` — TCB T6), `:255-273` (the IAT dispatch table;
  confirm the index-6 skip by grep — the `match` arms jump `some 5` → `some 7` with no `some 6`
  case at all), `:277+` (`loadMemory` — the synthetic IAT convention TCB T6 flags).
- `Gasm/Targets/X86_64/HardwareHarness.lean:281` (`runHardwareBatch`'s `Except`-typed signature)
  and `:331-336` (the positive/negative control-vector pattern) — the harness architecture this
  design should mirror at the OS-API level.
- `MODEL_DEBT.md` §C1–§C6 in full (the specific gaps this design closes) and the TOP-10 table's
  item 1 and item 8 (both name this class of gap).
- `TCB.md` §T6 in full (the IAT/loader-convention finding this design must also address).
- `docs/VISION.md` §3.2 (the exact obligation quoted above) and §3.3 (demand-driven growth — this
  design should scope error-path/socket coverage to what current and near-term spikes actually
  need, not the full Win32 surface, per Law 5/D7).
- `docs/REVIEW.md` Law 5 (stop-and-design — this task's own governing law), Law 9 (the read-binder
  mandate C1 exists to unblock), Law 13(4) (control-vector discipline).
- `references/windows/readfile.md` (28 lines — thin but present; mentions `GetLastError` and
  pipe/console sequential semantics) — the one piece of vendored ground truth already available;
  identify what else needs Law-4 ingestion (console-mode, overlapped I/O, `VirtualAlloc`,
  `CreateFile` are all currently unvendored per `MODEL_DEBT.md` C3).
- PLAN.md, Phase 2 "Win32 API differential harness design" bullet — the original scope note this
  task file supersedes and elaborates.

## Notes

- 2026-08-27: priority 9.0 — Win32 harness design doc is the direct prerequisite for closing MODEL_DEBT C1, its own #1 top-10 item ('highest-leverage OS gap'); owner is explicitly eager for networking buildout.

_(none yet — first entries append here as work begins; this task's whole output is the design
doc, so its Notes should track open modeling questions as they're resolved during authoring, and
get consolidated into the doc itself rather than into a separate inline `## Design` section here.)_
