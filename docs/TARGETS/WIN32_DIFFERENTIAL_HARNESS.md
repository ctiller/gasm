# Win32 Differential Harness — Design

> Status: design (task `N1`), revision 2 after design-review round 1
> (APPROVE-WITH-CHANGES, 8 mandatory items M1–M8). Governs implementation tasks `N2` (OS1:
> ReadFile/WriteFile/handle/VirtualAlloc rebuild) and `N3` (real socket model). Not yet
> implemented — no Lean code in this repository currently satisfies this design;
> `Gasm/Targets/Windows/Win32API.lean` is the pre-harness state this design replaces.
> The M1–M8 labels below are revision-local review items, not the canonical M0–M9 stages in
> `docs/MEMORY_MODEL.md` and not an active task ledger.

## Revision notes (round 1 → round 2)

Every mandatory item from round 1 is addressed in this revision; a per-item map is kept here
for the second reviewer rather than scattered as inline diff markers:

- **M1** → §4.0 (new): the model is now stated as a permitted-outcome relation with a
  containment criterion, a constructor→witness table, a parameter sweep, and an explicit
  NOT-MODELED list. Two new witness probes were added (§4.4, §4.6) that round 1's five-point
  battery was missing entirely.
- **M2** → §2 (three interpretations, not one) and every probe in §4/§8/§9 restated as an
  invariant rather than an exact literal; repeated-trial probing added to §3.1 and §4.2.
- **M3** → §1.3 is a full redesign: a single inherited duplex named pipe replaces the
  write-once-after-exit temp file, with an explicit phase protocol so the controller is told
  when a probe's call returns rather than guessing. §1.6 makes the bounded timeout a property
  of every probe, not an `N3` add-on.
- **M4** → §3 is restructured around the callee-invoked, memoized gate (`ensureWin32OracleControlsRan`,
  modeled on the Wasm harness's `ensureOracleControlsRan`, not the weaker X86_64 pattern —
  both cited by line number in §3.0), a third **distinguishability** control (§3.3, corrected —
  see below), a vacuity floor (§3.4), and a sum-typed wire record with magic/version/length/checksum
  and a stated prohibition on `Inhabited`/`Default` (§1.4).
- **M5** → §10 is rewritten around three named soundness properties (S1–S3, including
  fail-closed), the index-6 gap is now *explained* (not "unexplained") by direct citation of
  `Emitter.lean`'s stride arithmetic, a previously-undocumented **live latent bug** is named
  (positional dispatch shifts under a KERNEL32 import-list change), and Q3 is answered by
  parameterizing the loader over an abstract VA assignment rather than importing one measured
  set of addresses into the model.
- **M6** → §7 gains a step 0 (blast-radius enumeration) and a step 7 (re-establishment,
  with an explicit statement that a recomputed `decide`/`native_decide` pass is not evidence),
  plus a model-version-stamp proposal.
- **M7** → the genuine Microsoft `ReadFile` page is hash-pinned as `windows-readfile` in
  `references.json`, replacing the self-authored stub round 1 relied on. The PE format and the
  WinSock function pages used here are likewise registered. The broader source set this design
  once claimed was vendored — system error codes, `GetLastError`, `VirtualAlloc`/`VirtualFree`,
  pipe creation, WinSock error codes, and `WriteConsoleInput` — is **not** registered today.
  Claims depending on it are marked as ingestion prerequisites below rather than presented as
  established ground truth.
- **M8** → §4.7 drops the recorded-calibration fallback entirely; console reads are declared
  out of this design's modeled scope unless `AllocConsole`/`WriteConsoleInput` prove reliable,
  with the observation that follows from M1's outcome-set analysis: the two facts N2 actually
  needs (a pipe/disk "nothing more, but not an error" signal vs. a hard failure) are fully
  probeable without a console at all. §4.6 adds the missing `WriteFile` short-write probe — and
  corrects the review's own suggested mechanism (see disagreement note below).

**Recommended items, all taken**: `GetLastError` ordering discipline (§1.3, §6), a probe-side
checksum distinguishing "channel corrupted" from "probe crashed" (§1.4, folded into M4's wire
record), the Q6 inversion (§1.3 — resolved as a side effect of the M3 channel redesign, not as
a standalone special case), and the four tense fixes (§1.3, §1.5, §10.1 — §4.7's fallback
tense-fix is moot since the fallback was deleted per M8).

**Short-write fixture remains blocked on source intake.** An earlier revision rejected
`CreatePipe` and selected `CreateNamedPipe(... PIPE_TYPE_BYTE | PIPE_NOWAIT)` by citing a local
`createpipe.md` that no longer exists and was never migrated into `references.json`.
`windows-writefile` is registered, but the `CreatePipe`, `CreateNamedPipe`, and named-pipe-state
contracts needed to justify the fixture are not. §4's short-write probe must not become
normative until those official Microsoft pages are hash-pinned and the proposed mechanism is
rechecked against them.

---

## 0. Why this document exists

`docs/VISION.md` §3.2 requires every modeled Win32 contract to be "exercised by a native
harness that invokes the real API and compares observable behavior against the model's
state-transition hooks — the same discipline the ISA models already follow." No such harness
exists today: `Gasm/Targets/Windows/Win32API.lean`'s hooks (`readFileHook`, `writeFileHook`,
`virtualAllocHook`, the WinSock hooks) are pure inventions, never checked against a real
Windows process. `docs/TECHNICAL_NOTES.md` §2 catalogues the resulting gaps in
detail; this document is the Law-5 design that must exist before `N2`/`N3` write a line of
fix code (`docs/REVIEW.md` Law 5).

Per `docs/REVIEW.md` Law 5 this doc is authored, not implemented: it specifies harness
architecture, probe designs, and the model-update workflow. It contains no Lean beyond
illustrative sketches marked as such. `N2` and `N3` build against it. §11 distinguishes the
Microsoft sources already registered in `references.json` from the required intake that has not
landed; no vendored prose is part of this design.

---

## 1. Harness architecture

### 1.1 Symmetry with `HardwareHarness.lean`

`Gasm/Targets/X86_64/HardwareHarness.lean` validates the x86-64 ISA model by emitting a native
PE that executes candidate instructions on the host CPU and reports register/flag state back
to the Lean-side comparator (`runHardwareBatch`, `:281`). The Win32 harness is the OS-level
sibling: instead of asking "does the CPU do what the ISA model says," it asks "does the OS API
do what `Win32API.lean`'s hooks say." The reusable shape from `HardwareHarness.lean`:

| `HardwareHarness.lean` element | Win32 harness equivalent |
| :-- | :-- |
| `emitNativeBatchTestExe` — emits a PE that runs test vectors and writes a binary result record | **probe emitters** (§1.2) — one per Win32 surface (`ReadFile`, `WriteFile`, `VirtualAlloc`, WinSock, IAT dump), each a small PE built with `emitPE32Executable`/`emitPE32ExecutableMultiDll` |
| `decodeHardwareResult` — fixed-layout binary record decoder | **the wire-record decoder** (§1.4) — one sum-typed result per probe kind |
| `runHardwareBatch : IO (Except String (List HardwareExecutionResult))` | **`runWin32Probe : ProbeSpec → IO (Except String Win32ProbeResult)`** (§1.4) — same `Except`-typed contract |
| `verifyHardwareOracleControls` | **`ensureWin32OracleControlsRan`** (§3) — strengthened to the Wasm harness's callee-invoked, memoized pattern rather than copied from `HardwareHarness.lean`'s weaker caller-invoked one (see §3.0) |

The harness lives in a **new module**, `Gasm/Targets/Windows/Win32Harness.lean`, mirroring
`HardwareHarness.lean`'s placement under the same target directory. It depends on
`Win32API.lean` (to compare against) and `Windows/Emitter.lean` (to build probe PEs), exactly
as `HardwareHarness.lean` depends on both `Win32API.lean` and `Emitter.lean` today.

### 1.2 The controller/probe split — why this differs from `HardwareHarness.lean`

`HardwareHarness.lean` gets away with "one emitted PE, run it, read its stdout" because ISA
instruction semantics need no external OS state — a `mov`/`div` behaves identically regardless
of what spawned the process. Win32 semantics do not have this property: `ReadFile`'s behavior
is a function of what's on the *other end* of the handle (a pipe with 7 bytes buffered and the
writer still open, vs. a console with a pending line, vs. a closed pipe). That external state
cannot be set up by code running *inside* the probe process — it must be arranged by whatever
spawns it. (This split was the one piece of round 1's architecture the review confirmed as
correctly motivated; what changes below is the channel it communicates over, not the split
itself.)

- **The controller** (Lean `IO`, in `Win32Harness.lean`): for each probe, arranges the OS-level
  precondition (creates the pipe/file/socket, decides feed timing), spawns the probe process,
  and drives the rendezvous protocol over the reporting channel (§1.3).
- **The probe** (an emitted native PE, `.exe`, one per test *scenario*): performs exactly the
  sequence of Win32 calls under test and reports each phase over the same channel. Probes are
  built with the same `emitPE32Executable`/`buildTestText`-style machinery
  `HardwareHarness.lean` already uses — no new PE-emission mechanism is introduced;
  `computeSectionLayout`, `groupImportsByDll`, and the IAT-slot-address scheme (§1.5) are
  reused verbatim.

### 1.3 Probe rendezvous & result channel — redesigned (M3)

**Round 1's defect.** A write-once temp file, read by the controller only after the probe
process exits, cannot support the two probes that actually need it: §4.2 (old numbering)
requires the controller to feed the pipe's second chunk *after* the probe's first `ReadFile`
call returns — but a file the probe hasn't written yet tells the controller nothing about when
that happened. §9 (old numbering) needed the server probe to report "listening" before the
controller starts the client probe, with the identical defect. Both were unimplementable as
specified.

**The fix**: a single **inherited, duplex, message-mode named pipe** (`CreateNamedPipe` on a
per-session unique path, `PIPE_ACCESS_DUPLEX | PIPE_TYPE_MESSAGE`), created by the controller
*before* spawning the probe and passed to the probe as an inherited handle (Windows handle
inheritance preserves the numeric handle value across `CreateProcess` when the handle was
created inheritable and `bInheritHandles := TRUE`; the probe is told which numeric value to use
via a command-line argument, since it has no other way to discover it). This is a channel
**separate from whatever OS resource is under test** (the pipe/file/socket §4/§8/§9 probes
exercise is a distinct object from this reporting channel), so there is no interference between
"the resource being measured" and "the channel used to report the measurement" — the concern
round 1's file-based design was also trying to satisfy, just over a channel that couldn't
support ordering.

This controller-side `CreateProcess`/inheritance use is differential-harness infrastructure in the
test TCB, not a claim that gasm implements or verifies a process model. Hosted-process semantics are
deferred beyond M9 by `docs/MEMORY_MODEL.md` Decision 12.

**Phase protocol**: the probe writes one wire record (§1.4) per meaningful step — e.g.
`.phaseReady`, `.phaseCallReturned (callIndex) (result)`, `.phaseFinal (allResults)` — and the
controller reads incrementally, blocking on the next record exactly at the points where it
needs to react (feed more bytes, start a companion probe, etc.). This directly resolves both
of round 1's unimplementable probes: the controller now literally *is told* "my first `ReadFile`
returned" before deciding to feed the second chunk (§4.2), and a server probe literally reports
`.phaseListening` before the controller spawns the client (§9) — no guessing, no polling, no
timing assumption.

**This resolves the "Q6" question round 1 asked itself, as a side effect, not a special case.**
Round 1 exempted `VirtualAlloc`/IAT-dump probes from its side-channel design because opening a
disk file with `CreateFileA` would have added imports to the IAT-dump probe specifically,
corrupting the very import-table shape §10 depends on being representative. Under this
redesign, **every probe kind reports over the same inherited pipe handle using only `WriteFile`**
— which is already present in `WindowsExecutable.imports`' default set
(`GetStdHandle, ReadFile, WriteFile, ExitProcess, VirtualAlloc, VirtualFree`) for every probe,
including the IAT-dump probe. No probe needs to import `CreateFileA`/`CloseHandle` (or any
other extra symbol) purely to report its result, so the special case round 1 needed simply
does not arise: the IAT-dump probe imports nothing beyond the baseline set, preserving its
representativeness for free.

**`GetLastError` ordering discipline** (conservative probe rule): a probe must call
`GetLastError()` as the *very next* instruction after the measured call returns, before doing
anything else — including preparing the phase-record write. The official `GetLastError` page is
not yet registered in `references.json`, so its per-thread and reset-on-success semantics are an
explicit source-intake prerequisite, not ground truth established by this document. Immediate
capture is conservative even before that intake and prevents an intervening Win32 call from
invalidating the observation. `N2` must enforce this by probe construction or review.

### 1.4 Wire record and result type (M4c)

```
-- illustrative only; N2 defines the real shape
inductive Win32ProbeResult where
  | success (bytesTransferred : UInt32) (buffer : Option ByteArray)
  | failure (lastError : UInt32)
-- `deriving Inhabited` and any `Default` instance are FORBIDDEN on this type by convention
-- and by review: there is no legitimate "what a probe would have said" default value, and
-- The trust review already names the live consequence of allowing one (`Inhabited HardwareExecutionResult`
-- fabricates `faulted := false`, reachable via `getD`). A missing result must be `Except.error`,
-- never a constructed `Win32ProbeResult`.

structure Win32ProbeWireRecord where
  magic    : UInt32 -- fixed sentinel; a decode against an unrelated byte stream is rejected,
                     -- not silently accepted as a plausible-looking zeroed record
  version  : UInt16
  length   : UInt32
  payload  : ByteArray
  checksum : UInt32  -- e.g. CRC32 of payload; distinguishes "the probe crashed mid-write"
                      -- (truncated record, checksum absent/short) from "the channel or decode
                      -- logic is corrupted" (record present, checksum mismatch) — neither may
                      -- decode as a plausible `Win32ProbeResult`. This directly avoids
                      -- `HardwareHarness.lean`'s two live fabrication paths:
                      -- returning `0` out-of-range so an untouched zero buffer decodes
                      -- plausibly, and `Inhabited` fabricating a default result.
```

`runWin32Probe : ProbeSpec → IO (Except String Win32ProbeResult)` — never a bare
`Win32ProbeResult`, matching `HardwareHarness.lean`'s `runHardwareBatch` contract. A malformed
magic/version/length/checksum, a probe that fails to spawn, or a bounded timeout expiring (§1.6)
all produce `Except.error`; there is no code path that constructs a `Win32ProbeResult` other
than by decoding a wire record a probe process actually wrote and that passed its checksum.

### 1.5 IAT slot addressing for probes

Probe PEs are built the same way `HardwareHarness.lean`'s `buildTestText`/
`emitNativeBatchTestExe` already build the calibration PE: `groupImportsByDll` +
`computeSectionLayout` lay out the IAT, and probe code calls imports via `call [rax]` where
`rax` holds the IAT slot's absolute address (`HardwareHarness.lean:133-136`). Probes run under
the **real Windows loader**, not `Win32API.lean`'s symbolic interpreter — the loader is
*expected* to resolve each slot to the real function VA before the probe's first instruction
executes, but that expectation is precisely the hypothesis §10.1's IAT-dump probe exists to
verify, not an established fact this design is entitled to assume in its own architecture
description (tense fix, per review). `findIatIndex`'s self-referential convention (§10) plays
no role in probe construction either way: probes exercise the real loader; the symbolic
interpreter (and its IAT convention) is only ever compared against, never used to run a probe.

### 1.6 Universal bounded timeout (M3)

Round 1 scoped the bounded-timeout requirement to `N3`'s blocking socket probes only. That was
wrong: **every** probe that can legitimately block — any pipe read/write, any socket call — can
also hang for a reason that has nothing to do with legitimate blocking (a probe bug, a
controller rendezvous message that never arrives, a companion action the controller forgot to
fire). `runWin32Probe` therefore carries a bounded wall-clock timeout as a property of the
function itself, not an opt-in a probe author might forget to add. A companion action (the
controller feeding bytes, connecting a client, closing a handle) must fire within that window
for every probe whose scenario involves a legitimately-blocking call; a probe still blocked
after its companion action fired is a real `Except.error`, not a retried or extended wait.

---

## 2. Divergence severity and interpretation (M2)

Round 1 stated a single rule — "a divergence is always a model bug" — and the review correctly
identified that this collapses three distinct situations into one, with concrete failure modes
in both directions: a legitimate short pipe read could abort an entire harness session as a
"model bug" under the old §3.1 (which predicted an *exact* byte count), and conversely a
one-off scheduling accident in the old §4.1 could get "fixed" into the model permanently. Per
`docs/VISION.md` §3.2 (models are axioms, validated differentially), a probe's disagreement
with the model is filed under exactly one of three interpretations, determined *before* any fix
is written:

1. **Outside the model's permitted-outcome set** (§4.0's containment criterion fails) — this is
   a genuine model bug, at the highest severity this project tracks (same status a wrong axiom
   would have in the proof layer), and follows the workflow in §7.
2. **Inside the model's permitted set, but outside what this design's probe expectation
   predicted** — the expectation was a guess that turned out looser than the real behavior
   warranted (e.g. a probe expected `1 ≤ n ≤ 7` and observed `n = 3`, which is inside the
   permitted range but not what the specific scenario was staged to produce). This is a finding
   against *this design's* expectations, logged and used to tighten the probe's stated
   invariant in a future revision — it is not evidence the model is wrong.
3. **Varying across repeated trials of the identical scenario** — the *set* of observed
   outcomes is itself the datum. Recording `{3, 7}` across ten trials of the same short-read
   scenario is the correct record; picking one value and treating the other as noise discards
   real information about OS nondeterminism (scheduling, buffering) that `N2`'s model may need
   to represent as nondeterministic rather than as a single deterministic function. Repeated
   trials are mandatory precisely to make this interpretation available at all — a
   single-shot probe cannot distinguish "the OS does this" from "the OS did this once" (see
   §3.1, §4.2).

Every probe specified below (§4, §8, §9) is run in repeated trials (recommended default: 20
per scenario) as a consequence of interpretation 3 being unavailable otherwise.

---

## 3. Control-vector discipline (Law 13(4)) — restructured (M4)

### 3.0 Callee-invoked, memoized gating — choosing the stronger of two in-repo patterns

Two live patterns already exist in this codebase for "run mandatory controls before an oracle's
results count," and they are not equally strong. `Gasm/Targets/X86_64/SemanticsFuzzer.lean`
calls `verifyHardwareOracleControls` only from the top-level suite entry point (`:169`); the
lower-level per-instruction function that actually invokes `runHardwareBatch` (`:100`) does not
call it itself — so any caller reaching `:100` through a path other than the top-level suite
bypasses the controls entirely, with nothing in the types preventing that. `Gasm/Targets/Wasm/SemanticsFuzzer.lean`
does this differently: `ensureOracleControlsRan` (`:703`) is a memoized (`IO.Ref Bool`,
initialized `:694`) once-per-process runner, and it is called from **both** the top-level suite
(`:808`) **and** the lowest-level per-case verifier `verifyWasmDiffCase` (`:722`) — its own
docstring states the reason explicitly (`:696-702`): "there is no visibility modifier that
would stop a caller in this same file from invoking `verifyWasmDiffCase` directly... so the
guarantee is placed on the callee instead of relied upon at only one call site."

This design adopts the Wasm pattern, not the (weaker, currently-copied) X86_64 one:
`runWin32Probe` — the lowest-level function every entry point funnels through — begins with
`ensureWin32OracleControlsRan`, a memoized once-per-process runner. There is no code path to a
real probe result that does not pass through this call first.

### 3.1 Positive controls — invariants, not exact literals (M2)

- **`ReadFile`**: a pipe pre-loaded with N bytes, writer end closed immediately after writing (no
  ambiguity about "more coming"), a request for N bytes. **Invariant**: `TRUE`,
  `1 ≤ bytesTransferred ≤ N`, and the bytes actually returned are a prefix of the known feed
  (not necessarily `bytesTransferred == N` — a legitimate short read here is not a control
  failure). The probe loops additional `ReadFile` calls until `Σ bytesTransferred == N`,
  confirming eventual completion rather than asserting a single-call exact count.
- **`WriteFile`**: write a known string to a disk-file handle; **invariant**: `TRUE`,
  `bytesTransferred == len` (a plain disk write is documented as all-or-nothing on success, so
  this one remains an exact literal, not a range), confirmed independently by the controller
  re-opening and reading the file.
- **`VirtualAlloc`**: request `0x1000` bytes with `MEM_RESERVE | MEM_COMMIT`/`PAGE_READWRITE`;
  invariant: non-null, page-aligned (`% 0x1000 == 0`) return value, followed by a `VirtualFree`
  returning `TRUE`.
- **`GetStdHandle`**: request `STD_OUTPUT_HANDLE`; invariant: non-null (never a specific literal
  value — see §5).

Every positive control above is run in repeated trials (§2, interpretation 3) before the
session's controls are considered passed.

### 3.2 Negative controls — source status explicit

- **`ReadFile`** on a fabricated invalid handle (e.g. `(HANDLE)0xDEADBEEF`): proposed outcome
  `FALSE` + `GetLastError() == ERROR_INVALID_HANDLE (6)`. The symbol/value pair needs a
  hash-pinned Microsoft system-error-code source before this becomes a normative control.
- **`ReadFile`** on a pipe read handle whose write end has already been closed with nothing
  written: `FALSE` + `GetLastError() == ERROR_BROKEN_PIPE (109)` —
  the registered `windows-readfile` page ("If an anonymous pipe is being used and the write
  handle has been closed, when ReadFile attempts to read using the pipe's corresponding read
  handle, the function returns FALSE and GetLastError returns ERROR_BROKEN_PIPE"). The numeric
  value `109` separately requires the missing system-error-code registration.
- **`WriteFile`** to a `GENERIC_READ`-only handle: `FALSE` + `GetLastError() == ERROR_ACCESS_DENIED (5)`
  — proposed pending registration of the Microsoft system-error-code source.
- **`VirtualAlloc`** requesting an absurd size: `NULL` + `GetLastError() == ERROR_NOT_ENOUGH_MEMORY (8)`
  — proposed pending registration of the Microsoft system-error-code source; the registered
  `windows-readfile` page independently names the symbolic resource-exhaustion failure mode.

### 3.3 Distinguishability control (third control) — corrected from round 1's framing

The review asked for a control proving "`TRUE`+0-bytes (disk EOF)" is decoder-distinguishable
from `FALSE`+`ERROR_BROKEN_PIPE`. The registered `windows-readfile` source shows that
that phrasing conflates two different real outcomes: a disk read that begins at or beyond EOF
is documented as **`FALSE` + `ERROR_HANDLE_EOF`**, not `TRUE`+0; the numeric value `38` remains
provisional until the system-error-code source is registered.
The genuine `TRUE`+0 case is a **pipe** outcome: "If the `lpNumberOfBytesRead` parameter is
zero when `ReadFile` returns `TRUE` on a pipe, the other end of the pipe called `WriteFile`
with `nNumberOfBytesToWrite` set to zero" (`windows-readfile`). This is a real, useful
correction to bring back to the reviewer (see the disagreement note at the top of this
document), and it strengthens the control rather than weakening it: there are now **three**
mutually-confusable "nothing more right now" signals, not two, and the harness must confirm
its own decoder tells all three apart before any read probe counts:

- `.success 0` — pipe, peer wrote zero bytes (`windows-readfile`)
- `.failure ERROR_BROKEN_PIPE` — pipe, write end closed (`windows-readfile`)
- `.failure ERROR_HANDLE_EOF` — disk, read begins at/beyond EOF (`windows-readfile`)

The control constructs one probe producing each of the three outcomes and asserts the decoder
maps them to three distinct `Win32ProbeResult` values — a decoder bug that collapsed any two of
these would be exactly the kind of silent conflation C1/C3 exist to eliminate from the model,
and must not survive undetected in the harness that's supposed to be catching it.

### 3.4 Vacuity floor

A harness session that executes zero probes is a hard failure, not a vacuous "0 ran, 0 failed,
exit 0" pass — the same Law-13 failure class guarded concretely by
`Gasm/Targets/X86_64/PerfFuzzerCLI.lean`'s `--count 0` vacuity floor. `runWin32Probe`'s top-level suite runner
prints the executed probe count and a constructor-coverage table (§4.0) at the end of every
session; an executed count of zero, or a constructor-coverage table with an unfilled row, both
fail the session.

### 3.5 Harness-cannot-run aborts

Unchanged in substance from round 1, restated against the new architecture: a non-Windows host,
a probe spawn failure, a bounded timeout (§1.6, now universal) expiring, a malformed wire
record (§1.4's magic/version/length/checksum check failing), or required controller-side OS
setup failing (`CreateNamedPipe`/`CreatePipe` itself failing) all produce `Except.error` — never
a skipped probe or a synthesized pass.

---

## 4. C1 — the reachable read-outcome domain, with a reachability witness for each element (M1)

This is the section that determines whether Phase 4's
`read`-as-universal-binder plan (`docs/REVIEW.md` Law 9) is buildable at all. Round 1's mistake,
named precisely by the review: **the deliverable is not "a validated `readFileHook`" — it is
the reachable read-outcome domain, with a reachability witness for each element.** Five exact
scalar expectations are five regression tests; they are not evidence that a `∀`-quantified
model over that domain is sound, because measurement can only refute, never license a
universal claim by itself. Licensing the universal claim requires three sources round 1 used
none of, all supplied below.

### 4.0 Model shape, containment criterion, constructor table, sweep, and NOT-MODELED list

**Model shape** (illustrative; `N2` defines the real type):

```
inductive ReadOutcome where
  | success (n : Nat) (bytes : ByteArray)   -- 0 < n ≤ requested, OR n = 0 with a documented cause
  | zeroSuccess                              -- TRUE, n = 0 (pipe: peer WriteFile'd zero bytes)
  | failure (code : UInt32)                  -- FALSE + GetLastError

def readFilePermitted (kind : HandleKind) (requested : Nat) (streamState : StreamState)
    : Set ReadOutcome := ...
```

**Containment criterion**: this design recommends `N2` target **sound over-approximation**,
not exact characterization, as the default — following the precedent this project already
ratified for its other world-sampling oracle (`wsc`'s replacement of a `%`-error metric with
`real ∈ [min, max]` containment). Every probe below checks
`observedOutcome ∈ readFilePermitted kind requested streamState`, never equality against a
single predicted value. Exact characterization is achievable and preferred for the pipe and
disk cases specifically, since the registered `windows-readfile` Remarks pin their outcome sets
(quoted throughout §4.1–§4.6); it is not attempted for console (§4.7, scoped out) or for
anything in the NOT-MODELED list below.

**Three-legged comparison, all three legs now present** (round 1 had only the third):
1. **doc ⊨ model** — `readFilePermitted` is derived from `windows-readfile`'s Remarks, cited per
   constructor below, not authored from memory.
2. **probe ∈ doc** — every probe's observed outcome is checked against the registered source
   before it's used for anything else (an outcome the source doesn't predict is itself a
   finding about the *reference*, not just the model — see M7's residual note in §11).
3. **probe ∈ model** — the containment check against `readFilePermitted`, run every session.

**Constructor → witness table**:

| Constructor | Registered source | Witness probe |
| :-- | :-- | :-- |
| `.success (n, bytes)`, `1 ≤ n < requested`, more pending | "the number of bytes requested is read... a write operation completes on the write end of the pipe" (`windows-readfile`) | §4.1 |
| `.success (n, bytes)`, `n == requested` | same, exact-count branch of the above | §3.1 positive control |
| `.success (n, bytes)`, disk read straddling EOF | "If a read operation... extends past the end of the file, then the read operation succeeds, and the number of bytes read is the number of bytes that were read before the end of file was reached" (`windows-readfile`) | §4.5 |
| `.zeroSuccess` | "the other end of the pipe called WriteFile with nNumberOfBytesToWrite set to zero" (`windows-readfile`) | §4.4 (new) |
| `.failure ERROR_BROKEN_PIPE` | `windows-readfile`; numeric value needs system-error source intake | §4.3 |
| `.failure ERROR_HANDLE_EOF` | "a read operation on a file begins at or beyond the end of the file" (`windows-readfile`); numeric value needs system-error source intake | §4.6 (new) |

**Explicit NOT-MODELED list** (out of this design's scope, per Law 5 and the demand-driven
scoping — named so a gap is a decision, not a silent omission):
- Overlapped I/O (`ERROR_IO_PENDING`, the whole `OVERLAPPED`-structure discipline) — no current
  spike opens a handle with `FILE_FLAG_OVERLAPPED`.
- Named-pipe message mode and `ERROR_MORE_DATA` (numeric value provisional pending system-error
  source intake) — byte mode only is in scope; message mode is a distinct, separately-scoped
  read shape.
- `ERROR_OPERATION_ABORTED` from a console `Ctrl+C` (`windows-readfile`) — folds into §4.7's
  console-scope decision.
- `ERROR_INVALID_USER_BUFFER`/`ERROR_NOT_ENOUGH_QUOTA` from exhausted outstanding async I/O
  (`windows-readfile`) — overlapped-only, out of scope with the above.
- Mailslots (`ERROR_INSUFFICIENT_BUFFER`) and transacted-file reads (`windows-readfile`) — no
  current or near-term spike uses either.

**Parameter sweep** (turns five points into a surface, per the review's explicit suggestion):
`requested ∈ {0, 1, 7, 4095, 4096, 65537}` × `fed ∈ {0, 1, 7, 4095, 4096, 65537, more-than-requested}`
× `writer-close timing ∈ {before any read (→ broken pipe), between reads (→ zero-write or more
data), never (still open)}`. `N2`'s probe battery iterates this sweep rather than the six fixed
scenarios named individually below — §4.1–§4.6 name the *load-bearing* points in that surface
(the ones with a distinct constructor or a documented boundary condition), not its entirety.

**Coverage obligation**: per Law 13's "check ∀, fix ∀" and `docs/VISION.md` §3.2's
"executes ≠ discriminates" requirement, the finished battery must be run under mutation of each
`readFileHook` constructor (e.g. force the rewritten hook to always take the maximal-read
branch regardless of scenario) and confirm at least one probe goes red for every mutated
constructor. This is a build obligation for `N2`/`TC11`, not something this design doc can
discharge itself — named here so `N2` doesn't build a battery that executes every probe without
any of them actually discriminating a broken hook from a correct one.

### 4.1 Witness: pipe partial success (short read, more pending)

**Setup**: `CreatePipe`, a feeder (controller-side thread) writes 7 bytes then holds the write
handle open without writing more, awaiting the controller's signal (received via the phase
channel, §1.3, once the probe reports its first `ReadFile` has returned). Probe requests 4096
bytes.

**Invariant checked**: `TRUE`, `1 ≤ bytesTransferred ≤ 7`, returned bytes are a prefix of the
known feed. (Round 1 asserted `bytesTransferred == 7` as if it were guaranteed; the registered
`windows-readfile` source says "ReadFile returns when one of the following is true: a write operation
completes on the write end of the pipe, the number of bytes requested has been read, or an
error occurs" — a partial flush by the OS mid-write is not documented as impossible, so the
invariant is a range, not a literal, per M2. The `CreatePipe` fixture contract itself remains a
§11 source-intake gate.)

### 4.2 Witness: incremental, stateful reads (repeated trials required)

**Setup**: continuation of §4.1 — after the phase channel reports the first `ReadFile`
returned, the controller signals the feeder to write 5 more bytes and close. The probe issues a
second `ReadFile`.

**Invariant checked**: `TRUE`, `1 ≤ bytesTransferred₂ ≤ 5`, and `bytesTransferred₁ +
bytesTransferred₂ == 12` is confirmed by looping additional reads to completion rather than
asserted from two calls alone. Run in 20 repeated trials (§2) to surface whether the OS ever
splits this differently across runs — the *set* of observed `(bytesTransferred₁,
bytesTransferred₂)` pairs is the recorded datum, not a single chosen pair.

This is also the scenario that most exposes today's model gap: `Win32API.lean`'s
`stdinBuffer : ByteArray` is populated once at load time (`loadWithStdin`) and never appended
to, so it has no equivalent of "a second read after more data arrived on an already-open
handle" to compare against yet. This probe's result is what `N2` must make the rebuilt model
able to express — flagged per §2's framing rather than silently compared against a hook that
structurally cannot represent the scenario.

### 4.3 Witness: broken pipe

**Setup**: `CreatePipe`, controller closes the write handle before writing anything and before
signaling the probe to proceed.

**Invariant checked**: `FALSE`, `GetLastError() == ERROR_BROKEN_PIPE` (`windows-readfile`). The
numeric value `109` remains provisional until the Microsoft system-error-code source is registered.

### 4.4 Witness: pipe zero-byte success (new — closes a gap round 1's battery left uncovered)

**Setup**: `CreatePipe`; feeder calls `WriteFile(writeHandle, buf, 0, &written, NULL)` — a
documented "null write operation" in registered source `windows-writefile` — then holds the handle open.
Probe calls `ReadFile` requesting any nonzero length.

**Invariant checked**: `TRUE`, `bytesTransferred == 0` —
`windows-readfile` ("If the lpNumberOfBytesRead parameter is zero when ReadFile returns TRUE on
a pipe, the other end of the pipe called WriteFile with nNumberOfBytesToWrite set to zero").
This is the `.zeroSuccess` constructor's only witness and was entirely absent from round 1's
five probes — without it, `readFilePermitted`'s `.zeroSuccess` arm would have zero reachability
evidence.

### 4.5 Witness: disk read straddling EOF (success)

**Setup**: a disk file of known size `F`; `ReadFile` requests `F + k` bytes for some `k > 0`.

**Invariant checked**: `TRUE`, `bytesTransferred == F` — the registered `windows-readfile`
source's straddling-EOF rule. Retained from round 1 as the correctly modeled disk case and now
backed by a registered source rather than an inferred claim.

### 4.6 Witness: disk read beginning at/beyond EOF (failure — new)

**Setup**: the same file, fully consumed (file position at `F`, i.e. at EOF), a further
`ReadFile` call.

**Invariant checked**: `FALSE`, `GetLastError() == ERROR_HANDLE_EOF` — the registered
`windows-readfile` source states that a read beginning at or beyond EOF fails with that symbol.
The numeric value `38` remains provisional until the Microsoft system-error-code source is
registered. This constructor was entirely missing from round 1's battery
— §4.5's "extends past EOF" case and this section's "begins at/beyond EOF" case are
*documented as two different outcomes* (success-with-fewer-bytes vs. hard failure) by the same
paragraph, and conflating them (as a naive "min(requested, available)" model does) is exactly
the C1 defect this whole section exists to close.

### 4.7 Console reads — declared out of modeled scope (M8)

Round 1 proposed `AllocConsole`/`WriteConsoleInput` as primary with a "recorded calibration
data" fallback if that proved unreliable in CI. The review correctly rejected the fallback: its
trigger condition ("if console emulation proves unreliable in the actual CI environment")
references an environment that does not exist (the historical trust review's headline: "No CI; every gate
manual"), which makes the fallback the *default* path under any time pressure, not a rare
escape hatch; nothing in round 1's design made a saved recording self-describing (Windows
build/SKU, conhost vs. Windows Terminal vs. ConPTY, and — the specific gap the review named —
console **mode flags**, which is what CRLF/line-buffering behavior is actually a function of,
were never proposed to be captured); and it leaned on `docs/CALIBRATION_GOVERNANCE.md`'s calibration
governance, whose implementing task is itself unresolved.

**Resolution**: the official `WriteConsoleInput` contract is not registered in `references.json`,
so the proposed `AllocConsole`/`WriteConsoleInput` fixture cannot yet be a normative path.
Console handles remain out of `N2`'s modeled scope
under Law 5 and `docs/DECISIONS.md` §1's demand-driven rule, and `readFileHook`'s rebuild carries a stated restriction ("console handles:
unmodeled; falls back to today's behavior or a hard `Except`-visible unsupported-scenario
marker — `N2` decides which") rather than a silently-wrong console path. The review's own
observation motivating this: the actual observable `N2` needs from the read-outcome domain —
"nothing more right now, not an error" vs. "hard failure" (§3.3's three-way distinguishability)
— is fully probeable with a disk file and a pipe; no console is required to close C1 itself.
Console-specific `ReadFile` facts available from the registered `windows-readfile` source for
whenever this is revisited:
`ENABLE_LINE_INPUT` is the default console mode and causes `ReadFile` to read until a carriage
return; `Ctrl+C` succeeds the call but sets `GetLastError() == ERROR_OPERATION_ABORTED`
(`windows-readfile`) — no `Ctrl-Z`-as-EOF behavior is documented on this page, so round 1's
unsourced claim about `Ctrl-Z` is dropped rather than carried forward unverified.

---

## 5. Handle-table design (closes C2)

`getStdHandleHook`'s collapse of `STD_INPUT_HANDLE`/`STD_OUTPUT_HANDLE` to the same value `1`
is diagnosed by a dedicated probe, restated as an invariant per M2:

**Probe: handle distinctness.** Call `GetStdHandle(STD_INPUT_HANDLE)`,
`GetStdHandle(STD_OUTPUT_HANDLE)`, `GetStdHandle(STD_ERROR_HANDLE)` in one probe process.
**Invariant**: `h_in ≠ h_out ∧ h_out ≠ h_err ∧ h_in ≠ h_err`, all non-null — Windows handles are
opaque kernel object table indices with no documented literal-value contract, so the invariant
is distinctness, never a pinned value.

**Probe: `WriteFile`-to-stderr distinctness.** Redirect the probe's `hStdOutput`/`hStdError` to
two separate pipes (read by the controller over the same rendezvous mechanism as §1.3, since
these two pipes are themselves the resource under test here — distinct from the harness's own
reporting channel). Probe writes `"OUT"` to stdout's handle, `"ERR"` to stderr's handle.
**Invariant**: the controller reads `"OUT"` from the stdout-redirected pipe and `"ERR"` from
the stderr-redirected one, never interleaved or collapsed onto one channel — the concrete
falsification target for `writeFileHook`'s unconditional `ConsoleEvent.out` emission
(`Win32API.lean:122`).

**Probe: handle lifecycle (open/close/invalid-handle).** Open a disk file, close it, issue
`ReadFile` on the closed handle. **Invariant**: `FALSE` + `GetLastError() == ERROR_INVALID_HANDLE (6)`
— proposed value pending registration of the Microsoft system-error-code source, specialized to
"a handle that was once valid."

---

## 6. Error-path model (closes C3, scoped per Law 5)

The symbolic outcomes backed by `windows-readfile` are distinguished from numeric values that
still require a registered Microsoft system-error-code source:

| Error code | Provisional value | Current source status | Probe |
| :-- | :-- | :-- | :-- |
| `ERROR_BROKEN_PIPE` | 109 | Symbolic behavior: `windows-readfile`; numeric source not registered | §4.3 |
| `ERROR_INVALID_HANDLE` | 6 | System-error-code source not registered | §3.2, §5 |
| `ERROR_ACCESS_DENIED` | 5 | System-error-code source not registered | §3.2 |
| `ERROR_NOT_ENOUGH_MEMORY` | 8 | Symbolic resource failure: `windows-readfile`; numeric source not registered | §3.2 |
| `ERROR_HANDLE_EOF` | 38 | Symbolic behavior: `windows-readfile`; numeric source not registered | §4.6 |

`GetLastError`'s official page must be registered before its per-thread persistence claim can be
used normatively. **Probe: error-code persistence.** Call a failing API, then call
`GetLastError()` as a genuinely
separate subsequent call (not folded into the failing call's own return path), confirming this
project's model needs a real thread-local error-code field (or single-threaded-program
equivalent) rather than an extra return value threaded through each hook's own signature —
and confirming, per §1.3's ordering-discipline note, that nothing may intervene between the
measured call and this check.

---

## 7. Model-update workflow — a divergence is a MODEL bug (with blast radius and re-establishment, M6)

Per interpretation 1 of §2 (the "outside the permitted set" case): the model is fixed, at the
highest severity this project tracks. The full workflow, now with the two steps M6 identified
as missing:

0. **Blast-radius enumeration (new).** Before any fix lands, enumerate every declaration whose
   kernel-recorded dependency closure reaches the hook being changed. `Tools/CheckGatesAxioms.lean`
   already contains the adjacent capability this step extends: `collectAxiomsFor`
   (`:200-206`) walks `Lean.collectAxioms` over a declaration's environment to find which
   *axioms* it depends on; the blast-radius query this step needs is a sibling, not a reuse of
   that exact function — "which declarations' `ConstantInfo` transitively mentions this hook's
   name," a general dependency-closure walk over the environment, not an axiom-set walk. Naming
   this distinction explicitly matters (Law 8): claiming `collectAxiomsFor` already does this
   would be exactly the kind of overclaim this project's anti-facade law prohibits. `N2`/`TC13`-
   adjacent tooling should add the sibling query.
1. **The probe result is recorded** as ground truth, once §3's controls have passed for the
   session.
2. **The corresponding `Win32API.lean` hook is identified** by function name.
3. **A regression probe is added** to the permanent battery (Law 13(4), `docs/REVIEW.md` §2's
   "findings become gates") — the specific input/output pair that exposed the divergence never
   leaves the fixed battery again.
4. **The hook is rewritten** to make the newly-observed behavior representable in general, not
   merely to patch the one failing case.
5. **The fix is checked against every existing regression probe** (§4.5/§4.6's disk cases are
   the standing example: a pipe-focused rewrite must not regress the already-correct
   maximal-read-or-EOF disk behavior).
6. **The divergence and its resolution are logged** in `docs/TECHNICAL_NOTES.md` or the owning
   canonical target document.
7. **Re-establishment (new).** Every declaration named by step 0's blast-radius enumeration is
   re-derived or explicitly marked unproven against the new hook behavior. The loud case (a
   type changes, proofs fail to elaborate) needs no special process. The dangerous case is
   silent: a hook whose *value* changes while its type/shape doesn't (e.g. `VirtualAlloc`
   returning distinct pointers instead of a constant, `GetStdHandle` returning distinct handles)
   leaves every pointwise contract discharged by `decide`/`native_decide` free to simply
   **recompute and pass**, while the property it originally captured has silently changed
   underneath it. The retired exception mechanism historically named contracts of exactly this
   shape. **A recomputed `decide`/`native_decide` pass is not evidence a
   contract still means what it did; it must be re-justified by hand**, or explicitly marked as
   requiring re-derivation and left failing until that happens.

**Model version stamping (cheap, strongly recommended for `N2`)**: stamp `Win32API.lean`'s
hooks with a version tag, and have every contract discharged against a hook record the version
it was proven against (e.g. a `REF`-adjacent comment or a structured field). A model-version
bump then makes step 7's obligation *mechanically discoverable* — a linter (sibling to the
existing `check_refs.py`/doc-facade-linter family) flags any contract whose recorded version
predates the hook's current version as needing re-justification, rather than relying on someone
remembering to run the blast-radius query by hand every time.

This workflow applies identically to the IAT trust finding (§10) — a divergence there is a
defect in `loadMemory`'s convention, not in the harness that measured it.

---

## 8. `VirtualAlloc`/`VirtualFree` real semantics (closes C4)

The `VirtualAlloc`, `VirtualFree`, `VirtualQuery`, and `GetSystemInfo` pages are not registered in
`references.json`; registering them is an entry gate for this section. The probes below describe
the required validation shape, not source-backed outcome claims yet:

**Probe: distinct-pointer invariant.** Two consecutive `VirtualAlloc(NULL, 0x1000,
MEM_RESERVE|MEM_COMMIT, PAGE_READWRITE)` calls in one probe process. **Invariant**: two
non-null, distinct addresses, both `% 0x1000 == 0`. The probe additionally calls
`GetSystemInfo` and reports `dwAllocationGranularity`/`dwPageSize` directly, rather than this
design asserting a fixed 64 KB figure. The exact rounding and query contracts must come from the
future registered sources, not from this document. This probe is intended to falsify `virtualAllocHook`'s
current `0x20000000` constant (`Win32API.lean:134`) as a regression probe per §7 step 3.

**Probe: size-respecting allocation.** Allocate `0x1000` bytes, VEH-guarded (as
`HardwareHarness.lean`'s `buildTestText` VEH handler, `:87-109`) write attempt one page past the
requested region, plus a `VirtualQuery` call to report the *actual* granted region size (which
may exceed the request under allocation-granularity rounding) rather than assuming
requested-size equals granted-size.

**Probe: `VirtualFree` then re-access.** Free a region, VEH-guarded read attempt. **Invariant**:
access violation — falsifies `virtualFreeHook`'s "always returns 1, tracks nothing"
(`Win32API.lean:138-142`).

---

## 9. Socket harness scope (feeds N3; closes C5) — loopback sufficiency answered (Q4)

The review's answer to round 1's Q4: loopback is sufficient for everything this section pins,
**except** `recv` short reads, which are reachable but not reliably producible over loopback's
low latency and generous default buffering without deliberate staging. Fix, inside loopback,
rather than requiring cross-machine/cross-NIC infrastructure this project doesn't have:

- Set a small `SO_RCVBUF` on the server-side socket (`setsockopt`) to constrain how much can
  buffer before a `recv` call is forced to return short.
- A staged sender: the client `send`s a buffer larger than the constrained receive buffer, and
  the rendezvous protocol (§1.3's channel, extended to the socket probe pair) has the server
  probe report each `recv`'s byte count as its own phase, letting the controller confirm a
  genuine multi-call short-read sequence rather than guessing at buffer-size interactions.
- **MTU/latency omission is explicit, not silent**: this section's scope, per Law 5 and
  `docs/DECISIONS.md` §1, does
  not attempt to exercise real-WAN segmentation or latency-driven short reads — those remain
  named as out of scope rather than silently absent, matching the NOT-MODELED-list discipline
  §4.0 established for `ReadFile`.

**Architecture**: a probe pair (server, client) on `127.0.0.1`, both spawned by the controller,
each with its own inherited rendezvous pipe (§1.3) — the server probe reports `.phaseListening`
before the controller spawns the client, resolving round 1's unimplementable ordering
requirement the same way §4.2 was resolved.

**Pinned probes for `N3` to build against** (unchanged in substance from round 1, restated as
invariants. The WinSock function contracts are registered individually as
`windows-winsock2-*`; the numeric error-code table is not registered and is an entry gate):
- Blocking `accept` with no pending connection, then a connection arrives — replaces
  `acceptHook`'s `rip := 0` invention (`Win32API.lean:176-178`).
- Three-way `recv` distinction: data available, peer gracefully closed (`0` bytes),
  `SOCKET_ERROR`/`-1` + a real `WSAGetLastError` code — e.g. `WSAECONNRESET (10054)`
  (provisional value; source intake required) — as three separately observable outcomes.
- Short reads on `recv`, per the `SO_RCVBUF`-staged mechanism above.
- `bind`-to-in-use-port negative control: `WSAEADDRINUSE (10048)`
  (provisional value; source intake required).

This section stops at scope, not implementation — `N3`'s own design doc is where the concrete
hook rewrites land.

---

## 10. IAT/loader re-keying plan, restated around soundness properties (M5)

### 10.1 What "dump the real post-load IAT" means, concretely

Unchanged in mechanism from round 1: a dedicated IAT-dump probe, built with the same
`emitPE32ExecutableMultiDll`/`groupImportsByDll` machinery `WindowsExecutable.emit` already
uses, importing exactly `WindowsExecutable.imports`' default set. The probe walks its own PE
headers in its loaded memory image (DOS header → NT headers →
`OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_IAT]`, index 12, and
`[IMAGE_DIRECTORY_ENTRY_IMPORT]`, index 1, for the name correlation via `OriginalFirstThunk`),
reads each slot's live 8-byte value, and reports `{slotIndex, functionName, resolvedVA}` for
every import over the rendezvous channel (§1.3 — no special-case reporting mechanism needed
now; see §1.3's Q6 resolution).

**`imageBase`/ASLR as a measured invariant, not an aside (recommended item, promoted).** The
probe additionally compares its own `GetModuleHandle(NULL)` against its linked `imageBase`
(`0x140000000`) and reports whether the real loader honored or relocated it. This matters
beyond curiosity: the `0x140000000` image-base assumption is repeated across the PE emitter,
`WindowsExecutable`, and both hardware harnesses rather than derived from one checked source,
and `HardwareHarness.lean` emits absolute VAs that only work *because* the loader has, so far,
honored the requested base — this design does not fix that (it is a separate,
larger item), but it must not silently assume the fact away either; the probe measuring it
directly is the honest way to carry the dependency forward.

### 10.2 What it's diffed against

Two things, per round 1 (unchanged): the structural sanity check (no real resolved VA equals
its own slot address), and `loadMemory`'s currently-synthesized IAT for the equivalent import
list, confirmed to differ from the real dump in exactly the expected way.

### 10.3 Soundness properties, not just key properties (M5's central correction)

Round 1 specified only *key* properties ("VA-keyed, load-time, no self-reference, no positional
arithmetic") — properties of how the lookup is structured, not properties of whether the
lookup is *safe*. Three soundness properties `N2`'s fix must establish, named explicitly because
their absence is where the actual risk lives:

- **S1 — no false positives.** The reserved pseudo-VA range `loadMemory` assigns must be
  provably disjoint from every mapped section's address range (`.text`, `.rdata`, `.idata`
  themselves) — a call target that happens to land inside a real section must never be
  misidentified as an IAT dispatch target.
- **S2 — injectivity.** Distinct imported functions get distinct pseudo-VAs; no two hooks can
  ever be confused by the lookup.
- **S3 — fail-closed.** A call target that falls *inside* the reserved pseudo-VA range but is
  *absent* from the VA→hook table must be a hard fault, never silent fallthrough. This is the
  most important of the three and the one round 1's design implicitly made worse, not better,
  than today's code: `interceptCall`'s current `| _ => none` (`Win32API.lean:273`) fails open,
  but today that fallthrough still lands on whatever's actually mapped at that address (a
  real section, likely containing real bytes) — under a naive reserved-range scheme, a call
  target inside the reserved range with no table entry would fall through to `loadMemory`'s
  `| none => 0` default (`:308`), i.e. an address that decodes as the byte `0x00` repeated,
  which is `add [rax], al` — an infinite silent misexecution, *worse* than today's behavior, not
  better. `N2` must make this case a hard fault (an explicit `Except`/panic path), not rely on
  the existing default byte value to do something reasonable by accident.

### 10.4 Index 6 is explained, not unexplained (M5's factual correction)

Round 1 called the dispatch table's `some 5 → some 7` jump (no `some 6` arm) "unexplained." It
is not: `Emitter.lean`'s `buildMultiDllIDataSection` (`:53-146`) writes, per DLL, each real
import's IAT slot followed by **one null-terminator slot** (`:97`, `"idata := pushUInt64LE idata
0 -- Null terminator for this DLL"`), i.e. a stride of `(fns.length + 1) * 8` bytes per DLL —
exactly matching `loadMemory`'s own stride arithmetic (`Win32API.lean:304`,
`(fns.length + 1) * 8`). `WindowsExecutable.imports`' default KERNEL32 list has exactly 6
functions (`GetStdHandle, ReadFile, WriteFile, ExitProcess, VirtualAlloc, VirtualFree`), so
indices 0–5 are real imports and **index 6 is that DLL's null terminator** — a slot
`loadMemory` never writes a self-referential sentinel into (it falls through to the
memory-map's `0` default), so `findIatIndex`'s `s.read64 addr != addr` check correctly returns
`none` there, and index 7 is `ws2_32.dll`'s first real import (`wsaStartupHook`). This is not a
gap; it's the null terminator every `.idata` import table has, working exactly as the PE format
requires (the import-directory section of registered source `windows-pe-format`).

**The live latent bug this same arithmetic actually names (new, per the review).** The dispatch
table (`Win32API.lean:255-273`) is **positional across the entire IAT, keyed on absolute index,
not per-DLL relative index** — `some 7 => wsaStartupHook` hardcodes "the 8th absolute slot is
WSAStartup," which is only true because KERNEL32's import list currently has exactly 6 entries.
Adding a single new KERNEL32 import (e.g. `CreateFileA`, needed by §4's own probe-fixture
infrastructure if it were ever run through this dispatch table rather than a probe's own direct
IAT-slot calls) shifts KERNEL32's null terminator from index 6 to index 7 and `ws2_32.dll`'s
first import from index 7 to index 8 — but the dispatch table's `some 7 => wsaStartupHook` arm
does not move with it. Under the current fail-open `| _ => none` default, this means **every
WinSock hook silently stops being intercepted the moment a single new KERNEL32 import is
added**, with no error, just ordinary (wrong) instruction execution against whatever bytes sit
there. Per Law 13's "check ∀, fix ∀": this wants a **kernel-checked theorem** ("dispatch agrees
with the import list for every import list `WindowsExecutable.imports` can hold" — finite and
provable, since the import list is data, not a probe, since the world isn't being sampled here,
the model's own internal consistency is), not a probe — named explicitly here so `N2` doesn't
treat it as already covered by the IAT-dump probe battery, which measures the *real OS*, not
this *internal* consistency property.

### 10.5 Answering Q3: the real-vs-pseudo-VA axis was the wrong question

Round 1's Q3 asked whether gasm's synthesized pseudo-VAs need to resemble the real loader's
ASLR'd output more closely. The review's answer: parameterize instead. `loadWindowsProcess`/
`loadMemory` should take a **VA-assignment function** (imported-function-identity → chosen VA)
as an explicit parameter, and the trace-equivalence theorems this design feeds should be stated
`∀ (assign : VaAssignment), S1 assign → S2 assign → S3 assign → <trace equivalence holds>` —
universally quantified over *any* assignment satisfying the three soundness properties above,
rather than pinned to one measured set of addresses from one boot of one machine. Under this
framing, the real loader's actual (ASLR'd, per-boot-varying) VAs and gasm's synthetic ones are
both simply *inhabitants* of the same universally-quantified statement, and T6 closes as a
**proof obligation over the assignment class**, not a one-time measurement fed into the model —
feeding the harness's observed VAs directly into the model, as round 1's Q3 half-proposed,
would have pinned the model to a single non-reproducible fact about one run.

### 10.6 Residual — what closing T6 does *not* buy (named explicitly, per the review)

Even with S1–S3 established and the `∀`-over-assignments theorem proven, the model remains
faithful **only for programs that never inspect their own IAT contents as data** — that is,
programs whose only use of an IAT slot is to `call` through it, never to read the slot's VA
value and compute on it (self-relocation tricks, VA-dependent fingerprinting/hashing, pointer
arithmetic relative to a resolved import address). A real loaded IAT slot holds a real,
information-bearing virtual address; gasm's assigned pseudo-VAs are opaque symbols with no
numeric relationship to anything else in the loaded image. Recording this residual explicitly
is the point of this subsection: without it, T6 would get marked closed with a smaller,
un-cataloged T6 still alive inside it — exactly the kind of quiet re-narrowing Law 9's
domain-shrinking concern exists to catch.

---

## 11. Reference-registry status and intake gates (M7)

The repository does not vendor specification prose. Current authoritative sources are
hash-pinned metadata entries in `references.json`, with content fetched into the gitignored
cache only for validation (`docs/REFERENCE_INDEX.md`).

**Registered and usable by this design:**

- `windows-readfile` for §3–§6's symbolic `ReadFile` outcomes.
- `windows-writefile`, `windows-getstdhandle`, and `windows-exitprocess` for their respective
  function contracts.
- `windows-pe-format` for §10's import/IAT layout.
- The nine `windows-winsock2-*` per-function entries for the socket function contracts used in
  §9: `accept`, `bind`, `closesocket`, `listen`, `recv`, `send`, `socket`, `WSACleanup`, and
  `WSAStartup`.

**Required intake before the affected probes or claims become normative:**

- Microsoft system error codes, including the numeric bindings in §3/§6 and WinSock error
  codes in §9.
- `GetLastError`, for the per-thread and reset/persistence semantics used in §1.3 and §6.
- `VirtualAlloc`, `VirtualFree`, `VirtualQuery`, and `GetSystemInfo`, for §8.
- `CreateFile`/`CloseHandle`, for disk and handle-lifecycle fixture construction.
- `CreatePipe`, `CreateNamedPipe`, and named-pipe state APIs, for the short-write fixture and
  any future message-mode/`ERROR_MORE_DATA` coverage.
- `WriteConsoleInput` and any required console-mode APIs before console reads leave §4.7's
  explicitly unsupported scope.

These are registry additions, not requests to restore `references/windows/**`. Each must name an
official upstream URL, pin the exact bytes and edition, and pass the Law 6 cache/hash/anchor
validation before a model theorem or probe treats it as ground truth.

---

## 12. Design-review questions — resolved, restated, or superseded

Round 1's six questions, per the reviewer's own answers, plus what remains genuinely open:

1. **Resolved, but not as guessed.** The controller/probe split was right; the channel was
   wrong, for the concrete reason M3 identified (unimplementable rendezvous), not the
   filesystem-nondeterminism concern the question speculated about. §1.3's named-pipe
   redesign is the fix.
2. **Resolved: neither original option.** Recorded calibration was never primary, and per M8
   the fallback is deleted entirely rather than demoted — §4.7.
3. **Resolved: the axis itself was wrong.** Not "how real-VA-shaped must the pseudo-VA be" but
   "`∀` over any VA assignment satisfying S1–S3" — §10.5.
4. **Resolved.** Loopback is sufficient for everything §9 pins except `recv` short reads, fixed
   inside loopback via `SO_RCVBUF` staging; MTU/WAN latency stays explicitly out of scope — §9.
5. **Open behind source intake.** The five symbols in §6 are the outcomes this design's own
   probes produce, but their numeric bindings are not normative until the Microsoft system-error
   source is registered (§11). After that intake, expand the table only for a concrete probe or
   spike rather than speculatively.
6. **Resolved as a non-issue.** The IAT-dump probe does not need the side-channel exception at
   all once reporting goes over the inherited rendezvous pipe (§1.3) rather than a
   self-opened file — no import-count/stride risk remains to invert.

**Genuinely new questions for this round**:

7. §10.4's newly-named latent bug (positional dispatch shifting under a KERNEL32 import-list
   change) is scoped here as "`N2` should add a kernel-checked theorem." Is that the right
   priority relative to `N2`'s other committed work, or does this specific latent bug (silent,
   total loss of WinSock interception) warrant being pulled forward as its own small fix ahead
   of the rest of `N2`, given it's a live bug in the *current* tree, not a consequence of this
   design's changes?
8. §4.0 recommends sound over-approximation as `readFilePermitted`'s default characterization
   mode. Given the disk and pipe symbolic cases are pinned by `windows-readfile` (§4.0's
   three-legged comparison, leg 1), is exact characterization actually achievable — and
   preferable — for those two cases specifically, reserving over-approximation only for
   whatever residual nondeterminism §2's repeated-trial probing actually observes (as opposed
   to adopting over-approximation as a blanket default before that evidence exists)?
9. **Resolved for function contracts:** the WinSock function pages are registered individually
   as `windows-winsock2-*`. The remaining intake gate is the authoritative WinSock numeric
   error-code source used by §9.
