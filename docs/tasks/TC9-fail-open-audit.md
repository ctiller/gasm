---
id: TC9
title: Fail-open audit completion
status: implementing
blocked_on: ""
after: []
related: [TC17]
bar: ""
track: trust-core
priority: 7.5
priority_set: 2026-08-27T18:25:47Z
design: "inline"
design_review: "waived-mechanical"
date: 2026-08-27
---

# TC9: Fail-open audit completion

## Context

Two of this project's own oracles have already been caught silently failing open — the x86
hardware fuzzer (TC1) and the Wasm control-flow fuzzer (TC2), both found by adversarial review,
not by any gate. PLAN.md's Phase-3 tracker names the generalizable rule discovered from both
incidents: **"the x86 harness fail-open (catch → synthesized results) hid a total oracle
outage. Audit EVERY oracle/harness error path for the same class... Rule: an oracle that cannot
run must FAIL the run, never no-op or synthesize."** This task is that audit, generalized across
the rest of the tree, rather than assuming TC1/TC2 were the only two instances.

`docs/REVIEW.md` Law 13's preference-order item 4 states the target behavior precisely: for
harnesses that interact with the world (hardware, engines, OS) and therefore cannot be
theorems, mandatory positive and negative control vectors must both pass before any result
counts, and **"an oracle that cannot run must fail the run; it must never no-op, skip, or
synthesize results."** TC5 (the gate runner) already establishes fail-closed behavior at the
*orchestration* layer (abort the whole run if NASM/node is missing); this task is about the
*inside* of each individual oracle — what happens when the oracle itself, already invoked,
discovers mid-run that it cannot actually validate anything.

### The two named targets, and why they matter specifically

TASKS.md's one-liner names two concrete instances to fix: **"GzipFuzzer subprocess, spike
Test.lean 'sound (in-Lean)' fallback paths."**

**GzipFuzzer's subprocess handling** (`Stdlib/Zlib/GzipFuzzer.lean`): grep-confirmed at the time
of writing, `runOracleGunzip` (line 71) spawns a `python` subprocess and checks its exit code —
if the subprocess itself cannot be spawned (python absent from PATH), `IO.Process.spawn` raises
an IO exception that currently propagates uncaught rather than being turned into a labeled,
diagnosable failure; there is no explicit presence check for `python` before the fuzzer starts,
unlike TC1/TC2's post-fix NASM/node presence checks. TCB.md's ledger separately flags, in its
"One-line fixes to fold into TC5/TC9" note: **"GzipFuzzer.lean:84 reads binary .gz as UTF-8
lines, destroying its own diagnostic."** This is grep-confirmed still present: `runOracleGunzip`'s
error branch (line 83-85) does `let _stderr ← IO.FS.lines tmpGz` — it reads the *compressed
binary gzip file* as UTF-8 text lines (not even the subprocess's actual stderr stream, which was
piped and discarded), assigns it to an unused `_stderr` binding, and returns a generic "Python
gunzip oracle failed with exit code {exitCode}" message with no diagnostic content at all. On
any real divergence, the one thing that would help a human or agent understand *why* is
destroyed by this bug. Separately, `runGzipDifferentialFuzzer`'s `main` (grep-confirmed,
`GzipFuzzer.lean:209-232`) accepts `--count` with no floor: `--count 0` would print "0 TESTS
PASSED (100% SUCCESS)" and exit 0 — the same T11-b-shaped vacuity hole TCB.md documents
elsewhere ("`PerfFuzzerCLI --count 0` prints '100% SUCCESS' with no oracle at all").

**Spike Test.lean's "100% sound (in-Lean)" fallback** (grep-confirmed present, byte-identical
shape, in both `Spikes/Spike1Hello/Wasm/Test.lean:60-64` and `Spikes/Spike2Fibonacci/Wasm/
Test.lean`'s equivalent block): each spike's `Test.lean` tries a list of candidate host Wasm
runners (`node`, `wasmtime`, `wasmer`, `deno`), and if **none** are found on PATH, it prints
`"[i] Notice: No external Wasm CLI runner detected in PATH."` followed by `"In-Lean formal
verification succeeded (100% sound)."` and returns exit code `0`. This is precisely TC1/TC2's
disease in miniature: the in-Lean trace check is real and did pass, but the sentence "100%
sound" implies the spike's actual host-runtime behavior was validated, when in fact **zero
external validation occurred** — a machine with no Wasm runtime installed reports full success
indistinguishably from a machine that actually ran and passed the host-runtime check. TCB.md's
one-line-fixes note names this exact pattern for Spike1/Spike2's Wasm `Test.lean` files.

### This is explicitly an audit, not just two fixes

The task's name is "fail-open audit **completion**" — TASKS.md's one-liner gives two concrete,
already-known instances as a starting point, but per PLAN.md's Phase-3 framing, the actual scope
is **every** oracle/harness error path in the tree, generalized. A non-exhaustive list of other
candidates a fresh agent should check (grep for `catch`, `try`, subprocess-spawn call sites, and
any `IO.Process.spawn`/`.wait` pattern across `Gasm/`, `Stdlib/`, `Spikes/`, and `Tools/`):
`Gasm/Targets/X86_64/NASM.lean` (already partially hardened per TC1's history — confirm the
hard-error behavior is complete, not just improved); the Wasm `HostOracle`/node-spawn handling
generally (confirm TC2's fix covers every call site, not just the ones the reviewer happened to
exercise); `EncodingFuzzer.lean` (TCB.md's one-line-fixes note separately flags this file has
**zero** control vectors of any kind — the only oracle in the tree with none — which is a
control-vector gap, not strictly a fail-open bug, but the same Law 13(4) obligation applies and
this task is a natural place to close it alongside the audit); and any other spike `Test.lean`
files beyond Spike1/Spike2 that may share the same runner-fallback pattern (grep for the
literal string `"100% sound"` or `"In-Lean formal verification succeeded"` to enumerate all
occurrences, not just the two already named).

### Adjacent, explicitly out of scope

MODEL_DEBT B7/B8 (Wasm OOB-trap and `memory_grow` bounds — a live *soundness* gap in the Wasm
*model*, not a harness fail-open bug) is called out in TASKS.md's model-debt-intake note as
something to **"schedule with TC9-era work"** — i.e., temporally adjacent (same phase of
effort) but a different kind of defect (a model correctness gap, not an oracle-honesty gap). Do
not fold B7/B8 fixing into this task's scope; flag it as a sibling item to schedule alongside,
per TASKS.md's own phrasing, but this task's acceptance criteria are about oracle/harness
honesty, not ISA model completeness.

## Deliverables & acceptance criteria

- `GzipFuzzer.lean`'s subprocess-absent case (python not on PATH) fails the run with a labeled,
  diagnosable error — not an uncaught IO exception with an unhelpful backtrace and not a silent
  pass. Add an explicit presence check (mirroring TC1's NASM-presence pattern) before the fuzzer
  starts.
- `GzipFuzzer.lean:84`'s (or wherever it has moved to — verify by grep) UTF-8-lines-over-binary
  bug fixed: the actual piped stderr stream must be captured and surfaced in the failure
  message, not the compressed binary file misread as text.
- `GzipFuzzer.lean`'s `--count 0` (or any zero-iteration) case must not print a success message
  — either refuse to run with zero iterations, or require a nonzero minimum, mirroring TCB.md's
  vacuity-floor rule (T11-b) — coordinate with TC17 (vacuity floors) if that task's scope already
  covers this generically; do not duplicate work, but do not leave this instance unfixed if
  TC17 hasn't reached it yet.
- Every spike `Test.lean` file with the "no runner found → print '100% sound' → exit 0" pattern
  (at minimum Spike1Hello and Spike2Fibonacci's Wasm variants, confirmed present by grep; audit
  for others) changed so that a missing host runner is reported honestly as **"host-runtime
  validation did not run"** (or equivalent unambiguous wording) with a **non-zero exit code**
  when the CI/gate-runner context expects host validation to have occurred — per Law 13(4), an
  oracle that cannot run must fail the run, not no-op.
- `EncodingFuzzer.lean` gets at least one positive and one negative control vector (Law 13(4)) —
  currently the only oracle-shaped harness in the tree with zero control-vector compliance per
  TCB.md.
- A generalized audit pass across `Gasm/`, `Stdlib/`, `Spikes/`, and `Tools/` for the same class
  of bug (silent catch-and-synthesize, uncaught spawn failure, exit-0-on-vacuous-input), with
  any additional instances found either fixed here or filed as explicit follow-up items with
  file:line references preserved.
- Completion report must demonstrate, per Law 13(4)'s evidentiary bar: for each fixed oracle, a
  live demonstration that (a) the oracle passes with its dependency present and correct input,
  and (b) the oracle **fails the run** (non-zero exit, labeled diagnosis) with its dependency
  absent or given a known-bad input — a fix claimed without both directions demonstrated is not
  credible under this project's own review standard (see TC1/TC2's own completion evidence for
  the expected shape).

## Pointers

- `Stdlib/Zlib/GzipFuzzer.lean:71-107` (`runOracleGunzip`, `runOracleGzip`) — the subprocess-spawn
  call sites; line 84 is the UTF-8-over-binary bug (grep-confirmed present as of this writing:
  `let _stderr ← IO.FS.lines tmpGz` inside the error branch).
- `Stdlib/Zlib/GzipFuzzer.lean:209-232` (`main`) — the `--count`/`--seed` CLI parsing with no
  floor on iteration count.
- `Spikes/Spike1Hello/Wasm/Test.lean:60-64` and the equivalent block in
  `Spikes/Spike2Fibonacci/Wasm/Test.lean` — the "100% sound (in-Lean)" fallback pattern
  (grep-confirmed present at both locations at time of writing).
- `Gasm/Targets/X86_64/EncodingFuzzer.lean` — grep-confirmed present; the file TCB.md's one-line-
  fixes note flags as having zero control vectors.
- `Gasm/Targets/X86_64/HardwareHarness.lean:281-340` and `Gasm/Targets/Wasm/SemanticsFuzzer.lean`
  — the TC1/TC2 fail-closed precedents to imitate (`Except`-typed returns, mandatory pos/neg
  control checks that abort the run on failure).
- PLAN.md, "Phase 3 — Model validation expansion", the "**Fail-open audit**" bullet — the
  original scope note this task file supersedes; also TASKS.md's model-debt-intake note on
  scheduling Wasm OOB debt (B7/B8) alongside this task without folding it in.
- TCB.md's "One-line fixes to fold into TC5/TC9" note — the exact source of the GzipFuzzer and
  Spike1/2 findings this task must close.
- `docs/REVIEW.md` Law 13, preference-order item 4 — the governing standard for what "fixed"
  means here (mandatory pos/neg controls, fail-the-run on missing dependency).

## Notes

- 2026-08-27: priority 7.5 — fail-open audit completion folds in TCB's one-line fixes (EncodingFuzzer controls, Wasm Test.lean honesty, GzipFuzzer UTF-8) — closes the exact defect class TC1/TC2 already proved costly twice.
- 2026-08-27: related: [TC17] — TC9's fail-open audit and TC17's vacuity floors close two distinct but easily-confused failure modes (an oracle that silently no-ops vs. a suite that runs zero vectors and reports success); TC1/TC2's history is the shared precedent for both.

_(none yet — first entries append here as work begins; this looks like mechanical audit-and-fix
work following an already-established pattern (TC1/TC2's fixes), so an inline `## Design`
section in this file once work starts is likely sufficient — waived-mechanical design review —
unless the generalized audit surfaces a genuinely new class of fail-open bug not covered by the
TC1/TC2 precedent, in which case treat that specific finding as Law-5-class on its own.)_
