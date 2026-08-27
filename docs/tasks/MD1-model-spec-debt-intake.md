---
id: MD1
title: Model/spec debt intake queue
status: ready
blocked_on: ""
after: []
related: []
bar: ""
track: debt-intake
priority: 5.5
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# MD1: Model/spec debt intake queue

## Context

`MODEL_DEBT.md` is a 190-entry-equivalent inventory (sections A–F plus a target-class tag table)
of everything the x86-64/Wasm/OS/system-performance models currently omit or simplify, produced by
an Opus deep audit on 2026-08-27. Per its own framing and `docs/VISION.md` §3.3 (D7 — demand-driven
model growth): this is a ledger, not a backlog to clear — "Debt is chosen, not discovered." Most of
its entries already have a named forcing function and a place in the DAG: A1 (dependency-chain
cost) and A4 (branch-prediction) feed F3; A8 (uncited coefficients) feeds F3/F2; C1/C8 (short
reads) feed N1/N2; B7/B8 (Wasm OOB/limits) are explicitly on PLAN.md's Phase-3 list; E1/E2 feed
G8; F2 (constant-time) is N7; F4 (deadline contracts) is a GE-class item with no current spike
forcing it.

This task exists to hold the entries that **do not yet have a clean home** — either because no
current task's scope obviously covers them, or because they're genuinely "wait for a forcing
function" items per D7, and someone needs to periodically re-triage the ledger against the live
DAG rather than let items silently rot unscheduled. This is deliberately a thin, standing task
(closer to a recurring review checkpoint than a one-shot deliverable) — its "acceptance criteria"
is a triage pass, not a fix.

### Entries with no current task-DAG home (as of this conversion)

Cross-referencing every `MODEL_DEBT.md` entry against `TASKS.md`'s tasks, the following have no
task currently claiming them:

- **A0 — no memory hierarchy at all** (no L1/L2/L3/TLB/store-buffer modeling; every load is a
  flat `latencyCycles := 4`). TOP-10 item 7. Forcing function: LZ77 window/table-layout tuning in
  the zlib-to-infinity epic (F6), but no task currently owns *building* the hierarchy model itself
  — F3's "staged model calibration" covers uop/latency tables, dependency chains, branch model,
  then "hierarchy (A0)" last, so A0 has a home in F3's staging order but is worth flagging here
  since it's explicitly the *last* stage and the largest-cost item ("L — needs an address/
  working-set abstraction the uop model lacks").
- **A2 — port-pressure uniform-spread approximation** (not a real scheduling LP). No task
  currently names A2 specifically; it's implicitly inside F3's "uop/latency tables" work but should
  be called out explicitly when F3 is scoped, since TOP-10 doesn't rank it in the top 10 and it
  could be silently dropped.
- **A3 — five of nine `MicroarchProfile` fields and one of five `X86_64Uop` fields are dead**
  (`reciprocalThroughput`, `fetchBandwidthBytes`, `renameWidthUops`, `retireWidthUops`,
  `robCapacityUops`, `optMode` — zero read sites). TOP-10 item 9, bundled with B1's doc-overclaim
  fix ("Reconcile `X86_64.md` §3 TSO claim + dead profile fields with the code"). No task currently
  claims the A3 half specifically — either fold into F3's scoping or take as a small standalone
  Law-8 dead-abstraction cleanup (delete-or-wire the six fields) ahead of F3.
- **A5 — no fusion, front-end limits, alignment, store-forwarding, TLB, frequency**. Named as
  part of F3's staging implicitly (uop/latency tables), but not explicitly enumerated in any task
  file — flag for F3's scope-setting.
- **A6 — TMAM is unvalidatable dashboard output**, explicitly recommended for **demotion or
  deletion**, not calibration ("no class forces it" per the target-class tag table). No task
  currently owns deleting/demoting `computeTMAM`. This is a small, low-risk cleanup candidate that
  could be picked up standalone rather than waiting on F3.
- **B1 — TSO doc overclaim**. `TASKS.md`'s own header lists this explicitly: "TSO doc overclaim
  reconcile (doc fix, ready now)" — genuinely unclaimed by any lettered task. Cheap (a doc fix
  reconciling `docs/TARGETS/X86_64.md` §3's TSO/memory-type claims with the actual single-threaded
  total-function memory model) and explicitly called out as ready now with no blockers. **This is
  the single cheapest unclaimed item in the whole ledger and a reasonable first pick from this
  queue.**
- **B2 — no atomics/LOCK/fences/CPUID/RDTSC**. Forcing functions: any threaded spike (none exist
  yet) and the RDTSC harness (F1) — F1 needs `RDTSCP`/`CPUID` as modeled instructions or an
  explicit out-of-model harness escape hatch; confirm F1's scope actually covers this rather than
  silently assuming the harness can shell out around the gap.
- **B3 — no memory faults/permissions/canonicality/alignment**. Explicitly named as "what Law 11
  capabilities are for" — this is PA4's territory (capability adoption) but MODEL_DEBT.md's exact
  words are sharper than PA4's task file currently states: "until they bind, the memory model
  actively hides the bug class" — specifically the risk `Stdlib/Zlib/Windows.lean`'s hand-offset
  4096-byte scratch space represents. Confirm PA4 explicitly scopes in the Zlib/Windows.lean
  capability migration (its task file already lists this as "last/biggest" per PLAN.md) rather
  than treating B3 as automatically resolved by PA4 landing in general.
- **B4 — no FPU/SSE/AVX state**. Forcing functions named directly: SIMD CRC32/adler32 for the
  zlib epic (F6), the Windows ABI's XMM callee-saved obligations (currently unstatable), and
  Spike 6/7 entirely (G-track). No task currently owns *building* an XMM register file — this is
  a real gap: F6 and G-track tasks both assume FPU/SSE state will exist by the time they need it,
  but nothing currently commits to building it. Flag for whichever of F6/G6 reaches this
  dependency first to pull forward as its own sub-task rather than discovering the gap mid-work.
- **B5 — no FS/GS/TEB/TLS**. Blocks realistic Windows runtime interop; no forcing spike yet
  (demand-driven — correctly unscheduled per D7).
- **B6 — self-modifying/dynamically-generated code unrepresentable**. Tagged DB-class
  ("query JIT is a first-class use case") — no current task, correctly deferred (no DB-class spike
  exists yet).
- **C3 — no error model** (`GetLastError`, error codes). Partially covered by N1's design scope
  ("an error-path model... to the extent demand-driven growth justifies"), but MODEL_DEBT.md rates
  this as affecting all four target classes universally — confirm N1/N2 don't silently scope this
  down to nothing.
- **C6 — IAT/loader convention**. Now explicitly owned by N1 (design) and folded per the fourth
  amendment's instruction into N1/N2's briefs, and separately by `TCB.md` T6 / this conversion's
  TC-track coverage — **no longer an orphan as of this conversion**, listed here only so a future
  triage pass doesn't re-flag it as unclaimed.
- **E3 — storage performance model** (verified absent — `MonadFileSystem` is a four-method
  typeclass whose only implementation returns `ByteArray.empty`). No task currently owns building
  a storage cost model; E1/E2/E4 have F-track/G-track homes (G8 for PCIe, implicitly F-track for
  network), but E3 (disk) has none. DB-class forcing function; correctly low-priority absent a
  DB-class spike, but flag explicitly rather than silently dropping it — F6 (zlib epic) reads/writes
  files and could plausibly want a storage cost term before a full DB spike exists.
- **E4 — network performance model** (verified absent — `NetEvent` carries `String` payloads, no
  sizes, no timing). N6 ("networking buildout") is the natural home but its current task file
  scope is protocol semantics (TCP/HTTP/gRPC), not necessarily the *cost* model — confirm whoever
  picks up N6 also claims E4, or split E4 into its own perf-track task at that point.
- **F1 (disk durability), F3 (interrupts/privilege), F4 (audio/input + deadline contracts)** — all
  three explicitly named in `TASKS.md`'s own "Model/spec debt intake" closing paragraph as
  DB/OS/GE-class items to "schedule with TC9-era work" / "later." Correctly deferred; this queue's
  job is just to make sure "later" gets revisited rather than forgotten. F2 (constant-time/secrecy)
  is already N7 — not orphaned.

## Deliverables & acceptance criteria

This is a standing triage task, not a one-shot fix:

- On each pass: re-read `MODEL_DEBT.md` and the then-current `docs/tasks/` DAG; for every entry
  without a clear task owner, either (a) fold it explicitly into an existing task's scope (edit
  that task's `## Context`/pointers to name it), (b) spin up a new task file for it if it's grown
  a real forcing function, or (c) leave it here with a note on why it's still correctly
  unscheduled (D7 — no forcing function yet).
- Never silently "clear" an entry by scheduling it — an entry is only removed from this file once
  its owning task file exists and names it explicitly (grep-verifiable).
- B1 (TSO doc overclaim) is flagged above as the cheapest immediately-actionable item in the
  entire ledger — a reasonable default first pick, but not mandatory; state in the completion
  report (of whichever triage pass picks it up) that it was considered.
- Completion report per pass: which entries moved from "orphaned" to "owned," which new task files
  (if any) were created, and the updated orphan list.

## Pointers

- `MODEL_DEBT.md` in full — sections A (performance), B (correctness), C (OS/environment), D
  (graphics-forward), E (system-level transport/placement), F (class-forced items), and the
  TOP-10 priority table + target-class tag table.
- `TASKS.md`'s closing "Model/spec debt intake" paragraph — the original scope note this task file
  formalizes into a standing process.
- `docs/VISION.md` §3.3 (D7 — demand-driven growth; the governing principle for what stays
  unscheduled and why that's correct, not a failure).
- Every task file under `docs/tasks/F*`, `docs/tasks/G*`, `docs/tasks/N*`, `docs/tasks/PA*` whose
  `## Context` cites a `MODEL_DEBT.md` letter/number — cross-check those citations stay accurate as
  those tasks' scopes get refined during design/design-review.

## Notes

- 2026-08-27: priority 5.5 — model/spec debt intake queue is a standing triage process (like TC7 for TCB.md) rather than a single deliverable — useful ongoing hygiene, not a blocking dependency for anything.
- 2026-08-27: considered `related: [TC7]` (MD1 and TC7 are sibling ledger-triage processes for
  the model/spec vs. trust/proof debt classes) but did not add it: both MD1 and TC7 have no
  other graph edges, so a symmetric related link between only the two of them forms an
  isolated pocket that `scripts/task_frontier.py`'s PageRank recirculates almost losslessly,
  inflating both far above their actual leverage (empirically verified while building that
  tool — see its docstring). The conceptual link is real and worth a fresh agent's attention,
  but is left as this prose note rather than a `related:` edge until one of the two has other
  real connections to dilute into.

_(none yet — first entries append here as each triage pass runs; this task has no single
"design" to consolidate toward — it is a recurring process, not a Law-5-class deliverable, so
`design`/`design_review` stay empty indefinitely rather than progressing through the lifecycle.)_
