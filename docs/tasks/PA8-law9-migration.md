---
id: PA8
title: Law 9 migration — Spike5 domain-shrinking fix, then Tier-1 real env quantification
status: ready
blocked_on: ""
after: [PA6]
related: [B7]
bar: ""
track: proof-arch
priority: 9.4
priority_set: 2026-08-28T02:00:00Z
design: ""
design_review: ""
date: 2026-08-27
---

# PA8: Law 9 migration — Spike5 domain-shrinking fix, then Tier-1 real env quantification

## Context

This task executes the migration PLAN.md's Phase 4 has been building toward: moving the spikes off
pointwise/domain-shrunk `*_inst` verification and onto real Law-9-compliant universal quantification
over the canonical `Environment` type. `TASKS.md` phrases the ordering explicitly: "Spike5
singleton-domain fix first (also unblocks zlib epic), then tier-1 spikes (1,2,3-Wasm) to real env
quantification; shrink grandfathered allowlist." Follow that order — it is not incidental, as
explained below.

### The census this task must work from — quoted in full

PLAN.md's "Added by Opus review wave" findings ledger completed a full census of every spike's Law 9
posture, organized into three tiers. This is this task's primary input; do not re-derive it from
scratch, but do re-verify each item against current code before fixing it (the spikes have had
active development since this census was taken):

> **Complete Law 9 mock-verification census** (from linter warnings + re-review triage of all 16):
> **TIER 1** (constant fn ignores env — verbatim REVIEW.md violations): Spike1 Win+Wasm, Spike2
> Win+Wasm, Spike3 Wasm. **TIER 2** (**domain-shrinking evasion** — NEW finding): Spike5's
> `inductive GzipOp | compress` / `GunzipOp | decompress` are SINGLE-CONSTRUCTOR types, so `∀ op`
> quantifies over one element while spec ignores the parameter
> (`Spike5Gzip/Equivalence.lean:96-110,122-149`) — passes linter and casual Law 9 reading. **TIER 3**
> (legit pattern): Spike4's `HttpRoute` (3 constructors, exhaustive cases) and Spike3-Windows' `Bool`
> — genuine finite-∀ composition; their constituent theorems arguably deserve a
> `finite-forall-component` category. → **Phase 4 priority order: Tier 2 (Spike5) first (it's also
> the gzip epic bed), then Tier 1.** Gate question for Phase 4 design: mechanical prevention for
> domain-shrinking = contracts must quantify over the CANONICAL Environment type, not spike-defined
> input enums.

Grep-confirmed at time of writing: `Spikes/Spike5Gzip/Equivalence.lean:96` and `:108` define
`inductive GzipOp where | compress` and `inductive GunzipOp where | decompress` — single-constructor
types. A theorem universally quantified over `GzipOp` is, in substance, a theorem about exactly one
value, dressed in `∀`-notation that passes both the linter and a casual Law 9 reading. This is a
sharper evasion than Tier 1's outright constant functions, precisely because it looks compliant —
treat Tier 2 as the harder and more instructive fix, not a lesser version of Tier 1.

### Why Spike5 goes first: it is also the gzip optimization epic's bed

The census's ordering ("Tier 2 (Spike5) first — it's also the gzip epic bed") is not just
priority-by-severity; it is a scheduling dependency `TASKS.md`'s Performance path makes explicit:
`F6 zlib-to-infinity epic — after: PA8 (Spike5 honest), PA4 (Zlib capabilities), F4, TC12`. The
"zlib to infinity" candidate epic (PLAN.md's post-repair proving ground for the whole thesis —
optimizing zlib against zlib-ng/libdeflate-class baselines) cannot start from a Spike5 whose
verification is a single-instance domain-shrinking artifact: optimizing "the one case the spec
covers" is meaningless, and any optimization work built on Spike5 before this task lands would be
built on a foundation that does not actually constrain the implementation the way it appears to.
Fixing Spike5's domain-shrinking is therefore this task's highest-leverage first move, both because
it is the most instructive Tier-2 case and because it is a hard blocker for F6.

### Why Tier 1 comes after, not first

Tier 1's constant-function violations (Spike1 Win+Wasm, Spike2 Win+Wasm, Spike3 Wasm — verbatim
`docs/REVIEW.md` Law 9 violations, meaning the "spec" is a function that ignores its environment
argument entirely) are more obviously wrong but individually lower-leverage: no other task in
`TASKS.md` is gated on them the way F6 is gated on Spike5. Fix Spike5 first, then work through the
Tier 1 list; do not let Tier 1's larger item count (five spike/target combinations vs. one) tempt
front-loading it over the single higher-leverage Spike5 fix.

### The mechanical-prevention question this task must actually answer, not just satisfy

The census poses a design question for Phase 4 that this task inherits directly: "mechanical
prevention for domain-shrinking = contracts must quantify over the CANONICAL Environment type, not
spike-defined input enums." This is the Law-13 "findings become gates" obligation applied to this
exact defect class — fixing Spike5's and Tier 1's instances without also closing off the *general
mechanism* (a spike author defining a new single/few-constructor enum as their `∀`-domain instead of
using `Environment`) would leave the next spike free to reintroduce Tier 2's evasion in a new
guise. This task should therefore produce, alongside the concrete fixes, a mechanical answer to that
question — e.g. a build-time check or a type-level constraint that a `VerifiedProgram`'s (or its
PA9 successor's) environment-quantification type must be `Environment` itself (or a type provably
in bijection with the fields of `Environment` that the routine actually reads), not an
independently-defined enum. `docs/tasks/TC18-fuel-and-environment-honesty.md` covers the sibling
`Environment` dead-fields problem (four of six `Environment` fields have zero readers, per
`MODEL_DEBT.md` §C7 — the ∀ is "universal in form, 2-dimensional in substance"); this task's
domain-shrinking fix and TC18's dead-field fix are two sides of the same vacuous-∀ coin and should
be cross-checked against each other, though TC18 is a separately tracked task and this task should
not duplicate its scope.

### Why this depends on PA6 (and PA7, but only for the Spike4 slice)

`TASKS.md` states this task's dependency precisely: "after: PA6 (+PA7 for Spike4)." Read that
parenthetical literally — **PA7 is required only for the portion of this migration that touches
Spike4**, not for the whole task. Spike4 (`Spikes/Spike4HttpServer/`) is a reactive HTTP server, and
its Tier-3 `HttpRoute` verification is a genuine finite-∀ composition today, but Spike4 is exactly
the kind of non-terminating/reactive program `docs/EQUIVALENCE_PROOFS.md` §1.1 says must be verified
via `VerifiedReactiveProgram`'s mandatory inner/outer pair (PA7's deliverable) — so re-expressing
Spike4's verification in a way that is both Law-9-honest *and* structurally correct for a reactive
program needs PA7's contract type to exist first. The Tier-1/Tier-2 spikes this task must migrate
first (Spike1, Spike2, Spike3, Spike5) are not reactive-loop programs, and their migration does not
need PA7 — only PA6's read-binder contract shape (the general dependency for this whole task,
because migrating a spike off domain-shrinking/constant-function verification means re-stating its
contract in terms of real `∀`-quantified reads, which is exactly what PA6 specifies). Do not block
the bulk of this task's work on PA7 landing; sequence Spike4's re-verification specifically after
PA7, and the rest of the migration after PA6 alone.

## Deliverables & acceptance criteria

- Spike5 (`Spikes/Spike5Gzip/`) re-verified with `GzipOp`/`GunzipOp` (or their replacement) actually
  ranging over a real domain — either eliminated in favor of directly quantifying over
  `Environment`/the real gzip input `ByteArray` domain per PA6's read-binder contract shape, or
  legitimately widened to a multi-constructor type whose cases the spec genuinely branches on (the
  task should prefer the former, consistent with the census's own gate question about quantifying
  over the canonical `Environment` type rather than a spike-defined enum).
- Tier 1 fixed: Spike1 (Windows + Wasm), Spike2 (Windows + Wasm), Spike3 (Wasm) re-verified so their
  specs genuinely consume their environment argument — no constant function standing in for a
  `∀ env` claim.
- Spike4's Tier-3 `HttpRoute` verification re-expressed as a `VerifiedReactiveProgram` inner/outer
  pair once PA7 lands, preserving its legitimate finite-∀ composition property (3 constructors,
  exhaustive cases) rather than discarding it — Tier 3 was correctly identified as a *legitimate*
  pattern by the census, so this slice of the task is a re-framing, not a rewrite-from-scratch.
- A mechanical prevention for the domain-shrinking evasion class generally (not just Spike5's
  instance): a build-time check, type-level constraint, or equivalent gate answering the census's
  posed question — contracts must quantify over the canonical `Environment` type (or a type
  provably equivalent to the fields it actually reads), not a spike-defined input enum. State the
  mechanism chosen and why it closes the *class*, per Law 13.
- The grandfathered `*_inst` allowlist (`scripts/gate_allowlist.txt`) shrunk to reflect every
  migrated spike's removal from pointwise-verification status — PLAN.md's repair-epic exit
  criterion tracks this as a trend ("grandfathered allowlist shrinking (trend, not zero)"), so this
  task's completion report should state the before/after allowlist size for the migrated spikes.
- All migrated theorems are `∀`-quantified over their real domain and discharged by kernel-checked
  structural proof; `native_decide`/`decide` is never a substitute for the infinite-domain
  quantification this migration exists to restore (Law 10) — the whole point of this task is that
  these theorems stop being satisfiable by exhaustive/degenerate evaluation.
- Zero `sorry`, zero unauthorized axioms in migrated modules (`lake build` + `lake exe
  check_gates_axioms` clean); `scripts/check_refs.py` clean, citing `docs/REVIEW.md` Law 9 and this
  task's own design/consolidation doc.
- Completion report re-verifies each census item against current code (the spikes have had active
  development since the census was taken) and states explicitly if any item's status has changed
  (fixed already, worsened, or a new Tier-2-shaped evasion introduced elsewhere) before claiming it
  closed.

## Pointers

- PLAN.md's "Complete Law 9 mock-verification census" entry (quoted above, in full) — this task's
  primary input; re-verify against current code before acting on it.
- `Spikes/Spike5Gzip/Equivalence.lean:96` (`inductive GzipOp where | compress`), `:108` (`inductive
  GunzipOp where | decompress`) — grep-confirm current line numbers, this file is part of the
  actively-developing zlib/gzip surface.
- `Spikes/Spike1.../`, `Spikes/Spike2.../`, `Spikes/Spike3.../Wasm/Equivalence.lean` (Tier 1 —
  locate exact paths by grep; the census's own line-item names them Win+Wasm for Spike1/2, Wasm
  only for Spike3).
- `Spikes/Spike4HttpServer/Equivalence.lean` (Tier 3 — `HttpRoute`, 3 constructors, exhaustive
  cases; the portion of this task gated on PA7).
- `docs/tasks/PA6-read-binder-contract.md` — the direct prerequisite for the bulk of this
  migration; its contract shape is what Spike1/2/3/5's re-verification should be expressed against.
- `docs/tasks/PA7-verified-reactive-program.md` — the prerequisite for Spike4's slice only, per the
  parenthetical dependency explained above.
- `docs/tasks/TC18-fuel-and-environment-honesty.md` — the sibling `Environment` dead-fields task;
  cross-check but do not duplicate scope.
- `MODEL_DEBT.md` §C7 (`Environment` dead fields — the vacuous-∀-in-substance sibling problem) and
  TOP-10 table item 8.
- `docs/REVIEW.md` Law 9 in full (`docs/adr/0015-read-as-universal-binder.md` for the read-binder
  half of Law 9 specifically), Law 13 (findings become gates — the mechanical-prevention
  obligation; `docs/adr/0009-findings-become-gates.md`), Law 10 (kernel-checked proof requirement;
  `docs/adr/0002-native-decide-restricted-to-exhaustive-finite-domains.md`).
- `TASKS.md`'s Performance path, `F6 zlib-to-infinity epic` line ("after: PA8 (Spike5 honest)...")
  — confirms Spike5's fix is a hard scheduling dependency for F6, not just a priority preference.
- `scripts/gate_allowlist.txt` — the grandfathered-allowlist artifact this task's completion report
  should show shrinking.

## Notes

- 2026-08-27: priority 6.5 — Law 9 migration (Spike5 domain-shrinking fix + Tier-1 real-env quantification) closes a known universal-quantification gap once PA6/PA7 land.
- 2026-08-27 (oracle-debt audit, `docs/ORACLE_DEBT.md` Part 6): priority raised 6.5 → 9.4. Re-derived
  from `docs/ORACLE_DEBT.md`'s coverage matrix: this task's Tier-1 + Tier-2 fixes are the *only*
  existing-task coverage for 8 of the 37 `grandfathered` allowlist entries (Spike1 Win/Wasm, Spike2
  Win/Wasm, Spike3 Wasm, and 3 of Spike5's 5 entries), which the owner has named the top priority in
  the repository. Also noting for this task's Wasm-target slice (Spike1 Wasm, Spike2 Wasm, Spike3
  Wasm, Spike5 wasm_gzip): `docs/tasks/B7-wasm-oob-trap-and-limits.md` is concurrently changing
  `Gasm/Targets/Wasm/Semantics.lean`'s trap-handling paths; none of these four routines perform an
  out-of-bounds access, so no hard `after` edge is added, but re-verify against B7's post-fix
  semantics if B7 lands first, to avoid a proof stated against a since-superseded model.

_(none yet — first entries append here as work begins; this is Law-5-class proof-architecture
work — consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch; do not waive review on this track.)_
