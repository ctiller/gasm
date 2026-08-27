---
id: TC4
title: Decoder + registry build-gate branch
status: done
blocked_on: ""
after: []
related: []
bar: bar-1
track: trust-core
priority: 8.5
priority_set: 2026-08-27T18:25:47Z
design: docs/TARGETS/X86_64.md
design_review: predates-discipline
date: 2026-08-27
---

# TC4: Decoder + registry build-gate branch

## Context

**Read this Context carefully before treating TC4 as closed** — TASKS.md marks it `[x]` done,
which is why this file's `status` is `done`, but PLAN.md's own narrative (as of the same
2026-08-27 writing) shows a fix cycle for coverage-regression findings still **RUNNING**, not
landed. TASKS.md's one-liner even says "MERGE TRAIN 3 now" rather than "merged" — treat that as
"in the merge-train pipeline," not "verified in the merged tree." A fresh agent picking this up
should re-confirm the fix cycle described below has actually landed (grep for the specific
mutation-fix markers listed in Pointers) before assuming TC4's gate is fully hardened.

### What this branch built

Sourced from PLAN.md's findings ledger ("Added by Opus review wave") and the "Decoder gaps +
REGISTRY GATE" Phase-1 entry (branch `worktree-agent-afbbc6cd975969059`). This is the concrete
realization of D9's "gate obligations from today's findings" note — "decoder gaps → registry
roundtrip gate" — and of D11's DSL thesis: **"the registry gate is the closed-population
exemplar"** for proving a whole language once instead of one instruction at a time.

An initial decoder-gap fix cycle (`4ff4970`) landed first: universally-quantified `∀`-`rel8`
theorems, `rel32`→`_inst` regression naming discipline, the previously-undecodable `0xE8` opcode
now decoded, an `0x8B` REX.W soundness bug fixed (a silent wrong-width decode — the kind of bug
Law 9/10 exist to make structurally impossible), and 9 more instructions decoded; the test count
grew 2981→3508.

The registry gate itself (`b1e0c95`) is the headline deliverable, and its design is authored in
`docs/TARGETS/X86_64.md` — a real Law-5 design section written inside this implementing branch's
files (chosen deliberately because that file was untouched by the concurrent Phase-0 docs edits,
avoiding a merge conflict). Grep-confirmed present at the time of writing: `docs/TARGETS/X86_64.md`
§"1. The `roundtripCases` typeclass field" and §"2. The registry and the environment audit"
describe exactly the mechanism PLAN.md's findings ledger specifies — a **defaultless**
`roundtripCases : List ι` field added to the `X86_64Instruction` typeclass (no instance compiles
without declaring its own finite roundtrip domain — 79 instances were forced to add one), a
`Registry.lean` with a `run_cmd` elaboration-time environment audit (any typeclass instance not
in the registry fails the build — this was itself mutation-verified), 21 gate shards each
discharged by plain `decide` (**zero `native_decide`** — a stronger discharge than Law 10 even
requires, since these are per-family exhaustive finite domains small enough for the kernel
evaluator), suites *derived* from the registry rather than hand-maintained, and the old
hand-written ground theorems deleted once the registry superseded them.

**The gate construction process itself caught 2 real, previously-unknown encoder bugs** before
any adversarial reviewer even looked at it: `LeaRipRel`'s REX.R/REX.B swap for registers r8–r15,
and the `0xC7` decoder ignoring the REX.B bit entirely. PLAN.md calls this out explicitly as
"Law 13 validated" — the mechanical gate found defects a targeted review would have had to get
lucky to spot. Cost: the registry gate added +30.5s to the build (Gasm library build went from
55s to 85.5s).

### The re-review: coverage regression, and why the branch isn't simply "done"

Re-review verdict was **MERGE-WITH-FIXES** — the gate *architecture* held (the reviewer
reproduced the mutation-catching claims and added mutations of their own), but found a real,
exploitable gap: **0 of 1419 test cases set both the REX.R and REX.B extension bits
simultaneously** — the reviewer's own mutation M3 miscompiled `add r8, r15` to instead write to
`RAX`, while every gate stayed green. The old hand-written 16×16 register-pair loops (deleted
when the registry landed) had covered all 64 "both-extended" pairs; the registry-derived
replacement didn't reproduce that coverage. Additional findings from the same review: the
audit's import-closure had a hole (an unimported instruction module is invisible to the audit —
mutation-confirmed); two more decoder siblings shared the `0x8D`/`0xC6` SIB-base-4 REX.B bug
class; the roundtrip diagnostic was weaker than the gate itself (no `toLean` clause to show
what actually decoded wrong); an **empty** `roundtripCases` list was legal, which is a
shrink-to-green escape hatch (an instance could satisfy the typeclass by declaring zero test
cases and pass vacuously); the gate suffered intermittent `std::bad_alloc` under 21-way parallel
`decide` invocation; and documentation overclaimed "not a pointwise sample" in a way the actual
coverage gap contradicted.

The fix cycle PLAN.md records as **RUNNING** (not confirmed landed as of this writing) covers:
both-extended-register witness cases plus boundary-immediate × extended-register combinations;
a REX.B class fix routed through `codeToReg64`; documentation honesty corrections; the umbrella
import + audit-hole fix; a strengthened `decodesOk`-shaped diagnostic; a non-empty-
`roundtripCases` assertion (closing the shrink-to-green escape hatch); and OOM mitigation for
the parallel `decide` crash.

A separately-designed follow-on ("Stage B", design-doc'd but explicitly **not** part of this
branch's scope — implemented later, protected by this gate once it lands) modularizes the
decoder itself: per-instruction `tryDecode` co-located with `encode`, a thin registry-driven
dispatcher, and per-family dispatch-reachability/exclusivity lemmas. This is deliberately
deferred to keep TC4 scoped; see PLAN.md's findings-ledger entry and TASKS.md's B3 task.

### BAR 1 — what TC4 (together with TC5) actually triggers

TASKS.md marks TC4 with `bar: bar-1` because TC4 landing (together with TC5, the gate runner)
is the scheduled **trigger** for BAR 1. It is important not to misread what a BAR reviews:
per `docs/adr/0010-bar-triggered-deep-re-reviews.md`, **"the scope of a bar review is always
the entire codebase, never the recent work"** — a fresh Opus agent, blinded to prior review
conclusions beyond PLAN.md/TASKS.md/the ledgers (which it may read as the *claimed* state to
cross-check against reality, not as ground truth to inherit), re-does the full deep codebase
review from scratch and reports drift between docs/laws/ADRs and code reality anywhere in the
tree, whether recently-merged work's claimed outcomes hold, new findings ranked across the
whole codebase (not just the trust-core diff), an on/off-course tracking verdict, and the
right-theorem-vs-mechanical-catch convergence metric (`docs/VISION.md` §2). TASKS.md's own
label — "fresh-agent deep re-review of the trust core" — names what *triggered* the review,
not its scope; narrowing a BAR review to only the trust-core files it happens to follow is
the exact process violation ADR 0010 calls out. A fresh agent dispatching or conducting BAR 1
should read ADR 0010 directly rather than inferring scope from TASKS.md's terse label.

## Deliverables & acceptance criteria

Historical/in-flight — treat as substantially landed per TASKS.md's checkbox, but **re-confirm
the coverage-regression fix cycle before relying on this gate's completeness claims**. What
"done" means here: the `roundtripCases` typeclass field is defaultless and non-empty-enforced;
the registry audit rejects any unregistered or unimported instruction instance; all-64
both-extended register-pair witnesses exist in the roundtrip domain for every affected
instruction family; the `0x8D`/`0xC6` REX.B sibling bugs are fixed; the diagnostic reports what
actually decoded wrong, not just pass/fail; documentation no longer overclaims exhaustiveness
beyond what `roundtripCases` actually enumerates.

## Pointers

- `docs/TARGETS/X86_64.md` §1 ("The `roundtripCases` typeclass field") and §2 ("The registry and
  the environment audit") — the Law-5 design doc for this branch's gate; grep-confirmed present
  with matching section content at time of writing.
- `Gasm/Targets/X86_64/Instructions/Base.lean` — declares the `roundtripCases` typeclass field
  (per `docs/TARGETS/X86_64.md`'s own citation); confirm the non-empty-assertion fix has landed
  here.
- `Gasm/Targets/X86_64/Registry.lean` — the `run_cmd` environment audit; grep-confirmed present.
- `Gasm/Targets/X86_64/RoundtripGate/*.lean` (e.g. `Xor.lean`, `And.lean`, `Lea.lean`,
  `Mov.lean`) — the 21 per-family gate shards; grep-confirmed present as a directory of files,
  one per instruction family, matching the "sharded one-per-instruction-family" design revision
  in PLAN.md.
- `Gasm/Targets/X86_64/Roundtrip.lean`, `Gasm/Targets/X86_64/RoundtripTests.lean` — the
  registry-derived roundtrip test surface; confirm these are derived from the registry rather
  than hand-listed, per the design.
- PLAN.md, "Phase 1 — Mechanical trust fixes", the "Decoder gaps + REGISTRY GATE" bullet, and
  the findings-ledger's "**Instruction registry → BUILD-FAILURE roundtrip gate**" entry — the
  full narrative, including the exact re-review findings summarized above.
- TASKS.md's TC4 line ("MERGE TRAIN 3 now") — the terse status this file expands on; do not
  read "MERGE TRAIN 3" as "verified merged," per this file's opening caveat.
- `docs/adr/0010-bar-triggered-deep-re-reviews.md` — governs BAR 1's actual (whole-codebase)
  scope; read directly before dispatching or conducting BAR 1 rather than inferring scope from
  TASKS.md's "trust core" label.

## Notes

- 2026-08-27: priority 8.5 — done; decoder+registry build-gate branch triggered BAR 1 and unblocks TC5/TC14/TC19/PA1/B1/B3/F1 — high historical leverage.

_(2026-08-27) This task predates the notes→design→review→implementation discipline for its
initial landing, but per this file's Context section, a coverage-regression fix cycle was
PLAN.md-recorded as still RUNNING at the time these task files were written. A fresh agent
should grep for the both-extended-register witness cases and the non-empty-`roundtripCases`
assertion described above to determine whether that fix cycle has since landed, and update this
file's status/Notes accordingly if it finds the fix cycle incomplete or still open._
