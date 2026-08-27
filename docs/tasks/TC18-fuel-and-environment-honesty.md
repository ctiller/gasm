---
id: TC18
title: Fuel-exhaustion honesty + Environment dead-field resolution
status: ready
blocked_on: ""
after: []
related: []
bar: ""
track: trust-core
priority: 6.5
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# TC18: Fuel-exhaustion honesty + Environment dead-field resolution

## Context

Sourced from `TCB.md` **T12 — Verification harness layer** (TCB priority 3). Three findings,
bundled because they live in the same trace/verification-harness layer:

1. **Fuel exhaustion is indistinguishable from clean termination.** `runProgramTraceWithLoops`
   returns `[]` for fuel-out, for no-instruction-at-`rip`, and for a genuinely clean fault alike.
   TCB's framing: "any spec expecting `[]` is dischargeable by fuel exhaustion" — this is a
   soundness gap in the contract shape itself, not an implementation bug: a theorem stating "the
   trace is empty" can currently be satisfied by an interpreter that simply ran out of fuel before
   producing anything, rather than by a program that genuinely halts having emitted nothing. This
   is exactly the class of contract-shape defect PLAN.md's Phase-4 "read as universal binder" work
   and this project's general anti-vacuity stance (`docs/EQUIVALENCE_PROOFS.md` §1.1's "anti-
   vacuity" language for both-ways equality) already worry about elsewhere — fuel exhaustion is
   one more way a proof can be trivially, silently true.
2. **`Environment` is entirely dead.** TCB: "no `VerifiedProgram` instantiates it (Spike3 uses
   `Env := Bool`); its docstring claims to model all syscall-queryable data." This is the same
   defect MODEL_DEBT.md's **C7** catalogs from the model-fidelity side: `Environment`
   (`Core/Verification.lean:19-26`) declares `stdin, args, envVars, incomingRequests, fileSystem,
   clockTime`, but its `EnvironmentLoader` instance threads only `stdin` and `incomingRequests` —
   grep confirms zero readers for the other four fields. MODEL_DEBT.md's own words: "So
   `traceEquivalence : ∀ (env : Environment)` quantifies over four dimensions that provably cannot
   influence the machine — universal in form, 2-dimensional in substance." TCB adds the sharper
   diagnosis: this is a **Law 8 facade** (an abstraction defined and then bypassed), not merely an
   incompleteness. PA8 depends on this being resolved (it's listed as a needs-OS1 item touching
   the same `Environment` shape), so this task's fix should land before PA8's migration work
   assumes a clean `Environment` to quantify over.
3. **`rawEmitForFuzzing` is a dead, permanently-open bypass.** Zero call sites, but its mere
   existence is a standing escape hatch from `emitVerifiedExecutable`-only code generation
   (`docs/REVIEW.md` §4.1 item 1's "Code Generation Gating" requirement). TCB notes the *real*
   bypass in active use is `HardwareHarness.lean:270`'s direct call to `emitPE32Executable` (that
   one is legitimate — the harness is deliberately exercising raw machine code as an oracle input,
   not claiming verification) — but `rawEmitForFuzzing` sitting unused is a second, unnecessary
   door left unlocked.

### Why this is Law-5-adjacent

Changing the trace type to distinguish exhaustion from termination is a contract-shape change —
it alters what `∀`-quantified trace-equivalence theorems are even claiming, which is squarely
within Law 5's "any concept not yet fully designed" trigger. It doesn't need a large standalone
design doc, but it does need a fresh-agent design review before implementation, because getting
the new trace type's shape wrong would quietly reintroduce a different vacuity hole in the same
place this task is meant to close one.

## Deliverables & acceptance criteria

- The trace/verification harness's return type changed from a bare list to something like
  `Except Exhausted (List Event)` (TCB's suggested shape) or an equivalent sum type that makes
  fuel exhaustion **a distinct, observable outcome** from clean termination with an empty trace —
  such that no theorem stating "the trace equals `[]`" can be discharged by a fuel-starved run.
- Every existing consumer of the old bare-list return type updated to handle the new outcome type
  explicitly (not pattern-matched away with a wildcard that silently treats exhaustion as success).
- `Environment`'s dead fields (`args`, `envVars`, `fileSystem`, `clockTime`) either genuinely wired
  through `EnvironmentLoader` and read by at least one real consumer, or deleted from the type —
  per TCB/MODEL_DEBT C7, a declared-but-unread field is worse than an absent one, because it makes
  a `∀ env : Environment` claim look more universal than it is. Whichever direction is chosen,
  state the reasoning in the completion report (this is exactly the kind of "instantiate or
  delete" decision the design review should sign off on).
- `rawEmitForFuzzing` deleted (zero call sites — confirm by grep immediately before deleting, in
  case something changed since TCB's audit).
- Completion report must show: a concrete before/after case where a fuel-exhausted run and a
  genuinely-empty-trace run now produce distinguishable outcomes; the `Environment` field
  disposition and why; confirmation of `rawEmitForFuzzing`'s removal; `lake exe
  check_gates_axioms` clean.

## Pointers

- Grep for `runProgramTraceWithLoops` to locate the fuel-exhaustion/clean-termination collision.
- `Gasm/Core/Verification.lean:19-26` (`Environment`) and `:50-53` (`EnvironmentLoader` instance —
  confirm current line numbers by grep; MODEL_DEBT.md's citation is from the 2026-08-27 audit).
- Grep for `rawEmitForFuzzing` and `emitPE32Executable` / `HardwareHarness.lean:270` to confirm the
  legitimate vs. illegitimate bypass distinction before deleting anything.
- `TCB.md` §T12 in full; `MODEL_DEBT.md` §C7 (the model-fidelity framing of the same
  `Environment` defect).
- `docs/REVIEW.md` Law 8 (anti-facade — governs the `Environment`/`rawEmitForFuzzing` half of this
  task) and Law 5 (governs the fuel/trace-type half); `docs/EQUIVALENCE_PROOFS.md` §1.1
  (anti-vacuity framing this task's fuel fix directly serves).
- PA8 (Law 9 migration) — depends on `Environment` being resolved cleanly; sequence coordination,
  not a hard `after:` edge, since PA8's own dependency is on OS1/N2, not on this task by id.

## Notes

- 2026-08-27: priority 6.5 — TCB T12 (fuel-exhaustion/clean-termination confusion + dead Environment fields) — a real soundness gap, not in TCB's top-8 table but flagged priority 3 in its own entry.

_(none yet — first entries append here as work begins; consolidate Notes into a `docs/` design
doc for the trace-type change specifically before implementation, and route it through a fresh-
agent design review — do not waive review on this one.)_
