---
id: PA9
title: VerifiedProgram as derived theorem — routine contracts + linker facts
status: ready
blocked_on: ""
after: [PA3, PA4]
related: [TC14]
bar: ""
track: proof-arch
priority: 7.8
priority_set: 2026-08-28T02:00:00Z
design: ""
design_review: ""
date: 2026-08-27
---

# PA9: VerifiedProgram as derived theorem — routine contracts + linker facts

## Context

This is the capstone task of the proof-architecture track: it is where the whole modular-contracts
thesis stops being infrastructure and starts being the thing whole-program verification actually
runs on. `docs/VISION.md` §4 states the thesis this task realizes, in the exact words the rest of
Phase 4 has been building toward:

> **Composition rules.** Sequential composition, call, and loop rules assemble routine contracts
> into whole-program theorems. The whole-program equivalence statement (`VerifiedProgram`) becomes
> a *derived theorem*, not an obligation discharged by evaluation.

Read "derived theorem, not an obligation discharged by evaluation" precisely: today,
`VerifiedProgram` (`Gasm/Core/Verification.lean:64-72`) is a structure whose `traceEquivalence`
field is a proof obligation an agent must directly discharge for the whole program, from scratch,
every time — there is no mechanism by which proving routine A's contract and routine B's contract
and the fact that the program links A-then-B together automatically yields the whole-program
theorem. This task builds that mechanism: after it lands, a `VerifiedProgram` instance should be
*producible* from (a) each constituent routine's three split theorems
(`docs/EQUIVALENCE_PROOFS.md` §4) and (b) a linker fact stating how the routines are composed
(sequential order, call graph, loop structure) — via PA2/PA3's composition calculus — rather than
requiring a fresh whole-program proof.

PLAN.md's Phase 4 lists this as its own line item, distinct from the step-lemma/composition work:
"Rebuild `VerifiedProgram` as derived theorem from routine contracts + linker facts." This task is
that rebuild.

### Why this depends on both PA3 and PA4, and not on PA2 directly

`TASKS.md` states this task's dependency as `after: PA3, PA4` — notably, not `after: PA2` directly,
even though PA2 is the design this whole line of work descends from. This is because PA9 is a
*consumer*, not a re-implementer: it needs the composition calculus to already be built and
kernel-checked (PA3's deliverable), and it needs real capability tokens to exist as the frame
conditions those composition rules consume (PA4's deliverable), not just PA2's design sketch of how
capability tokens *would* serve as frame conditions. Attempting this task before PA3/PA4 land would
mean either re-doing their work inline or producing a `VerifiedProgram` rebuild that rests on
placeholder frame conditions — exactly the kind of premature dependency `docs/VISION.md` §3.3's
"validate before building on it" discipline warns against, transplanted from model-growth to
proof-architecture sequencing.

### What "routine contracts + linker facts" means concretely

- **Routine contracts** are the per-routine three-split-theorem outputs
  (`docs/EQUIVALENCE_PROOFS.md` §4: functional equivalence, callability/ABI preservation, memory
  safety) that PA1 pioneered for `crc32SymbolicProgram` and that any subsequently-verified routine
  produces the same way. This task's rebuild consumes these as inputs, not as something it proves
  itself — a routine's functional-equivalence theorem, once established, should be usable by PA9's
  machinery without re-deriving it.
- **Linker facts** are the structural facts about how a whole program's routines are assembled:
  which routine calls which, in what sequence, under what loop structure — the same information
  PA2/PA3's sequential/call/loop composition rules consume to chain routine-level facts into
  program-level ones. This task must specify what a "linker fact" looks like concretely (likely
  something derived from the program's control-flow graph / call graph, consistent with
  `Gasm/Core/CFG.lean`'s existing machinery) and how it feeds the composition calculus.
- The **derivation** this task builds is the mechanism that takes a set of routine contracts plus
  the linker facts connecting them and mechanically produces (via PA2/PA3's rules, not by hand) the
  `VerifiedProgram.traceEquivalence` obligation — ideally as a theorem whose proof term is built
  from the composition calculus's own lemmas, making the whole-program proof genuinely a
  consequence of the parts rather than a parallel, independently-authored proof that happens to
  agree with them.

### What must NOT regress

`docs/EQUIVALENCE_PROOFS.md` §5 states the existing universal-quantification law this rebuild must
continue to satisfy — the derived theorem is not exempt from Law 9 just because it is assembled
mechanically:

> For any binary executable $P_{asm}$ and monadic specification $S_{spec}$ operating in an
> environment domain $Env$: $\forall (env \in Env), Trace(runAsm(P_{asm}, loadEnvironment(P_{asm},
> env))) = Trace(S_{spec}(env))$

The rebuilt `VerifiedProgram` must still be universally quantified over the real `Environment` type
per PA8's mechanical-prevention gate (contracts quantify over the canonical `Environment`, not a
spike-defined enum), must still thread `∀` read-results per PA6's read-binder contract shape (this
task's rebuild is explicitly the "VerifiedProgram-successor" PA6's design doc names as its
destination), and — for reactive programs — must route through PA7's mandatory
`VerifiedReactiveProgram` inner/outer pair rather than a single flat trace-equality field. This
task's job is to make deriving these obligations from parts *easier and more mechanical*, not to
weaken what they state; a derivation mechanism that accidentally produces a weaker whole-program
theorem than direct proof would have is a regression, not a simplification, and Law 13's "findings
become gates" principle applies here too: if the derivation can silently drop a precondition or
narrow a domain relative to what direct proof would require, that gap must be closed structurally,
not documented as a known limitation.

## Deliverables & acceptance criteria

- A specification (consolidated from Notes into a design doc; fresh-agent design review required
  before implementation, per the task-lifecycle convention — this is Law-5-class work despite being
  framed as "implementation" of PA3/PA4's outputs, because the derivation mechanism itself is new
  model/spec-shaping infrastructure) of: what a "linker fact" is, how routine contracts combine with
  linker facts via PA2/PA3's composition calculus to produce a whole-program trace-equivalence
  theorem, and how the result is packaged as (or replaces) `VerifiedProgram`.
- `VerifiedProgram` (or its successor type, consistent with PA6's read-binder-shaped and PA7's
  reactive-loop-shaped requirements) rebuilt so that constructing an instance is possible by
  supplying routine contracts + linker facts and invoking the composition calculus, rather than
  requiring an independently-authored whole-program proof.
- Demonstrated on at least one real multi-routine program (a good candidate: extend PA1's
  `crc32SymbolicProgram` pathfinder with a second routine and prove the combination via this
  mechanism, since PA1's contracts already exist in the three-split-theorem shape this task
  consumes) — a design that only exists on paper without being exercised against a real composed
  program has not actually validated the derivation.
- No regression against the pre-existing `VerifiedProgram`/`docs/EQUIVALENCE_PROOFS.md` §5
  universal-environment law, PA6's read-binder universal quantification, or PA7's reactive-program
  inner/outer mandate — the derived theorem must be at least as strong as direct proof would have
  produced for the same program, and any place it is not must be treated as a defect requiring a
  structural fix (Law 13), not accepted as a documented limitation.
- Zero `sorry`, zero unauthorized axioms (`lake build` + `lake exe check_gates_axioms` clean);
  `native_decide`/`decide` is never a substitute for the infinite-domain proofs this derivation
  produces or consumes (Law 10) — a derivation mechanism that happens to work by exhaustively
  checking small composed programs would defeat the entire point of building it.
- `scripts/check_refs.py` clean, citing `docs/VISION.md#4-tractability-modular-contracts-composed-proofs`
  and `docs/EQUIVALENCE_PROOFS.md` §4/§5.
- Completion report states explicitly: what a routine author now needs to supply to get a
  whole-program `VerifiedProgram` instance (contrasted with what they needed to supply before this
  task), and whether PA1's pathfinder routine, extended with a second composed routine, was
  actually used as the validation exercise — if not, state why and what validation was substituted.

## Pointers

- `docs/VISION.md` §4 in full (quoted above) — the thesis statement this task realizes.
- `docs/EQUIVALENCE_PROOFS.md` §4 (the three split theorems — this task's routine-contract inputs),
  §5 (the universal whole-program law — quoted above, in full; the standard this task's output must
  continue to satisfy).
- PLAN.md Phase 4, "Rebuild `VerifiedProgram` as derived theorem from routine contracts + linker
  facts" bullet.
- `Gasm/Core/Verification.lean:19-26` (`Environment`), `:30` (`EnvironmentLoader`), `:64-72`
  (`VerifiedProgram`, current `traceEquivalence` field — the obligation this task mechanizes the
  construction of).
- `Gasm/Core/CFG.lean` — the existing control-flow-graph machinery likely relevant to defining what
  a "linker fact" is structurally.
- PA2's design doc (path TBD — see `docs/tasks/PA2-step-lemma-composition-design.md`) and PA3's
  implementation (see `docs/tasks/PA3-step-lemma-composition-impl.md`) — the composition calculus
  this task's derivation mechanism invokes.
- PA4's migration (see `docs/tasks/PA4-capability-adoption.md`) — the source of real capability
  tokens serving as frame conditions the composition calculus consumes.
- `docs/tasks/PA1-crc32-pathfinder.md` — the existing three-split-theorem instance this task's
  validation exercise should build on.
- `docs/tasks/PA6-read-binder-contract.md`, `docs/tasks/PA7-verified-reactive-program.md` — the
  contract-shape requirements this task's rebuilt type must not regress against.
- `docs/tasks/PA8-law9-migration.md` — the canonical-`Environment`-quantification gate this
  rebuild's output must satisfy for any spike consuming it going forward.
- `docs/REVIEW.md` Law 9 (universal quantification), Law 10 (kernel-checked proof;
  `docs/adr/0002-native-decide-restricted-to-exhaustive-finite-domains.md`), Law 13 (findings become
  gates — no silent weakening in the derivation; `docs/adr/0009-findings-become-gates.md`).
- `docs/adr/0003-universal-equivalence-via-modular-decomposition.md` (D2 — the architecture this
  task's rebuild is the culmination of).

## Notes

- 2026-08-27: priority 6.7 — VerifiedProgram-as-derived-theorem is where PA3's step lemmas and PA4's capabilities finally compose into the same bytes<->instructions link TC14 builds from the emitter side.
- 2026-08-27: related: [TC14] — PA9 (VerifiedProgram as a derived theorem from routine contracts + linker facts) and TC14 (the PE-parser/`codeMatches` connection theorem) are the proof-side and emitter-side halves of the same missing link: neither currently connects proven instructions to the bytes that actually ship.
- 2026-08-27 (oracle-debt audit, `docs/ORACLE_DEBT.md` Part 6): priority raised 6.7 → 7.8. Named in
  `docs/ORACLE_DEBT.md` Part 4 as part of the architecture chain PA17's Spike3/Spike4 domain-honesty
  closure ultimately wants, though not a hard `after` edge for PA17 itself; raised in proportion to
  the oracle-debt epic's overall priority without claiming a blocking relationship that isn't there.

_(none yet — first entries append here as work begins; this is Law-5-class proof-architecture
work — consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch; do not waive review on this track.)_
