---
id: PA3
title: step-lemma library + composition calculus implementation
status: ready
blocked_on: ""
after: [PA2]
related: []
bar: ""
track: proof-arch
priority: 7.3
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# PA3: step-lemma library + composition calculus implementation

## Context

This task builds the Lean code PA2 designs. `TASKS.md` lists it as a bare `after: PA2` implementation
task, and PLAN.md's Phase 4 list confirms the split: "Step-lemma library implementation
(per-instruction; agent-friendly, parallelizable)" and "Composition calculus implementation" are
listed as separate line items from the Phase 2 design bullet. Read PA2's design doc in full before
writing any Lean — per Law 1 (`docs/REVIEW.md`), every Lean item here must be completely motivated
by that doc's `REF:`-citable sections; if this task discovers the design doesn't cover something it
needs, the design doc must be updated and reviewed first (Law 5), not patched around in proof code.

### Why this is framed as DSL-total theorems, not per-routine plumbing

PLAN.md's Decision D11 frames the entire point of this task:

> Phase 4's step-lemma library + composition calculus ARE the total theorems of the assembly DSL
> (frame it that way in the design doc)... DSL-level proving is the primary mechanism making proof
> cost sublinear at the D-scale (10M LOC).

Concretely, this means the acceptance bar for this task is not "the step lemmas needed for one
routine exist" — it is "every instruction constructor PA2's design says needs a step lemma has one,
proven once, universally quantified over its operands and the initial machine state, registered
into the simp-set PA2 specifies." A step lemma proven only for the specific register/immediate
combination one routine happens to use is exactly the kind of pointwise regression-test-shaped proof
Law 9/10 (`docs/REVIEW.md`) prohibit as verification evidence — it must be `∀` over the instruction's
real operand domain and discharged by kernel-checked proof (native_decide/decide is acceptable only
where PA2's design explicitly identifies a sub-obligation as exhaustively finite, e.g. an 8-bit
opcode field — never as a substitute for a proof that should be structural over `Nat`/`ByteArray`/
register values).

### What PA1 already found, that this task must not re-discover the hard way

PA1's task file (`docs/tasks/PA1-crc32-pathfinder.md`) required its own agent to report, for BAR
2's benefit, "any place a per-instruction step lemma had to be hand-derived from scratch (i.e.,
candidate content for PA2/PA3's lemma library)." Read that completion report and PA2's design doc's
treatment of it before starting: PA1's hand-derived facts about the specific instructions
`crc32SymbolicProgram` uses (`mov_r32`, `xor_r32`, shift/conditional-XOR chain, per
`Stdlib/Zlib/Windows.lean:36-119`) are the most concrete acceptance test this task has for whether
its step-lemma library is actually usable: after PA3 lands, it should be possible to re-derive PA1's
proof using the library's lemmas instead of PA1's ad-hoc reasoning, with less proof text, not more.
Consider (agent's judgment, not a hard requirement) redoing PA1's proof against the new
infrastructure as a validation exercise, if time allows — a library that cannot re-prove the one
routine that motivated it is a strong signal something in the design didn't transfer to code.

## Deliverables & acceptance criteria

- Per-instruction step lemmas implemented for the instruction set PA2's design doc scopes,
  registered into the simp-set PA2 specifies, each `∀`-quantified over the instruction's operand
  domain and the initial machine state per Law 9 — no lemma pinned to concrete register numbers or
  immediate values standing in for the general case.
- Composition rules implemented: sequential composition, call composition (consuming a callee's
  `docs/EQUIVALENCE_PROOFS.md` §4.2 callability theorem as a frame the caller's proof can assume),
  and loop composition (turning a per-iteration invariant plus a decreasing measure into a
  `docs/EQUIVALENCE_PROOFS.md` §3 total-correctness statement) — the loop rule in particular must
  satisfy `docs/REVIEW.md` Law 7: no manual jump/offset table standing in for dynamic instruction
  fetch, proof by induction over the loop's real trip-count domain.
- Capability-token frame-condition wiring implemented per PA2's design's connection point — this
  need not consume real capability tokens yet if PA4 (capability adoption) has not landed; if so,
  state explicitly what stub or placeholder is used and file it as a dependency PA4/PA9 must close,
  rather than silently under-delivering the frame-condition piece.
- Trace-algebra composition implemented to the extent PA2's design specifies; if PA2 deferred the
  full causal-order machinery to PA5, this task should implement only the interface PA2 sketched,
  and must not invent trace-composition behavior PA2 did not specify (Law 1 — no un-designed
  invention in Lean code).
- Zero `sorry`, zero unauthorized axioms: `lake build` clean, `lake exe check_gates_axioms` clean
  (run from repo root; confirms no accidental `native_decide` dependency snuck into an
  infinite-domain step lemma or composition rule). `native_decide`/`decide` is never a substitute
  for the infinite-domain structural proofs this library exists to provide (Law 10) — every use
  must correspond to a sub-obligation PA2's design or this task's own Notes explicitly justify as
  exhaustively finite.
- `scripts/check_refs.py` clean: every new declaration carries a `REF:` citation back to the
  specific section of PA2's design doc that motivates it (Law 1), and — per Law 2 — once a section
  of that design doc is cited, it must be 100% implemented, not partially.
- Per this project's evidence convention, the completion report should state which parts of PA1's
  pathfinder proof this library can now re-derive more directly, and flag any gap where PA1's
  hand-derived reasoning still cannot be expressed through the new step-lemma/composition
  infrastructure — that gap is itself a finding for PA9 (which consumes this library to derive
  `VerifiedProgram`) and potentially a follow-up to PA2's design.

## Pointers

- PA2's design doc (path TBD at time of writing — PA2 has not yet run; find it via
  `docs/tasks/PA2-step-lemma-composition-design.md`'s `design:` field once populated, or via
  `scripts/check_refs.py`'s index once the doc exists).
- `docs/tasks/PA1-crc32-pathfinder.md` — the pathfinder proof this library should be able to
  re-derive; its Notes/composition-sketch section is the concrete validation target described
  above.
- `docs/EQUIVALENCE_PROOFS.md` §3 (total correctness), §4 (the three split theorems the composition
  rules must assemble).
- `docs/REVIEW.md` Law 1 (strict derivation from `REF:`s — no invented behavior beyond PA2's
  design), Law 7 (anti-jump-table loop proof discipline), Law 9 (universal quantification — every
  step lemma is `∀` over its real domain), Law 10 (kernel-checked vs `native_decide` boundary;
  `docs/adr/0002-native-decide-restricted-to-exhaustive-finite-domains.md`).
- `docs/adr/0011-dsls-as-unit-of-proof-leverage.md` (D11 — the framing this implementation must
  honor: these are total theorems about the assembly DSL, not per-routine plumbing) and
  `docs/adr/0003-universal-equivalence-via-modular-decomposition.md` (D2).
- `Gasm/Targets/X86_64/Instructions/*.lean` — the instruction semantics definitions step lemmas are
  proven about; `Gasm/Targets/X86_64/Semantics.lean` (`instructionAtRip`, `runUntilHalt`-shaped
  execution) — the dynamic-fetch machinery Law 7's loop rule must build on rather than bypass.
- `Gasm/Core/Permissions.lean:50` (`MemoryPermissions`) — the capability-token type the
  frame-condition wiring integrates with (real integration may wait on PA4).

## Notes

- 2026-08-27: priority 7.3 — step-lemma/composition implementation — the mechanical follow-through on PA2's design.

_(none yet — first entries append here as work begins; this is Law-5-class proof-architecture
work — consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch; do not waive review on this track.)_
