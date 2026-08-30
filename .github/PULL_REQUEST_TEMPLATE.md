<!--
Copyright 2026 Craig Tiller

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-->

<!--
Review in this repository is not "LGTM." docs/REVIEW.md defines a Three-Pillar
protocol, and its own north star is explicit: "the one question review can
never delegate is *are we proving the right theorems?*" CI (Pillar 1) is a
floor, not the review. Fill in what applies; delete sections that genuinely
don't apply to this PR (e.g. a pure-docs PR has no Domain Gap Matrix) rather
than leaving them blank.
-->

## What & why

<!-- One or two sentences: what changed, and the docs/ section(s) or design
     rationale that motivated it. If this introduces a new Lean declaration,
     every one of them needs a `/- REF: ... -/` citation (Law 1) -- CI's
     citation audit (`scripts/check_refs.py`) enforces this mechanically, but
     say here *why* the cited section justifies what you built. -->

## Pillar 1 -- Mechanical truth

- [ ] CI is green on this PR (both platforms; see `docs/CI.md` for exactly
      what each platform's job covers and what it deliberately does not).
- [ ] No mandatory gate was skipped, bypassed, or weakened. The temporary
      Law-10 debt ledger was not widened.

## Pillar 2 -- Semantic integrity (only for new/changed theorems)

For every formal theorem this PR adds or changes, `docs/REVIEW.md` §4.2
requires:

**A. Structured spec-to-theorem derivation**
1. **Spec requirement**: quote the exact domain contract *P(x)* and
   precondition *Q(x)* from the cited `docs/` section.
2. **Formal theorem**: paste the exact Lean signature
   `∀ x, H₁(x) ∧ ... ∧ Hₖ(x) → C(x)`.
3. **Fidelity mapping**: `Hᵢ ⟺ Q` and `C ⟺ P`, argued step by step, not
   asserted.

**B. Domain Gap Matrix** (adversarial -- actively look for input space,
edge conditions, or spec-mandated behavior your theorem's hypotheses
accidentally weaken or exclude):

| Spec Permitted Behavior / Input Space | Theorem Hypothesis / Bound | Gap Status (`Verified` / `Weakened` / `Uncovered`) | Justification & Impact |
| :--- | :--- | :--- | :--- |
| | | | |

## Pillar 3 -- Architectural health (only for non-trivial structural changes)

- **Target separation**: does everything live in its correct domain
  (`Core/`, `Effects/`, `Targets/`, `Stdlib/`) without OS/hardware concepts
  bleeding across a boundary?
- **Abstraction cleanliness**: are typeclasses actually invoked on their
  operational path (Law 8 -- no inert/dead typeclasses), and are event
  types open via `Inject` rather than closed enums?
- **Factoring & DRY**: is anything here a copy-paste twin of existing
  infrastructure that should have been factored into a shared module
  instead (Law 12)?
- **Diffusion vs. concentration**: are the invariants this PR touches
  centralized in their authoritative module, or now scattered?

## Findings become gates (Law 13)

If reviewing this PR (by hand, by fuzzing, or by debugging a failure)
surfaced a defect, the fix is not complete until its *class* is mechanized
away -- a stricter type, a new kernel-checked theorem, a build-failing
linter, or a mandatory oracle control vector (see Law 13's preference
order). Name the new gate here, or cite the existing gate that should have
caught this and explain why it didn't.

## Checklist

- [ ] Every new/changed Lean declaration carries a `/- REF: ... -/` citation
      to a `docs/` (or `references/`) section that already 100% justifies it
      (Law 1/2), or the referenced section was updated *first*, in this same
      PR or a prior one (Law 5 -- stop-and-design).
- [ ] No new file introduces an un-vendored, self-authored approximation of
      an external spec (Law 4).
- [ ] New first-party `.lean`/`.py`/`.ps1`/`.sh`/`lakefile.toml`/
      `.github/**/*.yml` files carry the Apache-2.0 header
      (`python scripts/check_licenses.py`).
