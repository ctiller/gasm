# 0035. Decision-Record Integrity Gate

## Status

Accepted, 2026-08-27.

## Context

D23 ([`0031`](0031-flatten-not-history-scrub.md)) makes `PLAN.md`, `docs/adr/`, and
`docs/tasks/` the sole surviving decision history of this project once the repository is
flattened — commit messages stop being a durable record. A trajectory-grounded review of
that record on the same day found it demonstrably unchecked: `docs/adr/OWNER_DIRECTIVES.md`,
a hand-maintained index of owner quotes, went 12 messages stale while its own header
claimed to be "the full inventory of the owner's directives" — including omitting the two
most consequential rulings in the project (the flatten itself, D23, and the third-party-prose
ban, D25). Separately, `PLAN.md` had two different decisions both numbered D25, making
every cross-reference to "D25" ambiguous. Both defects were caught only by a human
adversarial review, which [`0009`](0009-findings-become-gates.md)'s own standard treats as
a missing-gate report, not merely a defect report: "remember the purpose here is to get to
mechanical verification... the outcome should have been theorems that prevented the
mistakes." `OWNER_DIRECTIVES.md` itself was deleted rather than fixed
([`0024`](0024-trajectory-grounded-record-review.md)'s updated Context section) because it
was unintended duplication in the documentation layer — the same failure class the repair
epic's own founding vision names for the model layer ("broadly detect unintended
duplication growing") — and duplication should be prevented mechanically, not managed by
hand a second time.

## Decision

Build `scripts/check_record.py` as a Pillar 1 gate enforcing five properties of the
decision record, mirroring the conventions of `scripts/check_refs.py` and
`scripts/check_licenses.py` (a `scripts/decision_record_allowlist.txt` allowlist in the
same 5-field `::`-delimited shape as `scripts/gate_allowlist.txt`, for genuine, recorded
exceptions):

1. Every `D`-numbered decision defined in `PLAN.md` has a unique ID (never allowlistable).
2. Every such decision has a corresponding ADR, or an explicit allowlisted reason it does
   not.
3. Every ADR carries a `## Provenance` section, or an explicit allowlisted reason it does
   not.
4. Every in-scope cross-reference (markdown link, or backtick-quoted file path with a
   directory component) inside `PLAN.md`, `docs/adr/*.md`, `docs/tasks/*.md`, `TCB.md`,
   `MODEL_DEBT.md`, and `docs/REVIEW.md` resolves to a real file on disk, or has an
   explicit allowlisted reason it does not (e.g. a doc committed on a not-yet-merged
   sibling worktree, or a task's own explicitly-hedged forward mention of a not-yet-written
   future design doc). `references/**` paths and literal `NNNN` numbering-template
   placeholders are out of scope by construction, not by allowlist, since that corpus's
   prose narrates the fast-moving reference-index migration's past and present file
   existence as fact, not as navigation pointers.
5. A phrase claiming a document is a "full inventory," "complete list," or similar of
   something is paired with either a nearby citation of the mechanical check that verifies
   it, or an explicit allowlisted reason the claim is trusted without one.

## Consequences

`scripts/check_record.py` is wired into `docs/REVIEW.md` §4.1 as a numbered Pillar 1 gate,
into `scripts/run_gates.py`'s gate table, and into `.github/workflows/ci.yml`, so it runs
on every push and pull request rather than existing as a tool nobody invokes — the same
"a gate that exists but never runs protects nothing" lesson this project has already
learned once for `check_publishable.py` and `check_references.py`. Its own `--self-test`
flag plants one defect per check into the real tree, asserts the specific check goes red,
reverts, and asserts green again, following `scripts/run_gates.py`'s existing TCB T4
meta-gate fixture pattern — a gate only ever seen to pass is untested. Check 5
(unverified completeness claims) is explicitly a heuristic phrase-tripwire, not a semantic
verifier: it can confirm someone has taken responsibility for a completeness claim, not
that the claim is true. This gate does not replace human review of the decision record's
substance; it only makes the specific class of defect this pass found — duplicate IDs,
missing ADRs, missing provenance, dangling references, unverified completeness claims —
mechanically impossible to reintroduce silently.

## Provenance

Coordinator-decided under delegation ([`0021`](0021-coordinator-role-executive-function-and-mandatory-delegation.md)),
in direct response to the owner's standing review discipline — "don't check pointwise,
check forall — and don't fix pointwise, fix forall" ([`0009`](0009-findings-become-gates.md))
— applied by the coordinator to a defect the owner did not personally specify a gate for,
but whose remediation this project's own Law 13 requires: a reviewer-caught defect is a
missing-gate report.
