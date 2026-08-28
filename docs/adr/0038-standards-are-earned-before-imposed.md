# 0038. Standards Are Earned Before They Are Imposed

## Status

Accepted, 2026-08-28. (PLAN.md D29.)

## Context

A second team, working outside this session and reachable only through the repository,
merged an x86-64 bare-metal target. Their merge added four entries to
`scripts/gate_allowlist.txt` — including one `grandfathered` pointwise proof,
`spike1_baremetal_canonical_effect_trace_equivalence` — taking oracle-dependent
declarations from 80 to 84.

The coordinator surfaced this as a trend running against the owner's stated target ("no
axioms, strong verification, checked models") and proposed a ratchet gate: store the
current count as a baseline and fail any change that increases it.

At the time of that proposal, this session's own count was 80, with six agents mid-flight
attempting to reduce it and two entries (PA14, PA16) assessed as possibly unreachable.

## Decision

The owner's words: "we get to hold standards of others when we can hold them of
ourselves."

The ratchet gate is not built now. The oracle-dependent declaration count is driven down
against our own work first. A standard is proposed for enforcement once we demonstrably
meet it.

## Consequences

The other team's four entries were not a lapse: they followed the established convention
in this codebase faithfully, and that convention is pointwise `native_decide` equivalence
proofs. The convention is the defect, and it is ours. Gating them on a standard we have
not met would export our debt as their obstacle.

The practical reasoning generalizes past fairness. A gate imposed by a team that does not
meet it produces one of two outcomes, both bad: it is bypassed, or it blocks legitimate
work — and this project has already recorded (ADR-0035 and the doc-facade linter's rollout
reasoning) that a gate which fires on legitimate work trains people to stop reading red.
A gate that codifies practice already demonstrated is not an imposition at all; it is
writing down what is already true, which is why it holds.

This does not weaken the target. Zero remains the goal, and the count remains the score.
It changes only the order of operations: reduce, demonstrate, then ratchet. When our own
number is at or near zero, the ratchet becomes a statement of practice rather than an
aspiration enforced on others, and `check_gates_axioms` already emits the count needed to
implement it in a few lines.

A corollary worth stating, since the repository is the only channel between teams: a gate
IS a message. It is the one form of communication that reaches another team without being
read, and it cannot be replied to or argued with. That asymmetry is exactly why the bar
for introducing one should be practice rather than intention.

## Provenance

Owner-stated. The sentence in the Decision section is the owner's own words. The
generalization in Consequences — that a gate is an unanswerable message, and that
premature enforcement exports debt as obstacle — is the coordinator's elaboration of it.
