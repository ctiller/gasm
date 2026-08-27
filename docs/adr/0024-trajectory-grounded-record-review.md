# 0024. Trajectory-Grounded Record Review

## Status

Accepted, 2026-08-27. (PLAN.md D16, D16-a.)

## Context

[`0020`](0020-coordinator-work-is-reviewed.md) established that the coordinator's own
authored artifacts get a fresh adversarial reviewer before merge, closing the gap of an
unreviewed writer. That decision, on its own, does not specify what a coordinator-work
reviewer should check *against*. Reviewing coordinator-authored governance text against
`PLAN.md` or against the coordinator's own prior summaries is a closed loop: if the
coordinator's summary drifted from what the owner actually said, and the review checks
the ADR against that same summary, the review can only validate that the transcription
is internally consistent — it cannot detect that the transcription is wrong. This is
precisely the failure mode this remediation pass was commissioned to fix: ADRs 0011,
0014, 0015, 0016, 0019, and 0020 all contained instances of owner modality upgraded
("i think i like that" read back as ratified fact, "probably" read back as settled
certainty, "my preferred vector" read back as a universal/exclusive rule, "i'm imagining"
read back as "mandated"), coordinator design filed under the owner's name, and in
ADR-0020's case, one fact invented outright and attributed to the owner.

## Decision

Two owner directives, ratified together as D16 and its follow-up D16-a:

**D16.** "decision-record reviews are grounded in the recorded trajectory: ADRs and
governance docs are audited against the session's JSONL transcript (the owner's actual
words), never only against derived artifacts like PLAN.md — a record backfilled from a
summary and verified against the same summary is a closed loop that validates
transcription, not truth." (Coordinator framing of the rule the owner's review-discipline
directives below establish; the transcript path pattern is
`~/.claude/projects/<project>/<session-id>.jsonl`.)

**D16-a**, the owner's own words: "let's write down the review discipline for anything
you author: the reviewing agent *MUST* also check the trajectory for my words."

## Consequences

Every review of a coordinator-authored decision record or governance document must read
the session's JSONL transcript directly and check the record's claims (attribution,
quoted text, modality) against what the transcript actually shows — not against
`PLAN.md`, not against the coordinator's own summary of the conversation, and not against
a prior review's conclusions. This is a stricter standard than
[`0010`](0010-bar-triggered-deep-re-reviews.md)'s bar reviews (which may read `PLAN.md`
as the *claimed* state to check against code reality, but are not themselves auditing
attribution of quotes) and stricter than [`0020`](0020-coordinator-work-is-reviewed.md)'s
general coordinator-review requirement (which did not, until this ADR, specify what the
reviewer checks against). This remediation pass — the ADR Provenance sections across
0001–0020, the corrections to PLAN.md D15/Phase 4, VISION.md, EQUIVALENCE_PROOFS.md, and
SYSTEM_EFFECTS.md, and this batch of new ADRs (0021 onward) — is itself the first
execution of D16/D16-a against this session's transcript. An earlier version of this pass
maintained a hand-transcribed index of owner quotes (`OWNER_DIRECTIVES.md`) intended to
make every future execution of this review cheaper than re-extracting the transcript from
scratch; that index was itself a second, hand-maintained source of truth for facts whose
ground truth is the trajectory, and it drifted from the trajectory within hours of being
written — the exact defect class D16/D16-a exists to prevent, one layer up. It was
removed rather than kept current: this ADR's own transcript citation
(`1f217b14-bc2d-42d4-9c2e-8d73bc78b4b2.jsonl`) is the durable pointer, and
`scripts/check_record.py` ([`0035`](0035-decision-record-integrity-gate.md)) is the
mechanism that keeps the surviving record (`PLAN.md`, `docs/adr/`, `docs/tasks/`) honest
without a redundant transcription layer.

## Provenance

Owner-stated (D16-a) plus coordinator framing (D16). D16-a is the owner's own words,
quoted in full above. D16 states the general principle the coordinator derived as the
immediate, obvious complement to D16-a — audit against the transcript, not against
derived artifacts — and is recorded as coordinator framing rather than a separate owner
utterance, since the transcript does not contain the owner stating D16 as a distinct
sentence prior to D16-a.
