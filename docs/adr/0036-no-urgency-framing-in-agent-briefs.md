# 0036. No Urgency Framing in Agent Briefs

## Status

Accepted, 2026-08-27. (PLAN.md D27.)

## Context

CI failed on both platforms at the load-bearing Law 10 axiom gate, so every push to the
newly-public repository showed red regardless of its content — including pushes from a
Linux-target team that works outside this session and has no channel to ask why. The
coordinator dispatched a fix and opened the brief with "URGENT AND BLOCKING", intending to
convey that the task sat ahead of other queued work.

The owner corrected the framing rather than the priority.

## Decision

The owner's words: "i would discourage sending \"URGENT\" prompts to agents -- it will only
encourage shoddy work / send them the task, but keep things clear for them if it's urgent."

Agent briefs state the facts that make a task matter and let the agent draw its own
conclusion about priority. They do not use urgency framing, emphasis, or pressure language
to convey importance.

## Consequences

The reasoning generalizes past politeness: pressure framing does not buy speed, it buys
shortcuts, and the shortcuts available in this codebase are exactly the ones it cannot
afford. On the very task that prompted this, the tempting shortcuts were to skip the
root-cause investigation (can the colliding `main` declarations be namespaced?) in favour
of the symptom-managing fallback (spawn a process per module); to narrow the gate's module
coverage until it fit the runner, reopening a 32-module blind spot that TC15 had closed;
and to quiet the loud failure that was correctly refusing to silently skip unloadable
modules. Each would have produced a green gate that checked less — the single worst
outcome available for a load-bearing correctness gate, and one that reads as success.

Facts inform; adjectives pressure. A brief conveys stakes by naming who is affected and
how ("CI is red for every pusher; a team that cannot reach us depends on it"), which is
both more actionable and more truthful than an adjective.

When a task genuinely is time-sensitive, the clarity that helps is a precise scope and an
explicit statement of which corners may **not** be cut — never emphasis. A correct fix that
lands later beats a fast one that hides the problem, and saying so plainly in the brief is
what actually protects the work.

This ADR governs how the coordinator writes briefs. It does not change how tasks are
prioritized, only how that priority is communicated.
