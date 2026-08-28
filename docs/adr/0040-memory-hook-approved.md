# 0040. Memory Hook Design Approved

## Status

Accepted, 2026-08-28. (PLAN.md D31.)

## Context

D30 (`0039-x86-isa-expansion-prerequisites.md`) recorded the owner's ruling that memory
contracts should become a hook: "let's plan out a memory hook -- apis every instruction needs
to go through to access memory, so we can do the perf and permissions in one place."

`docs/MEMORY_HOOK.md` is the resulting design. It closed with three questions the designer
declined to settle alone, one of which had to be answered before any instruction-set expansion
could begin, because it changes what gets written.

## Decision

The owner answered all three: "all yes."

1. **The v1 enforcement line counts as Law 11 compliance.** Literal-displacement accesses
   discharge by `decide`/`omega` auto-param; no-citation accesses and literal overruns (such as
   `[rsp+4096]` against a 4096-byte frame) are unrepresentable; dynamic bounds are carried but
   semantically discharged, with flow-sensitive typestate deferred to PA2/PA3.
2. **`MemRef` becomes the operand convention** for the expansion's new memory forms.
3. **The mandatory, defaultless `memAccesses` field is accepted**, at a cost of 88 one-line
   edits now and one line per instruction form forever.

## Consequences

**The defaultless field is the load-bearing decision.** `memAccesses : ι → List MemAccessSpec`
has no default, so an instruction form cannot be declared without stating its memory behaviour.
That is the `roundtripCases` shape, and it is deliberately the opposite of `canFuzzHardware`'s
silent opt-out — the mechanism by which 50 of 88 forms escaped silicon validation without
anyone noticing. A convention that can be forgotten will be; a missing field is a build error.

One declaration then feeds four consumers: permissions quantify over it, the interpreter
pre-checks faults against it, the performance model derives uops from it, and it is the address
stream a future cache model will consume. That is the "perf and permissions in one place" the
owner asked for, generalised one step further.

**Q2 has the longest reach and is why it needed answering first.** Adopting `MemRef` collapses
the number of instruction forms, changes how roundtrip enumeration works, and interacts with
B3's decoder modularization — all of which govern what a large expansion writes. Deciding it
after the expansion started would have meant rewriting the expansion, which is the wsc failure
mode this project exists to avoid.

**Q1 accepted a bounded rather than complete mechanism, deliberately.** Rejecting it would have
gated all Law 11 enforcement behind PA2/PA3, both unstarted. The accepted line is honest about
its limits — the design states plainly which accesses are unrepresentable, which are carried but
semantically discharged, and what the upgrade path is — which is worth more than a stronger
mechanism that does not exist.

**The two memory mechanisms stay separate, and their composition is the payoff.**
`docs/READ_BINDER_CONTRACT.md` (PA6) concluded that the syscall read-binder must not unify with
the capability contract, argued from Spike 4's real stack-buffer-overflow: the read's quantifier
must range over the syscall's declared cap (128 bytes) while the write bound is the destination
capability (16 bytes), because the gap between them *is* the defect. Under this design their
composition makes that overflow an undischargeable obligation — the bug becomes unprovable to be
absent, which is exactly the outcome sought.

**Perf falsifiability improves as a side effect.** Memory cost collapses from 14 sets of
duplicated, uncited inline literals — a Law 12 twin population — into one table of roughly eight
named coefficients, each carrying `Cited` provenance under Law 14. The sibling instruction
obligation gate then has something mechanical to check, where today 0 of 88 coefficients cite
any source.

Implementation is MH1 (sealed memory field, width API, access descriptors, fault plumbing),
then MH2 and MH3 in parallel. Expansion Wave B requires all three.

## Provenance

Owner-stated for the decision itself ("all yes" to three enumerated questions). The three
questions and the design they belong to are the planning agent's; the reasoning in Consequences
is the coordinator's elaboration, assented to but not stated by the owner.
