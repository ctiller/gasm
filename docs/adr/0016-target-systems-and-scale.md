# 0016. Target Systems and Scale

## Status

Accepted, 2026-08-27. (PLAN.md, Scale directive.)

## Context

Every downstream design question — how much decomposition machinery is worth building,
whether a gate's cost model matters, what "demand" means for
[`0008`](0008-demand-driven-model-growth.md) — is unanswerable without first fixing what
scale and which systems the project is actually building toward. Left unstated, this
invites scope drift in both directions: over-building infrastructure nothing demands, or
under-building decomposition machinery that a real target will need.

## Decision

Ratify the target-system list and scale target stated in
[`docs/VISION.md`, The Target Systems](../VISION.md#the-target-systems) and
[§4](../VISION.md#4-tractability-modular-contracts-composed-proofs): **game engines,
operating systems, web/gRPC servers, and databases**, at **millions to tens of millions
of lines of code** (Rust-equivalent; larger still as generated assembly), and nothing
beyond this list drives model or capability growth. Each class forces a specific,
named extension of the standards elsewhere in this repository (deadline budgets and
multi-loop reactivity for game engines; the bare-metal/interrupt model and the
model-becomes-implementation inversion for operating systems; threading, protocol
causality, and secrecy contracts for servers; durability semantics and crash-observable
traces for databases) rather than an undifferentiated "go faster" mandate.

## Consequences

Decomposition — seams, per-module contracts, composition rules, sharded and
incrementally-cached gates, per-module cost budgets that sum — becomes a primary
deliverable of the project, on equal footing with the models themselves, per VISION §4's
closing standing question for every piece of infrastructure: *what does this cost at ten
million lines when one module changes?* The instruction registry gate's decide-shards and
the associated OOM finding are recorded as the first live test of this principle. Any
target-family proposal that is not one of these four classes (or a documented extension
serving one of them) needs its own ADR justifying the exception before model work begins
on it.

## Provenance

Mixed. The target-system list itself is owner-stated, verbatim: "just to push on scope
here: the target systems we'll build with gasm are game engines, operating systems,
web/grpc servers, databases." The scale figure is also owner-stated, from a related
remark: "all that and note the scale: millions to tens of millions LOC of Rust typically,
so more for gasm -- the correctness and performance modelling is crucial, and developing
ways to decompose even moreso." Everything else in this ADR's Decision and Consequences
is the coordinator's elaboration, not owner-specified: the exclusivity claim ("nothing
beyond this list drives model or capability growth," "needs its own ADR justifying the
exception"), and all four per-class "forced extensions" (deadline budgets for game
engines, the bare-metal/inversion model for operating systems, secrecy contracts for
servers, crash observability for databases) were not stated by the owner — he named the
four target classes and the scale, not the specific standards each one forces.
