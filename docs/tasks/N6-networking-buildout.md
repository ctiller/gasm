---
id: N6
title: "Networking buildout: TCP semantics, HTTP/1.1, HTTP/2, protobuf codecs, gRPC server"
status: ready
blocked_on: ""
after: [N5]
related: []
bar: bar-3
track: networking
priority: 8.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# N6: Networking buildout — TCP semantics, HTTP/1.1 hardening, HTTP/2 framing, protobuf codecs, gRPC server

## Context

`TASKS.md`'s line for this task states its scope plainly and calls it out explicitly as a
milestone: "N6 networking buildout: TCP semantics model, HTTP/1.1 hardening, HTTP/2 framing +
protobuf stdlib codecs → gRPC server (**a target-system deliverable**) — after: N5; threading
edges (B-ledger items) join here for concurrency." This is not a small task. It is the
culmination of the entire networking path — everything N1 through N5 built (a real Win32 OS
model, a real socket model, an end-to-end validated Spike4, and Spike4 proven as gasm's first
`VerifiedReactiveProgram`) exists to make this buildout possible on solid foundations rather than
on invented socket/OS behavior. Do not understate its scope when picking this up: it comprises at
minimum five distinct, individually substantial pieces of new model/protocol/target surface:

1. **A TCP semantics model** beyond what N3 already delivers at the WinSock-call boundary — this
   task's scope includes modeling TCP as a protocol with its own state machine and guarantees
   (ordered, reliable, byte-stream-not-message-boundary delivery — the property
   `docs/SYSTEM_EFFECTS.md` §6.1's `NetEvent.send` coalescing rule already assumes: "TCP is a byte
   stream (chunking invisible), but specs at message granularity observe message ordering"),
   distinct from N3's per-syscall socket-hook semantics.
2. **HTTP/1.1 hardening** — Spike4's current HTTP/1.1 implementation is a minimal three-route
   demo (`/`, `/status`, `/unknown` → 404, per `Spikes/Spike4HttpServer/Spec.lean`); "hardening"
   here means bringing it to a real protocol implementation: proper request-line/header parsing
   against malformed input, chunked transfer-encoding, keep-alive/connection reuse, and the
   request/response framing edge cases a real HTTP/1.1 server must handle correctly, not just the
   happy path three routes currently cover.
3. **HTTP/2 framing** — an entirely new protocol layer with no existing gasm surface at all:
   binary framing, stream multiplexing, HPACK header compression, flow control. This is new
   target/protocol model surface requiring its own Law 5 design, not an extension of the HTTP/1.1
   work.
4. **Protobuf stdlib codecs** — a new `Stdlib` serialization surface (wire-format encode/decode
   for the protobuf binary format) that gRPC's message framing depends on; this is exactly the
   kind of surface `docs/VISION.md` §4's DSL principle applies to (a wire-format encoding language
   with total roundtrip theorems, not a one-off encoder).
5. **A gRPC server** built on top of all four of the above — HTTP/2 transport, protobuf message
   bodies, TCP-level reliability — as the actual "target-system deliverable" `TASKS.md` names this
   task. This is explicitly one of `docs/VISION.md` §1's four target system classes: "Web/gRPC
   servers: threading and async I/O; protocol causality (§ SYSTEM_EFFECTS 6.4); cryptography..."
   — gRPC is not an example application, it is one of the four systems gasm exists to build.

### Threading edges join here

`TASKS.md`'s line also states: "threading edges (B-ledger items) join here for concurrency." This
means N6 is where the project's first genuinely concurrent (multi-connection, likely
multi-thread-or-async) reactive program gets built, and it inherits the full weight of
`docs/SYSTEM_EFFECTS.md` §6's multi-loop composition obligations, quoted directly from §6.3:

> Craig additions (2026-08-27): (d) threading/multiprocessing ⇒ MULTIPLE reactive loops per
> program — contract generalizes to per-loop inner/outer pairs + composition obligations
> (deadlock/livelock freedom at declared sync points, explicit fairness), cross-loop interaction
> confined to the causal layer (dormant VectorClock machinery becomes load-bearing)... full
> concurrent semantics needs Law 5 design before first threaded spike.

A gRPC server handling concurrent client connections is very likely exactly this "first threaded
spike" the note anticipates — multiple accept-loop-derived reactive loops (one per connection, or
a pool serving many) running concurrently, each with its own inner/outer `VerifiedReactiveProgram`
pair (per N5's contract type, generalized here to the multi-loop case), with explicit
composition obligations (**deadlock/livelock freedom at declared synchronization points**,
**explicit fairness** — i.e. no connection can be starved indefinitely by the scheduler) proven
across the loops, not just within each one. This is new proof-architecture surface, not merely new
protocol surface, and the note is explicit that full concurrent semantics needs its own Law 5
design "before the first threaded spike" — meaning N6 cannot simply reuse N5's single-loop pattern
unmodified; it must design the multi-loop composition obligations first.

### Protocol causality — §6.4, quoted in full

`docs/SYSTEM_EFFECTS.md` §6.4 is the section this task's entire causality discipline rests on,
quoted here in full because it directly governs how N6's HTTP/1.1/HTTP/2/gRPC request-response
handling must be modeled — an ack-then-request-arrives ordering bug is exactly the class of
protocol bug real servers ship, and the observation algebra must be able to state it as a defect:

> For protocol work, happens-after and coalescing interact deeply, and getting it wrong changes
> program meaning:
>
> **Writing an ack *in response to* a read IS NOT EQUIVALENT to writing an ack *before* the
> read.**
>
> A server that pre-emptively emits `OK` and then reads the request is a different — broken —
> program from one that reads and then acks, even though each direction's byte stream is
> identical in isolation. The distinction lives entirely in the cross-direction causal order, and
> the peer can observe it (an ack that arrives before the request was sent proves the ack did not
> depend on the request). Therefore:
>
> - Input events (`recv`, file/console reads, `accept`) are first-class contract-trace events,
>   recorded with their position in the causal order — not silent environment consumption. Their
>   payloads come from the `Environment` oracle as before; what observation adds is their
>   *occurrence and ordering*. (The current `FileSystemEvent`/`TraceM` model records no read
>   events; that is a defect to fix under this section, not a precedent.)
> - Inputs are coalescing barriers: output coalescing (§6.1) applies only within input-free causal
>   segments. Outputs on either side of an input event never merge and never commute across it.
> - The input→dependent-output happens-after edge is observable and must be preserved by
>   `canonicalizeTrace`: an implementation that hoists an output above an input it
>   specification-depends on is NOT equivalent, no matter how the per-stream bytes compare.
> - Symmetrically, an output with no specification-level dependence on a subsequent input may be
>   ordered freely relative to it only if the spec explicitly declares that independence — the
>   conservative default is that program order into and out of input events is preserved.

Every layer N6 builds — TCP-level reads, HTTP/1.1 request parsing, HTTP/2 frame receipt, gRPC
message deframing — is an input event in this sense, and every response N6's server emits must be
provably causally-after the input(s) it depends on. This is not an incidental detail; it is the
correctness property that distinguishes a genuinely causal protocol implementation from one that
merely produces byte-identical output on the happy path while being silently reorderable under
concurrency or pipelining.

### Governing laws

`docs/REVIEW.md` Law 5 (stop-and-design — every one of the five pieces above is new model/protocol
surface requiring its own design doc before implementation; this is the single largest
concentration of Law-5-class work in the networking path), Law 9 (universal quantification — HTTP
parsing, protobuf decoding, and gRPC message framing must all be proven correct for arbitrary
valid wire-format inputs per the read-binder discipline, not fixed test vectors), Law 12 (protobuf
wire-format encode/decode is exactly the kind of population-of-encodings the DSL/connection-
theorem discipline targets — a decoder and encoder must be connected, not two independently
"probably correct" halves), Law 13 (findings from HTTP/2/gRPC differential testing must become
gates, not one-off fixes). `docs/VISION.md` §1 (the web/gRPC servers target class this task
directly realizes, including its named cryptography/secrecy-contract forcing function — see N7)
and §4 (DSL discipline — protobuf wire format and HTTP/2 framing are both populations of
artifacts that should get language-level total theorems, not per-message ad-hoc proofs).

## Deliverables & acceptance criteria

Because this is explicitly a multi-part "target-system deliverable," acceptance criteria are
listed per component; none may be waived as "implied" by another component's completion.

- **TCP semantics model**: a design doc (new, since none of N1-N5's design docs cover TCP as a
  protocol rather than a syscall interface) stating ordering/reliability guarantees the model
  provides and how they interact with N3's socket-call semantics; differential validation against
  real TCP behavior (segment reordering/coalescing at the OS level should be invisible to the
  model, per `docs/SYSTEM_EFFECTS.md` §6.1's existing `NetEvent.send` rule, but this task must
  state and validate that explicitly for the TCP layer specifically, not merely assume it).
- **HTTP/1.1 hardening**: request-line/header parsing proven correct for the real grammar (not
  just the three current happy-path routes), chunked transfer-encoding, keep-alive/connection
  reuse — each with its own universal (Law 9) correctness statement over malformed and
  well-formed inputs, plus a hardening pass that documents what class of malformed input is now
  handled vs still out of scope (Law 5/D7 demand-driven scoping, stated explicitly rather than
  silently incomplete).
- **HTTP/2 framing**: binary frame encode/decode, stream multiplexing, HPACK header compression,
  flow control — as a new Law-5 design doc (this is new protocol/target surface with no existing
  gasm precedent) with differential validation against a real HTTP/2 implementation/tooling
  (analogous to the Wasm host-oracle pattern: a real HTTP/2 client or server library as ground
  truth for the framing layer).
- **Protobuf stdlib codecs**: wire-format encode/decode built as a DSL per `docs/VISION.md` §4 —
  total roundtrip theorem over the wire-format grammar (varints, length-delimited fields, nested
  messages), connected (Law 12) rather than having encode/decode be two independently-trusted
  halves; differential validation against a real protobuf implementation (e.g. Python/C++
  `protoc`-generated code as oracle).
- **gRPC server**: assembled from the above four layers plus N3/N5's socket/reactive-program
  foundations; proven as a `VerifiedReactiveProgram` (generalized to the multi-loop case per the
  threading-edges note above) with the protocol-causality discipline of §6.4 explicitly checked —
  at minimum one test demonstrating that a response is never observably ordered before the
  request it answers, across a real concurrent-connection exercise (not merely single-connection,
  single-request).
- **Multi-loop composition obligations designed before any threaded code lands**: per
  `docs/SYSTEM_EFFECTS.md` §6.3's explicit statement that "full concurrent semantics needs Law 5
  design before the first threaded spike," this task must produce that design (deadlock/livelock
  freedom at declared sync points, explicit fairness, cross-loop interaction confined to the
  causal/VectorClock layer) before implementing concurrent connection handling — this is very
  likely gasm's first threaded spike, so there is no existing precedent to reuse.
- **BAR 3 compliance**: `TASKS.md` names a bar directly gating this task: "BAR 3 — before N6
  buildout starts: fresh-agent deep re-review of the networking model + contracts." This task's
  own implementation must not start before that review completes — the `bar: bar-3` field in this
  file's frontmatter records that gate. The review should cover everything N1-N5 built (Win32
  harness, OS1 rebuild, socket model, Spike4 end-to-end + reactive reverification) as the
  foundation N6 is about to build five major new pieces on top of.
- Every one of the five components above is independently Law-5-class (new model/protocol/contract
  surface): none should be waived to mechanical implementation. Given the scope, this task will
  very likely need to be further decomposed into sub-tasks once design work begins — that
  decomposition is itself part of N6's design-phase output, not a reason to treat the whole thing
  as one implementation dispatch.

## Pointers

- `Spikes/Spike4HttpServer/Spec.lean`, `Equivalence.lean` — the current minimal HTTP/1.1
  three-route implementation this task hardens and builds HTTP/2/gRPC on top of.
- `docs/tasks/N5-spike4-reactive-verified.md` — the direct prerequisite; N6's gRPC server
  generalizes N5's single-loop `VerifiedReactiveProgram` pattern to the multi-loop/concurrent
  case.
- `docs/SYSTEM_EFFECTS.md` §6 in full (the observation algebra this task's protocol layers must
  respect), §6.1 (per-effect coalescing rules — `NetEvent.send`/`.recv` rows directly govern
  TCP/HTTP framing), §6.3 (multi-loop composition obligations — quoted above), §6.4 (protocol
  causality — quoted in full above; read in full, this is the section most directly relevant to
  every layer N6 builds).
- `docs/VISION.md` §1 (the web/gRPC servers target class — "threading and async I/O; protocol
  causality... cryptography — which adds a third contract class... secrecy contracts" — the
  crypto clause is N7's scope, not this task's, but is the reason gRPC's TLS layer will eventually
  need N7's contract class), §4 (DSL discipline for protobuf/HTTP-2 framing).
- `TASKS.md` "Networking path" section (N6's line and BAR 3) and the B-ledger reference
  ("threading edges (B-ledger items) join here") — check `TASKS.md`'s Build/scale section (B1-B3)
  for what those threading-adjacent items currently are, since this task is where they connect to
  networking.
- `docs/REVIEW.md` Law 5, Law 9, Law 12, Law 13.

## Notes

- 2026-08-27: priority 8.0 — the networking buildout epic (TCP/HTTP/1.1/HTTP2/protobuf/gRPC) is exactly the class of work the owner is explicitly eager to see happen, and it triggers BAR 3 — kept high despite sitting deep in the N-track DAG.

_(none yet — first entries append here as work begins; this is Law-5-class networking-model work
— consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch.)_
