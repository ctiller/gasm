# M1/P2 Checked x86 Memory-Form Authoring Proof Brief

Status: design review; no execution or admission authority.

This brief defines the first implementation slice that connects the memory model to instruction
authoring. It does not create a second authority ledger, alter decoded instruction data, or claim
that ghost ownership establishes physical mappedness or fault freedom.

## Target theorem

The checked M1 authoring path produces an existing x86 `MOV` store only from the canonical typed
obligation world, a latest-live binding/view witness for the exact dynamic use, and target
physical-access evidence. Proof erasure yields the ordinary decodable and encodable instruction.
A production x86 demonstration uses this sealed high-level path and connects the same evidence to
its sole `VerifiedProgram.compose` value.

Raw instruction constructors and decoders remain available to low-level target machinery. This
slice does not claim that an ordinary MOV value can never be constructed. It proves that the
checked path cannot produce or admit its store without the selected witnesses, and that the
demonstration artifact is actually authored through that path.

The selected demonstration is a small real straight-line Windows x86 artifact with exactly one
dynamic execution of a registered byte-store form followed by a real terminal transition. A
single-use artifact avoids falsely identifying one static loop instruction with one dynamic use,
while still exercising the production assembler, loader, operational semantics, emitter, platform
admissibility, and `VerifiedProgram.compose`. This is not a mock platform or detached example.

Its concrete instruction shape allocates a Windows x64 stack frame with `sub rsp, frameSize`, then
performs one checked byte store at `[rsp + offset]` inside that frame. Ordinary target-owned setup
and the later call to `ExitProcess` provide the typed process terminal outcome. The CALL's indirect
load and return-address stack store are explicitly outside this first selected checked family; the
prototype makes no claim that those effects have already migrated to M1 checked authoring.

## Current semantic gap

`memAccesses` and the frame theorems describe where an instruction reads and writes, but the current
authoring path does not require authority. The typed `ObligationWorld` is the sole resource world;
the checked-authoring layer must extend it and reuse `BindingHistory` identities rather than
introducing a parallel permission ledger or region-identity namespace.

## Decomposition

1. Use `BindingHistory.BindingInstanceId`, `BindingGeneration`, `CaptureOccurrenceId`, and
   `UseOccurrenceId`. These are execution-local nominal identities until a target load/world
   relation establishes freshness.
2. Represent exclusive memory access as an `ObligationKind`. Its value names the exact binding
   instance, generation/locator, logical footprint, and owning relation. Dynamic authority is only
   `ObligationWorld.Owns world token`. Its protocol discriminator comes only from the canonical
   discriminator governance accepted with the typed world; this slice allocates no ad hoc numeric
   protocol constant.
3. Define a typed memory view as a relational witness over one envelope execution, one well-formed
   binding history, and one canonical world. Because `BindingHistory.WellFormed` intentionally
   proves neither temporal latestness nor liveness, a profile-owned occurrence/path certificate
   additionally proves that the capture selected the latest live binding at the capture event and
   that the captured binding and view remain valid along the exact path through the use event. The
   view also proves that the use resolves through its exact capture to the token's binding; the
   binding record matches the token's generation, locator, containing logical footprint, and
   selected exclusive rights; and the world owns the access obligation and exact view-invalidation
   obligation.
4. Represent view invalidation/return as another `ObligationKind` in the same world. View
   destruction discharges that exact token through `ObligationTransition`; return or exit must
   discharge it or explicitly deliver it. `CanDischarge` is provided only by a concrete
   lifecycle-derived capability tied to the exact binding/view owner and terminal result; it is not
   `Unit`, a blanket instance, or a freely constructible witness. There is no arbitrary world
   replacement.
5. Select only exclusive byte-store authority in this slice. Shared-read and atomic obligation
   kinds are unselected and impose no obligations.
6. A provisional, profile-local checked MOV wrapper contains the ordinary instruction, typed view,
   and target store realization. A sealed high-level constructor is the only authoring entry used
   by the demonstration. Erasure returns the ordinary instruction. Decoding alone returns ordinary
   data and provides no world ownership, view, latest-live path, or target realization evidence;
   separately supplied valid evidence may still be used by the checked path.
7. The target store realization separately proves effective-address equality, mapped and writable
   access, non-wrapping range, width/alignment, exact event origin, and descriptor fidelity. The
   byte-store descriptor footprint equals the selected byte view; the byte view is contained in
   the authority/binding logical footprint and a proved offset/range translation maps it into the
   containing backing footprint. A byte view is not required to equal the whole allocation. The
   `UseOccurrence.event` is tied to the actual fetched and stepped MOV event, not merely static text
   membership. Ghost ownership alone proves none of these facts.
8. The demonstration capability context contains the exact entry world and binding/view evidence.
   Establishment connects it to the actual loaded Windows state. Platform admissibility requires
   the logical and physical evidence but does not consume the world. The exact indexed
   `ObligationTransition` chain retains authority across the store and later discharges or delivers
   every selected token. Behavior proves execution of the erased instruction. Completion is one
   real `VerifiedProgram.compose` value for the exact artifact.

All checked MOV, typed-view, lifecycle, and x86 realization declarations in this prototype are
explicitly provisional and profile-local. They test the load-bearing shape but do not freeze the
public M1 interface.

## Windows process-entry grant prerequisite

The current `X86_64MachineState` uses total memory and carries no virtual mapping or page-protection
state. Total `X86_64Mem.read`/`write` operations prove neither mappedness nor writability. The
prototype therefore depends on a distinct
`M2-B[Windows-x64-process-entry]` loader-established stack grant; `X86StoreRealization` consumes
that profile evidence rather than deriving physical access from the generic machine state.

The grant is tied to a pinned official Windows loader/ABI source and proves:

- the exact emitted artifact and `Platform.load` state to which the grant applies;
- the exact initial `rsp` relation at process entry;
- a committed and writable stack byte range covering the explicitly allocated frame;
- non-wrapping range arithmetic and the selected byte's required alignment;
- containment of `[rsp + offset, rsp + offset + 1)` in that range after `sub rsp, frameSize`;
- lifetime of the grant through the exact dynamic store occurrence;
- that this exact occurrence—and no unrelated access merely sharing its address—is the selected
  access authorized by the profile evidence.

The grant is not logical ownership, does not appear in generic x86 state, and does not mint an
`ObligationWorld` entry. If the accepted canonical World/M2-B rewrite supplies an entry-grant seam,
the spike instantiates that seam. Otherwise it may define a provisional spike-local relation with
the same obligations. It must not rely on a Windows red zone—Windows x64 has none—or on the total
memory implementation as evidence of physical accessibility.

## Principal invariant

Every admitted dynamic store has one connected chain:

```text
ordinary instruction descriptor
  <- erasure of checked authoring
  <- exact typed view
  <- BindingHistory use/capture/binding
  <- exact canonical ObligationWorld ownership

plus an independent target physical realization for the same address and range.
```

The occurrence/path certificate connects the binding capture to the exact dynamic store event and
proves liveness along that path. Structural `BindingHistory.WellFormed` is never cited as providing
that temporal fact.

## Bounds and framing

The first profile has an eight-bit store width and alignment one. It proves exact logical and
backing footprints, non-wrapping address arithmetic below `2^64`, one-instruction text membership,
and finite binding/event/use carrier membership. It claims no global generation bound.

The existing `MovMem8Reg8.writesWithin` and `MovMem8Reg8.readsWithin` theorems remain the machine
memory-frame authority. The instruction retains the logical world; unrelated world entries frame
exactly. View invalidation and exclusive return discharge only their exact entries.

## Proof applicability and burden

| Selected feature/profile | Required evidence | Owner | Unselected effect |
|---|---|---|---|
| Generic envelope and binding history | Existing carrier and `WellFormed` certificates for the exact execution/history | Memory-model projection | No x86 access or platform-admission claim |
| Exclusive byte-store authoring | Exact exclusive-access and view-invalidation entries in the canonical world; exact use/capture/binding resolution | Checked instruction author | Required only for the selected checked store occurrence |
| Windows x86 physical realization | M2-B process-entry stack grant, effective address after explicit frame allocation, mapped+writable byte, nonwrap, alignment one, view containment/backing translation, exact dynamic event origin, descriptor footprint, emitted/decode connection | Windows x86 profile and straight-line demonstration artifact proof | No burden on Linux, AArch64, Wasm, graphics, or non-CPU events |
| Existing MOV operational semantics | Existing `step`, `writesWithin`, and `readsWithin` theorems | x86 instruction family | Reused without a new per-caller proof |
| View invalidation and exclusive return | Exact canonical-world transitions or explicit terminal delivery through a lifecycle-derived capability | Demonstration lifecycle/terminal proof | No arbitrary cleanup or token deletion |
| Shared-read authority | Not selected | Future M1/M4 profile | No typeclass, world-entry, or proof obligation in this slice |
| Atomic-object authority and ordering | Not selected | Future M2-X/M4 profile | No atomic compatibility, coherence, or TSO burden in this slice |
| Device/platform memory domains | Not selected | Their future target profiles | No CPU footprint or authority projection imposed |

The local proof delta is therefore limited to the one selected store and its production-platform
connection. Generic binding/history facts and existing MOV frame facts are reused. The adapter must
not install catch-all typeclass instances that make exclusive authority globally applicable or
force unrelated instruction families to construct empty evidence.

## Required negative controls

- missing canonical-world ownership;
- stale binding generation;
- a different binding instance with the same raw address;
- wrong access rights or access kind;
- wrong logical or backing footprint;
- raw `UInt64` or decoded instruction alone supplying no ownership/view/realization evidence;
- non-latest capture, invalidated view, or use after a rebind;
- use occurrence whose event is not the actual fetched and stepped MOV;
- instruction-descriptor mismatch;
- missing target mapping or writability;
- reliance on total memory or a nonexistent Windows red zone as physical-access evidence;
- entry grant that does not cover the post-`sub rsp` selected byte or survive through its use;
- omitted view-invalidation obligation;
- freely fabricated or wrong-lifecycle discharge capability;
- platform admissibility that ignores either the logical or physical witness.

## Completion gate

The smallest decisive prototype constructs the checked existing MOV store from a real
binding/history/world, latest-live path, and target entry state; proves erasure/encoding/decoding,
exact dynamic-origin, containment/translation, and step/frame connections; connects it to the
emitted straight-line Windows artifact; proves the exact retain/discharge transition chain; and
constructs that artifact's sole production-platform `VerifiedProgram.compose` instance. A detached
checked constructor, mock platform, or plan to add `VerifiedProgram` later does not complete the
slice.

The whole-program claim explicitly scopes the checked-family result to the one selected byte store.
It records the terminal CALL's memory effects as ordinary and unselected rather than silently
presenting them as capability-checked.

## Rejected alternatives

- a detached `AuthorizedAccess` proposition or permission ledger;
- arbitrary `RegionId` values presented as fresh identities;
- a proof-only mock `Platform`;
- identifying one static loop instruction with only one dynamic use occurrence;
- whole-view equality with the containing allocation footprint;
- ad hoc numeric obligation protocol discriminators;
- freely constructible lifecycle discharge authority;
- total-memory execution presented as proof of a mapped writable Windows page;
- implicit use of a Windows red zone;
- authority fields in decoded instruction structures;
- ghost ownership implying mapping or fault freedom;
- atomic/shared proof burdens in an unselected profile;
- a detached spike with whole-program admission deferred.
