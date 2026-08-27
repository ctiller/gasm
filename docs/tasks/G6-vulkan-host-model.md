---
id: G6
title: Vulkan host model + GPU capability mapping
status: ready
blocked_on: ""
after: [G2, PA4]
related: []
bar: ""
track: graphics
priority: 7.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# G6: Vulkan host model + GPU capability mapping

## Context

`GRAPHICS_PREBUILD_AUDIT.md` §7 (Capability / memory-safety mapping, Law 11) states the
problem directly: **"Handles are tracked via linear obligations; memory ranges are not."**
This task extends `docs/REVIEW.md` Law 11's memory-access-capability mandate ("Every
instruction that reads or writes memory MUST carry proof of a valid, in-scope capability")
from the CPU/host memory model it currently governs to GPU device memory and descriptor
resources. It is sequenced `after: [G2, PA4]` for two independent reasons: G2's
synchronizes-with/happens-before edges are the mechanism by which this task's
fence-guarded temporal release obligations are actually discharged (a capability cannot be
proven released "until fence signaled" without G2's fence = queue→host edge existing to
formalize what "signaled" means); and PA4 (Law 11 capability adoption: "Core machinery as
authoring surface, SymbolicInstr migration plan") is where this project's capability
machinery is first made load-bearing for real memory-touching programs on the CPU side —
this task is the direct GPU-domain extension of that same machinery, so PA4's authoring
patterns should be reused, not reinvented, here.

### The full audit quote

Audit §7, quoted in full: "Needed: host-visible mapped ranges under Law 11 literally (real
pointers today); **device-local capability over `(VkDeviceMemory, offset, size)`** with
`vkBindBufferMemory` as hierarchical provenance/borrows (MEMORY_PROVENANCE §1.2 reuse);
**descriptors as capability handoff to the device** with fence-guarded temporal release
(`MustNotFree until fence signaled`); shader-side `OpAccessChain`/`OpLoad`/`OpStore` bounds
proofs against descriptor ranges that fail to assemble; GPU `ObligationType` constructors
(doc before Lean, Law 1)." Each clause is a distinct design element this task must cover:

1. **Host-visible mapped ranges** — a `vkMapMemory`'d region is, from the host's
   perspective, exactly the kind of raw pointer Law 11 already governs; this task states
   how an existing host-side `MemoryPerm`-style capability token covers such a range once
   mapped, rather than treating GPU-mapped memory as somehow exempt from the capability
   discipline that already governs ordinary host memory.
2. **Device-local capability over `(VkDeviceMemory, offset, size)`** — memory the host
   cannot directly address (device-local, non-host-visible allocations) needs its own
   capability shape, keyed on the allocation handle plus a byte range, with
   `vkBindBufferMemory` (the call binding a `VkBuffer` to a region of a `VkDeviceMemory`
   allocation) modeled as the provenance/borrow-establishing operation — reusing the
   hierarchical-provenance pattern already established for host memory: the audit's
   pointer to "MEMORY_PROVENANCE §1.2 reuse" is `docs/MEMORY_PROVENANCE.md` §1.2
   ("Hierarchical Provenance & Active Borrows," grep-verified present) — this task should
   reuse that section's borrow/hierarchy pattern for `vkBindBufferMemory`'s
   allocation→buffer binding relationship rather than inventing a parallel one.
3. **Descriptors as capability handoff to the device** — binding a buffer/image to a
   descriptor set and submitting a command buffer that references it is, formally, handing
   a capability to an agent (the GPU) that the host cannot supervise synchronously; the
   design must state this as a genuine handoff (the device "holds" the capability for the
   duration of in-flight execution) with **fence-guarded temporal release**: the host may
   not treat the capability as returned/freeable (`MustNotFree`) until the fence guarding
   that submission has signaled. This is a *temporal* capability discipline layered on top
   of the *spatial* one in item 2, and it is exactly why this task needs G2's fence
   semantics settled first.
4. **Shader-side bounds proofs** — `OpAccessChain`/`OpLoad`/`OpStore` inside a shader
   kernel must carry proof that the accessed offset lies within the descriptor's bound
   range, such that an out-of-range access "fails to assemble" (Law 11's fail-to-assemble
   mandate, applied inside the shader kernel language rather than only at the host
   command-recording layer).
5. **GPU `ObligationType` constructors** — new obligation-ledger constructor(s) (analogous
   to existing CPU-side obligation types) representing "this GPU resource is
   allocated/bound/in-flight" states, to be **designed in this doc before any Lean is
   written**, per `docs/REVIEW.md` Law 1 (doc-before-code, cited directly by the audit
   here).

### The concrete bug this task should NOT re-fix, but should note as precedent

Audit §7 also flags: "Concrete bug: `SPIRV_VULKAN.md:43`'s `returnVoid (h_clean : ∀ (s :
ComposedState spirv S), s.obligations = [])` quantifies over ALL states rather than the
exit state — unprovable for any inhabited state type with a nonempty ledger; the
terminator is unconstructible as written." **G1 already fixes this** (see
`docs/tasks/G1-graphics-doc-rework.md`'s deliverables: "`docs/TARGETS/SPIRV_VULKAN.md`'s
`returnVoid` quantifier fixed to bind the actual reached state"). This task should not
re-scope that fix. It is worth restating here, though, as the concrete illustration of
*why* this project's doc-then-review-then-code discipline matters: a quantifier error that
makes an obligation-discharge terminator permanently unconstructible is exactly the kind of
defect that is cheap to catch in a design doc (as the audit did) and would have been
expensive to discover only after Lean code and proofs were built on top of it — the same
argument `GRAPHICS_PREBUILD_AUDIT.md`'s own framing note makes for the whole graphics track
("every fix below is cheap now and expensive after code"). This task's own GPU
`ObligationType` design should be reviewed with exactly this quantifier-correctness
question in mind, since it is designing the same kind of obligation-ledger machinery the
bug appeared in.

## Deliverables & acceptance criteria

- A design document extending Law 11's capability model to GPU resources, covering all
  five numbered items above: host-visible mapped-range capabilities; device-local
  `(VkDeviceMemory, offset, size)` capabilities with `vkBindBufferMemory` as the
  provenance-establishing operation; descriptor capability handoff with fence-guarded
  `MustNotFree` release (stated formally in terms of G2's fence = queue→host edge); shader-
  side `OpAccessChain`/`OpLoad`/`OpStore` bounds-proof obligations; and new GPU
  `ObligationType` constructors, authored and reviewed before any Lean encodes them (Law 1).
- A stated composition with PA4: this task should reuse PA4's Core-machinery-as-authoring-
  surface pattern (permission tokens, obligation ledgers, `BlockM` typestate monad) rather
  than inventing a parallel GPU-specific capability system, per Law 12's single-source-of-
  truth preference — if genuine re-encoding for the GPU domain is unavoidable (e.g. because
  device-local memory has no host-addressable pointer), the design must say so explicitly
  and note what, if anything, needs a connection theorem back to the CPU-side machinery.
- Per Law 13(4): state what differential/control-vector evidence downstream implementation
  (G7) will need to produce — at minimum, a case demonstrating that a descriptor's
  `MustNotFree` obligation is genuinely load-bearing (an attempt to free/reuse the backing
  memory before the guarding fence signals must fail to assemble or fail at proof time, not
  merely be discouraged by convention), and a case demonstrating the shader-side bounds
  proof actually rejects an out-of-range `OpAccessChain`.
- Law-5/Law-13 discipline: design doc authored, then routed through fresh-agent design
  review before `design_review` is marked approved and before any Lean cites it.

## Pointers

- `GRAPHICS_PREBUILD_AUDIT.md` §7 in full — read in full; this task's Context section
  quotes but does not exhaustively restate it.
- `docs/TARGETS/SPIRV_VULKAN.md:43` (the `returnVoid` quantifier bug — handled by G1, noted
  here only as precedent; do not re-scope its fix into this task).
- `docs/REVIEW.md` Law 1 (doc-before-code — cited directly by the audit for the GPU
  `ObligationType` constructors), Law 11 in full (the capability mandate this task extends
  to GPU resources), Law 12 (connection-theorem mandate, relevant if GPU capabilities
  require genuine re-encoding rather than reuse of PA4's machinery).
- `docs/tasks/G1-graphics-doc-rework.md` — confirms the `returnVoid` fix's status and
  scope boundary.
- `docs/tasks/G2-synchronization-dsl.md` — the fence = queue→host edge this task's
  `MustNotFree until fence signaled` obligation depends on formally.
- `docs/MEMORY_PROVENANCE.md` §1.2 (Hierarchical Provenance & Active Borrows,
  grep-verified present) — the borrow/hierarchy pattern to reuse for
  `vkBindBufferMemory`'s allocation→buffer binding, per the audit's explicit pointer.
- The PA4 task entry in TASKS.md ("PA4 capability adoption (Law 11): Core machinery as
  authoring surface, SymbolicInstr migration plan, Zlib\Windows.lean last — after: PA2") —
  read PA4's own task file under `docs/tasks/` if it exists by the time this task is
  authored (it had not yet been written as a standalone file as of this task's writing;
  confirm before citing a path).
- `references/vulkan/ch_05_devices_and_queues.md`, and any chapter covering
  `vkBindBufferMemory`/descriptor sets (search `references/vulkan/` for the relevant
  memory-binding and descriptor-set chapters at authoring time; the directory contains
  numbered chapters and appendices, grep-verified present, but this task file does not pin
  an exact filename since the binding/descriptor chapter was not directly inspected while
  writing this task).
- Zero graphics Lean exists yet (verified: `grep -rn "Gasm/Targets/Spirv\|Gasm/Targets/Vulkan\|Gasm/Graphics" Gasm/` returns nothing), so this design targets a future
  `Gasm/Targets/*` Vulkan host-model module, name TBD during authoring, and extends
  whatever Core capability module PA4 establishes (`Gasm/Core/` — check PA4's actual
  landing location once merged).

## Notes

- 2026-08-27: priority 7.0 — Vulkan host model + GPU capability mapping is PA4's capability machinery applied to the graphics target — gates G7.

_(none yet — first entries append here as work begins; this is Law-5-class graphics-model
design work — consolidate Notes into a real docs/ design doc before implementation, and
route it through a fresh-agent design review before any implementation dispatch. Do not
waive review on this track — the pre-build audit this whole track responds to is the proof
that reviewing designs before code is where this project's cheapest findings come from.)_
