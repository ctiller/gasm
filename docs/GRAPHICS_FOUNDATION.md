# Graphics Foundation Prototype: SPIR-V, Vulkan, and Win32 Window/Input

**Status:** nonnormative exploratory prototype. This document does not select or close the
SPIR-V/Vulkan future profile required by `docs/MEMORY_MODEL.md` §15.1, does not define a public
graphics semantic API, and does not authorize verified artifact emission.

This prototype exists to make the first graphics design choices executable without getting ahead of
the canonical memory/concurrency model or the active ABI/CFG work. Its Lean modules live under
`Spikes/GraphicsFoundation/` and are intentionally absent from the `Gasm` umbrella. They may be
discarded or rebased when the exact graphics profile, shared authority algebra, and boundary
certificates are accepted.

The registered `spirv-grammar` source was hash-verified on 2026-08-29. Refreshing the registered
rolling `spirv-spec` and `vulkan-spec` pages on the same date reported hash drift, so this prototype
does not treat either live page as a newly accepted pin. Opcode and enumerant values in the SPIR-V
subset are connected only to the cached, hash-matching grammar data. Vulkan transitions below are a
conservative executable architecture sketch grounded in the already-reviewed project documents;
they are not a claim of conformance to a newly selected Vulkan edition.

---

## 1. Layering and authority boundary

The governing architecture is `docs/MEMORY_MODEL.md` §§3, 6, and 11:

1. Logical requirements remain placement-free.
2. A domain plan chooses Vulkan agents, queues, references, bindings, relations, and failure modes.
3. A target realization later proves the selected Vulkan plan is implemented by exact loader,
   calling-convention, driver, SPIR-V, and emitted-artifact behavior.

The prototype therefore keeps four concepts separate:

- generative logical identities, never reconstructed from raw handles or addresses;
- ownership/authority and cleanup obligations for host, device, and callback contexts;
- Vulkan-domain execution/completion transitions, which are not CPU program order;
- target-owned ABI, loader-symbol, callback-entry, and artifact identity certificates, which are
  deliberately absent here.

`ValidatedModule` and Vulkan transition success are local certificates only. Neither is a
`VerifiedProgram`, and neither can write or publish an executable artifact under verified authority.

## 2. Frontend-local SPIR-V subset

The SPIR-V prototype selects only the compute entry-point skeleton needed to serialize and inspect a
minimal module:

- `OpCapability Shader`, `OpMemoryModel Logical GLSL450`;
- `OpEntryPoint GLCompute` and `OpExecutionMode LocalSize`;
- void/function types, function start/end, labels, selection merge, branches, and return.

IDs are phantom-typed (`TypeId`, `FunctionId`, `ValueId`, `BlockId`) and scoped by a generative
`ModuleScope`. A raw number in one role cannot be silently used in another. The scope is
frontend-local so it can later be replaced by the core nominal `BlockId` without changing the
instruction vocabulary.

Structural validation checks the selected grammar only: nonzero and in-bound IDs, unique result IDs,
defined branch destinations, entry-point/function agreement, local-size declaration, function/block
bracketing, block termination, and `OpSelectionMerge` immediately preceding the selected
`OpBranchConditional` form. It deliberately imposes no rasterization, descriptor, floating-point,
dominance, loop, or future-feature obligations that the small compute grammar cannot express.

Serialization emits an in-memory `Array UInt32` beginning with the five-word SPIR-V physical header.
It is data for inspection and later target-owned linking. Structural acceptance does not establish
semantic shader correctness, Vulkan-environment acceptance, driver correctness, or equivalence to a
pure kernel.

## 3. Vulkan host lifecycle prototype

The host model specializes the authority rules of `docs/MEMORY_MODEL.md` §6.1.2 rather than treating
a buffer handle as a CPU pointer. Device memory, buffers, bindings, descriptor references, command
buffers, fences, and submissions each have generative, device-owned identities. A binding records
both logical resource identity and the exact backing generation/range.

Every operation returns an explicit success or failure. Limits cover allocation count, total device
bytes, buffers, descriptors, command buffers, and in-flight submissions. Partial construction is
observable in the returned state: a later failure does not erase resources successfully constructed
earlier, so callers must execute the available inverse operations.

Command submission snapshots the exact descriptor, logical buffer, binding, backing-allocation
generation, and range, transfers those leases to the device agent, and changes the command buffer and
fence to pending. A descriptor captured by an active submission cannot be updated. Host submission
order does not complete work. An explicit device-completion transition records `executionComplete`,
leaves the correlation record live, and physically signals the fence; it deposits a
`completedButUnobserved` return credit rather than granting host authority. Successful, repeatable
host observation of the still-signaled fence separately materializes `hostReuseAllowed`. Range-scoped
`availableToHost` and `visibleToHost` consequences are separate again; the latter requires an
explicit host-visibility transition and is never inferred from fence wait alone. Resource destruction
is rejected while a descriptor, binding, or active/unobserved submission still owns or borrows the
resource.

The prototype's nonsparse binding policy is deliberately conservative: buffer destruction internally
retires its immutable binding generation, and backing-memory reclamation is a separate operation that
requires no live logical alias or device lease. Vulkan may permit some reclamation patterns that this
first executable subset rejects. Buffer destruction alone never implies allocation reclamation.

Cancellation means stopping new cooperation or abandoning a host wait. It never revokes work already
submitted to the device and never releases its resource-retirement obligations. Device loss records a
local device-phase transition but preserves every live resource and obligation. A separate
loss-aware wait/idle disposition may retire one exact submission's device-use leases for cleanup while
marking its results and contents unusable; an arbitrary device-loss error does not retire unrelated
work. Generational validation remains available after loss so child destruction and memory free can
discharge the retained cleanup ledger.

Generational handles are checked together with their parent device. Stale generation, wrong parent,
wrong kind, double destruction, and destruction-order violations are ordinary typed failures.

## 4. Window and input prototype

The Windows model separates portable input meaning from Win32 message realization. Its selected
surface covers class registration, window creation, keyboard, character, mouse motion/buttons/wheel,
resize, focus, close request, destruction, and quit.

Window classes, windows, queued messages, and callback entries are owned by one UI thread. Dispatch
creates a linear callback token and increments callback depth; returning consumes the exact token.
Nested dispatch is therefore representable without pretending callbacks are ordinary sequential
calls. A close request does not destroy the window. Destruction invalidates the live handle and later
quit processing terminates the loop.

The model records semantic import requirements, not DLL names, symbol spellings, register placement,
TLS state, callback machine entry, or PE import identity. Those belong to a later Windows boundary
profile and link certificate. Until that exists, no window-capable verified export is claimed.

## 5. Cube and presentation prototype

The cube slice is still nonnormative because the accepted graphics profile is compute-only and the
registered rolling Vulkan/SPIR-V sources have drifted. It nevertheless makes the future
rasterization/WSI obligations executable without importing them into the public API.

`Cube.lean` fixes eight exact logical vertices, twelve nondegenerate indexed triangles, and the
vertex-to-fragment color interface. Lean proves the finite geometry indices are in range and the
selected stage interface matches. Rotation remains a parametric frame input: the prototype does not
claim bit-exact equivalence between mathematical rotation and native floating-point shader results.

`Presentation.lean` keeps instance/window-scoped surfaces and device-scoped swapchain, image, shader,
pipeline, depth, semaphore, and frame identities separate and generational. A frame identity is only
correlation; authority is carried by orthogonal facts for exact image acquisition, acquire-signal
availability/consumption, render and depth submission leases, present-wait registration/consumption,
presentation-engine use, and image-reuse credit. The single selected path uses one swapchain and one
queue family; it does not invent a queue-family transfer.

Acquisition is result-indexed: success/suboptimal return an exact image generation, while not-ready,
timeout, out-of-date, surface-loss, and device-loss outcomes return no image authority. Presentation
may enqueue an exact render-semaphore wait before execution completes. An opaque `PresentReadyWitness`
captures the exact image, swapchain, pipeline, required layout, same-family disposition, and render
dependency without inventing Vulkan memory relations before profile intake. Render completion may
return command/pipeline/depth leases but cannot retire present-engine use or its semaphore wait.
Optional begin-present observation is separate and is not called display visibility.

Binary semaphore use is a single linear, frame-indexed sum state. Acquire and render-finished roles
must use distinct idle semaphore generations; every signal, queue-wait registration, signal
availability, and wait-consumption transition checks its exact frame owner. Recording may name a
shared depth attachment, but submission atomically rechecks and acquires its depth lease, closing the
record/submit TOCTOU interval.

A same-image reacquisition is eligible to retire prior presentation use only after that exact prior
frame's render execution and registered presentation wait have completed. Out-of-date and
surface-lost present results are modeled as enqueued rejections: they register and later consume the
semaphore wait and release image acquisition, but create no presentation-engine/display lease.
Pre-enqueue host/device allocation failures are separate no-effect outcomes and do not consume the
one-shot readiness witness. Device loss remains an uncertain transition that preserves records.

Reacquisition of the same image generation is the selected witness that retires its prior present
use and grants reuse credit; a host render fence is insufficient. Recreation allows coexisting
swapchain generations and retires the old swapchain for new acquisitions even when replacement
creation fails. Already-acquired images may continue through presentation. Swapchain images are
implementation-owned: destroying the handle moves them to a separate backing-retirement ledger,
which may outlive the handle. Surface/device loss preserves unresolved ownership records.

An explicit presentation-agent completion transition provides the selected closure path for a
retired old swapchain generation when reacquisition is no longer possible. It is intentionally not
derived from a render fence. Swapchain destruction waits for application render leases and queued
semaphore waits, retires every implementation-owned image generation, and may leave presentation
backing in the independent ledger until the presentation agent closes its exact use. Out-of-date is
monotone, recreation requires the same surface and a previously non-retired old swapchain, and frame
capacity exceeds image capacity so the correlation record needed for reacquisition credit is not
itself exhausted.

The base-KHR model has no public acquired-image release operation. The optional
`releaseAcquiredImageExt` transition is feature-gated by `swapchainMaintenance1`; when the extension
is absent it returns `extensionUnavailable` without changing ownership. Otherwise an unsubmitted
acquired image remains obligated until presentation or parent swapchain destruction.

The presentation model captures a local serialization digest for each shader only as correlation
data. It does not prove that a native shader module has those bytes or that the Vulkan implementation
accepted it. A later target-owned artifact/link certificate must establish those identities.

## 6. Opt-in native behavior probes

`scripts/run_graphics_window_probe.ps1` is an explicitly unverified, opt-in Windows behavior probe.
It may open a native window, observe keyboard/mouse/resize messages, and provide differential evidence
for later modeling. It is not imported by Lean, is not part of verified emission, and cannot create a
`ValidatedModule`, Vulkan certificate, equivalence theorem, or `VerifiedProgram`.

`scripts/run_graphics_cube_probe.ps1` launches the optional managed cube probe. It pins Veldrid
packages, requests its Vulkan backend explicitly, compiles the selected vertex and fragment GLSL to
SPIR-V at runtime, and draws a continuously rotating indexed cube in a resizable input window.
Escape closes it and the arrow keys alter its rotation axis.

The optional managed cube probe uses a Vulkan-only backend and runtime GLSL-to-SPIR-V compilation.
It is behavioral evidence, not a realization certificate, and its package/runtime/native-library
identity is not part of `VerifiedProgram`.

## 7. Promotion gates

Promotion from this spike into `Gasm/Targets/*` requires all of the following:

1. the immutable Vulkan/SPIR-V profile and reference intake required by
   `docs/MEMORY_MODEL.md` §15.1;
2. replacement/adaptation of prototype authority records to the accepted shared generative
   authority/obligation algebra;
3. reviewed Vulkan synchronization and deterministic-kernel profiles;
4. grammar connection and registered-shader validation over the selected SPIR-V grammar;
5. native Vulkan/Win32 callable-entry, loader/import, callback, and artifact/link certificates;
6. composition through the sole final proof/emission authority, `VerifiedProgram`;
7. positive and negative differential controls, including stale handles, exhaustion, partial
   construction cleanup, invalid structured control flow, early resource destruction, abandoned
   waits, device loss, reentrant callbacks, and close-versus-destroy behavior.
