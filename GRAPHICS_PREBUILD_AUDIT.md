# Graphics Plans Pre-Build Audit (2026-08-27)

> Opus audit of the unbuilt graphics plans (`docs/GRAPHICS_ARCHITECTURE.md`,
> `docs/TARGETS/SPIRV_VULKAN.md`, Spikes 6/7) against the ratified lenses
> (VISION, Laws 9–13, EQUIVALENCE_PROOFS §1.1, SYSTEM_EFFECTS §6, PLAN decisions).
> Zero graphics Lean exists and no `REF:` cites either graphics doc, so every fix
> below is cheap now and expensive after code. VERDICT: **NOT ready for Spike 6.**
> Repo-root ledger companion: MODEL_DEBT.md §D.

## 1. Law 5 stop-and-design backlog

Blocking Spike 6 (compute/headless):
1. `docs/TARGETS/DXIL_D3D12.md` — DXBC container, LLVM-3.7 bitcode, DXC signing, root signatures, COM vtable calling. **No DXIL/DXBC/D3D12 reference corpus is ingested** (Law 4); no MANIFEST entry.
2. `docs/TARGETS/WGSL_WEBGPU.md` — same; no `references/wgsl` or `references/webgpu`.
3. GPU memory & capability model (see §7).
4. GPU observation & synchronization model (see §2) — the single largest undesigned item.
5. Floating-point determinism profile (see §2) — the hardest open question in the plan.
6. GPU differential-validation harness design (oracles + Law 13 control vectors, §3).
7. `Environment` extension for GPU — adapter enumeration, device features/limits, memory heaps, format support (today there is no binder to quantify over).

Blocking Spike 7 additionally:
8. `docs/TARGETS/WIN32_WINDOWING.md` (RegisterClassEx/CreateWindowEx/GetMessage/DispatchMessage/WM_*) — nothing windowing is vendored.
9. WSI/swapchain doc (vkAcquireNextImageKHR, OUT_OF_DATE/SUBOPTIMAL, present modes) — `references/vulkan/ch_40` IS ingested.
10. Reactive multi-loop design — Spike 6 already trips the "before the first threaded spike" trigger (host + device queue are two agents).

Ingestion in place to lean on: full SPIR-V unified spec; Vulkan 1.3 incl. `ch_07_synchronization`, `appendix_b__memory_model`, `appendix_i__invariance`, `ch_23_queries`. Missing: GLSL.std.450 extended instruction set (fine for a deterministic compute spike; blocking for transcendentals).

## 2. Observation standard mapping

- Vulkan/DX12/WebGPU entry points are the analog of `VirtualAlloc`: **audit trace, attached to per-target typeclass instances — not equivalence observables**. The contract trace for Spike 6 is what leaves the process: PNG bytes on disk + exit code. The GPU is an internal coprocessor exactly as an allocator is internal.
- `GRAPHICS_ARCHITECTURE.md:59-72` gets this backwards: `GpuEvent` mixes resource/command events (audit) with dispatch/readback (contract-ish) in one trace, and §7.3's "100% constructive trace equivalence across all 4 target pairings" is **incoherent under §1.1** — a trace containing Vulkan resource events can never equal a DX12 trace.
- **Top finding: `readbackPixels (buffer) (pixelCount)` carries no pixel data.** The trace records that a readback happened, not what came back — an implementation rendering garbage satisfies trace equality. The VISION §2 canned-output exhibit rebuilt in a new domain.
- Sync: `SPIRV_VULKAN.md:65-67` models barriers as a resource-layout FSM claiming WAR/WAW prevention — **RAW is omitted** (Spike 6's critical hazard: shader store → transfer read), and a layout FSM will "prove" a barrier correct with an empty srcAccessMask (the classic real bug). The right shape: Vulkan's own memory model — synchronizes-with / happens-before / availability+visibility (`appendix_b` §§367, 481, 545, 563) mapped onto the repo's VectorClock machinery. **vkQueueSubmit = host→queue edge; fence = queue→host; semaphores = queue→queue; barriers = intra-queue with availability/visibility.** GPU work is where the dormant causal machinery becomes load-bearing FIRST — earlier than threading.
- **FP vs both-ways equality — MAJOR, docs silent.** Vulkan: "not pixel exact... does not guarantee an exact match between images produced by different Vulkan implementations" (`appendix_i:24-26`); repeatability is per-device only and relaxed for shaders with side effects (i.e. storage-buffer compute); absent decorations, contraction/reassociation are permitted. Buildable answer: a **Deterministic Shader Profile** (integers + basic FP ops only, NoContraction, float-controls execution modes as hard device preconditions) inside which both-ways byte equality survives; outside it, ULP-tolerance refinement + liveness, and cross-driver equality abandoned. Corollary: **the planned gradient-triangle spike is the worst possible first spike** (rasterization tie-breaks are implementation-defined); Spike 6 should be compute-only.
- Second determinism condition: dispatch determinism requires **disjoint invocation writes** — a per-invocation capability obligation (Law 11 machinery as the determinism proof).

## 3. Differential validation — absent from the docs

Two axes: model faithfulness and artifact validity. Oracles: **SwiftShader/lavapipe** (deterministic CPU reference) primary; real GPUs as cross-vendor divergence detectors; **SPIRV-Tools** (`spirv-val`, `spirv-dis`/`as` roundtrip — a finite-∀ structural gate and Law 12 connection theorem vs the ingested `spirv.core.grammar.json`); **WARP** for DX12; **naga/Tint/wgpu** for WGSL. The `spirv-val` "guarantee" claim at `SPIRV_VULKAN.md:46` must become a build-time Lean SPIR-V validator + ∀-over-registered-shaders validity theorem (the Wasm precedent), with spirv-val demoted to external cross-check. Law 13 controls: positive (known dispatch), negative (malformed modules MUST be reported as rejection, not laundered — the V8 INVALID/TRAP lesson), device-loss control, **driver-absent aborts the run**, and an **FP-divergence canary** (a vector that differs when float-controls are not honored). Except-typed outcomes throughout.

## 4. Read-binder / anti-pointwise mapping

The GPU analog of `read` is **input buffer/texture contents** plus device-reported limits. Spike 6 as specified renders a fixed gradient with no input — its equivalence theorem is pointwise by construction, satisfiable by a shader that stores a precomputed table (the Tier-1 pattern). Golden-image comparison is likewise pointwise and cannot count as verification. Law 9-compliant statement: *for all input buffer contents b (within declared bounds), all dispatch dimensions within advertised limits, all memory-model-permitted interleavings, readback = specFn(b)* — with write-set race-freedom a discharged side condition and `evalShader` differentially validated. Readback via staging copies is the input-chunking dual and must be robust to arbitrary partial copies.

## 5. Performance model + placement queries

The graphics docs say nothing about cost, bandwidth, occupancy, timestamps, or transfers — staging buffers appear as a mechanism with no cost attached, precisely the term that flips placement decisions. Perf oracle: `VK_QUERY_TYPE_TIMESTAMP` bracketing (`timestampPeriod` scaling, `timestampValidBits` masking; `ch_23`/`ch_24` are ingested) + a PCIe bandwidth benchmark (size × direction × pinned × batching → affine `latency + bytes/bandwidth` terms per device profile), median-of-N + warmup + calibration subtraction (the wsc technique), range containment + rank-order faithfulness as the criterion. Cost shape making placement computable: `cost_gpu(N) = upload(N) + dispatch(N) + readback(N)` in nanoseconds under a named device profile, comparable to `cost_cpu(N)` via the CPU profile's clock. Occupancy/coalescing/divergence make GPU body-cost far less predictable than a uop model — first version deliberately coarse, validated for monotone faithfulness only. **Recommendation: Spike 6 carries NO perf contract, explicitly, until the timestamp/bandwidth harnesses are calibrated.**

## 6. Reactive contracts (Spike 7)

The present loop is a `VerifiedReactiveProgram`: inner = per-frame deterministic equality for every input-event sequence; outer = liveness. Complications: `vkAcquireNextImageKHR` returns a nondeterministic image index and OUT_OF_DATE/SUBOPTIMAL on resize are spec-permitted — so the outer obligation is refinement + liveness, with the recreate-swapchain path *inside* the ∀ domain. Host + device queue are two agents even single-threaded, so multi-loop composition (deadlock-freedom of frames-in-flight fence/semaphore rings, explicit fairness) applies at Spike 6 already. Windowed observability: defensible answer = contract-trace observables are the sequence of presented image contents (validated headlessly via an offscreen mirror), presentation itself audit-trace.

## 7. Capability / memory-safety mapping (Law 11)

Handles are tracked via linear obligations; memory ranges are not. Needed: host-visible mapped ranges under Law 11 literally (real pointers today); device-local capability over `(VkDeviceMemory, offset, size)` with vkBindBufferMemory as hierarchical provenance/borrows (MEMORY_PROVENANCE §1.2 reuse); **descriptors as capability handoff to the device** with fence-guarded temporal release (`MustNotFree until fence signaled`); shader-side `OpAccessChain/OpLoad/OpStore` bounds proofs against descriptor ranges that fail to assemble; GPU `ObligationType` constructors (doc before Lean, Law 1). Concrete bug: `SPIRV_VULKAN.md:43`'s `returnVoid (h_clean : ∀ (s : ComposedState spirv S), s.obligations = [])` quantifies over ALL states rather than the exit state — unprovable for any inhabited state type with a nonempty ledger; the terminator is unconstructible as written.

## 8. Contradictions & staleness

- `STDLIB_PNG.md:10` says "Headless GPU Readback (Spike 5)" — stale (Spike 5 is gzip).
- Target count internally inconsistent: §2 lists six, §1 mermaid shows four, §7.3 claims "all 4 pairings".
- Naming drift: `Gasm.Targets.Spirv/Dxil/Wgsl` vs `Gasm/SPIRV/` vs `Gasm.SPIRV`; real tree is `Gasm/Targets/*`.
- `SPIKES.md:11` / `PLAN.md` law-count references need updating to 13.
- Doc-level twin (Law 12 spirit): `GRAPHICS_ARCHITECTURE.md:118-126` copies `png_idempotent_canonical_roundtrip` verbatim from `STDLIB_PNG.md` — cite, don't copy.
- **Wasm+Vulkan targets are fiction as written**: browsers have no Vulkan; WASI has no GPU; "Host FFI trampolines" = inventing host imports, the same defect class as Spike 4's fabricated `sock_*`. Target 3 impossible; target 6 needs a real documented import surface.
- **D7 violation**: six speculative targets, zero built, is the bulk-import pattern D7 forbids. Shrink to ONE (Windows x86-64 + Vulkan compute, headless); demote the rest to a non-obligating "possible futures" appendix. Law 2 exposure: any `REF:` citing the six-target section makes all six a 100%-implementation obligation.

## 9. Verdict and top-10 pre-build fixes

**NOT ready for Spike 6.** Three load-bearing conflicts: the trace design cannot observe the rendered result; cross-target bit-exact equality is forbidden by the Vulkan spec itself; synchronization is a layout FSM instead of happens-after edges. Ranked amendments:

1. Redefine Spike 6 as **parametric compute** (∀ input buffer b, readback = specFn(b)); delete the input-free gradient. *(Law 9 / VISION §2.)*
2. Give `GpuEvent.readbackPixels` a payload; split contract vs audit trace. *(§1.1; Law 8.)*
3. Author the GPU sync model on Vulkan's memory model — synchronizes-with edges in `canonicalizeTrace`, availability/visibility, **add RAW**. *(SYSTEM_EFFECTS §6.3-6.4.)*
4. Author the FP determinism section + **Deterministic Shader Profile** with float-controls as hard preconditions; ULP-refinement elsewhere; no bit-exact rasterization claims. *(§1.1 vs appendix_i.)*
5. Shrink the six-target matrix to Win-Vulkan-compute; non-obligating appendix for the rest; fix 6/4/4. *(D7; Law 2.)*
6. Author the GPU differential-validation design (lavapipe/SwiftShader/WARP/naga; positive+negative+device-loss+FP-canary controls; Except-typed; abort-on-absent-driver). *(VISION §3.2; Law 13.)*
7. Replace the spirv-val claim with a gate: Lean SPIR-V validator + ∀-registered-shaders validity theorem; grammar-driven encode/decode roundtrip. *(Law 13; Law 12.)*
8. Author the GPU memory capability section (device provenance, descriptor handoff with fence-guarded release, shader bounds proofs, GPU ObligationType). *(Law 11.)*
9. Author the GPU cost + placement model design (common time currency, PCIe terms, timestamp/bandwidth oracles under controls); **Spike 6 carries no perf contract until calibrated — say so**. *(VISION §5.)*
10. Ingest missing references + MANIFEST entries (DXIL/DXBC, D3D12, WGSL, WebGPU, Win32 windowing, SPIRV-Tools) or explicitly defer those targets. *(Laws 4, 6.)*

Housekeeping: STDLIB_PNG Spike 5→6; naming drift; law-count refs; duplicated PNG theorem; the `returnVoid` quantifier bug.
