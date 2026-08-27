# MODEL DEBT LEDGER — gasm machine/OS models

> Inventory of what the machine/OS models omit or simplify. Lives at repo root
> (like PLAN.md): this is a ledger, not a design spec — items graduate into
> docs/ design documents (Law 5) when their forcing function arrives. Debt is
> chosen, not discovered (VISION.md §3.3).
> Produced by Opus deep audit 2026-08-27; line numbers from that day's tree.
> Supplement (sections E–F + target-class tag table) appended 2026-08-27.

**Framing.** Two lenses. Performance debt mis-*ranks* optimizations (bad search, not bad code). Correctness debt mis-*states axioms* (bad proofs). Where a model surface is not exercised by any differential harness, the entry says so — unvalidated surface is where both kinds of debt hide.

---

## A. PERFORMANCE-MODEL DEBT

**A0. There is no memory hierarchy at all — not even unused constants.**
No L1/L2/L3 latency constants exist anywhere in `Gasm/`. `MicroarchProfile` (`Gasm/Targets/X86_64/Uop.lean:57-68`) has fields for fetch bandwidth, decode/rename/dispatch/retire widths, ROB capacity, branch-mispredict penalty and active ports — and *nothing* about caches, TLB, store buffer, line size, or frequency. Every load in the ISA is a flat `latencyCycles := 4` (`Mov.lean:422,525,568`, `Pop.lean:35`, `Ret.lean:25`, `Call.lean:29`), independent of address, stride, or working-set size. **When it bites:** immediately on zlib. A sliding-window LZ77 match loop over a 32 KB window and a Huffman table lookup have wildly different real costs and identical model costs; any blocking/tiling/prefetch/table-layout transformation is invisible to the model, and a variant that halves cache misses will be ranked *equal or worse* than one that reduces uop count. **Validation:** pointer-chase and stride-sweep microbenchmarks under the (planned) RDTSC harness. **References:** SDM is vendored, but it does not carry latency tables — Intel *Optimization Reference Manual*, Agner Fog, or uops.info must be ingested (Law 4). None are present in `references/`.

**A1. Dependency chains are not modeled in the nominal cost.**
`computeCycleBounds` (`Performance.lean:76-96`) computes `nominalCycles = max(minCycles, maxPortCycles, divLatencyTotal)`. `latencyCycles` enters *only* via the `intDiv` filter (line 88). Ten dependent `ADD`s and ten independent `ADD`s produce identical nominal cycles. `maxCycles` is the fully-serial sum (line 92), i.e. the model offers throughput-only or latency-only, never the true `max(port-bound, critical-path)`. **Severity: critical for the zlib epic.** Every latency-hiding transformation — unrolling to break a CRC or adler accumulator chain, software pipelining, reassociation into independent accumulators — is exactly the class this cannot rank. **Validation:** RDTSC on paired kernels (dependent vs independent chains). **Cost to model:** moderate — requires uops to carry register read/write sets, which `X86_64Uop` (`Uop.lean:47-53`) does not.

**A2. Port pressure is a uniform-spread approximation, not a scheduling LP.**
`computePortPressure` (`Performance.lean:62-72`) adds `1/|eligiblePorts|` to *every* eligible port. A uop restricted to `{p0}` and one eligible on `{p0,p1,p5,p6}` do not compete correctly: the constrained one is not given priority. This over-charges wide-eligibility ports and under-charges narrow ones, systematically flattening port-pressure differences — the very signal the model exists to expose. **Bites:** shift-heavy vs ALU-heavy bit-reader variants in DEFLATE.

**A3. Five of ten `MicroarchProfile` fields and one of five `X86_64Uop` fields are dead.**
Grep-verified: `reciprocalThroughput` (`Uop.lean:52`), `fetchBandwidthBytes`, `renameWidthUops`, `retireWidthUops`, `robCapacityUops`, `optMode` have **zero read sites**. Only `dispatchWidthUops`, `activePorts`, `branchMispredictPenalty` and (waterfall-only) `decodeWidthUops` are consulted. Consequence: `skylakeProfile` vs `goldenCoveProfile` vs `zen4Profile` (`Uop.lean:87,72,102`) differ observably only in dispatch width, port count and mispredict penalty — the model cannot express that Zen 4 and Golden Cove schedule differently. `reciprocalThroughput` being dead means throughput limits are inferred purely from port counts. **This is a Law 8 dead-abstraction exposure as much as a fidelity gap.**

**A4. Branch prediction is "every branch mispredicts, in the pessimistic bound only."**
`maxCycles` adds `branchCount * branchMispredictPenalty` (`Performance.lean:93-94`) — unconditionally, for every branch uop including unconditional `JMP` and `CALL`. Nominal adds nothing. There is no taken/not-taken model, no loop-exit special case, no BTB/indirect-branch cost. **Bites hard on zlib:** branchless (CMOV) vs branchy Huffman decode is *the* canonical DEFLATE tradeoff, and the model ranks it purely on uop count — CMOV loses, always, regardless of entropy. Under an unpredictable-symbol stream the real answer inverts. **Validation:** RDTSC on branchy/branchless decode pairs over high- and low-entropy inputs.

**A5. No fusion, no front-end limits, no alignment, no store forwarding, no TLB, no frequency.**
Macro-fusion (`CMP`+`Jcc` → 1 uop) is unmodeled, so every compare-and-branch is charged 2 uops — biasing the search *toward* fused-idiom-avoiding code. Micro-fusion of load+op likewise. `fetchBandwidthBytes` and `decodeWidthUops` never gate the nominal path, so 16-byte-fetch effects, uop-cache hit/miss, LSD, and code-alignment (JCC erratum, 32B-boundary) are absent — an unroll that blows the uop cache is scored as pure win. Store-to-load forwarding and 4K aliasing are absent, which matters directly for LZ77 overlapping copies. Turbo/frequency and TLB are absent (the latter fine at current scales).

**A6. TMAM is unvalidatable dashboard output.**
`computeTMAM` (`Performance.lean:100-141`) derives every number from fixed coefficients: front-end bound is hard-capped at `15.0` (line 120), memory-bound splits are literal `0.5/0.2/0.1/0.05` fractions of memory-uop count (lines 133-136), bad-speculation is `branchUops * 2.0` (line 119). None of these are measurements or derivations. Ledger position: **explicitly demote or delete** — it currently reads as authoritative telemetry.

**A7. The perf fuzzer validates the model against itself.**
`verifyPerfInvariants` (`Fuzzer.lean:150-175`) checks uop conservation and `0 < min ≤ nominal ≤ max`. Both hold for an arbitrarily wrong model. There is no RDTSC anywhere in the tree; `HardwareHarness.lean` captures 16 GPRs + RFLAGS + a faulted byte (`HardwareHarness.lean:29-70`, 136-byte record) and no timestamps. **Forcing function:** the zlib epic is unstartable as a *ranking* exercise until containment (`real ∈ [min,max]`) plus rank-order agreement exists.

**A8. Concrete coefficients have no vendored source (Law 4 gap).**
Every perf declaration cites `references/intel_sdm/vol_1.../ch_03_basic_execution_environment.md#32-overview...` — a generic anchor that contains no port, latency, or throughput data. Spot-check of two coefficients against public data: `SHL/SHR r64, CL` is modeled as **1 uop** (`Shift.lean:158,188`) but is 3 uops on Intel P-cores (flag-merge) — directly relevant to DEFLATE bit-readers; `DIV r64` is modeled as 5 uops / 14 cycles (`Div.lean:43-49`) against a real ~36-uop, 30-90-cycle operation. These numbers are currently *invented*, not cited. (Both spot-checks are hypotheses-to-measure, not vendored facts — which is itself the argument for this entry.)

---

## B. CORRECTNESS-MODEL DEBT (x86-64 + Wasm)

**B1. No memory ordering model exists, despite the doc asserting one.**
`docs/TARGETS/X86_64.md` §3 states TSO and displays a theorem `x86_mov_store_is_release` referencing `m.getMemoryType` and `m.isNonTemporalInstr`. Neither symbol, nor any memory-type notion, exists in the code. The model is a single-threaded `memory : Address → Byte` total function (`Registers.lean:43`) — ordering is trivially program order. **Severity: low today (single-threaded), blocking for the concurrency work sketched in PLAN.md Phase 4(d).** Near-term fix: the doc *overclaims* — reconcile it.

**B2. No atomics, no `LOCK`, no fences, no `CPUID`/`RDTSC`.** Grep-confirmed absent. `XCHG` exists but only in its non-locked reg-reg form. Forcing functions: any threaded spike; also the RDTSC perf harness (A7) needs `RDTSCP`+`CPUID` as *modeled* instructions or an explicitly out-of-model harness escape hatch.

**B3. The memory model has no faults, no permissions, no canonicality, no alignment.**
`memory : Address → Byte` is total and everywhere-defined; `write8`/`write64` (`Registers.lean:221-236`) succeed at any address. There is no page table, no unmapped region, no W^X, no canonical-address (bits 63:48) check, no `#GP`/`#PF`, no alignment-check semantics. Only `#DE` is modeled (`Div.lean:29,37` are the *only* two `faulted := true` sites in the tree). Consequence: a proof of a Zlib routine cannot distinguish "correct" from "scribbles outside its buffer" — precisely the risk PLAN.md flags for `Zlib/Windows.lean`'s hand-offset 4096-byte scratch. **This is what Law 11 capabilities are for; until they bind, the memory model actively hides the bug class.**

**B4. No FPU/SSE/AVX state.** No XMM registers, no MXCSR, no x87. Excludes: all SIMD (`PCLMULQDQ` CRC32, vectorized adler32, wide `MOVDQU` copies — likely zlib-epic demands), the float half of the Windows ABI (`XMM0-3` args, `XMM6-15` callee-saved per `docs/TARGETS/WINDOWS.md` §1.1 — the model cannot state that obligation), and Spike 6/7 entirely.

**B5. No segment registers / FS/GS.** No TEB access, no stack-cookie (`GS:[0x28]`), no TLS. Blocks any realistic Windows runtime interop.

**B6. Self-modifying / dynamically generated code is unrepresentable.** `instructionAtRip` (`Semantics.lean:29-37`) walks a static `List X86_64Instr` and re-encodes to advance — code is not in `memory`. Also an O(n²) perf wall already noted in PLAN.md.

**B7. Wasm: out-of-bounds accesses do not trap — and silently mutate memory size.**
`readMem8` returns `0` past the end (`Wasm/Semantics.lean:63-64`); `writeMem8` **appends zero-padding and grows the array** (lines 92-97). No load/store checks bounds (lines 326-349). Real Wasm traps. Worse, an OOB store changes `memory_size`'s answer (lines 350-352), so the divergence is observable, not merely latent. **Structurally invisible to the current fuzzer:** `Fuzzable.lean:136-158` generates only in-bounds addresses (16, 64) in exactly one page. **Severity: high** — a live soundness gap in a model the project already claims is engine-validated.

**B8. Wasm: `Limits.max` and `memory_grow` failure are dead.** `Limits.max` (`Types.lean:35`) is never consulted; `memory_grow` (`Semantics.lean:353-358`) always succeeds, never returns `-1`, and binds an unused `_newSize`. Already on PLAN.md Phase 3.

**B9. Wasm: large ISA and validation gaps.** Absent: all f32/f64 (declared in `ValType`, zero instructions), all *signed* ops (`div_s`, `rem_s`, `lt_s`, `shr_s` …), `clz/ctz/popcnt/rotl/rotr`, sub-width loads/stores beyond `load8_u`/`store8`, `br_table`, `call_indirect`/tables, multi-value, and function calls proper (`.call idx` is delegated wholesale to the host hook, `Semantics.lean:369`). `global_get`/`global_set` exist in the AST (`AST.lean:29-30`) with **no semantics and no globals in the machine state** — they fall through `| _ => (s, .next)` (`Semantics.lean:393`) as silent no-ops. There is no validator: `popI32` on a type mismatch returns `0` (`Semantics.lean:44-47`) rather than rejecting.

---

## C. OS/ENVIRONMENT-MODEL DEBT

**C1. `ReadFile` cannot return fewer bytes than available.** `readFileHook` (`Win32API.lean:85-104`) reads `min(nNumberOfBytesToRead, |stdinBuffer|)` and always returns `RAX=1`. It therefore models *disk* semantics only. It cannot express: a pipe delivering 7 bytes when 4096 were requested with more coming; console line-buffering (one line per call, CRLF, Ctrl-Z EOF); `FALSE` + `ERROR_BROKEN_PIPE`; or handle-type differences at all — the handle in `RCX` is **never read**. Given "`read` as the universal binder" (Law 9 / PLAN Phase 4), this is the single most load-bearing OS gap: a `∀ read-result` contract proven against a model that can only produce maximal reads proves nothing about chunk-robustness. **The Win32 differential harness must pin this first.**

**C2. `WriteFile` never short-writes, and ignores the handle.** `writeFileHook` (`Win32API.lean:108-122`) always writes all `R8` bytes, always succeeds, and always emits `ConsoleEvent.out` — so **stdout and stderr are indistinguishable**, which also breaks the two-stream observation algebra `SYSTEM_EFFECTS.md` §6.1 depends on. Compounding this, `getStdHandleHook` (`Win32API.lean:75-79`) returns handle `1` for *both* `STD_INPUT_HANDLE` and `STD_OUTPUT_HANDLE`. There is no handle table and no lifecycle.

**C3. No error model whatsoever.** No `GetLastError`/`SetLastError`, no error codes, no failure paths on any hook. Every modeled Win32 call succeeds unconditionally. `references/windows/` contains only 6 pages (`readfile.md` is 28 lines and does mention `GetLastError` and pipe/console sequential semantics, so the source exists but is thin); no `VirtualAlloc`, `CreateFile`, console-mode, or overlapped-I/O documentation is vendored — yet `VirtualAlloc` is modeled.

**C4. `VirtualAlloc` is a constant.** `virtualAllocHook` (`Win32API.lean:132-135`) returns `0x20000000` regardless of size, address, or protection flags — **two allocations return the same pointer**. `virtualFreeHook` always returns 1 and tracks nothing. `Zlib/Windows.lean`'s fixed 8 MB/8 MB split rests on this.

**C5. Sockets are wholly invented.** `socket`→100, `accept`→101, `bind`/`listen`/`WSAStartup`→0 (`Win32API.lean:146-182`); `recv` delivers an entire queued request in one call and never short-reads or blocks (lines 186-203); `send` always sends everything. No `WSAGetLastError`, no `WSAEWOULDBLOCK`, no graceful-close (`0`) vs `SOCKET_ERROR` (`-1`) distinction, no blocking semantics. `acceptHook` on an empty queue sets `rip := 0` to terminate the program (lines 176-178) — an invention with no Win32 counterpart. Nothing opens a real socket against an emitted binary (PLAN Phase 6 concurs).

**C6. IAT interception rests on a synthetic loader convention.** `findIatIndex` (`Win32API.lean:247-251`) identifies an import slot by the slot containing *its own address* — a convention `loadMemory` invents (line 299). The real Windows loader writes the function VA. Dispatch is then positional 0-15 (lines 255-273), **skipping index 6 with no comment**, and `iatBase := (addr >>> 12) <<< 12` assumes the IAT begins exactly at a 4 KB boundary. Interception is keyed on an artifact of gasm's own emitter, not on OS behavior.

**C7. Four of six `Environment` fields are dead — the ∀ is partly vacuous.** `Environment` (`Core/Verification.lean:19-26`) declares `stdin, args, envVars, incomingRequests, fileSystem, clockTime`. Its `EnvironmentLoader` instance (lines 50-53) threads only `stdin` and `incomingRequests`; grep confirms **zero readers** for `args`, `envVars`, `fileSystem`, `clockTime`. So `traceEquivalence : ∀ (env : Environment)` (lines 70-72) quantifies over four dimensions that provably cannot influence the machine — universal in form, 2-dimensional in substance. There is no clock syscall hook at all (`ClockEvent` exists; `MonadClock` in `TraceM` returns `0`, `Effects/Trace.lean:61-64`).

**C8. WASI: `errno` is always 0, and `sock_*` are non-existent syscalls.** `wasiHostCall` (`WASI/ABI.lean:76-174`) discards `fd` (`_fd`), returns `0` from every path, never `EBADF`/`EFAULT`/`EAGAIN` (all four codes documented in `docs/TARGETS/WASI.md` §4 but unmodeled). `fd_read` cannot short-read. `sock_listen/accept/recv/send/close` (lines 129-171) are **not WASI preview1 functions with these signatures** — preview1 has no `sock_listen`, and its `sock_recv`/`sock_send` are iovec-based and errno-returning. Binaries importing these cannot run on any real engine, so the host oracle can never validate them. `initWasmMemory` (lines 67-72) allocates exactly one 65536-byte page and `set!`s data segments into it — segments past 64 KB are silently dropped. Missing entirely: `fd_close`, `fd_seek`, `args_get`, `environ_get`, `clock_time_get`, `random_get`, `path_open`. `references/wasi/preview1.md` **is** vendored, so this debt is ingestion-ready.

---

## D. GRAPHICS-FORWARD DEBT (brief)

Spike 6/7 demand model surface that does not exist in any form: floating-point semantics (B4 — SPIR-V is float-first, and the Vulkan spec's invariance appendix means bit-exact both-ways equality is likely *unachievable*, forcing a tolerance/refinement notion of equivalence the observation algebra does not yet have); a GPU-side memory and execution model with fences/semaphores/barriers as first-class happens-after edges (`Core/Types.lean`'s `VectorClock` is the right hook and is currently dead); COM vtable dispatch for DX12; asynchronous queue submission, which no current effect models; and a differential oracle story (spirv-val, lavapipe/WARP). Ingestion status is unusually good — Vulkan 1.3 (56 chapters incl. the memory model and invariance appendices) and SPIR-V unified are fully vendored; DX12/DXIL and WGSL are **not**, and per Law 5 the corresponding design docs do not exist. Note the golden-image tension: pixel-comparison tests are pointwise and therefore prohibited under Law 9 — the buffer-contents ∀-binder analogue is an open design question. **See GRAPHICS_PREBUILD_AUDIT.md for the full pre-build audit.**

---

## TOP-10 PRIORITY TABLE

| # | Item | Lens | When it bites | Cost to model |
| :-- | :-- | :-- | :-- | :-- |
| 1 | `ReadFile`/`fd_read` short reads, handle types, error paths (C1, C8) | Correctness/OS | Now — Phase 4 `read`-as-binder is unsound without it | M (harness + hook rewrite); refs ingestion needed for console/pipe |
| 2 | RDTSC harness + containment criterion; kill the self-referential perf fuzzer (A7) | Perf | Blocks the zlib epic's premise | M — extend the 136-byte record, calibration PE |
| 3 | Dependency-chain / critical-path cost (A1) | Perf | First zlib unroll or accumulator split | M — needs reg read/write sets on `X86_64Uop` |
| 4 | Wasm OOB trap + `memory_grow` bounds (B7, B8) | Correctness | Live soundness gap today; fuzzer blind to it | S — trap on bounds; add OOB fuzz vectors |
| 5 | Calibrate latency/throughput/uop-count tables against a real source (A8) | Perf | Every ranking decision; `SHL r64,CL` and `DIV` already suspect | S per entry, but **needs Law 4 ingestion first** (Opt. Manual / uops.info) |
| 6 | Branch-prediction model beyond "all branches mispredict, in max only" (A4) | Perf | Branchy vs branchless Huffman decode — the DEFLATE decision | M |
| 7 | Memory hierarchy: line size, L1/L2/L3, miss cost (A0) | Perf | LZ77 window and table-layout tuning | L — needs an address/working-set abstraction the uop model lacks |
| 8 | `Environment` dead fields + IAT/handle/`VirtualAlloc` inventions (C4, C6, C7) | Correctness/OS | Any ∀-claim over `Environment`; any real-loader interop | S (delete or wire dead fields) / M (handle table, allocator) |
| 9 | Reconcile `X86_64.md` §3 TSO claim + dead profile fields with the code (B1, A3) | Both | Now — docs overclaim; Law 8 exposure | S — doc + field deletion |
| 10 | XMM/SSE state and float semantics (B4) | Correctness | zlib SIMD demand; hard blocker for Spike 6 | L — new register file, MXCSR, IEEE-754 in Lean |

*E5 calibration governance: prerequisite to item 5 and all of section E — do first (not itself table-numbered above; renumbering the table for one late addition is churn, see §E5 below).*

---

## Auditor's uncertainty notes

(a) Dead fields verified by grep across `Gasm/`, `Stdlib/`, `Spikes/`; a metaprogramming or `deriving` consumer could evade that. (b) Claims about real hardware coefficients (SHL-by-CL uop count, DIV latency) are from memory, not a vendored source — treat as *hypotheses to measure* (itself the argument for item 5). (c) `Stdlib/Zlib/Windows.lean` was not read in full; zlib-specific mis-ranking examples are inferred from the ISA surface and RFC 1951 algorithm shape, not the emitted assembly.

---

# SUPPLEMENT (2026-08-27)

## E. SYSTEM-LEVEL TRANSPORT & PLACEMENT COST MODELS

The existing cost model answers exactly one question: *how many cycles does this x86 basic block take on one core?* Every entry below is a question the owner wants answered by comparing closed-form cost functions, and for which **nothing exists** — not a stub, not a constant.

**E1. PCIe / interconnect transfer model — verified absent.**
`Gasm/Targets/` contains four targets (X86_64, Wasm, WASI, Windows). There is no device, no bus, no transfer. Nothing models: per-direction bandwidth, per-transfer fixed latency, **host→device vs device→host asymmetry** (the readback penalty that decides most offload questions), pinned vs pageable staging cost, submission/doorbell overhead, or batching amortization (N small transfers vs one coalesced). Without these, "CPU vs GPU *including readback*" is not expressible even in principle — a GPU kernel cost alone always wins. **Forcing function:** Spike 6 pixel readback is literally a device→host transfer; the debt lands the moment Spike 6 has a cost contract. **Validation:** a transfer-size sweep (64 B → 256 MB, both directions, pinned and pageable) as a differential oracle; fit latency + inverse-bandwidth coefficients; oracle must fail closed when no device is present (Law 13 control-vector rules — a missing GPU must abort the run, never silently pass).

**E2. No composable cost views between CPU and GPU — the central missing abstraction.**
`PerfCycleBounds` (`Uop.lean:132-136`) is `Nat` cycles under an implicitly single, unnamed clock. Cycles are not comparable across devices: a GPU "cycle" is a different clock at a different width, and both are unstable under turbo/DVFS. **Ratified design (Craig 2026-08-27, VISION §5): layered views that COMPOSE, not one flattened unit.** Each system keeps its native precision view as first-class (cycle counts for x86 — valuable, keep them; device ticks for GPU; latency+bandwidth terms for transports); a **system-architect view in µs/ms** is derived through explicit conversions owned by named device profiles (profile carries clock/frequency provenance). Placement decisions compare `t_cpu(N)` vs `t_h2d(bytes) + t_gpu(N) + t_d2h(bytes)` at the architect level; within-domain optimization keeps native units. The composition (validated conversions) is the contract. This still forces the frequency/turbo gap (A5) closed — the cycles→time conversion is exactly what A5 blocks — but does NOT demote cycles to a derived unit. Cost: conversion layer is small; the honesty burden (which profile, which frequency, measured how — see E5) is the real work.

**E3. Storage performance model — verified absent.**
`MonadFileSystem` (`Effects/FileSystem.lean:47-51`) is a four-method typeclass whose only implementation emits events and returns `ByteArray.empty` (`Effects/Trace.lean:50-58`); `Environment.fileSystem` has zero readers (C7). No model of: sequential vs random cost, block/page size, queue depth and NVMe parallelism, OS page-cache hit vs miss, write amplification, or fsync latency. "Recompute vs spill?" is unanswerable. **Validation:** fio-style sweeps (block size × queue depth × read/write × cached/uncached) as a calibration oracle.

**E4. Network performance model — verified absent.**
`NetEvent` (`Effects/Network.lean:11-17`) carries `String` payloads and no sizes, no timing. No RTT, no bandwidth, no MTU/segmentation, no syscall-per-message overhead, no batching (writev/sendmmsg), no congestion behavior. "Local vs remote?" is unanswerable, and the syscall-overhead term is what usually dominates small-message server workloads. **Validation:** loopback and LAN latency/bandwidth sweeps across message sizes and batch factors.

**E5. Governance of measured calibration data under Law 4 — an open policy gap; resolve first.**
Law 4 governs *vendored authoritative text*. Every Section E entry, and TOP-10 item 5, produces something Law 4 has no category for: **measured numbers from this machine**. wsc died of exactly this — RDTSC medians hand-transcribed as `Nat` literals and left to rot. Proposed position: calibration is a *third* reference class — checked in, machine-readable, `references/`-style, with (a) named device/profile identity and provenance (host, frequency policy, OS build, date), (b) the regenerating harness committed alongside so the data is reproducible rather than transcribed, (c) staleness surfaced mechanically (a gate failing when data predates its harness or names a profile the build doesn't define), (d) a hard prohibition on hand-editing a calibration value. Model coefficients then *cite* calibration files the way semantics cite the SDM. Without this, every Section E model becomes a second wsc.

## F. CLASS-FORCED ITEMS (from the declared target systems)

**F1. Disk durability correctness (databases, OS).** Distinct from E3 — axioms, not ranking. Nothing models write ordering, fsync/FlushFileBuffers guarantees, torn/partial writes at sector or page granularity, barrier semantics, or rename-as-atomic. A WAL cannot be specified, let alone proven, against the current filesystem model. **Also flagged (design, not scope now):** forces an observation-algebra extension — *crash-cut traces*: equivalence must hold for every prefix a crash could expose, a new quantifier over cut points interacting directly with `canonicalizeTrace` and happens-after.

**F2. Constant-time / secrecy debt (servers, crypto).** Unrepresentable in *either* current lens: correctness contracts say nothing about secret-dependence; the cost model reports one number per block with no notion of input-dependent timing. This is a **third contract class** — non-interference ("no branch condition or memory address depends on secret input"), a static analysis over the uop stream, not a proof about results. Cheap to state, and cheaper now than after the optimizer starts introducing data-dependent branches for speed.

**F3. Interrupt/privilege depth beyond `#DE` (OS).** Only two fault sites exist in the tree (`Div.lean:29,37`). No IDT, no rings/CPL, no `SYSCALL`/`SYSRET`, no `IRET`, no MSRs, no control registers, no preemption. The OS target class is blocked at the model layer, not the ISA-coverage layer.

**F4. Audio/input device classes and frame-deadline cost consumption (game engines).** No device model beyond console/file/socket — no input events, no audio buffer/callback with hard underrun deadline, no display/vsync. Separately: game engines consume cost functions as **deadline satisfaction** (`cost(N) ≤ budget`), not minimization, and need a tail/worst-case notion — p99 frame time is the requirement, and `nominalCycles` is a mean-ish estimate that says nothing about it. A new contract shape (Law 5 design item), like F2.

## TARGET-CLASS TAG TABLE

**GE** game engines · **OS** operating systems · **SRV** web/gRPC servers · **DB** databases

| Entry | Classes forcing it | Note |
| :-- | :-- | :-- |
| A0 memory hierarchy | GE, OS, SRV, DB | DB scans and GE frame budgets are cache-bound by construction |
| A1 dependency chains | GE, OS, SRV, DB | universal |
| A2 port-pressure fidelity | GE, DB | tight inner loops |
| A3 dead profile fields | OS, SRV, DB | cross-CPU portability claims |
| A4 branch prediction | SRV, DB, GE | DB predicate eval; SRV parsing |
| A5 fusion / front-end / alignment / store-forwarding | GE, SRV, DB | |
| A6 heuristic TMAM | — | no class forces it; **demote, don't calibrate** |
| A7 no hardware perf validation | GE, OS, SRV, DB | universal |
| A8 uncited coefficients (Law 4) | GE, OS, SRV, DB | universal |
| B1 memory ordering / TSO | OS, DB, SRV | first threaded spike |
| B2 atomics, LOCK, fences | OS, DB, SRV, GE | |
| B3 faults / permissions / canonicality | OS, DB, SRV | OS *is* the fault handler; DB mmap |
| B4 FPU / SSE / AVX | GE, DB, SRV | GE math; DB SIMD scan; SRV crypto/checksum |
| B5 FS/GS segments, TEB/TLS | OS, SRV, DB | per-thread state |
| B6 self-modifying / generated code | DB, GE, OS | **DB query JIT is a first-class use case** |
| B7 Wasm OOB trap | SRV, DB | plugin sandboxes, UDFs |
| B8 Wasm limits / memory_grow | SRV, DB | |
| B9 Wasm ISA + validation gaps | SRV, DB, GE | |
| C1 short reads / handle types | OS, SRV, DB | highest-leverage OS gap |
| C2 WriteFile, stdout≡stderr, handle table | OS, SRV, DB | |
| C3 no error model | GE, OS, SRV, DB | universal |
| C4 VirtualAlloc is a constant | DB, GE, OS | DB buffer pool; GE arenas |
| C5 socket inventions / blocking | SRV, DB | |
| C6 IAT + loader convention | OS | |
| C7 dead `Environment` fields | GE, OS, SRV, DB | universal (vacuous ∀) |
| C8 WASI errno + invented `sock_*` | SRV | |
| D graphics-forward (SPIR-V/Vulkan, FP invariance) | GE, DB, SRV | DB/SRV via GPU compute offload |
| E1 PCIe / interconnect transfer | GE, DB, SRV | gates every offload decision |
| E2 composable cost views (native precision + architect-view time; E2) | GE, DB, SRV | **prerequisite for all placement questions** |
| E3 storage performance | DB, OS, SRV | |
| E4 network performance | SRV, DB | |
| E5 calibration-data governance | GE, OS, SRV, DB | universal; **do first — wsc's actual failure mode** |
| F1 disk durability + crash-cut traces | DB, OS | new quantifier over crash prefixes |
| F2 constant-time / secrecy | SRV, OS | third contract class |
| F3 interrupts / privilege depth | OS | blocks the whole class at the model layer |
| F4 audio/input devices + frame deadlines | GE | cost as *deadline satisfaction*, needs tail bounds |

**Cross-cutting read.** E2 and E5 have the widest blast radius: E2 is prerequisite for every placement question; E5 governs the data every Section E model produces. F2 and F4 each introduce a **contract shape** the framework does not have (non-interference; deadline satisfaction with tail bounds) — Law 5 stop-and-design items before any code.
