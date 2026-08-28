# Bare-Metal Investigative Kernel for Instruction Validation — Assessment

**Owner's question**: *"for instruction validation is there some value in building a bare
metal investigative kernel that can check instruction shapes"*

**Status**: this document is an assessment and a design position, not a build. No
investigative kernel exists in the tree today, and this document's verdict is that none
should be built yet. Every mechanism described in §5–§7 is unbuilt design; the only
follow-on work this assessment creates is the userspace fault-oracle extension tracked
as `docs/tasks/MH4-fault-oracle-veh-capture.md`.

**Verdict, stated up front**: yes, there is value — but not now, and never under plain
QEMU for semantics. The current harness already executes on real silicon; a kernel under
QEMU's TCG emulator would trade that strong oracle for a weaker one (QEMU's model of
x86). Almost everything the kernel is intuitively wanted for — fault taxonomy, timing,
litmus tests — has a materially cheaper userspace step that is the actual next action
and is already the planned path (PLAN.md Phase 3, F1). The kernel becomes genuinely
demanded on the day the *model* grows privileged or hidden state (paging, IDT delivery,
`syscall` MSR semantics, WC memory ordering) — and when that day comes, the right first
vehicle is the kernel booted under KVM on the vendor Linux fleet, not a natively booted
machine. §8 names the concrete triggers.

---

## 1. Baseline: what validation observes today, precisely

Three oracles exist. Each observes a different slice of reality, and each has a hard
ceiling.

### 1.1 `x86_fuzzer` — real silicon, observed through an OS

`Gasm/Targets/X86_64/HardwareHarness.lean` emits a native Windows PE (via
`emitNativeBatchTestExe`), spawns it, and executes each test vector's instruction bytes
**directly on the host CPU** — genuinely real silicon (one i9-13900H; TCB.md T11 names
it the sole silicon truth source, and `microarchitecturesValidated : Nat := 1` in
`SemanticsFuzzer.lean` discloses it every run).

What it **sets** per vector: 15 GPRs (RSP stays stack-backed) plus the six arithmetic
status flags, masked through `arithmeticStatusMask` (`CF PF AF ZF SF OF`) with bit 1
forced on — the harness cannot set DF, AC, IF, TF, or any system flag.

What it **observes** per vector (the 136-byte record decoded by
`decodeHardwareResult`): 16 GPRs, RFLAGS via `pushfq`, and **one fault bit** — a
Vectored Exception Handler writes `faulted := 1` into the record's byte 135 (RFLAGS'
always-zero top byte) and redirects RIP to the next test. `verifyHardwareOracleControls`
runs a known-answer positive control and a known-#DE negative control through the same
path before any real vector, and `runHardwareBatch`'s `Except` return type makes a
fabricated success unrepresentable (the fail-closed structure TCB.md T10 documents).

What it **cannot** observe:

- **Fault identity.** The VEH receives a full `EXCEPTION_RECORD` (exception code,
  faulting address, read/write disposition) but the harness captures none of it — one
  bit. Meanwhile MH1 just landed `X86_64Fault` (`divideError | memFault (kind, width,
  addr) | halted`) in `Registers.lean`, and `SemanticsFuzzer.lean` compares only
  `modelS.faulted != hwRes.faulted`. **The model's fault taxonomy is now richer than
  the oracle's observation.** A model that mislabels a #GP as a #DE, or reports the
  wrong faulting address, passes today's differential.
- **Memory effects.** No memory state is initialized or read back; nothing
  memory-touching is differentially validated. Together with branches, this is the
  `canFuzzHardware := false` half of the ISA (50 opt-out sites across
  `Gasm/Targets/X86_64/Instructions/`; TCB.md T11: "~half the ISA … unvalidated SDM
  transcription").
- **Privileged and hidden state.** CR0/CR3/CR4, EFER, MSRs, segment descriptors, the
  IDT, TLB behavior, system RFLAGS bits: userspace can neither set nor read them. Every
  instruction's observed behavior is conditioned on whatever Windows configured.
- **Time.** No timestamps of any kind (MODEL_DEBT §A7; the F1 task exists to fix this).
- **Other silicon.** One microarchitecture, one OS.

### 1.2 `encoding_fuzzer` — bytes against NASM, no semantics

`EncodingFuzzer.lean` diffs `X86_64Instruction.encode` output byte-for-byte against
NASM assembling `toNASM` text. It validates *encodings*, never behavior; a perfectly
encoded instruction with wrong `step` semantics passes it. Its known false-positive
classes (shortest-form preferences) are filtered, not fixed.

### 1.3 Spike 1 BareMetal — a real boot, but against QEMU's model

`Spikes/Spike1Hello/BareMetal/Test.lean` genuinely boots a gasm-emitted ELF under
`qemu-system-x86_64 -kernel` (Xen PVH boot note, per `docs/TARGETS/BARE_METAL.md` §3.2),
captures 16550 UART output over `-serial stdio`, and terminates via `isa-debug-exit`.
Two limits matter here:

1. **The oracle is QEMU, not silicon.** The Spike 1 invocation passes no `-accel` flag,
   so it runs under TCG — pure software emulation. Nothing in the tree references KVM
   or WHPX. A green run means "gasm's model agrees with QEMU's model."
2. **It is not even long mode.** QEMU's PVH path enters at `XEN_ELFNOTE_PHYS32_ENTRY`
   in 32-bit protected mode, paging off, and `Spikes/Spike1Hello/BareMetal/Program.lean`
   runs entirely on instructions whose encodings behave identically there — no GDT of
   our own, no IDT, no page tables, no long-mode transition exists anywhere in the
   tree. "We already boot bare metal" is true, but what boots is a 32-bit
   protected-mode UART loop, not a kernel.

### 1.4 `perf_fuzzer` — self-referential, and the CI carve-out

`verifyPerfInvariants` checks the model against itself (MODEL_DEBT §A7); 0 of 1611
registry witnesses carry a `.cited` cost coefficient — all are
`.modelInternalUnvalidated`, and `docs/REVIEW.md` item 10 records that no coefficient
*can* be legitimately cited until F1 exists. `docs/CI.md` §5 already excludes
`perf_fuzzer` from both hosted runners because a shared vCPU cannot give a trustworthy
cycle signal — the project has already accepted "timing needs controlled hardware" as a
principle.

---

## 2. What a bare-metal kernel would add — candidate by candidate, honestly

The test for each candidate is not "could a kernel observe this?" (it could) but "is a
kernel the *cheapest sufficient* observer, and does any in-flight work demand it?"
(Law 5 / ADR-0008: capability grows on spike demand, never speculatively — the
predecessor died of the opposite.)

### 2.1 Fault taxonomy (MH1) — kernel helps, but userspace gets ~90% for ~1% of the cost

A kernel's IDT sees the raw vector (#DE=0, #UD=6, #GP=13, #PF=14), the pushed error
code, and CR2 on #PF. That is the full-fidelity observation.

But the current harness's VEH *already receives* nearly all of this and throws it away:
`EXCEPTION_POINTERS.ExceptionRecord` carries `ExceptionCode`
(`0xC0000094` = divide, `0xC0000005` = access violation, `0xC000001D` = illegal
instruction, `0xC0000096` = privileged instruction) and, for access violations,
`ExceptionInformation[0]` (read/write/DEP) and `ExceptionInformation[1]` (the faulting
virtual address — Windows' relay of CR2). Extending the VEH capture block and the
result record by ~20 bytes validates `divideError` vs `memFault(kind, addr)` vs
"neither" differentially, today, on the same real silicon. (Width is the one field no
fault observation provides at either ring level — hardware does not report access
width; it must come from the decoder on both sides of the diff, or be excluded from
the comparison.) That extension is the concretely demanded follow-on — tracked as
`docs/tasks/MH4-fault-oracle-veh-capture.md`; the capture described here does **not
exist in the tree today**.

What only a kernel adds: raw vector numbers (distinguishing faults Windows folds into
one code), the #PF error-code bits (P/W/U/RSVD/ID), fault classes that never reach a
user-mode handler, and double-fault/interrupt-frame mechanics. Nothing in the model
represents any of those yet.

### 2.2 The unvalidated half of the ISA — already planned as a userspace fix

PLAN.md Phase 3 names the path: "memory-operand instructions via scratch-region support
in HardwareHarness; branch instructions via landing pads." A reserved arena in the
harness PE plus fault capture handles memory forms; landing pads (or TF single-step)
handle branches. A kernel would also work — mapping a scratch region is even cleaner
when you own the page tables — but it is not the cheapest sufficient observer, and
Phase 3 committed to the userspace shape. Building a kernel *for this* would repeat the
wsc failure mode: infrastructure ahead of the validation it serves.

### 2.3 Timing and F1 — bare metal is the *upgrade* path, not the blocker

F1's design (CPUID+RDTSCP bracketing, median-of-N, timer-overhead subtraction,
containment not percent-error) is precisely the technique for getting trustworthy
cycle counts *under an OS*. Its own sources note wsc found containment + median
tolerable with no core pinning at all. F1 is not blocked on bare metal; building bare
metal first would delay the only path to a citable coefficient
(`docs/CALIBRATION_GOVERNANCE.md` §9 rules out external tables).

Where bare metal genuinely raises the ceiling — later, for F3-era calibration, if F1's
measured dispersion proves too wide for containment to discriminate: interrupts fully
off, no SMT sibling, no scheduler, and — the part userspace can never do — **frequency
pinned via MSRs** (turbo disabled, fixed P-state) and prefetchers controllably
disabled. That converts median-of-20k-with-outlier-rejection into
near-deterministic counts. Two honest caveats: SMIs survive even on bare metal, and
**this only means anything on a real machine** — TCG has no cycle model at all
(`-icount` counts translated instructions), so a QEMU timing kernel would calibrate
the model against nothing.

### 2.4 Memory-model litmus tests — userspace pinned threads are the industry standard

x86-TSO's observable relaxations (store-buffer forwarding, StoreLoad reordering) are
routinely demonstrated from userspace — the standard litmus7-style harness is exactly
pinned OS threads hammering shared locations. The in-flight memory-model design and
multithreading spike need *that*, plus affinity control, which the vendor Linux fleet
provides trivially. A kernel with SMP bring-up adds: runs with interrupts disabled
(cleaner statistics), exact core placement without a scheduler, and — the only
qualitatively new observation — **memory-type interactions** (WC via PAT, non-temporal
stores, fence semantics against WC), which userspace cannot configure. No in-flight
design models memory types; when one does, that is a §8 trigger.

### 2.5 Privileged and hidden state — the one thing only a kernel can ever do

CR/MSR-dependent behavior, segment descriptor loads, IDT delivery mechanics (error-code
push, interrupt-frame layout — which `docs/TARGETS/BARE_METAL.md` §1.1's red-zone
prohibition already *asserts* without any oracle behind it), TLB/`invlpg` semantics
(§5's "TLB invalidation proofs" — likewise currently oracle-less), A/D-bit setting by
the page walker, and the `syscall` instruction's actual MSR-driven transition (B2
landed `SyscallOp` with `canFuzzHardware := false`; its semantics are validated by
nothing). None of this is observable from ring 3 under any OS. **But none of it is in
the model yet either** — gasm's `X86_64MachineState` today is GPRs, RFLAGS, RIP, a
sealed memory field, and a fault option. The kernel is the right oracle for a
privileged-state model that does not exist; building the oracle first is building
ahead of need.

---

## 3. The tension resolved: emulator vs silicon is not a binary

There are three rungs, not two, and conflating the top two is what makes the question
hard:

| Rung | What executes the instruction | Oracle strength | Cost to reach |
|---|---|---|---|
| **QEMU TCG** (today's Spike 1) | QEMU's software model | *Weaker than today's harness* for semantics — it validates gasm against QEMU. Fine for structure: boot protocol, device protocol, harness plumbing | Already here |
| **Kernel under KVM** (vendor Linux fleet) | **Real silicon**, ring 0, VMX non-root | Real fault delivery to *our* IDT (vector, error code, CR2), real page walks, real RFLAGS/GPR semantics; most MSR/CR accesses genuinely reach hardware, a filtered subset is emulated by KVM and must be allowlisted per-register | Kernel bring-up (§5) but **zero boot-ops**: `qemu -accel kvm -kernel ours.elf` on any fleet box |
| **Native boot** | Real silicon, nothing between | Adds: trustworthy *timing* (frequency-pinned, interrupt-free), SMM-adjacent realism, real devices, exact memory-type behavior | Kernel bring-up **plus** boot/ops: PXE or kexec, serial capture, remote power/watchdog for hangs |

Two consequences:

1. **A TCG kernel is never a semantic oracle.** Anything observed under TCG is a claim
   about QEMU. Its legitimate uses are exactly Spike 1's: packaging, boot protocol,
   device-protocol structure, and as the fast dev loop while building the kernel
   itself.
2. **KVM dissolves most of the dilemma.** The vendor fleet runs Linux; KVM is a kernel
   module away. A kernel image booted under KVM executes its faults, page walks, and
   unprivileged instructions on the actual CPU — the same trust shape as today's
   harness (which itself already runs under a hypervisor on `windows-latest` CI,
   per `docs/CI.md`). The only things KVM still denies are calibration-grade timing
   and full MSR realism; those, and only those, justify the native-boot rung.

**What would make the vendor machines usable for this** (in priority order, and note
the first two have nothing to do with bare metal): (a) registered as self-hosted
runners with a recorded CPU identity — this alone delivers multi-silicon `x86_fuzzer`
(T11's stated fix) and `perf_fuzzer`'s promised home (CI.md §5); (b) userspace litmus
capacity — pinned cores, isolcpus if possible; (c) KVM enabled — that is the entire
prerequisite for the kernel-under-KVM rung; (d) only for native boot: serial console
access, remote power control or an IPMI/watchdog story, and a netboot/kexec path.

---

## 4. What it would unblock, ranked

| In-flight work | Blocked on a kernel today? | What actually unblocks it |
|---|---|---|
| **MH1 fault taxonomy** | No | VEH capture extension (MH4) — userspace, real silicon, small |
| **F1 coefficients** (0/1611 cited) | No | F1 as designed, userspace RDTSCP; kernel is the F3-era precision upgrade if dispersion demands it |
| **Memory-model litmus** | No | Pinned userspace threads on the Linux fleet; kernel only when memory *types* enter the model |
| **Multithreading spike (SMP)** | No | OS threads + affinity; SMP bring-up is for the kernel's own later life |
| **Phase 3 excluded ISA half** | No | Scratch region + landing pads in HardwareHarness (already the plan) |
| **Privileged-state semantics** (syscall MSRs, IDT frames, paging §5/§6 of BARE_METAL.md, memory types) | **Yes — and only this** | The kernel, under KVM first. But no spike demands this state yet |

The bottom row is the honest answer to "is there some value": the kernel is the *only
possible* oracle for an entire future tier of the model, and the tree already contains
design prose (BARE_METAL.md §1.1, §5, §6) making claims about that tier with no oracle
behind them. The value is real and exclusive — it is just not yet *demanded*, and this
project has a constitution (ADR-0008) written in the blood of its predecessor about
what to do with real-but-undemanded capability: don't build it yet.

---

## 5. Costs, so the trigger decision is informed

**Status**: everything in this section is unbuilt design — a cost estimate, not a
description of the tree.

- **Bring-up** (from the existing PVH 32-bit entry): load a GDT with 64-bit code/data
  descriptors; build identity-mapped page tables (PML4→PDPT→PD, 2 MB pages suffice);
  set CR4.PAE, EFER.LME, CR0.PG; far-jump to 64-bit code; load an IDT with ~20
  exception stubs pushing a normalized (vector, error-code, CR2, saved-GPR) record;
  per-test recovery mirroring the VEH's redirect-RIP pattern. This is well-trodden
  (~1–2k lines of assembly-shaped emission) but every byte of it is *harness*
  infrastructure emitted by hand — the same "94 raw ByteArray literals" self-hosting
  debt TCB.md T10 already flags for the PE harness, and it should be emitted through
  `X86_64Instruction.encode` from day one rather than repeating that debt. SMP (for
  litmus) adds INIT-SIPI-SIPI, per-CPU stacks, and a cross-core barrier protocol —
  defer until a litmus demand exists.
- **Results out**: the 16550 UART (already modeled and validated both directions) as
  the record channel — frame the same binary record format `decodeHardwareResult`
  uses, plus a length/checksum footer; `isa-debug-exit` (already used by Spike 1) for
  status under QEMU/KVM; a port-write watchdog convention so a hung vector can be
  distinguished from a dead VM by the spawning side's timeout.
- **Trustworthiness (Law 13)**: same structure the tree already enforces twice —
  positive control (known-answer instruction must produce its record), negative
  control (known #DE and known #PF must arrive at the IDT with the right vector and
  CR2), `Except`-shaped runner so an unbootable kernel is unrepresentable as success,
  exit 2 = "oracle absent" per the Spike 1 / `docs/SPIKES.md` §4 convention, and
  TC17 vacuity floors on vector counts. A kernel that triple-faults must fail the
  run loudly — QEMU reboot loops (`-no-reboot`) are the silent-no-op hazard here.
- **Gate/CI wiring**: a `kernel_fuzzer`-shaped gate in `scripts/run_gates.py` with
  `tools: ["lean", "qemu"]` (the `detect_qemu()` prerequisite already exists and
  fail-closes); TCG mode runnable everywhere as a *structural* gate only; KVM mode
  gated on `/dev/kvm` presence with absence reported as NOT RUN (never silently
  substituting TCG for KVM — the same no-silent-substitution rule `detect_qemu()`
  already applies to a broken `GASM_QEMU`); excluded from hosted runners for timing
  work exactly as `perf_fuzzer` is (CI.md §5).
- **Trust surface**: under KVM the TCB grows by KVM's instruction-emulation and
  MSR-filtering paths for the specific registers exercised — these must be enumerated
  per-test (a `.kvmEmulated` provenance mark, in the spirit of
  `CoefficientProvenance`), not hand-waved. Native boot removes that but buys the
  full ops burden above.

---

## 6. Verdict and sequencing

**Direct answer**: yes, there is value — exclusive, real value — but it is confined to
model tiers that do not exist yet, and every currently blocked or in-flight thing has a
cheaper, already-planned observer. Building the kernel now would be capability ahead of
demand (ADR-0008), and building it under TCG for semantics would be strictly worse than
the harness we have.

**Sequence** (each step gated on its own demand, none speculative):

1. **Now — MH4** (`docs/tasks/MH4-fault-oracle-veh-capture.md`): widen the VEH capture
   to exception code + faulting address + access kind; diff the model's `X86_64Fault`
   against it. Closes the "taxonomy richer than the oracle" gap MH1 opened, on real
   silicon, this week, and directly discharges the fault-shaped half of what the
   investigative kernel was intuitively for.
2. **Now, unchanged — F1** as designed (userspace RDTSCP). **Phase 3** scratch-region /
   landing-pad work as planned. Neither waits for anything in this document.
3. **When the fleet lands — Linux userspace first**: self-hosted runners with recorded
   CPU identity (multi-silicon `x86_fuzzer`, `perf_fuzzer`'s home), pinned-thread
   litmus harness for the memory-model track. Ask the vendor for KVM capability and a
   serial/IPMI story now — it is cheap to specify at purchase time and expensive after.
4. **On trigger (§8) — investigative kernel under KVM** on the fleet: long mode + IDT +
   paging, faults and privileged state as first-class observations, emitted self-hosted
   through `X86_64Instruction.encode`. TCG retained only as the structural dev loop.
5. **Last, and only if F3's dispersion data demands it — native boot** of the same
   kernel image on one fleet machine (kexec or PXE): frequency-pinned,
   interrupt-free calibration as the terminal upgrade for coefficient citation.

---

## 7. What this does *not* recommend

- No kernel task is created by this assessment. (Law 5: the demand does not exist yet;
  a task created now would be the wsc pattern.)
- No TCG-based semantic validation, ever — TCG results are claims about QEMU and must
  never feed `validationOracle` provenance as if they were silicon.
- No replacement of the Windows userspace harness. It is the strongest semantic oracle
  in the tree and remains primary; the kernel, when it exists, is additive (privileged
  tier + timing tier), not a successor.

## 8. Triggers that convert "not yet" into a task

Any one of these, arriving as a concrete spike or design demand, justifies opening the
kernel task (as step 4 above, KVM-first):

1. A spike or contract that needs **validated `syscall`/MSR transition semantics**
   (today `SyscallOp` is `canFuzzHardware := false` and effect-intercepted, so nothing
   demands it).
2. The memory-model design adopting **memory types** (WC/PAT, non-temporal stores,
   fence-vs-WC ordering) as modeled state.
3. **Paging/TLB obligations** becoming load-bearing — the moment BARE_METAL.md §5's
   "TLB invalidation proofs" or §6's IDT claims acquire a consumer, they need an
   oracle that can actually observe a TLB or an interrupt frame.
4. **F1/F3 dispersion evidence** that userspace medians cannot support containment at
   the precision calibration needs (a measured trigger, not a vibe).
5. MH4's differential surfacing a **fault class Windows' exception translation cannot
   distinguish** and that matters to a proof.

Absent all five, the bare-metal investigative kernel stays what it is in this
document: a well-costed option with a named vehicle, waiting for its demand.
