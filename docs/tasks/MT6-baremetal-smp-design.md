---
id: MT6
title: "Bare-metal SMP bring-up: Stop-and-Design (MP init, trampoline, LAPIC, accel honesty)"
status: ready
blocked_on: ""
after: [MT5]
related: [MT4]
bar: ""
track: concurrency
priority: 4.5
priority_set: 2026-08-28T00:00:00Z
design: "docs/SPIKES/SPIKE8_MULTITHREADING.md"
design_review: ""
date: 2026-08-28
---

# MT6: Bare-metal SMP bring-up — Stop-and-Design for Spike 8 Phase C

## Context

`docs/SPIKES/SPIKE8_MULTITHREADING.md` §6.3. The current bare-metal target boots one
CPU via QEMU's PVH path (`Gasm/Targets/BareMetal/`, in tree, Spike 1 runs on it).
"Spawn a thread" with no OS means SMP bring-up: INIT–SIPI–SIPI via the LAPIC, a
real-mode trampoline below 1 MB crossing three execution modes (16-bit real and 32-bit
protected are design-only today — `docs/TARGETS/X86_REALMODE.md`, `docs/TARGETS/
X86_32.md`), per-CPU stacks, an AP rendezvous protocol, and MMIO (UC) ordering for the
LAPIC that sits outside the memory model's v1 WB-only scope. Cost is roughly
comparable to the original bare-metal bring-up itself, which is why Phase C is
sequenced after Phases A+B rather than presented as an equal third leg.

This task is design-only (Law 5): every listed decision must be authored, reviewed,
and committed before any Phase C Lean is written.

## Deliverables & acceptance criteria

- Ingestion of the Intel SDM multiple-processor initialization material into the
  `intel_sdm` corpus citation surface (Law 4), plus the LAPIC/xAPIC/x2APIC register
  interface sections needed for the ICR.
- The trampoline decision, decided and recorded with reasons: verified 16/32-bit
  execution modes (activating the real-mode/x86-32 designs) versus a declared
  unverified byte-blob in the TCB ledger (TC7) — including the SIPI-vector placement
  and page-table sharing story off the PVH entry state.
- LAPIC device model design: xAPIC MMIO vs x2APIC MSR (`RDMSR`/`WRMSR` are unmodelled
  instructions — if chosen, they become a scoped ISA demand), and the memory-type
  (UC) ordering extension this forces on the memory model — coordinated as a demand
  on `docs/X86_MEMORY_MODEL.md`'s post-v1 scope, not designed unilaterally here.
- Per-CPU stack layout, AP parking/rendezvous protocol, and the mapping from
  CPU/APIC id to `ThreadId` so MT2/MT3 machinery is reused unchanged.
- QEMU harness extension design: `-smp 2`, accelerator detection, and the honesty
  rule wired into verdicts — TCG runs report SB `witness=absent` / exit 2 (TCG does
  not model the store buffer; only WHPX/KVM/silicon runs bind the witness floor).
- Explicit go/no-go recommendation to the owner with a cost estimate, before any
  implementation task is filed.
