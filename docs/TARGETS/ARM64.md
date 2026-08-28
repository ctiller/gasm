# AArch64 Bring-Up Reconnaissance & Target Handoff

**Status**: this is a reconnaissance note, not a design document and not an implementation.
No AArch64 code exists anywhere in `Gasm/Targets/` (confirmed by directory listing at the
time of writing — the only ARM content in the tree is `docs/TARGETS/ARM.md`, itself a
design-only document per the project README's own account). Everything below the emulator
invocations in §2 was produced by hand — no `gasm` ARM backend, no instruction model, no
encoder — for the sole purpose of answering one question empirically: **can this machine
close the loop (emit bytes, run them, observe output) for AArch64 the way it already does
for x86-64 bare metal?** The answer is yes, on both axes that matter (serial output and
programmatic exit), and this document exists so a second team can pick up the actual target
implementation without re-deriving any of this from scratch.

---

## 1. Bottom line

- **`qemu-system-aarch64` is already installed** — same directory as the `qemu-system-x86_64`
  binary the bare-metal x86 target already depends on (`C:\Program Files\qemu\`, the
  winget/upstream default). No install step was needed on this machine. Every other
  `qemu-system-<arch>` target ships in that same directory, for what it's worth.
- **The boot-and-observe loop closes completely.** A hand-assembled AArch64 program, wrapped
  in a hand-built ELF64 with no external assembler involved, boots under
  `qemu-system-aarch64 -M virt` and (a) produces exact, byte-for-byte serial output over the
  PL011 UART and (b) exits with a process exit code chosen by the guest program, via AArch64
  semihosting. Both were reproduced and observed directly — see §2.
- **Recommendation: `qemu-system-aarch64` bare metal, `-M virt`, PL011 UART, semihosting
  `SYS_EXIT`.** This is the direct AArch64 analogue of what already works for x86-64
  (`Gasm/Targets/BareMetal/QEMU.lean`, `Spikes/Spike1Hello/BareMetal/Test.lean`): same
  posture (least OS surface between our bytes and the CPU), same shape of harness (spawn
  QEMU, capture stdio, check exit code), same "if the oracle is absent, skip honestly rather
  than silently pass" convention already established for the x86 side. §3 evaluates this
  against `qemu-aarch64` user-mode and states why bare metal wins for this project
  specifically.
- **One thing that came out simpler than the x86 side, empirically, not by assumption:**
  QEMU's AArch64 `virt` machine loads a non-Linux ELF passed to `-kernel` as a plain ELF —
  it maps the `PT_LOAD` segment(s) at their physical addresses and jumps to `e_entry`. No
  Linux boot-protocol header, no device tree blob, no PVH-style note was needed. The x86-64
  bare-metal target needed a `PT_NOTE` Xen PVH note (`docs/TARGETS/BARE_METAL.md` §3.2)
  specifically because QEMU's x86 `-kernel` path enforces that convention when the image
  isn't a Linux bzImage; the AArch64 path has no equivalent requirement for a bare
  `EM_AARCH64` `ET_EXEC` ELF. One fewer moving part for an AArch64 target's minimal-ELF
  packaging than x86 needed.

---

## 2. Reproduction — exact commands, exact bytes, observed output

### 2.1 `qemu-system-aarch64` availability

```
$ "C:\Program Files\qemu\qemu-system-aarch64.exe" --version
QEMU emulator version 11.1.0 (v11.1.0-12130-ge470268ff4)
```

`-machine help` lists `virt` (aliased to `virt-11.1`) among the AArch64 machine types;
`-M virt -cpu help` lists `cortex-a53`, `cortex-a72`, `cortex-a76`, etc. as available CPU
models. No `GASM_QEMU`-style override was needed to find it — same standard install path
`Gasm/Targets/BareMetal/QEMU.lean`'s `findQemuPath` already knows for the x86_64 binary,
substituting `qemu-system-aarch64.exe` for `qemu-system-x86_64.exe`.

### 2.2 The hand-assembled program

Two probe programs were built, using nothing but a from-scratch Python script that computes
each 32-bit AArch64 instruction word directly from the architecture's own encoding tables
(MOVZ/MOVK, STRB unsigned-offset, unconditional B, HLT) — no assembler, no `gasm` machinery.
Both target the PL011 UART's fixed base address on the `virt` machine, `0x09000000`, and
write to its data register (offset `0`) with a raw `STRB`, exactly as
`docs/TARGETS/BARE_METAL.md` §2.2 already documents for MMIO in general (writes to a device
register, not idempotent RAM).

**Probe 1** — write `"Hi\n"` then spin forever (`b .`):

```
entry=0x40000078  8 instruction words, 32 bytes of code
  0xd2a12000   movz x0, #0x0900, lsl #16      ; x0 = 0x09000000 (PL011 base)
  0x52800901   movz w1, #0x48                 ; 'H'
  0x39000001   strb w1, [x0]
  0x52800d21   movz w1, #0x69                 ; 'i'
  0x39000001   strb w1, [x0]
  0x52800141   movz w1, #0x0a                 ; '\n'
  0x39000001   strb w1, [x0]
  0x14000000   b .                            ; infinite loop
```

**Probe 2** — same UART writes, then AArch64 semihosting `SYS_EXIT` (op `0x18`) with the
extended-exit reason `ADP_Stopped_ApplicationExit` (`0x20026`) and exit code `42`:

```
entry=0x40000078  11 instruction words + 16 bytes of trailing data (the {reason, code} block)
  0xd2a12000   movz x0, #0x0900, lsl #16
  0x52800901   movz w1, #0x48
  0x39000001   strb w1, [x0]
  0x52800d21   movz w1, #0x69
  0x39000001   strb w1, [x0]
  0x52800141   movz w1, #0x0a
  0x39000001   strb w1, [x0]
  0xd2a80001   movz x1, #0x4000, lsl #16      ; x1 = 0x400000a4 (address of the exit block)
  0xf2801481   movk x1, #0x00a4
  0x52800300   movz w0, #0x18                 ; SYS_EXIT
  0xd45e0000   hlt  #0xf000                   ; semihosting trap
  ; trailing data at 0x400000a4: two little-endian u64 words: 0x0000000000020026, 0x000000000000002a
```

Each is wrapped in the smallest possible `ET_EXEC` / `EM_AARCH64` (`e_machine = 183`) ELF64:
64-byte ELF header + one 56-byte `PT_LOAD` program header (R+X, `p_vaddr = p_paddr =
0x40000000`, `p_filesz = p_memsz` = whole file, `p_align = 0x10000`) immediately followed by
the code (and, for probe 2, the trailing data block). `e_entry = 0x40000078` (base + header
size). No section headers, no relocations, no linker — this is the same "flat physical
memory model" `docs/TARGETS/BARE_METAL.md` §3.3 already describes for x86-64, just without
that section's Xen PVH note requirement (see §1 above).

The full generator (self-contained, stdlib-only Python, ~70 lines per probe) computes every
word directly from field formulas — e.g. `MOVZ` 64-bit: `(1<<31)|(0b10<<29)|(0b100101<<23)|
(hw<<21)|(imm16<<5)|Rd`, `STRB` (immediate, unsigned offset): `(0b00<<30)|(0b111<<27)|
(0<<26)|(0b01<<24)|(0b00<<22)|(imm12<<10)|(Rn<<5)|Rt` — cross-checked against known hex
patterns (`0xD2800000` = bare `MOVZ Xd,#0` with `hw=0`, `0x39000000` = bare `STRB` with
`imm12=Rn=Rt=0`) before use. Available on request; not committed to the tree since it is
throwaway reconnaissance tooling, not part of any target implementation.

### 2.3 Boot commands and observed output

**Probe 1** (serial only, no exit device — the program spins forever by design, so the
observer applies its own timeout and kills the process after capturing output):

```
qemu-system-aarch64.exe -M virt -cpu cortex-a53 -kernel spike_arm_hello.elf \
  -serial stdio -display none -nodefaults
```

Observed stdout, byte for byte: `Hi\n` — then the process was killed externally after 10s
(exit status reflects the kill, not the guest program, since probe 1 has no exit path by
construction).

**Probe 2** (serial + semihosting exit):

```
qemu-system-aarch64.exe -M virt -cpu cortex-a53 -semihosting -kernel spike_arm_exit.elf \
  -serial stdio -display none -nodefaults
```

Observed stdout, byte for byte: `Hi\n`. **Observed process exit code: `42`** — exactly the
value placed in the guest's semihosting exit-code block, propagated unmodified as QEMU's own
process exit status. `-semihosting-config help` on this same QEMU build confirms
`semihosting-config` is a real, present option for this target (`arg`, `chardev`, `enable`,
`target`, `userspace`) — semihosting on `virt` is not a hypothetical.

This is the complete demonstrated loop: hand-written bytes → emulator → observed serial
output → observed programmatic exit, both halves closed and both directly witnessed, not
inferred from documentation.

---

## 3. Options evaluated

- **`qemu-system-aarch64` bare metal, `-M virt` (recommended).** Directly demonstrated
  above. Least OS surface between emitted bytes and the CPU — the same property that made
  bare-metal x86 the right first target rather than Linux/Windows. PL011 UART + semihosting
  exit is a complete, minimal I/O story, mirroring 16550 UART + `isa-debug-exit` on x86
  almost exactly (see §4 for where the two conventions diverge).
- **`qemu-aarch64` user-mode.** Not tried in this reconnaissance — noted as cheaper to reach
  *if* an ARM target were emitting ELF64 Linux binaries (the way the existing Linux/x86-64
  target does), since it runs a static ARM Linux ELF directly against the host kernel's
  syscall translation, no machine model needed at all. But it validates strictly less of the
  stack: no MMIO, no device model, no boot sequence, and Linux user-mode syscall ABI is a
  different, larger surface than a bare-metal UART loop. Given bare metal is already proven
  reachable and is the more informative target (see the memory-model argument in §7), this
  option is not the recommendation, but it remains available later as a second, cheaper
  AArch64 target once a Linux-target-style ARM story exists, the same way x86-64 has both a
  bare-metal and a Linux/SysV target today.
- **Nothing else was seriously considered.** `sbsa-ref` and the various vendor `virt` boards
  QEMU also ships are real machine models but add fidelity (ACPI/SBSA compliance surface)
  this project has no present use for; `virt` is QEMU's own minimal reference platform for
  exactly this kind of bring-up.

---

## 4. Exit-code and serial conventions: AArch64 vs. the existing x86 harness

| | x86-64 bare metal (existing, `QEMU.lean` / `Spike1Hello/BareMetal/Test.lean`) | AArch64 bare metal (this reconnaissance) |
|---|---|---|
| Serial device | 16550 UART, port I/O, COM1 `0x3F8` | PL011 UART, **memory-mapped**, fixed base `0x09000000` on `virt` |
| Serial access | `IN`/`OUT` instructions, poll LSR bit 5 (THRE) before each byte | `STRB` to the data register; this reconnaissance did not poll the flags register (`UARTFR`, TX-full bit) before writing — safe for a 3-byte burst into an empty FIFO, but a real target's UART driver should poll `UARTFR` the way the x86 side polls LSR, for the same reason |
| Exit mechanism | `isa-debug-exit` device, `OUT 0xF4, val` | Semihosting `HLT #0xF000` trap, `SYS_EXIT` (`W0=0x18`) with extended reason `ADP_Stopped_ApplicationExit` (`0x20026`), `X1` → `{reason, code}` block |
| QEMU flag needed | `-device isa-debug-exit,iobase=0xf4,iosize=0x04` | `-semihosting` (confirmed present: `-semihosting-config help` responds) |
| Exit-code arithmetic | `(val << 1) \| 1` — writing `0` yields process exit `1` | **Passed straight through** — writing `42` yields process exit `42`, empirically confirmed in §2.3. A test harness checking `exitCode == 1` (the x86 pattern) would be wrong for AArch64; it should check the exact code the guest chose (e.g. `0` for success, matching the ordinary Unix convention, not `1`) |
| ELF boot requirement | Needs a `PT_NOTE` Xen PVH note (`BARE_METAL.md` §3.2) | None observed — a bare `PT_LOAD` `ET_EXEC`/`EM_AARCH64` ELF booted with no note segment at all |

---

## 5. What a real ARM target would cost

Grounded in what was actually run above, not estimated in the abstract:

- **A `Gasm/Targets/BareMetal/QEMUAArch64.lean` (or equivalent) resolver**, structurally
  identical to `findQemuPath` in `Gasm/Targets/BareMetal/QEMU.lean` — same override chain
  (explicit path → `GASM_QEMU_AARCH64` env var → PATH → standard install locations), just
  probing `qemu-system-aarch64(.exe)` instead. Since both binaries live in the same install
  directory on this machine, a shared `C:\Program Files\qemu\` candidate path covers both;
  Linux CI's `/usr/bin/qemu-system-aarch64` is the parallel case to the existing
  `/usr/bin/qemu-system-x86_64` candidate.
- **An AArch64 test harness alongside `Spikes/Spike1Hello/BareMetal/Test.lean`**, following
  its exact shape: spawn QEMU with the args demonstrated in §2.3 (`-M virt -cpu cortex-a53
  -semihosting -kernel <elf> -serial stdio -display none`), capture stdout, capture the exit
  code, and check it against the AArch64 convention in §4 (not the x86 one — this is the one
  concrete place a copy-paste from the x86 harness would silently produce a wrong assertion).
- **`run_gates.py` wiring**: a `detect_qemu_aarch64()` mirroring `detect_qemu()`
  (`scripts/run_gates.py` lines ~268–315) — same override-does-not-fall-through discipline,
  same "explicit broken override reported as NOT FOUND, never silently substituted" rule —
  registered in `PREREQ_DETECTORS`, plus a new gate table entry with `"tools": ["lean",
  "qemu_aarch64"]` following `test_spike1_baremetal`'s pattern exactly.
- **CI**: `ubuntu-latest` can `apt-get install qemu-system-arm` (the Debian/Ubuntu package
  that provides `qemu-system-aarch64`, confusingly named after the 32-bit architecture) the
  same way the existing pipeline presumably provisions `qemu-system-x86`.
- **The actual instruction model, encoder, and semantics** — an `AArch64Instruction`
  typeclass, a decoder, `step` semantics, a roundtrip registry — is the large remaining cost
  and is explicitly out of scope for this reconnaissance and for this document. §6 below
  exists so whoever takes that on knows the shape of the gates they will be building against
  before they start, not after.

---

## 6. The conventions an ARM implementor will be gated by

These are not suggestions — they are mechanically enforced today, on every instruction of
every existing target, and will fire on ARM work exactly as they fire on everything else.
Stated explicitly here, with the real x86 files as worked examples, because a competent
implementor with no other context should not have to discover any of these by hitting a red
gate first.

- **Every instruction type needs a mandatory `validationOracle` and `costProvenance` — no
  defaults exist for either field.** See `Gasm/Targets/X86_64/Instructions/Base.lean`'s
  `X86_64Instruction` class (`validationOracle : ι → ValidationOracle`, `costProvenance : ι →
  CoefficientProvenance`, both with no `:=` default, unlike e.g. `canFuzzHardware := fun _ =>
  true`) and `Gasm/Targets/X86_64/Instructions/Obligations.lean` for the two option types
  (`ValidationOracle = .silicon | .nasmEncoding reason | .optedOut reason`;
  `CoefficientProvenance = .cited artifact | .modelInternalUnvalidated reason`). The gate is
  `lake exe check_x86_obligations` (`Tools/CheckX86Obligations.lean`); an ARM equivalent
  (`check_arm_obligations`, or a generalization of the x86 one) would need to exist before
  ARM instructions could pass CI, and every `.nasmEncoding`/`.optedOut`/
  `.modelInternalUnvalidated` reason string is length-checked, so a placeholder reason will
  not pass.
- **`.silicon` and NASM-encoding cross-checks are both x86-specific machinery, not available
  to ARM as-is.** `.silicon` claims real-hardware differential fuzzing via `HardwareHarness`
  running on the CPU actually executing the build — there is no ARM silicon in this loop (the
  machine running CI is x86). `.nasmEncoding` claims NASM cross-validated the encoding — NASM
  does not assemble AArch64. **This is genuinely open, not decided**: an ARM target needs its
  own encoding-oracle equivalent (candidates: `llvm-mc`, GNU binutils' `aarch64-*-as`) and
  its own answer to what, if anything, plays `HardwareHarness`'s role — running under
  `qemu-system-aarch64` and comparing against the Lean model is a plausible oracle (this
  reconnaissance's §2 demonstrates the boot loop such a harness would ride on) but is
  *emulated*, not silicon, and whether `.silicon` may honestly be claimed for
  emulator-validated instructions, or whether a third `ValidationOracle` constructor is
  needed, is a real design decision this document does not make.
- **`.modelInternalUnvalidated` is available to ARM on exactly the same honest footing it is
  used on today — checked, not assumed.** All ~1611 of this project's own x86-64 cost
  witnesses are currently `.modelInternalUnvalidated`, because the RDTSC calibration harness
  (`docs/CALIBRATION_GOVERNANCE.md`'s "F1") does not exist yet, and that document's §9 rules
  out third-party tables (Agner Fog, uops.info) as a `.cited` source for any shipped
  coefficient. The gate (`Tools/CheckX86Obligations.lean`) only requires a non-empty, honest
  *reason string* for `.modelInternalUnvalidated` — it does not require the coefficient to be
  measured. An ARM implementor declaring every `costProvenance` as
  `.modelInternalUnvalidated "no calibration source exists yet"` is not taking a shortcut;
  it is doing exactly what this project's own x86 side does everywhere today, and the gate
  will accept it. **This is not a D29 problem** (`docs/adr/0038-standards-are-earned-before-imposed.md`
  — "we get to hold standards of others when we can hold them of ourselves"): the standard
  this specific gate enforces is *honest disclosure of provenance*, not *validated
  provenance*, and that is a standard this project already meets on every one of its own
  instructions. An ARM contributor cannot be blocked by it doing what x86 already does.
- **Every declaration needs a `REF:` citation** — a `docs/` path + anchor, or a
  `references.json` slug + anchor (see `Gasm/Targets/X86_64/Instructions/Base.lean`'s
  `/- REF: docs/TARGETS/X86_64.md#... -/` comments immediately above each declaration, and
  `references.json`'s existing `intel-sdm` entry as the pattern for a future
  `arm-architecture-reference-manual`-style slug). `scripts/check_refs.py` validates that the
  cited anchor actually resolves; **inventing an anchor that doesn't exist fails the gate**,
  it is not merely a lint warning.
- **No `partial def`, anywhere.** It compiles to a kernel-opaque constant with zero equation
  lemmas, and (per this repository's own finding, `PLAN.md` line ~535) has already blocked
  proofs in four subsystems here. A decoder, an interpreter loop, or any recursive AArch64
  machinery must be structurally or well-founded recursive, provably terminating — the same
  discipline the x86 decoder/interpreter already follows.
- **Registration in the roundtrip registry is build-enforced, not optional.**
  `roundtripCases : List ι` on `X86_64Instruction` has no default either — see the same
  `Base.lean` class definition — every instance must enumerate a finite, representative
  sample of its own argument domain (registers, boundary immediates) or the type does not
  compile. `Gasm/Targets/X86_64/Registry.lean`'s `allEncodableInstructions` and the sharded
  `RoundtripGate/*.lean` theorems consume this list to make `decode (encode i) = i` a
  build-failure gate, not a hand-run test. An ARM registry would need the equivalent
  aggregate list and gate theorem(s), sharded the same way (one Lean module per instruction
  family, per `PLAN.md`'s D-series decoder-modularization decision) if the ARM ISA subset
  grows large enough for build-time cost to matter the way it already does for x86.
- **`Gasm/Targets/X86_64/Memory.lean`'s memory-access declaration convention
  (`memAccesses : ι → List MemAccessSpec`, also no default) is the newest of these**, landed
  via `docs/MEMORY_HOOK.md` (D30/D31, approved 2026-08-28) as the single chokepoint for
  Law 11 permission-checking and the performance model's latency/cache accounting. Any new
  target's memory-touching instructions will need the equivalent declaration once/if a
  target-generic version of the memory hook exists — see §7 for why this is listed as open
  rather than settled for ARM specifically.

---

## 7. What is settled for x86 only, versus what ARM must decide

The x86 target made several concrete conventions that read, from inside `Gasm/Targets/
X86_64/`, as though they were architectural requirements. They are not — they are x86-64
choices, and an ARM target is not bound by them:

- **`MemRef` (`Gasm/Targets/X86_64/Memory.lean`: `base + index*scale + disp`) is the
  operand shape for x86-64's SIB-byte-derived addressing modes specifically** — approved as
  "the operand convention for the expansion's new memory forms" in D31/Q2, but that ruling is
  scoped to x86-64's own instruction expansion, not stated as a cross-target requirement.
  AArch64 addressing is a substantially different shape: pre/post-indexed writeback
  (`STR X0, [X1], #16`), register-offset with optional extend/shift
  (`STR X0, [X1, X2, LSL #3]`), and PC-relative literal-pool loads (`LDR X0, =const` /
  `ADR`/`ADRP`) have no direct `base+index*scale+disp` analogue for the writeback and
  PC-relative forms. **Open**: whether ARM gets its own `MemRef`-shaped operand type, reuses
  `MemAccessSpec`'s declarative-access-list *idea* with a different concrete operand
  representation, or something else — this document does not decide it, it flags that reusing
  x86's `MemRef` verbatim will not fit AArch64's addressing modes without modification.
- **The memory model is the sharpest of these, and may be a genuine prerequisite, not a
  deferrable choice.** x86-64 is TSO; AArch64 is a weak memory model (relaxed load/store
  ordering, `LDAR`/`STLR` for acquire/release, `DMB`/`DSB` barriers, `LDXR`/`STXR` exclusive
  monitors — `docs/TARGETS/ARM.md` §4 already sketches proof obligations for these, though
  that section is design-only, unimplemented). This matters concretely right now: this
  session was told that a memory-model design and a multithreading spike are being worked on
  concurrently, elsewhere, and both are presumably being reasoned about against x86's TSO
  semantics by default, since x86 is the only target with a memory model to reason about
  today. **If the emerging memory-model abstraction is written in a way that is only ever
  exercised by a TSO target, an AArch64 implementor inherits an unstated assumption they may
  not be able to satisfy** — ARM will observably reorder accesses that a TSO-shaped
  abstraction assumes cannot reorder. Whether the memory-model design needs to be
  target-generic *before* ARM instruction work starts, or whether ARM can safely defer to a
  restricted subset (e.g. no relaxed atomics, full barriers on every shared access, as a
  first cut) and tighten later, is a decision for whoever owns that concurrent work — this
  document's only claim is that the dependency is real and cheap to state now, versus
  expensive to discover after AArch64 instructions have been written against assumptions a
  weak-memory target cannot honor.
- **The `.silicon`/`.nasmEncoding` oracle split (§6) is x86-shaped by construction** — it
  names NASM and `HardwareHarness` specifically. Genuinely open for ARM, not merely
  unimplemented; see §6's bullet on this.
- **Everything else in §6 — mandatory `validationOracle`/`costProvenance`, `REF:` citation
  discipline, the `partial def` ban, roundtrip-registry build enforcement — is
  target-generic.** These are properties of how this codebase is built and gated, not of
  x86-64 specifically, and apply to ARM (or any future target) exactly as written.

---

## 8. Strategic note (not a task for this reconnaissance)

ARM's weak memory model is not just a checkbox difference from x86's TSO — it is the
strongest available empirical check on whether a concurrency memory-model design is real
semantics or x86-shaped hand-waving. A memory-model abstraction that only ever runs against
a TSO target cannot distinguish "correctly models relaxed ordering" from "happens to work
because the only target tested never reorders anything." An AArch64 target, once it exists,
is a genuine adversarial witness for that work: ARM will observably reorder accesses where
x86 will not, and a multithreading spike that passes on both targets is evidence the model
is actually sound, not merely x86-compatible. This is worth keeping in view when the
memory-model and multithreading-spike design work referenced in §7 reaches the point of
deciding what its own test matrix should include — but building that target is out of scope
here, and this section states the argument, not a plan.

---

## 9. Blockers

None found on this machine. `qemu-system-aarch64` is present and working, the `virt`
machine boots a hand-built bare-metal ELF with no special preparation beyond what's
documented in §2, PL011 UART output was captured byte-exact, and semihosting `SYS_EXIT`
propagates a chosen exit code through to QEMU's own process exit status. Everything in §5–§8
is scoping and design-dependency information for the follow-on implementation work, not a
list of things preventing it from starting.
