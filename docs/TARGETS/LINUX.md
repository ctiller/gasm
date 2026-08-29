# Target Specification: Linux Platform

**Concurrency status (2026-08-28): unimplemented.** The x86-64 and AArch64 syscall dispatchers do
not implement `clone` or futex operations, and currently map thread exit and process exit through a
single whole-machine termination path. The required process/thread split, child-TID join protocol,
and process-private 32-bit `FUTEX_WAIT`/`FUTEX_WAKE` refinement are specified in
`docs/MEMORY_MODEL.md` §§8–9 and stages M6-P/M6-X/M6-A. The executable checks are in
`docs/SPIKES/SPIKE8_MULTITHREADING.md`.

This document defines the calling conventions, system call ABIs, kernel interface state models, ELF64 binary emission standards, and module architecture for the **Linux platform target** in `gasm`.

---

## 1. ABIs & Calling Conventions

### 1.1 System V AMD64 Function Calling Convention
For standard subroutine execution, `gasm` models the System V AMD64 ABI discipline (`AbiDiscipline X86_64 SystemVAMD64`):
- **Argument Registers (1 to 6)**: `RDI, RSI, RDX, RCX, R8, R9`
- **Return Register**: `RAX` (and `RDX` for 128-bit values)
- **Caller-Saved Registers**: `RAX, RCX, RDX, RSI, RDI, R8, R9, R10, R11`
- **Callee-Saved Registers**: `RBX, RSP, RBP, R12, R13, R14, R15`
- **Shadow Space**: None (`shadowSpaceRequired = 0`)
- **Stack Alignment**: 16-byte aligned before `call` instructions
- **Red Zone**: 128 bytes below `RSP` reserved for leaf functions

### 1.2 System Call ABIs Across Architectures

| Architecture | Instruction | Syscall Number Register | Argument Registers (1 to 6) | Return Register | Kernel Clobbered Registers |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **x86-64** | `syscall` (`0F 05`) | `RAX` | `RDI, RSI, RDX, R10, R8, R9` | `RAX` | `RCX, R11` |
| **x86-32** | `int 0x80` | `EAX` | `EBX, ECX, EDX, ESI, EDI, EBP` | `EAX` | None |
| **AArch64** | `svc #0` | `X8` | `X0, X1, X2, X3, X4, X5` | `X0` | None |

#### Error Return Value Convention
On Linux, return values in the range `[-4095, -1]` (unsigned `[0xFFFFFFFFFFFFF001, 0xFFFFFFFFFFFFFFFF]` in 64-bit) indicate negative error numbers (`-errno`).

---

## 2. Linux Kernel API State Models & Interceptor

In `gasm`, interactions with the Linux kernel are evaluated constructively through formal state transitions and unified system call interception.

### 2.1 File Descriptor State Machine
Standard stream descriptors (FD 0 stdin, FD 1 stdout, FD 2 stderr) map directly to machine state buffers and effects domain events:
- **FD 0 (stdin)**: `sys_read` consumes bytes from `s.stdinBuffer` and injects `ConsoleEvent.in`.
- **FD 1 (stdout)**: `sys_write` captures bytes from memory and emits `ConsoleEvent.out`.
- **FD 2 (stderr)**: `sys_write` captures bytes from memory and emits `ConsoleEvent.err`.
- **Dynamic FDs**: Other descriptors validate file handles, returning descriptor values on success or `-EBADF` (`-9`) on invalid handle access.

### 2.2 Memory Mapping (`mmap`) State Model
- Intercepts `SYS_mmap` (nr 9) to provide simulated memory regions (base address `0x70000000`) for user heap allocations.
- Intercepts `SYS_munmap` (nr 11) returning success (`0`).
- Programs conventionally allocate required buffers before passing pointers to subroutines; the
  current hook does not enforce capability-based memory safety.

### 2.3 Semantic Syscall Interception
`Gasm.Targets.Linux.Syscall` provides a `SyscallInterceptor` / dispatch hook that intercepts `syscall` execution in `runAsmTrace`:
- Reads `RAX` for syscall number (`SYS_read=0`, `SYS_write=1`, `SYS_open=2`, `SYS_close=3`, `SYS_mmap=9`, `SYS_munmap=11`, `SYS_socket=41`, `SYS_accept=43`, `SYS_sendto=44`, `SYS_bind=49`, `SYS_listen=50`, `SYS_exit=60`).
- Reads argument registers (`RDI, RSI, RDX, R10, R8, R9`).
- Emits strongly typed effect events (`ConsoleEvent.out`, `ConsoleEvent.err`, `ProcessEvent.exit`, `NetworkEvent.send`).
- Updates `RAX` with return value / bytes written / error code, and advances `RIP`.

### 2.4 Required thread, join, and futex refinement

The first concurrency profile must add the architecture-specific raw thread-creation ABI, distinct
thread exit versus `exit_group`, and a true join based on child-TID clear-and-wake semantics. A
user-written done flag is not enough to prove actual termination or stack reclamation.

Parking supports aligned, mapped, stable-lifetime 32-bit words; atomic compare-and-block,
value-changed/error results, permitted return/recheck loops, nondeterministic bounded wake, and
waiter cleanup. Futex wake changes scheduler state but is not a memory fence; publication remains an
x86- or AArch64-proved atomic release/acquire protocol.

---

## 3. ELF64 Binary Emission Standards

For freestanding Linux executables, `gasm` directly emits standard ELF64 binaries (`ET_EXEC` or `ET_DYN`) requiring zero external linkers or C runtime (`crt0`) dependencies.

### 3.1 ELF64 Layout & Header Structure

```
+-----------------------------------------------------------------+
| ELF64 Header (Elf64_Ehdr):                                      |
|   e_ident: Magic (\x7fELF), ELFCLASS64, ELFDATA2LSB, EV_CURRENT |
|   e_type: ET_EXEC (0x0002)                                      |
|   e_machine: EM_X86_64 (0x003E)                                 |
|   e_entry: Entry Point VMA (e.g. 0x401000 or 0x400000 + offset) |
|   e_phoff: Program Header Table Offset                          |
|   e_shoff: Section Header Table Offset (optional / enabled)     |
+-----------------------------------------------------------------+
| Program Header Table (Elf64_Phdr):                              |
|   1. PT_PHDR: Program headers segment (optional)                |
|   2. PT_LOAD: .text segment (RX, 4KB page aligned)              |
|   3. PT_LOAD: .rodata / .data segment (R / RW, 4KB page aligned)|
+-----------------------------------------------------------------+
| Section Data:                                                   |
|   - .text (executable machine code)                             |
|   - .rodata (read-only string literals and constants)           |
|   - .shstrtab (section name string table)                       |
+-----------------------------------------------------------------+
| Section Header Table (Elf64_Shdr, optional for tooling):        |
|   - SHT_NULL                                                    |
|   - .text (SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR)              |
|   - .rodata (SHT_PROGBITS, SHF_ALLOC)                          |
|   - .shstrtab (SHT_STRTAB)                                      |
+-----------------------------------------------------------------+
```

### 3.2 Standard Virtual Memory Layout
- **Default Base Address**: `0x400000` (standard 64-bit Linux static base).
- **Segment Alignment**: 4096 bytes (`0x1000`).
- **Headers & Code Segment (`PT_LOAD`)**: VMA `0x400000`, Flags `PF_R | PF_X`.
- **Data Segment (`PT_LOAD`)**: VMA `0x401000` or `0x402000`, Flags `PF_R` (or `PF_R | PF_W`).

### 3.3 ELF64 Parser & Stability Fuzzer

`gasm` emitted ELF64 binaries with no in-tree way to read them back until this section's
machinery landed: `Gasm/Targets/ELF/Parser.lean` is a total (no `partial def`), panic-free,
`Except`-returning ELF64 reader -- `bytes -> Except ElfParseError Elf64Parsed` -- accepting
exactly what `Gasm.Targets.Linux.emitELF64Executable` and the shared `Gasm.Targets.ELF`
structures describe (64-bit, little-endian, `ET_EXEC`/`ET_DYN`, `EM_X86_64`), and rejecting
every other case through a typed `ElfParseError` rather than a hang, a silent accept, or a
panic.

**Parser-stability property.** `Spikes/Common/ElfStabilityFuzzer.lean` checks, with no
external oracle, that `parseElf64 b = .ok r1 -> parseElf64 (serializeElf64Parsed r1) = .ok r2
-> r1 = r2` -- the same "1.5-roundtrip" shape as `Stdlib/Png/StabilityFuzzer.lean`. It runs
this against the real ELF64 bytes every one of the five Linux Spikes (1-5, including the
Spike 5 gunzip variant) emits via `LinuxExecutable.emit`, plus randomized, structurally
mutated instances generated from `Gasm.Targets.Linux.emitELF64Executable` itself (never
uniform noise alone -- see that module's own header for the vacuity-floor rationale this
mirrors). It additionally cross-checks each Spike's parsed `.text`/`.rodata` section payload
byte-for-byte against the exact `textBytes`/`rodataBytes` that `LinuxExecutable` was built
from -- the direct check for an emitter defect (a mismatch here means the writer and this
project's own understanding of what it wrote have diverged).

**Roundtrip theorem: not proven, scope of the gap.** `serializeElf64Parsed`'s placement
strategy (each piece written at its own recorded file offset, gaps zero-filled) is only
provably correct under a `WellFormed`-shaped hypothesis on the `Elf64Parsed` value being
written back (offsets pairwise non-overlapping and consistent with declared sizes; `e_phnum`/
`e_shnum` matching the `phdrs`/`shdrs` list lengths; `e_shstrndx` in range) -- every ELF64
file this project's own writer produces satisfies it, but an arbitrary/adversarial
`Elf64Parsed` need not (e.g. two `Elf64_Shdr` entries sharing one `sh_offset` breaks the
sorted-chunk-append reconstruction). Proving `parseElf64 (serializeElf64Parsed x) = .ok x` for
such well-formed `x` is a real, further engineering task, not merely an unstated gap: it needs
`ByteArray.get!`/`.extract` lemmas through `++` (append) that do not yet exist in this tree
(`Stdlib/Zlib/ByteArrayBridge.lean` only has `.push`-indexed lemmas today), plus the
`WellFormed` predicate itself. **Status**: tracked as follow-on work, not attempted in this
pass; the empirical parser-stability fuzzer above is this pass's substitute evidence, per this
project's own established PNG-parser precedent (`Stdlib/Png/StabilityFuzzer.lean`'s own header
makes the identical trade explicitly).

---

## 4. Module Architecture & Roadmap

The Linux target implementation is organized under `Gasm/Targets/Linux/`:
- `ABI.lean`: System V AMD64 function call ABI and Linux Syscall register conventions.
- `Syscall.lean`: Syscall numbers, argument marshaling helpers, and semantic effect interceptors.
- `ELFFormat.lean`: ELF64 header, Program Header (`Elf64_Phdr`), Section Header (`Elf64_Shdr`), and constants (re-exporting from unified `Gasm.Targets.ELF`).
- `Emitter.lean`: Byte serialization for ELF64 headers and segments.
- `Linker.lean`: Static freestanding ELF64 linker and memory layout engine (`LinuxExecutable`, `linkLinuxProgramStatic`).

The shared ELF64 machinery lives under `Gasm/Targets/ELF/` (used by both `Linux` and
`BareMetal`):
- `Format.lean`: `Elf64_Ehdr`/`Elf64_Phdr`/`Elf64_Shdr` structures, format constants, and
  little-endian byte writers.
- `Parser.lean`: the total, panic-free ELF64 reader and `Elf64Parsed` structured result (see
  §3.3 above).

The parser-stability fuzzer (`lake exe elf_stability_fuzzer`, see §3.3 above) lives at
`Spikes/Common/ElfStabilityFuzzer.lean` rather than under `Gasm/Targets/ELF/`, because it must
import every `Spikes.SpikeN*.Linux.Program` module to check against each Spike's real emitted
binary -- `Gasm/` never depends downward on `Spikes/` elsewhere in this tree, and
`Spikes/Common/` is this tree's established location for cross-spike shared tooling (see
`Spikes/Common/WasmHostRunner.lean`).

### Spikes & Verification
**Status** (corrected 2026-08-28): this section previously read "All 5 Linux Spikes are fully
implemented, verified via **constructive** `native_decide` proofs", attributing `native_decide`
to all five uniformly. Two things were wrong. **`native_decide` is not constructive** — it is an
oracle, evaluated by the compiler and not re-checked by the kernel, which is why Law 10 governs
it, `docs/TECHNICAL_NOTES.md` §1 records it as trusted-but-unprovable, and every use needs a
`scripts/gate_allowlist.txt` entry. Calling it constructive is the facade Law 8 exists to catch.
The uniform attribution was also **wrong in the direction that undersells the best result here**:
Spike 1's Linux proof is `decide`, fully kernel-checked, needing no oracle and no allowlist entry
at all. Per spike, verified against the tree on 2026-08-28:

| Spike | Equivalence theorem lives in | Proved by | Trust |
| :-- | :-- | :-- | :-- |
| 1 — Hello World | `Spikes/Spike1Hello/Linux/Equivalence.lean:39` | **`decide`** | kernel-checked; no oracle, no allowlist entry |
| 2 — Fibonacci | `Spikes/Spike2Fibonacci/Linux/Equivalence.lean:44` | `native_decide` | oracle; allowlisted |
| 3 — Sort Lines | `Spikes/Spike3SortLines/Linux/Equivalence.lean:63`, `:69` | `native_decide` ×2 | oracle; allowlisted. Both are `_inst`-suffixed — single-vector ground checks, not universal claims |
| 4 — HTTP Server | `Spikes/Spike4HttpServer/Equivalence.lean:156`, `:163`, `:170` | `native_decide` ×3 | oracle; allowlisted. **Not** under `Linux/`, which holds only `Emit.lean`/`Program.lean` |
| 5 — Gzip & Gunzip | `Spikes/Spike5Gzip/Equivalence.lean:77`, `:141` | `native_decide` ×2 | oracle; allowlisted. **Not** under `Linux/`, same as Spike 4 |

All five are implemented, emitted as standalone ELF64 executables (`hello_linux`, `fib_linux`,
`sort_lines_linux`, `spike4_http_linux`, `spike5_gzip_linux`/`spike5_gunzip_linux`) and tested
natively; Spike 5's interoperability against the host system `gzip` is real. What the theorems
establish is trace equivalence between each lowering and its specification **at the concrete
inputs each proof evaluates**, not over an input domain — see
`docs/SPIKES/SPIKE4_HTTP_SERVER.md#4-semantic-trace-equivalence-verifiedprogram-contract` for
the worked statement of that limit, which applies to all five.

