# Target Specification: Windows (MS x64 Fastcall & PE/COFF)

**Concurrency status (2026-08-28): unimplemented.** The current Win32 hook set has no thread
creation, thread exit, wait, handle-lifecycle, or wait-on-address operations, and it has no genuine
multi-process topology. M3 is only the single-address-space logical-thread model; M6-T[Windows] adds
hosted thread/object semantics, M6-NX[Windows] its native lifecycle/object realization, and
M6-X[Windows] only its optional x86-64 wait/parking adapter. The separately
gated semantic M6-PW stage owns `CreateProcess`, process/address-space/image identity, process-object status and
observation, handle inheritance/derivation, jobs and resource-specific failure dispositions;
M6-PW-X owns native ABI/emission realization. Thread-only validation belongs to
`docs/SPIKES/SPIKE8_MULTITHREADING.md`.

This document defines the machine state model, Microsoft x64 calling convention, PE/COFF binary emission, and SEH unwind table requirements for **64-bit Windows**.

---

## 1. Microsoft x64 Calling Convention

The Microsoft x64 calling convention is strictly defined and differs significantly from System V AMD64:

### 1.1 Register Allocation & Callee-Saved Non-Volatile Registers
- **First 4 Arguments**: `RCX`, `RDX`, `R8`, `R9` (Integer/Pointers) or `XMM0`–`XMM3` (Floating-Point).
- **Return Value**: `RAX` (Integer/Pointer) or `XMM0` (Floating-Point).
- **Callee-Saved Non-Volatile Registers**:
  `RBX`, `RBP`, `RDI`, `RSI`, `RSP`, `R12`–`R15`, and the full 128-bit `XMM6`–`XMM15` values.
  When AVX state is present, the upper halves of `YMM6`–`YMM15` remain volatile.
  *(Note: Unlike System V AMD64 where `RSI` and `RDI` are scratch, on Windows x64 `RSI` and `RDI` MUST be preserved by the callee).*
- **Caller-Saved Scratch**: `RAX`, `RCX`, `RDX`, `R8`–`R11`, `XMM0`–`XMM5`.

### 1.2 Mandatory 32-Byte Shadow Space & 16-Byte Stack Alignment

The Microsoft x64 ABI requires:
1. **16-Byte Stack Alignment**: $RSP \equiv 0 \pmod{16}$ immediately before executing any `CALL` instruction.
2. **Mandatory 32-Byte Shadow Space (Home Space)**: Callers **MUST allocate at least 32 bytes of stack space** immediately preceding the `CALL` instruction, even for leaf/0-argument API calls.
3. **Stack Alignment Arithmetic from an Ordinary Called-Function Entry**:
   - After an ordinary `CALL`, the return address has been pushed, so $RSP \equiv 8 \pmod{16}$ at the callee entry.
   - A process/bootstrap root is not assumed to have a caller-pushed return address. Its initial
     stack shape and authority come from the selected loader/platform bootstrap witness.
   - To allocate 32 bytes of shadow space and achieve $RSP \equiv 0 \pmod{16}$ before a `CALL`, the caller must subtract **40 bytes** ($8 - 40 = -32 \equiv 0 \pmod{16}$) or **56 bytes** ($8 - 56 = -48 \equiv 0 \pmod{16}$):
     - `sub rsp, 40`: 32 bytes shadow space (`[RSP + 0]`–`[RSP + 24]`) + 8 bytes 5th stack argument slot (`[RSP + 32]`).
     - `sub rsp, 56`: 32 bytes shadow + 8 bytes 5th arg + 8 bytes local variable slot + 8 bytes alignment pad.

#### Caller View (Immediately Prior to `CALL` instruction with 40-byte allocation)
```
High Addresses
+------------------------------------------+
| Argument 5 (lpOverlapped / Stack Arg)    | [RSP + 32]
+------------------------------------------+
| Shadow Space for R9                      | [RSP + 24]
| Shadow Space for R8                      | [RSP + 16]
| Shadow Space for RDX                     | [RSP + 8]
| Shadow Space for RCX                     | [RSP + 0]
+------------------------------------------+ <- RSP at point of CALL (RSP = 0 mod 16)
Low Addresses
```

#### Callee View (Immediately Upon Function Entry)
Because `CALL` pushes the 8-byte return address, stack offsets inside the callee shift by 8 bytes:
```
High Addresses
+------------------------------------------+
| Argument 5 (if present)                  | [RSP + 40]
+------------------------------------------+
| Shadow Space for R9                      | [RSP + 32]
| Shadow Space for R8                      | [RSP + 24]
| Shadow Space for RDX                     | [RSP + 16]
| Shadow Space for RCX                     | [RSP + 8]
+------------------------------------------+
| Return Address (pushed by CALL)          | [RSP + 0]
+------------------------------------------+ <- RSP at function entry (RSP = 8 mod 16)
Low Addresses
```

This is a target requirement, not a current enforcement claim. The tree has neither a
`WindowsCallerDiscipline` declaration nor an `asmCall` constructor. Its current
`AbiDiscipline X86_64 WindowsFastcall` instance records GPR lists, shadow-space size and stack
alignment, but does not model XMM state or prove every call site's complete physical admissibility.
The relational ABI/link gate in `docs/MEMORY_MODEL.md` M1 and M2-B[Windows-x64-call] realization
must close that gap before a call is certified.

### 1.3 Strict Prohibition of Red Zone
Windows x64 defines no red zone. Storage below the current `RSP` is volatile and unowned by the
function: the OS, debugger, interrupt/exception machinery or another permitted agent may clobber it.
A target proof therefore rejects use of that area without first moving `RSP` and establishing the
corresponding stack authority; it models nondeterministic permitted clobber rather than claiming an
immediate overwrite always occurs.

### 1.4 Required thread lifecycle and parking refinement

The exact profiles are M6-T[Windows], M6-NX[Windows], and M6-X[Windows].

Thread creation has success/failure outcomes and may make the child runnable before the API returns,
so authority donation commits before that point and is restored on failure. Thread-function return
and `ExitThread` terminate one thread; `ExitProcess` terminates the process. A terminated thread
object becoming signaled, consuming a logical task/thread `JoinRight`, waiting on a thread-object
handle, and closing that handle are distinct transitions and obligations. `JoinRight` is not a
Windows process wait or a process handle.

M2-B[Windows-x64-call] owns the API-call relation and M2-B[Windows-x64-thread-start] owns the exact
OS-to-thread-function entry/artifact binding. M6-NX[Windows] composes those certificates with the
M6-T[Windows] lifecycle semantics; none substitutes for another.

Wait operations retain handle lifetime and represent success, timeout, and failure. The standard
`ParkedMutex32` adapter uses a four-byte `WaitOnAddress` comparison and rechecks the user-space
atomic state after every return. A specialized mutex must prove the comparison width, representation
lifetime, retry rule, and lost-wakeup behavior of any adapter it claims. Wake-to-resume is scheduler
causality, not memory synchronization.

### 1.5 Process and asynchronous-context boundary (M6-PW/M6-PW-X)

Windows process creation, address-space/image generations, persistent signaled process objects,
duplicable status/observation handles, exact inheritance, jobs, object survival, process-ID/handle
reuse, `DuplicateHandle` and object-specific transfer belong to M6-PW. Process terminality, status
availability/query, notification, repeated wait and final handle/object reclamation remain separate.
Termination applies a selected disposition to each private or shared resource and external effect;
it does not return a task terminal bundle or globally invalidate surviving objects.

Creation failure produces no child/object/returned-handle authority. Success creates distinct process
and primary-thread objects, PID/TID generations, and separate `PROCESS_INFORMATION.hProcess`/
`hThread` handle entries with independent close obligations. M6-PW states these semantics. M6-PW-X
composes M2-B[Windows-x64-call] with M2-B[PE32+-x64-bootstrap] to prove the selected OS-bootstrap
state before the loader may schedule the child, including the selected `CREATE_SUSPENDED`/runnable-
before-return behavior. Only a selected verified-child profile additionally selects
M2-B[PE32+-x64-application-entry] to connect a later application entry and its logical world to exact artifact bytes; an
opaque child receives no internal linear authority and requires no application-code theorem.

M6-PW owns the logical result-indexed success/failure transition. M6-PW-X must relate the physical
`BOOL`, `GetLastError`, and `PROCESS_INFORMATION` outputs to its after-world: failure creates no child,
handle entry or close obligation; success creates fresh process/thread identities, handle-entry
generations and independent `MustClose` obligations through that relation. Raw PID, TID or `HANDLE`
bits cannot manufacture any of them. `GetLastError` is interpreted for this operation only on a zero
`BOOL`; a stale last-error value after success proves nothing, and every `PROCESS_INFORMATION` bit on
failure is unusable. This process certificate does not depend on `WaitOnAddress`
unless the selected implementation actually uses address parking.

APCs, exceptions and other asynchronous entries use the separately pinned asynchronous-context
callable seam. They do not inherit an ordinary thread's authority, blocking, allocation, fault,
reentrancy, stack or progress permissions. A normal `ParkedMutex32` proof is therefore not
automatically APC-safe. M6-PS is the optional POSIX/Linux process-shared robust profile and is not
implied by this Windows process-object model.

---

## 2. Structured Exception Handling (SEH) & `.pdata` / `.xdata` — Required, Not Implemented

Every non-leaf x64 function that allocates stack space or saves non-volatile registers **must have verified `.pdata` and `.xdata` unwind opcodes**:

- **`RUNTIME_FUNCTION` Table (`.pdata`)**:
  - `BeginAddress`: 32-bit RVA of function start.
  - `EndAddress`: 32-bit RVA of function end.
  - `UnwindData`: 32-bit RVA of unwind info structure.
- **Unwind Opcodes (`.xdata`)**:
  - `UWOP_ALLOC_SMALL` / `UWOP_ALLOC_LARGE`: Stack frame allocation.
  - `UWOP_PUSH_NONVOL`: Callee-saved register pushes (including `RSI`, `RDI`).
  - `UWOP_SET_FPREG`: Frame pointer establishment (`MOV RBP, RSP`).

The current PE emitter serializes only `.text`, `.rdata`, and `.idata`; it has no `.pdata`/`.xdata`
emission or verified derivation from prologues. The rule above is the required future target profile,
not an existing capability. Until unwind metadata generation, loader connection, and negative
controls are implemented, no non-leaf/unwind-safety claim may cite this section as completed.

A selected SEH-callable profile must also distinguish its nonlocal control outcomes. A filter or
handler may request continuation at a profile-permitted (possibly modified) machine context,
continue search/propagation, or unwind to a selected handler while intervening termination/cleanup
handlers run. Unwinding retires frames one at a time and accounts for every frame-local authority and
obligation according to the emitted unwind metadata and handler contract. None of these outcomes is
ordinary function return, and continue-search is not by itself fatal termination. Profiles that do
not admit SEH-callable code incur no such proof; profiles that do must connect every admitted outcome
to the exact `.pdata`/`.xdata`, entry/exit ABI, and emitted artifact.

---

## 3. PE32+ Binary Header Loader Invariants

For 64-bit Windows PE images emitted by `gasm`:
- **Subsystem**: `IMAGE_SUBSYSTEM_WINDOWS_CUI` (`3`) for console applications.
- **Optional Header Magic**: `0x20B` (PE32+ 64-bit).
- **Default Image Base**: `0x140000000` (standard 64-bit base).
- **Alignment**: `SectionAlignment = 0x1000` (4KB page aligned), `FileAlignment = 0x200` (512-byte sector aligned).
- **Data Directories**:
  - `DataDirectory[IMAGE_DIRECTORY_ENTRY_IMPORT]` (`1`): Points to `IMAGE_IMPORT_DESCRIPTOR` table binding to `KERNEL32.dll`.
  - `DataDirectory[IMAGE_DIRECTORY_ENTRY_IAT]` (`12`): Points to the contiguous Import Address Table mapped into writable/read-only memory.
