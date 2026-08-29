# Target Specification: Windows (MS x64 Fastcall & PE/COFF)

**Concurrency status (2026-08-28): unimplemented.** The current Win32 hook set has no thread
creation, thread exit, wait, handle-lifecycle, or wait-on-address operations. The required lifecycle,
join-right, handle obligation, and parking semantics are specified in `docs/MEMORY_MODEL.md`
§§8–9 and stages M6-P/M6-X; validation belongs to
`docs/SPIKES/SPIKE8_MULTITHREADING.md`.

This document defines the machine state model, Microsoft x64 calling convention, PE/COFF binary emission, and SEH unwind table requirements for **64-bit Windows**.

---

## 1. Microsoft x64 Calling Convention

The Microsoft x64 calling convention is strictly defined and differs significantly from System V AMD64:

### 1.1 Register Allocation & Callee-Saved Non-Volatile Registers
- **First 4 Arguments**: `RCX`, `RDX`, `R8`, `R9` (Integer/Pointers) or `XMM0`–`XMM3` (Floating-Point).
- **Return Value**: `RAX` (Integer/Pointer) or `XMM0` (Floating-Point).
- **Callee-Saved Non-Volatile Registers**:
  `RBX`, `RBP`, `RDI`, `RSI`, `RSP`, `R12`–`R15`, `XMM6`–`XMM15` (lower 64 bits only).
  *(Note: Unlike System V AMD64 where `RSI` and `RDI` are scratch, on Windows x64 `RSI` and `RDI` MUST be preserved by the callee).*
- **Caller-Saved Scratch**: `RAX`, `RCX`, `RDX`, `R8`–`R11`, `XMM0`–`XMM5`.

The Microsoft x64 convention below specifies machine call layout. Allocator, request, cancellation,
Winsock, Vulkan, and other library requirements belong to the placement-free contracts in
[Composable Boundary ABI Contexts](../ABI_CONTEXT.md). The still-unimplemented Windows realization
must classify the full signature and prove alias-aware argument, register, TLS/FLS, helper-clobber,
and teardown footprints.

### 1.2 Mandatory 32-Byte Shadow Space & 16-Byte Stack Alignment

The Microsoft x64 ABI requires:
1. **16-Byte Stack Alignment**: $RSP \equiv 0 \pmod{16}$ immediately before executing any `CALL` instruction.
2. **Mandatory 32-Byte Shadow Space (Home Space)**: Callers **MUST allocate at least 32 bytes of stack space** immediately preceding the `CALL` instruction, even for leaf/0-argument API calls.
3. **Stack Alignment Arithmetic from Function Entry**:
   - At function entry (or process entry), the return address has been pushed, so $RSP \equiv 8 \pmod{16}$.
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

In `gasm`, `WindowsCallerDiscipline` enforces `s.stackDepth ≥ 32 ∧ (s.machine.rsp % 16 = 0)` before allowing `asmCall` to any Windows API symbol.

### 1.3 Strict Prohibition of Red Zone
Windows x64 **strictly prohibits the Red Zone**. The OS kernel, hardware interrupts, and APCs (Asynchronous Procedure Calls) immediately overwrite memory below `RSP`. Any stack access beyond `[RSP - 1]` without adjusting `RSP` triggers catastrophic memory corruption.

### 1.4 Required thread lifecycle and parking refinement

Thread creation has success/failure outcomes and may make the child runnable before the API returns,
so authority donation commits before that point and is restored on failure. Thread-function return
and `ExitThread` terminate one thread; `ExitProcess` terminates the process. A terminated thread
object becoming signaled, consuming a logical join right, waiting on a handle, and closing that
handle are distinct transitions and obligations.

Wait operations retain handle lifetime and represent success, timeout, and failure. The standard
`ParkedMutex32` adapter uses a four-byte `WaitOnAddress` comparison and rechecks the user-space
atomic state after every return. A specialized mutex must prove the comparison width, representation
lifetime, retry rule, and lost-wakeup behavior of any adapter it claims. Wake-to-resume is scheduler
causality, not memory synchronization.

---

## 2. Structured Exception Handling (SEH) & `.pdata` / `.xdata`

Every non-leaf x64 function that allocates stack space or saves non-volatile registers **must have verified `.pdata` and `.xdata` unwind opcodes**:

- **`RUNTIME_FUNCTION` Table (`.pdata`)**:
  - `BeginAddress`: 32-bit RVA of function start.
  - `EndAddress`: 32-bit RVA of function end.
  - `UnwindData`: 32-bit RVA of unwind info structure.
- **Unwind Opcodes (`.xdata`)**:
  - `UWOP_ALLOC_SMALL` / `UWOP_ALLOC_LARGE`: Stack frame allocation.
  - `UWOP_PUSH_NONVOL`: Callee-saved register pushes (including `RSI`, `RDI`).
  - `UWOP_SET_FPREG`: Frame pointer establishment (`MOV RBP, RSP`).

`gasm` mechanically derives `.pdata` unwind opcodes directly from verified function prologues during PE/COFF binary serialization.

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
