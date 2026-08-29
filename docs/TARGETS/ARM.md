# Target Specification: ARM (AArch64 & AArch32)

**Status (2026-08-28): partial AArch64 substrate plus design sketch.** The tree does not enforce
the stack/access claims or implement the weak-memory/barrier/exclusive semantics sketched below.
The live implementation inventory is `docs/TARGETS/ARM64.md`; the canonical concurrency design is
`docs/MEMORY_MODEL.md` §§4–5.2 and 10.2.

This document records target intent for the **ARM architecture**, focusing primarily on 64-bit
**AArch64**. Exact architecture/profile scope must be pinned before its weak-memory semantics land.

---

## 1. AArch64 Machine State Model

### 1.1 General Purpose Registers
31 general-purpose registers accessible as 64-bit (`X0`–`X30`) or 32-bit (`W0`–`W30`):

| Register | Alias | Description / ABI Role |
| :--- | :--- | :--- |
| `X0`–`X7` | `W0`–`W7` | Function arguments / Return values (`X0`, `X1`) |
| `X8` | `W8` | Indirect result location / Syscall number on Linux |
| `X9`–`X15` | `W9`–`W15` | Caller-saved scratch registers |
| `X16`, `X17` | `IP0`, `IP1` | Intra-procedure call scratch registers |
| `X18` | `PR` | Platform register (reserved on Windows / iOS) |
| `X19`–`X28` | `W19`–`W28` | Callee-saved registers |
| `X29` | `FP` | Frame pointer (callee-saved) |
| `X30` | `LR` | Link register (return address) |
| `SP` / `XZR` | `WZR` | Stack pointer (register index 31) or Zero Register |

---

## 2. Binary Instruction Encoding (AArch64)

Every AArch64 instruction is encoded as a **fixed-length 32-bit word** (little-endian).

```
31        28 27       24 23                                    0
+-----------+-----------+--------------------------------------+
|  Op0/Type |  Op1/Grp  |           Instruction Payload        |
+-----------+-----------+--------------------------------------+
```

---

## 3. AAPCS64 Calling Convention & Stack Return Semantics

- **Arguments**: First 8 integer/pointer arguments in `X0`–`X7`; first 8 floating-point/vector in `V0`–`V7`.
- **Return Value**: Returned in `X0`–`X1` (or `V0`–`V3`).
- **Callee-Saved**: `X19`–`X28`, `X29` (FP), `X30` (LR), `V8`–`V15` (lower 64 bits only).
- **Return Stack Equation**:
  On AArch64, `RET` branches to `X30` (`LR`) without popping from the stack. Upon return, the stack pointer exactly equals the entry stack pointer:
  $$\text{m\_final.sp} = m_0.\text{sp}$$
- **Hardware SP Alignment Mandate**:
  In ARMv8 silicon, using `SP` as a base register for memory access when `SP[3:0] != 0` generates an automatic **Hardware SP Alignment Fault**. `gasm` enforces `s.stackDepth % 16 == 0` on all public boundaries and memory access instructions.

### Standard Function Prologue / Epilogue

```lean
def aarch64FunctionTemplate :
    BasicBlock arm S := {
  label := "aarch64_routine"
  expectedDepth := 0
  entryProof := fun _ => True
  body := ⟨S, do
    -- Prologue: allocate 32 bytes on stack, save FP and LR (stackDepth: 0 -> 32)
    stp x29, x30, preIndex sp (-32)
    mov x29, sp
    
    -- Function body ...
    
    -- Epilogue: restore FP and LR, deallocate stack (stackDepth: 32 -> 0)
    ldp x29, x30, postIndex sp 32
    pure (CpuTerminator.ret [])⟩
}
```

---

## 4. Weak Memory Model & Proof Obligations

**Status: designed in the canonical model, unimplemented.** AArch64 uses a separate consistency
predicate pinned to official Arm formal-model material; it does not refine x86 TSO.

1. **Acquire/release semantics**: `LDAR`/`STLR` and relevant exclusive variants emit explicit
   acquire/release events. Barrier sequences carry their exact access classes, scope,
   ordering/completion, and instruction-synchronization semantics rather than being recognized by
   syntax alone.
2. **Exclusive monitors**: `LDXR`/`STXR` are two events connected by reservation/monitor state.
   The model includes reservation granules, architecturally required invalidation/`CLREX`, and
   permitted spurious store-exclusive failure. Only a successful store-exclusive is an acquisition
   linearization point; failure transfers no authority.
3. **Progress**: any eventual-success claim states a fairness/progress assumption separately from
   mutual-exclusion safety.

See `docs/MEMORY_MODEL.md` §5.2 for the normative model and stage M2-A for its exit criteria.
