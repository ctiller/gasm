# Target Specification: ARM (AArch64 & AArch32)

This document defines the machine state model, instruction encodings, and semantics for the **ARM architecture**, focusing primarily on 64-bit **AArch64** (ARMv8-A / ARMv9-A) with design provisions for 32-bit **AArch32** (ARMv7-A).

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

1. **Acquire Semantics**: Proving acquire ordering requires demonstrating the presence of `LDAR` (Load-Acquire) or `DMB ISH`.
2. **Release Semantics**: Proving release ordering requires demonstrating the presence of `STLR` (Store-Release) or `DMB ISH`.
3. **Exclusive Atomic Monitor Invariant (`LDXR`/`STXR`)**:
   - In ARMv8 silicon, the exclusive monitor is invalidated by any exception/interrupt, any second `LDXR` to *any* address, cache maintenance, or context switching.
   - `gasm` restricts `LDXR`/`STXR` sequences to **tight, atomic-only basic blocks** containing zero function calls, zero intermediate loads, and bounded instruction counts.
