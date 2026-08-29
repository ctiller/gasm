# Stack Discipline & Local Jump Obligations

In `gasm`, function local stack manipulation must be strictly checked to guarantee that:
1. Every allocated byte on the stack is restored before a return instruction (`ret`).
2. Functions satisfy their target architecture's **Application Binary Interface (ABI)** calling conventions.
3. Stack alignment invariants (e.g. 16-byte alignment before `call` on x86-64 and AAPCS64) are preserved across all basic blocks.

---

## 1. Concrete Stack Frame Tracking in `ComposedState`

Instead of relying on unconstrained ghost counters, stack management is tracked directly within `ComposedState`:

```lean
structure ComposedState (Arch : Type) (ApiStateType : Type) where
  machine      : MachineState Arch
  stackDepth   : Nat                         -- Current stack frame depth relative to function entry
  api          : ApiStateType
  perms        : MemoryPermissions Arch     -- Discrete capability permissions
  obligations  : List Obligation             -- Linear obligation ledger
  causalClock  : VectorClock                 -- Logical timestamps
  eventHistory : EventTag → VectorClock      -- Monotonic event history map
```

### 1.1 Instruction Soundness on `stackDepth`

Every instruction in `BlockM` that manipulates the stack pointer must satisfy exact step soundness on `stackDepth`:

- **`push reg` / `push imm`**:
  $$\text{stackDepth}' = \text{stackDepth} + \text{TargetArch.wordWidth Arch}$$
- **`pop reg`**:
  $$\text{Precondition: } \text{stackDepth} \ge \text{TargetArch.wordWidth Arch}$$
  $$\text{stackDepth}' = \text{stackDepth} - \text{TargetArch.wordWidth Arch}$$
- **`sub rsp, N`**:
  $$\text{stackDepth}' = \text{stackDepth} + N$$
- **`add rsp, N`**:
  $$\text{Precondition: } \text{stackDepth} \ge N$$
  $$\text{stackDepth}' = \text{stackDepth} - N$$

---

## 2. Multi-ABI Calling Conventions & Stack Restoration Laws

Different operating systems and architectures mandate distinct calling conventions. Rather than hardcoding one global convention into the architecture, `gasm` models calling conventions as **ABI Disciplines** parameterized over `Arch` and `ABI`:

This document uses *ABI* narrowly for the machine calling convention: registers, stack layout,
preservation, and return. Logical allocator, request, cancellation, or library capabilities are
defined by [Composable Boundary ABI Contexts](ABI_CONTEXT.md). A call must satisfy both layers;
neither an OS nor this stack discipline implicitly supplies the contextual layer.

```lean
class AbiDiscipline (Arch : Type) (ABI : Type) where
  callerSavedRegs     : List (Register Arch (TargetArch.wordWidth Arch))
  calleeSavedRegs     : List (Register Arch (TargetArch.wordWidth Arch))
  shadowSpaceRequired : Nat
  stackAlignment      : Nat
  argumentRegisters   : List (Register Arch (TargetArch.wordWidth Arch))
  returnRegister      : Register Arch (TargetArch.wordWidth Arch)
  
  /-- Post-call return invariant verified on the machine state -/
  calleePreservesStack : ∀ (s_pre s_post : MachineState Arch),
    CalleeDiscipline Arch s_post →
    s_post.rsp = s_pre.rsp + TargetArch.wordWidth Arch
```

### 2.1 ABI Stack Restoration Matrix

| Target Architecture & ABI | Callee-Saved Non-Volatile Registers | Stack Frame Cleanup Responsibility | Stack Alignment at Call Boundary |
| :--- | :--- | :--- | :--- |
| **x86-64 System V (Linux)** | `RBX, RBP, R12, R13, R14, R15` | Caller cleans up stack arguments | $RSP \equiv 0 \pmod{16}$ before `CALL` |
| **x86-64 MS Fastcall (Windows)** | `RBX, RBP, RDI, RSI, R12, R13, R14, R15, XMM6-15` | Caller cleans up shadow space & stack args | $RSP \equiv 0 \pmod{16}$ before `CALL` (32B shadow space mandatory) |
| **x86-32 `cdecl`** | `EBX, ESI, EDI, EBP` | Caller pops arguments via `add esp, N` | $ESP \equiv 0 \pmod 4$ (or $\pmod{16}$ for modern gcc) |
| **x86-32 `stdcall` (Win32)** | `EBX, ESI, EDI, EBP` | **Callee pops arguments** via `ret N` | $ESP \equiv 0 \pmod 4$ |
| **ARM AAPCS64 (AArch64)** | `X19-X28, X29 (FP), X30 (LR), D8-D15` | Caller cleans up stack arguments | $SP \equiv 0 \pmod{16}$ on all memory accesses |

---

## 3. BasicBlock Structure & Typed Terminators

All basic block CFG transitions are checked against `expectedDepth` and `s_exit.stackDepth`:

```lean
structure BasicBlock (Arch : Type) [TargetArch Arch] (InState : Type) where
  label         : String
  expectedDepth : Nat
  entryProof    : ComposedState Arch InState → Prop
  body          : Σ (S_exit : Type), ComposedState Arch InState → (Σ (s_exit : ComposedState Arch S_exit), TargetArch.Terminator Arch s_exit)

inductive CpuTerminator (Arch : Type) [TargetArch Arch] {S : Type} (s_exit : ComposedState Arch S) where
  | jmp   {TargetIn : Type}
          (target  : BasicBlock Arch TargetIn)
          (h_state : S = TargetIn)
          (h_entry : target.entryProof (h_state ▸ s_exit))
          (h_depth : target.expectedDepth = s_exit.stackDepth) : CpuTerminator Arch s_exit

  | jcc   {TrueIn FalseIn : Type}
          (cond        : ConditionCode Arch)
          (targetTrue  : BasicBlock Arch TrueIn)   (h_true    : S = TrueIn)
          (h_entry_t   : targetTrue.entryProof (h_true ▸ s_exit))
          (h_depth_t   : targetTrue.expectedDepth = s_exit.stackDepth)
          (targetFalse : BasicBlock Arch FalseIn) (h_false   : S = FalseIn)
          (h_entry_f   : targetFalse.entryProof (h_false ▸ s_exit))
          (h_depth_f   : targetFalse.expectedDepth = s_exit.stackDepth) : CpuTerminator Arch s_exit

  | ret   (exportedObligations : List Obligation) (bytesToPop : UInt16 := 0)
          (h_zero      : s_exit.stackDepth = 0)
          (h_match     : s_exit.obligations = exportedObligations)
          (h_callee    : CalleeDiscipline Arch s_exit) : CpuTerminator Arch s_exit

  | sysExit (exitCode : UInt8)
            (h_droppable : ∀ o ∈ s_exit.obligations, o.isDroppableOnExit) : CpuTerminator Arch s_exit

  | halt    (h_droppable : ∀ o ∈ s_exit.obligations, o.isDroppableOnExit) : CpuTerminator Arch s_exit
```

---

## 4. Inductive Prefix Stack Invariant (Eliminating Divergence Vacuity)

To prevent infinite-loop or diverging routines from bypassing stack restoration obligations, `gasm` defines the **Inductive Prefix Stack Invariant**:

$$\forall (k : \mathbb{N}), \text{Trace}(P, s_0, k) \implies \text{ValidStackFrame}(s_k)$$

Even if an assembly routine executes infinitely (e.g. an operating system idle loop or server dispatch queue), every single execution step $k$ must preserve the bounded stack frame invariant and non-negative `stackDepth`.
