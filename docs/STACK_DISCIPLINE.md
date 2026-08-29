# Stack Discipline & Local Jump Obligations

**Status (2026-08-29): required design with an unsoundly weak partial substrate.**
`ComposedState.stackDepth`, CFG terminators and a minimal stack-clean predicate exist, but current
`jmp`/`jcc` constructors carry only string labels and depth equality: they do not establish the
destination block's entry contract or transfer its ghost world. `BlockM` also has unrestricted state
replacement and no checked stack-instruction authoring surface. The trust-repair milestone must
complete the typed-edge and composition rules below before treating spike proofs as exemplars.
`AbiDiscipline` vocabulary and a stack-restoration fact are necessary but not sufficient for
relational entry/exit, target admissibility, artifact/link identity or boundary certification.

Completed function-local stack manipulation must be strictly checked to guarantee that:
1. Every allocated byte on the stack is restored before a return instruction (`ret`).
2. Functions satisfy their target architecture's **Application Binary Interface (ABI)** calling conventions.
3. Stack alignment invariants (e.g. 16-byte alignment before `call` on x86-64 and AAPCS64) are preserved across all basic blocks.

---

## 1. Concrete Stack Frame Tracking in `ComposedState`

The current state contains a `stackDepth` field. The completed authoring surface must update it only
through checked constructors rather than relying on an unconstrained ghost counter or arbitrary
state replacement:

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

Every future checked `BlockM` instruction that manipulates the stack pointer must satisfy exact step
soundness on `stackDepth`:

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

Different operating systems and architectures mandate distinct calling conventions. The current
partial substrate records structural **ABI Discipline** vocabulary parameterized over `Arch` and
`ABI`; a selected M2-B profile must add exact relational entry/exit and caller/link certification:

This document uses *ABI* narrowly for the machine calling convention: registers, stack layout,
preservation, and return. Logical allocator, request, cancellation, or library capabilities are
specified by [Composable Boundary ABI Contexts](ABI_CONTEXT.md). The row-level connection remains
unimplemented. Its eventual call rule must satisfy both layers; neither an OS nor this stack
discipline implicitly supplies the contextual layer.

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

The basic-block authoring surface checks direct, conditional, and closed-set indirect CFG
transitions against typed entry contracts and `expectedDepth`. Connecting indirect decoding to the
final emitted artifact and the generic whole-CFG theorem are the remaining parts of this substrate:

A jump is a local call-like proof boundary. Its source proves the destination entry relation over
the complete logical state, not merely representation compatibility or stack depth. That relation is
the ghost-world transfer point for permissions, ownership, outstanding obligations, cancellation,
request accounting, and other erased context. The target may demand exactly the property its body
needs; unrelated resources are carried by the frame law without being mentioned at every edge.

The implementation must provide one generic CFG composition theorem: if the entry block is
established, every reachable direct edge establishes its typed target, every indirect edge resolves
within a proved closed target set and establishes the selected member contract, and every return
establishes the routine exit contract, then the whole routine preserves its contract. Loops close by
proving the header relation on each back-edge. This theorem is the routine-level certificate consumed
by `VerifiedProgram`; path enumeration or restating target-block proofs at whole-program level is not
an acceptable substitute.

```lean
structure BlockEntry (Arch : Type) [TargetArch Arch] where
  State : Type
  label : String
  expectedDepth : Nat
  accepts : ComposedState Arch State → Prop

structure BlockEdge {Arch : Type} [TargetArch Arch] {Source : Type}
    (source : ComposedState Arch Source) where
  target : BlockEntry Arch
  targetState : ComposedState Arch target.State
  framePreserved : JumpFramePreserved source targetState
  depthEstablished : target.expectedDepth = targetState.stackDepth
  entryEstablished : target.accepts targetState

inductive CpuTerminator (Arch : Type) [TargetArch Arch] {S : Type} (s_exit : ComposedState Arch S) where
  | jmp (edge : BlockEdge s_exit)
  | jcc (cond : ConditionCode Arch)
      (targetTrue : ConditionalBlockEdge s_exit (cond.holds s_exit.machine))
      (targetFalse : ConditionalBlockEdge s_exit (¬ cond.holds s_exit.machine))

structure BasicBlock (Arch : Type) [TargetArch Arch] where
  entry : BlockEntry Arch
  body : (state : ComposedState Arch entry.State) → entry.accepts state →
    Σ ExitState, Σ exit : ComposedState Arch ExitState, CpuTerminator Arch exit
```

---

## 4. Inductive Prefix Stack Invariant (Eliminating Divergence Vacuity)

To prevent infinite-loop or diverging routines from bypassing stack restoration obligations, `gasm` defines the **Inductive Prefix Stack Invariant**:

$$\forall (k : \mathbb{N}), \text{Trace}(P, s_0, k) \implies \text{ValidStackFrame}(s_k)$$

Even if an assembly routine executes infinitely (e.g. an operating system idle loop or server dispatch queue), every single execution step $k$ must preserve the bounded stack frame invariant and non-negative `stackDepth`.
