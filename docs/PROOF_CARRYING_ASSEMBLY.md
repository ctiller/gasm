# Proof-Carrying Assembly DSL & Invariant Model

**Status (2026-08-28): mixed current inventory and design sketch.** Typed instruction ASTs,
`BlockM`, permission value types, and selected ABI/equivalence proofs exist. The checked authoring
surface does **not** currently verify every dereference or enforce linear capabilities, and neither
the x86-TSO nor AArch64 weak-memory model is implemented. Fenced examples below are illustrative
unless tied to a current declaration. See `docs/MEMORY_MODEL.md` §§2 and 4–7.

`gasm` represents assembly with typed instruction structures rather than raw strings. The required
next layer is a closed indexed authoring surface where memory access, stack use, and protocol
transitions carry formal authority and obligations.

---

## 1. Capability-Based Discrete Memory Permissions

The current tree defines the following **discrete memory-permission values**, but does not yet make
them linear or require them at every access:

```lean
inductive PermissionShare where
  | ReadOnly  : PermissionShare  -- Shared read capability (fractional read semantics)
  | Exclusive : PermissionShare  -- Exclusive read/write ownership
  | Locked    : PermissionShare  -- Synchronized atomic capability

structure MemoryPerm (base : Address) (len : Nat) (share : PermissionShare) where
  validRange : base.toNat + len ≤ 2^64
  nonEmpty   : len > 0
```

### 1.1 Capability Splitting and Joining Laws
Permissions can be split across contiguous memory regions or joined back together with arithmetic non-overflow preconditions:

$$\frac{P \vdash \text{Perm}(base, L_1 + L_2, S) \quad h_{\text{no\_overflow}} : base + L_1 + L_2 < 2^{64}}{P \vdash \text{Perm}(base, L_1, S) \otimes \text{Perm}(base + L_1, L_2, S)} \quad (\text{Split})$$

$$\frac{P \vdash \text{Perm}(base, L_1, S) \otimes \text{Perm}(base + L_1, L_2, S) \quad h_{\text{no\_overflow}} : base + L_1 + L_2 < 2^{64}}{P \vdash \text{Perm}(base, L_1 + L_2, S)} \quad (\text{Join})$$

---

## 2. Architecture-Defined Memory Disciplines

Different hardware targets enforce distinct memory-ordering models. `gasm` must capture them with
separate target predicates connected to a common event graph; this is planned, not current:

- **x86-64 WB/TSO**: the profile preserves load-load, load-store, and store-store order while
  permitting the store-buffer store-load relaxation; locked operations and fences add constraints.
- **AArch64 weak memory**: plain accesses are weakly ordered but remain constrained by coherence,
  dependencies, acquire/release operations, barriers, and the selected formal Arm profile.
- **SPIR-V Vulkan Memory Model**: Memory operations across invocations within a subgroup or workgroup require explicit `OpMemoryBarrier` and `OpControlBarrier` with `Acquire`/`Release` storage semantics.

---

## 3. ABI Boundary Disciplines: Caller vs Callee

The caller/callee boundary is strictly checked across two directions:

```
+-------------------------------------------------------------------------+
|                          Caller-Side Discipline                         |
|  - Prepares argument registers (e.g. RCX, RDX, R8, R9 on Windows x64)   |
|  - Allocates required shadow/home space on stack (≥ 32 bytes)           |
|  - Enforces 16-byte stack alignment (RSP ≡ 0 mod 16) before CALL        |
|  - ASSUMES all caller-saved scratch registers are DESTROYED post-call   |
+-------------------------------------------------------------------------+
                                    |
                                    | Executes CALL
                                    v
+-------------------------------------------------------------------------+
|                         Callee-Side Discipline                          |
|  - Preserves all non-volatile (callee-saved) registers                 |
|  - Restores stack pointer per ABI law (e.g. m_final.rsp = m₀.rsp + 8)  |
|  - Places return values in designated ABI return registers              |
|  - ALL caller-saved scratch registers are POISONED (⊤) upon return     |
+-------------------------------------------------------------------------+
```

---

## 4. Monadic Program Construction (`BlockM` Multi-Block CFG)

```lean
/-- Multi-block CFG representation of verified x86-64 memcpy loop -/
def memcpy_entry_block (len : UInt64) : BasicBlock x86_64 InState := {
  label := "memcpy_entry"
  expectedDepth := 0
  entryProof := fun s => s.stackDepth = 0
  body := ⟨InState, fun s =>
    -- push rbp ; mov rbp, rsp ; test rdx, rdx
    let s' := { s with stackDepth := 8 }
    ⟨s', CpuTerminator.jcc .ZeroFlag (memcpy_exit_block len) (memcpy_loop_block len 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩⟩
}

def memcpy_loop_block (len : UInt64) (i : Nat) : BasicBlock x86_64 InState := {
  label := "memcpy_loop"
  expectedDepth := 8
  entryProof := fun s => s.stackDepth = 8 ∧ i < len.toNat
  body := ⟨InState, fun s =>
    -- mov al, byte ptr [rsi + i] ; mov byte ptr [rdi + i], al ; dec rdx
    let s' := s
    ⟨s', CpuTerminator.jcc .ZeroFlag (memcpy_exit_block len) (memcpy_loop_block len (i + 1)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩⟩
}

def memcpy_exit_block (len : UInt64) : BasicBlock x86_64 InState := {
  label := "memcpy_exit"
  expectedDepth := 8
  entryProof := fun s => s.stackDepth = 8
  body := ⟨InState, fun s =>
    -- pop rbp ; ret
    let s' := { s with stackDepth := 0 }
    ⟨s', CpuTerminator.ret [] 0 (by decide) (by decide) (by decide)⟩⟩
}
```

---

## 5. Binary Code Emission & Round-Trip Soundness

$$\forall (p : \text{Program Arch}) (s : \text{MachineState}), \text{Step}_{\text{Hardware}}(\text{Decode}(\text{toBinary}(p)), s) \equiv \text{Step}_{\text{AST}}(p, s)$$
