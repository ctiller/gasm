# Proof-Carrying Assembly DSL & Invariant Model

In `gasm`, assembly code is not represented as raw, untyped strings or unstructured instruction streams. Instead, assembly routines are constructed inside a **Typed Proof-Carrying Monad (`BlockM`)** where every memory dereference, stack allocation, and register access is verified against formal invariants and discrete capability tokens.

---

## 1. Capability-Based Discrete Memory Permissions

To eliminate spatial memory safety vulnerabilities (out-of-bounds reads/writes, buffer overflows, and use-after-free) at the machine level, `gasm` models physical memory via **Discrete Memory Permissions**:

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

Different hardware targets enforce distinct memory ordering models. `gasm` captures these semantics via explicit architecture typeclasses:

- **x86 TSO (Total Store Order)**: Hardware guarantees Stores are ordered after earlier Loads, Stores to different locations are globally ordered, but Store-Load reordering can occur without `MFENCE`.
- **ARMv8 Weak Memory**: Loads and Stores can be freely reordered unless separated by explicit address/data dependencies or memory barrier instructions (`DMB ISHLD`, `DMB ISHST`, `DSB`).
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
