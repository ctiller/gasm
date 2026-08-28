# Equivalence, Layered Proofs & Automated Stack Verification

In `gasm`, verification is structured around **Total Correctness**, **Layered Function Composition**, and **Concrete Stack Depth Invariants**, adhering to the **Split Theorem Principle**.

---

## 1. Mathematical Formulation of Equivalence

Let:
- $\Sigma_{\text{spec}}$ be the high-level specification state space.
- $f_{\text{spec}} : \Sigma_{\text{spec}} \to \Sigma_{\text{spec}}$ be the high-level mathematical function or state transformer.
- $\mathcal{M}$ be the target architecture machine state (`MachineState`).
- $\text{step}_{\text{arch}} : \mathcal{M} \to \text{Option } \mathcal{M}$ be the formal single-step transition function of the target ISA.
- $\text{runUntilHalt} : \text{Program} \to \mathcal{M} \to \text{Option } \mathcal{M}$ be the multi-step operational execution.
- $\alpha : \mathcal{M} \to \Sigma_{\text{spec}}$ be the abstraction relation mapping low-level registers and memory to high-level values.

### The Commutative Equivalence Diagram

```
                 f_spec
   SpecState_0 -------------> SpecState_final
        ^                           ^
        | α                         | α
        |                           |
   MachineState_0 -----------> MachineState_final
                 runUntilHalt
```

### 1.1 The Definition of Observation (Canonical Equivalence Standard)

All equivalence obligations in `gasm` are **observational equivalence, in both directions**, over a precisely delimited set of observables. This subsection is the canonical statement of what "observable" means; any equivalence theorem whose observation set silently differs from this standard fails review.

**1. Observational, both ways.**
- For **deterministic specifications** (the current norm): the obligation is trace *equality* — `machTrace == specTrace` for all environments. Equality is symmetric, so bidirectionality holds by construction; its purpose is anti-vacuity (a do-nothing implementation must not refine a prefix of the spec).
- For **nondeterministic specifications** (permitted-behavior sets — e.g. a server that may accept connections in any order): the obligation splits into **refinement** (every machine behavior is spec-permitted) **plus progress/liveness** (the machine realizes some complete permitted behavior). Demanding literal both-ways equality there is wrong — it would require the implementation to exhibit *every* permitted behavior. The liveness half inherits the anti-vacuity role.
- **Non-terminating programs (reactive loops) are enforced as inner/outer proof pairs.** A program whose spec is an infinite service loop (e.g. a server) carries a distinct contract type (`VerifiedReactiveProgram` — ratified design, implementation tracked as PA7; Spike 4 currently ships as a plain `VerifiedProgram` without the liveness half and is the first migration target) with two *mandatory* proof fields, so neither half can be omitted: the **inner** obligation is deterministic both-ways trace equality for one iteration (∀ request/session in the request domain, the handler's contract trace equals the spec's), and the **outer** obligation is progress/liveness (the loop always returns to its accept state, consumes every arriving request, and never wedges). A reactive program verified only per-request (no liveness) or only live (no per-request equality) must be unrepresentable as verified; `emitVerifiedExecutable` for reactive programs accepts only the paired contract.
- **Concurrency generalizes the pair, it does not replace it.** Once threading/multiprocessing lands, a typical program contains *several* reactive loops. The contract then becomes: one inner/outer pair **per loop** (each loop's inner obligation is deterministic both-ways equality for its iteration; each loop's outer obligation is its own progress), plus **composition obligations** across loops — absence of deadlock/livelock at the declared synchronization points, and any fairness assumptions stated explicitly as part of the contract rather than assumed. The per-loop pairs must remain independently checkable (a loop's inner proof must not depend on another loop's scheduling); cross-loop interaction is confined to the composition layer, expressed through the causal-order machinery of `docs/OBLIGATIONS_AND_CAUSALITY.md` (vector clocks, synchronizes-with edges). Full design under Law 5 before the first threaded spike.

> **Provenance note.** The owner's own words on this point, both hedged: "we'll need to
> adjust when we build threading/multiprocessing -- we will have more than one infinite
> loop in a typical program," and "we should probably have a happens-after tracking in
> the trace normalization." The specific composition obligations above (deadlock/livelock
> freedom, explicit fairness assumptions, the vector-clock machinery) are the
> coordinator's design for satisfying that point, not stated by the owner in this detail.
> See ADR-0014's Provenance section.

**2. The observables are: syscall-boundary effects and contract-boundary data.**
- For **whole programs**: the bytes and effects crossing the kernel boundary — console/file/socket payloads at syscall time, exit codes, and the cross-stream ordering of effects. Observation is taken **up to a declared coalescing congruence**: consecutive writes to the same stream compose by byte concatenation (chunking is an internal detail — `write("ab")` and `write("a"); write("b")` are equivalent); ordering across distinct streams is conservatively preserved until a spec deliberately relaxes it. **The congruence is not per-program**: each effect's observation algebra is defined once, canonically, in the effects library specification (`docs/SYSTEM_EFFECTS.md` §6) alongside the effect typeclass it belongs to, with target specs refining only where a platform genuinely observes differently. Individual programs and proofs consume the declared algebra; they never invent their own.
- For **library routines** (no syscalls at their boundary): the observables are the routine's **contract footprint** — the memory the caller retains a capability to, plus any events the contract declares it emits. Caller-visible result structures ARE observable at this level.
- **Timing is never an observable for equivalence.** Otherwise no optimization is ever equivalent; performance is governed separately by cost contracts (see `docs/VISION.md` §5).
- **Contract trace vs. audit trace**: resource events proven to occur for safety/obligation purposes belong to the **audit trace** and are NOT equivalence observables — otherwise no allocator could ever be swapped. Equivalence ranges over the **contract trace** only. Be precise about where audit obligations attach: they are **target-realization obligations stated against per-target typeclass instances**, never portable-spec obligations. `VirtualAlloc`/`VirtualFree` are a *Windows implementation requirement*, proven of the Windows `PageSource` instance; a Linux realization proves `mmap`/`munmap` of its own instance; the portable spec knows only the abstract typeclass operation (`fetchPages`). Law 8's audited-tracing mandate binds each target instance to its platform's real calls — it says nothing about, and must not leak into, cross-target equivalence.

**3. Internal data structures are specifically excluded.** Heap layouts, allocator state, intermediate buffers, lookup tables, register allocation, algorithmic strategy — none are observables, and no equivalence proof may constrain them. This exclusion is what licenses wholesale reimplementation: any artifact producing the same observations is the same program. The boundary is exact: internal state becomes observable at the instant it crosses the contract boundary (buffer *contents at syscall time* are observable; the structures that produced them never are). Formally, **the capability frame is the observability boundary** — memory the caller (or kernel) holds a capability to is observable, memory the routine holds exclusively is internal (Law 11's tokens thus define both memory safety and observation).

---

## 2. Automated Stack Preservation via Local Jump Obligations

In `gasm`, stack depth is tracked directly as a concrete field inside `ComposedState` (`s.stackDepth : Nat`), enforcing frame safety locally across jump instructions:

```
+-------------------------------------------------------------------------+
| Entry Block (expectedDepth = 0)                                         |
|   push rbp; mov rbp, rsp; sub rsp, 64   --> stackDepth: 0 -> 64         |
|   jmp "bb_compute"                      --> Target expectedDepth = 64   |
+-------------------------------------------------------------------------+
                                    |
                                    | [Jump requires target expectedDepth = 64]
                                    v
+-------------------------------------------------------------------------+
| Compute Block (expectedDepth = 64)                                      |
|   - Compute logic, loop branches                                        |
|   - Cannot execute `ret` (Type error: `ret` requires stackDepth = 0)    |
+-------------------------------------------------------------------------+
                               /          \
  [Jump to Success Epilogue]  /            \  [Jump to Error Epilogue]
                             v              v
+-------------------------------------------------------------------------+
| Epilogue Block (expectedDepth = 64)                                     |
|   mov rsp, rbp; pop rbp                 --> stackDepth: 64 -> 0         |
|   ret                                   --> LEGAL (stackDepth = 0)      |
+-------------------------------------------------------------------------+
```

---

## 3. Total Correctness & Layered Composition

To prevent vacuous truths from diverging programs or invalid memory states, verification is formulated as **Total Correctness with Explicit Preconditions**:

$$\forall m_0, m_0 \models \text{Pre} \implies \exists m_{\text{final}}\text{ }k, \text{Step}^k(\text{prog}, m_0) = \text{Halt}(m_{\text{final}}) \land \text{Post}(m_0, m_{\text{final}})$$

---

## 4. The Three Independent Split Theorems

Every verified routine exports three independent theorems for distinct verification consumers:

**Status**: the `memcpy_*` theorems in §4.1–§4.3 are a **worked illustration of the shape**, not
tree contents — `memcpy`, `memcpy_program` and all three theorem names appear in no `.lean` file.
They are the canonical example of what a routine's three-way split looks like; the real instances
of this pattern live in the spike equivalence modules (`Spikes/*/Equivalence.lean`). Read them as
a template to write against, not as a claim about what is proved today.

```
                                 +-------------------------------------+
                                 | Verified Assembly Program AST (ASM) |
                                 +-------------------------------------+
                                       /          |          \
                                      /           |           \
                                     v            v            v
+------------------------------------------+  +------------------------------------------+  +------------------------------------------+
|      Consumer 1: Spec Verifiers          |  |      Consumer 2: Caller Call Sites       |  |      Consumer 3: Memory Safety Logic     |
+------------------------------------------+  +------------------------------------------+  +------------------------------------------+
| Theorem: Functional Equivalence          |  | Theorem: Callability & ABI Preservation  |  | Theorem: Memory Capability Invariants   |
| "The bytes are copied! Result = Spec"    |  | "The stack is preserved! Callee-saved OK"|  | "No write conflicts / Locked safety OK"  |
+------------------------------------------+  +------------------------------------------+  +------------------------------------------+
```

### 4.1 Theorem 1: Functional Equivalence & Memory Framing (Spec Consumer)

```lean
/-- Proves that the routine's output memory matches spec and leaves all unmodified memory intact -/
theorem memcpy_functional_equivalence :
  ∀ (m₀ : MachineState Arch) (src dst : List UInt8) (len : Nat),
    m₀.readMemory m₀.rsi len = some src →
    m₀.readMemory m₀.rdi len = some dst →
    m₀.rdx = len.toUInt64 →
    (m₀.rsi + len ≤ m₀.rdi ∨ m₀.rdi + len ≤ m₀.rsi) → -- Explicit Disjointness Precondition
    ∃ (m_final : MachineState Arch) (steps : Nat),
      runUntilHalt memcpy_program m₀ steps = some m_final ∧
      m_final.readMemory m₀.rdi len = some (specMemcpy src dst len) ∧
      -- Strict Separation Logic Frame Condition: Unmodified memory outside dst buffer is preserved!
      (∀ (addr : BitVec 64), (addr.toNat < m₀.rdi.toNat ∨ addr.toNat ≥ m₀.rdi.toNat + len) →
        m_final.readByte addr = m₀.readByte addr)
```

### 4.2 Theorem 2: Callability & ABI Preservation (Caller Consumer)

```lean
/-- Proves that the routine obeys the specified ABI discipline and restores stack and callee-saved registers -/
theorem memcpy_callability [abi : AbiDiscipline Arch ABI] :
  ∀ (m₀ : MachineState Arch),
    ValidFunctionEntryStack m₀.getSP →
    ∃ (m_final : MachineState Arch) (steps : Nat),
      runUntilHalt memcpy_program m₀ steps = some m_final ∧
      abi.returnStackRestoration m₀ m_final ∧
      (∀ reg ∈ abi.calleeSavedRegs, m_final.getReg reg = m₀.getReg reg) ∧
      m_final.callerSavedPoisoned
```

### 4.3 Theorem 3: Memory Safety (Memory Logic Consumer)

```lean
/-- Proves that the routine preserves discrete memory permissions during execution -/
theorem memcpy_memory_safety :
  ∀ (m₀ : MachineState Arch) (steps : Nat) (m_final : MachineState Arch),
    MemoryPerm m₀.rsi len .ReadOnly →
    MemoryPerm m₀.rdi len .Exclusive →
    runUntilHalt memcpy_program m₀ steps = some m_final →
    PreservesMemoryBounds m₀ m_final
```

---

## 5. Universal Parametric Program Equivalence over All Environment Inputs

Whole-program verification in `gasm` rejects pointwise, single-sample test assertions in favor of **Universally Quantified Parametric Contracts** over arbitrary environment interactions ($\forall env$).

### The Universal Whole-Program Equivalence Law

For any binary executable $P_{\text{asm}}$ and monadic specification $S_{\text{spec}}$ operating in an environment domain $\text{Env}$:

$$\forall (\text{env} \in \text{Env}),\ \text{Trace}\big(\text{runAsm}(P_{\text{asm}}, \text{loadEnvironment}(P_{\text{asm}}, \text{env}))\big) = \text{Trace}\big(S_{\text{spec}}(\text{env})\big)$$

```lean
structure VerifiedProgram (Env : Type := Unit) (Event : Type := AnyEvent)
    [ExternalCallInterceptor X86_64 Event] [BEq Event] [EnvironmentLoader Env] where
  name             : String
  executable       : WindowsExecutable
  instructions     : List X86_64Instr
  spec             : Env → List Event
  traceEquivalence : ∀ (env : Env),
    let s0 := EnvironmentLoader.loadEnvironment executable env
    (runAsmTrace (Event := Event) instructions s0 == spec env) = true
```

### Why Pointwise Single-Sample Equivalence Is Prohibited
1. **Prevents Canned Bypasses**: Proving equivalence on a single hardcoded 63-byte buffer does not prevent an assembly routine from being a hardcoded static table.
2. **Mandates Dynamic Syscall Processing**: The quantifier $\forall (env : Env)$ obligates the machine program to correctly handle empty streams, multi-block buffer splits, EOF conditions, and arbitrary byte lengths.

