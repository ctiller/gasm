# Portable System Effects Library & Architectural Lowering

In `gasm`, high-level software modeling in Stage 1 of the SDLC does not hardcode target-specific operating system syscalls or machine registers. Instead, programs express their interactions with the outside world using **Portable System Effect Typeclasses** (`Gasm.Effects.*`).

During architectural decomposition (Stage 3) and gasm realization (Stage 4), these abstract effects are systematically lowered into target-specific **Seams** and verified **Proof-Carrying Assembly Routines (`BlockM`)** carrying simulation equivalence proofs.

---

## 1. Universal Environment Oracle and Syscall Effects

Programs executing in real operating systems or bare-metal environments do not receive fixed, compile-time inputs. Instead, they interact with the outside world through **Syscall Interaction Oracles** (`Environment`).

```lean
/-- Universal model of the external operating system and runtime environment. -/
structure Environment where
  stdin            : ByteArray := ByteArray.empty
  args             : List String := []
  envVars          : List (String × String) := []
  incomingRequests : List String := []
  fileSystem       : List (String × ByteArray) := []
  clockTime        : UInt64 := 0

/-- Typeclass defining how an abstract environment `Env` is loaded into a machine's initial execution state. -/
class EnvironmentLoader (Env : Type) where
  loadEnvironment : WindowsExecutable → Env → X86_64MachineState

/-- Typeclass defining how an abstract environment `Env` is loaded into initial WASI state. -/
class WasiEnvironmentLoader (Env : Type) where
  loadWasiEnvironment : Env → ByteArray × List String
```

---

## 1.1 Core Effect Typeclass Hierarchy (`Gasm.Effects.*`)

```
                           +------------------------+
                           |      Monad (m)         |
                           +------------------------+
                                       |
          +----------------------------+----------------------------+
          |                            |                            |
          v                            v                            v
+-------------------+        +--------------------+       +-------------------+
|   MonadConsole    |        |  MonadFileSystem   |       |   MonadProcess    |
| - printStr        |        | - openFile         |       | - exitProcess     |
| - printLine       |        | - readFile         |       | - getEnvVar       |
| - readLine        |        | - writeFile        |       |                   |
+-------------------+        | - closeFile        |       +-------------------+
          |                  +--------------------+                 |
          +----------------------------+----------------------------+
                                       |
                                       v
                             +-------------------+
                             |    MonadClock     |
                             | - getMonotonicTime|
                             +-------------------+
```

---

## 2. Portable Effect Typeclass Specifications

### 2.1 `MonadConsole` (Standard I/O)

```lean
class MonadConsole (m : Type → Type) [Monad m] where
  /-- Outputs a string slice to the standard output stream -/
  printStr  : String → m Unit
  /-- Outputs a string slice followed by a newline character to standard output -/
  printLine : String → m Unit := fun s => do
    printStr s
    printStr "\n"
  /-- Reads a single line from standard input, returning none on EOF -/
  readLine  : m (Option String)
```

#### Algebraic Laws for `MonadConsole`:
1. **Sequential Output Composition**:
   $$\text{printStr } s_1 \gg \text{printStr } s_2 \equiv \text{printStr } (s_1 ++ s_2)$$
2. **Empty Output Identity**:
   $$\text{printStr } "" \equiv \text{pure } () $$

---

### 2.2 `MonadFileSystem` (File I/O & Descriptor Typestates)

```lean
inductive OpenMode where
  | Read
  | Write
  | ReadWrite
  | Append

inductive FileError where
  | NotFound
  | PermissionDenied
  | DiskFull
  | InvalidHandle
  | IoError (code : Nat)

structure FileHandle where
  id : Nat
  deriving DecidableEq, Repr

class MonadFileSystem (m : Type → Type) [Monad m] where
  openFile  : String → OpenMode → m (Except FileError FileHandle)
  readFile  : FileHandle → (maxBytes : Nat) → m (Except FileError ByteArray)
  writeFile : FileHandle → ByteArray → m (Except FileError Nat)
  closeFile : FileHandle → m (Except FileError Unit)
```

#### Algebraic Laws for `MonadFileSystem`:
1. **Linear Lifetime Law (No Use-After-Close)**:
   $$\forall h, \text{closeFile } h \gg \text{readFile } h \text{ } n \equiv \text{closeFile } h \gg \text{pure } (\text{Except.error } .InvalidHandle)$$
2. **Write-Read Preservation Law**:
   Writing bytes $B$ to an empty file followed by reading yields $B$.

---

### 2.3 `MonadProcess` (Lifecycle & Environment)

```lean
class MonadProcess (m : Type → Type) [Monad m] where
  /-- Terminates process execution unconditionally with the given exit code -/
  exitProcess : ∀ {α : Type}, UInt32 → m α
  /-- Retrieves an environment variable value by key -/
  getEnvVar   : String → m (Option String)
```

#### Algebraic Laws for `MonadProcess`:
1. **Exit Divergence Law**:
   $$\forall k, \text{exitProcess } c \gg k \equiv \text{exitProcess } c$$

---

## 3. High-Level Software Modeling Workflow

In Stage 1 & 2 of the SDLC, programs are written generically over effect typeclasses:

```lean
/-- Pure high-level software model for a greeting program -/
def greetAndExit [Monad m] [MonadConsole m] [MonadProcess m] (name : String) : m α := do
  MonadConsole.printLine s!"Hello, {name}!"
  MonadProcess.exitProcess 0
```

This model is completely independent of operating system, CPU architecture, or binary encoding. It can be tested in pure Lean using a state monad mock, and reasoned about with equational proofs.

---

## 4. Architectural Lowering Guidance (Stage 3 $\to$ Stage 4)

To translate a high-level effectful program into verified `gasm` assembly:

The design requires the seam's effect capabilities to compose as the placement-free typed row in
[Composable Boundary ABI Contexts](ABI_CONTEXT.md); that row-level connection is not implemented.
The diagrams below show semantic operations and machine calling conventions, not a global allocator,
cancellation token, or OS-owned context. A future realization must establish each runtime binding
and prove its complete target footprint.

```
+---------------------------------------------------------------------------------------------------+
| Stage 1 & 2: Pure Domain Model: greetAndExit [MonadConsole m] [MonadProcess m]                   |
+---------------------------------------------------------------------------------------------------+
                                                  |
                                                  | Architectural Seam Decomposition (Stage 3)
                                                  v
+---------------------------------------------------------------------------------------------------+
| Target ABI Seam Interfaces:                                                                       |
| - ConsoleOutSeam (Buffer : MemoryPerm .ReadOnly) -> Result                                        |
| - ProcessExitSeam (Code : UInt32) -> !                                                            |
+---------------------------------------------------------------------------------------------------+
                                                  |
                  +-------------------------------+-------------------------------+
                  | Lowering for Windows x64                      | Lowering for Linux x86-64
                  v                                               v
+-----------------------------------------------+ +-----------------------------------------------+
| Stage 4: Windows Realization                  | | Stage 4: Linux Realization                    |
| - printLine -> GetStdHandle + WriteFile       | | - printLine -> sys_write (RAX=1, RDI=1)       |
| - exitProcess -> ExitProcess                  | | - exitProcess -> sys_exit (RAX=60)            |
| - ABI: MS x64 (40B frame, 32B shadow)         | | - ABI: SysV x64 (Syscall registers)           |
+-----------------------------------------------+ +-----------------------------------------------+
```

### 4.1 Target Realization Matrix

| Portable Effect | Windows x64 Target Realization | Linux x86-64 Target Realization | Bare-Metal x86 Target Realization |
| :--- | :--- | :--- | :--- |
| `MonadConsole.printStr` | `RCX = GetStdHandle(-11)` $\to$ `WriteFile(RCX, RDX, R8, R9, [RSP+32])` | `RAX = 1` (`sys_write`), `RDI = 1`, `RSI = buf`, `RDX = len`, `syscall` | `OUT DX, AL` polling loop on UART `0x3F8` |
| `MonadFileSystem.openFile` | `CreateFileA` / `CreateFileW` | `RAX = 2` (`sys_open`), `syscall` | In-memory FAT32 sector walker / RAMDisk |
| `MonadProcess.exitProcess` | `RCX = exitCode` $\to$ `ExitProcess(RCX)` | `RAX = 60` (`sys_exit`), `RDI = code`, `syscall` | `CLI` $\to$ `HLT` infinite loop |

---

## 5. Formal Simulation Proof Bridge

For every lowering of a `MonadEffect` program into `BlockM`, a simulation theorem proves that the trace of external interactions matches the effectful specification:

$$\forall (s_0 : \text{ComposedState Arch InState}), \text{Trace}(\text{Realize}(P), s_0) \approx \text{Trace}(P.\text{eval})$$

---

## 6. The Observation Algebra (Canonical Coalescing Congruence)

Equivalence in `gasm` is observational **up to a coalescing congruence** on contract traces (see `docs/EQUIVALENCE_PROOFS.md` §1.1). That congruence is defined **here, once, per effect** — alongside the effect typeclasses it governs — and is to be consumed by every equivalence proof (see §6.3 for implementation status). Programs and proofs never define their own observation algebra; target specifications may refine an entry only where a platform genuinely observes differently, and must document why.

### 6.1 Per-Effect Coalescing Rules

| Effect | Coalescing rule | Rationale |
| :--- | :--- | :--- |
| `ConsoleEvent.out` / `.err` | Consecutive writes to the **same** stream compose by byte concatenation; the two streams are distinct. | Chunking is an internal buffering detail; no consumer of the stream can distinguish it. |
| `FileSystemEvent.write` | Consecutive writes to the same descriptor compose by concatenation at the current offset. | Same as console; a reader observes final content and ordering, not syscall counts. |
| `NetEvent.send` | Sends on the same connection compose by concatenation **only within a protocol message boundary declared by the spec** AND only within an input-free causal segment (§6.4); message boundaries and cross-connection ordering are preserved. | TCP is a byte stream (chunking invisible), but specs at message granularity observe message ordering, and responses must stay causally after the inputs they answer. |
| `NetEvent.recv` / reads / `accept` | **Never coalesced; input events are causal anchors and coalescing barriers** (§6.4). | Cross-direction causality (read-then-ack vs. ack-then-read) is protocol meaning. |
| `ProcessEvent.exit` | Never coalesced; terminal; exactly one per trace. | The exit code and the finality of exit are observable. |
| `ClockEvent.queryTime` | Not an equivalence observable (see below). | Timing is excluded from observation entirely. |
| Cross-stream / cross-effect ordering | Preserved (conservative default). | Relaxation is a per-spec decision requiring explicit justification, not a library default. |

### 6.2 Exclusions Restated

- **Timing** is never an observable: neither the wall-clock cost of any operation nor the values returned by clock queries participate in equivalence (clock *values* are environment inputs supplied by the `Environment` oracle; the spec and machine consume identical oracle values by construction). Performance is governed by cost contracts (`docs/VISION.md` §5).
- **Audit-trace events** (per-target resource calls such as Windows `VirtualAlloc`/`VirtualFree`, Linux `mmap`/`munmap`) are obligations of target typeclass instances under Law 8 and are not part of the observation algebra. See `docs/EQUIVALENCE_PROOFS.md` §1.1.

### 6.3 Canonical Trace Normal Form (with Happens-After Tracking)

`Gasm/Effects/CanonicalizeTrace.lean` now implements `canonicalizeTrace`,
`canonicalizeCausalTrace`, `CausalEvent`, and single-thread causal stamping. Not every
`VerifiedProgram` consumer has migrated to this normal form, and multi-thread stamping is not
implemented. Raw-trace equality accidentally observes chunking and is deprecated for contracts
whose effect algebra has a canonicalizer.

The normal form carries **happens-after tracking** from day one, even while all programs are single-threaded:

- The concurrent representation is a labelled partial order with stable event identities. A
  target/profile `TraceProjection` selects admitted labelled source-path reachability and every
  `ProjectedCausalEdge` retains that path witness. A vector clock may cache only a separately proved
  transitive relation/projection; it is neither an ISA consistency model nor an information-
  equivalent replacement for native relation labels (`docs/MEMORY_MODEL.md` §11). In the initial
  one-thread CPU profile the selected order is total.
- **Coalescing respects causality**: adjacent same-stream writes fold together only when causally consecutive — no observable event ordered between them. This is what makes the congruence correct once multiple loops/threads interleave: two writes with an intervening causally-ordered observable on another stream must not merge.
- **Equivalence under concurrency** is equality of labelled canonical causal partial orders modulo
  event-key renaming/poset isomorphism, using the selected profile projection rather than one
  scheduler linearization. In a CPU profile, a release/acquire source path is admitted only when the
  architecture model establishes its relevant read-from relationship; plain reads-from and futex
  wake are not automatically synchronizes-with. GPU/API, device, transport, acknowledgement, and
  persistence profiles contribute their own native labelled paths and composition laws.
- The concurrent normal form uses an explicit total, non-inventing quotient from raw observables to
  canonical nodes. Coalescing is allowed only by the per-effect rules above and must preserve the
  stream, label, specified payload fold, and causal barriers. Between quotient nodes, trace order is
  faithful in both directions to profile-selected labelled source-path reachability, independent of
  whether the source graph stores one direct edge or a multi-edge path/transitive reduction.
- The multi-thread representation and trace-order soundness theorem are stage M8 of
  `docs/MEMORY_MODEL.md` §14. Current list-based single-thread normalization is its degeneration,
  not the final concurrent representation.

### 6.4 Input Events Are Causal Anchors and Coalescing Barriers (Protocol Causality)

For protocol work, happens-after and coalescing interact deeply, and getting it wrong changes program meaning:

> **Writing an ack *for* a read IS NOT EQUIVALENT to writing an ack *before* a read.**
>
> (Owner's exact words, 2026-08-27: "writing an ack for a read IS NOT EQUIVALENT to
> writing an ack before a read." An earlier draft of this section rendered it as "an ack
> *in response to* a read" — a paraphrase, not the owner's wording; restored here.)

A server that pre-emptively emits `OK` and then reads the request is a different — broken — program from one that reads and then acks, even though each direction's byte stream is identical in isolation. The distinction lives entirely in the cross-direction causal order, and the peer can observe it (an ack that arrives before the request was sent proves the ack did not depend on the request). Therefore:

- **Input events (`recv`, file/console reads, `accept`) are first-class contract-trace events**, recorded with their position in the causal order — not silent environment consumption. Their payloads come from the `Environment` oracle as before; what observation adds is their *occurrence and ordering*. (The current `FileSystemEvent`/`TraceM` model records no read events; that is a defect to fix under this section, not a precedent.)
- **Inputs are coalescing barriers**: output coalescing (§6.1) applies only within input-free causal segments. Outputs on either side of an input event never merge and never commute across it.
- **The input→dependent-output happens-after edge is observable** and must be preserved by `canonicalizeTrace`: an implementation that hoists an output above an input it specification-depends on is NOT equivalent, no matter how the per-stream bytes compare.
- Symmetrically, an output with **no** specification-level dependence on a subsequent input may be ordered freely relative to it only if the spec explicitly declares that independence — the conservative default is that program order into and out of input events is preserved.
