# Citation Adequacy Review (Pillar 2, first pass)

**Scope**: this is a review of *citation semantics* — whether the `docs/` section a
`/- REF: -/` names actually justifies the Lean declaration it sits above. It changes no code
and no other document. `scripts/check_refs.py` validates that an anchor **resolves**; nothing
in the tree has ever checked that it **holds up**. `docs/REVIEW.md` §4.2 (Pillar 2) is where
that obligation would live, and until this pass no reviewer had been asked to discharge it.

**Method**: for each of six clusters flagged by the docs audit, every citation's declaration
signature was read, the cited section was read in full, and each pair was judged. Roughly a
fifth were additionally read with surrounding file context to confirm the judgement and to
capture verbatim examples. Counts were verified by reading, not by grepping; the grep totals
below match the docs audit's exactly once the `.claude/worktrees/` copies of the tree are
excluded (they inflate every raw count by roughly 45×).

**Corpus reviewed**: 289 citations across six anchors.

---

## 1. Classification taxonomy

| Class | Meaning |
| :--- | :--- |
| `justified` | The cited section states something the declaration genuinely depends on. |
| `understated` | The section is on-topic but states strictly less than the declaration commits to. |
| `misaimed` | Right document, wrong section — the justifying content exists elsewhere in the same file. |
| `false` | The section describes something else entirely, or contradicts the declaration. |
| `vacuous` | The cited heading has no body at all. |

### 1.1 One interpretive fork, stated up front

Two of the six anchors are **parent headings whose own body is empty or near-empty but whose
subsections carry real content** (`X86_64.md#1`, `WINDOWS.md#1`). Whether a citation to §1 is
read as pointing at §1's own prose or at §1-including-§1.1–1.3 changes the verdict on ~96
citations. This review adopts the **charitable reading** — a section citation subsumes its
subsections — because that is how documents are ordinarily read and because
`check_refs.py` resolves headings rather than spans. Under the strict reading every one of
those 96 is `vacuous`. Both numbers are given where it matters.

---

## 2. Cluster totals

| # | Anchor | Read | `justified` | `understated` | `misaimed` | `false` |
| :-- | :--- | --: | --: | --: | --: | --: |
| 1 | `docs/TARGETS/X86_64.md#2-binary-instruction-encoding` | 129 | 2 | 111 | 2 | 14 |
| 2 | `docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing` | 57 | 3 | 4 | 9 | 41 |
| 3 | `docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention` | 39 | 3 | 4 | 17 | 15 |
| 4 | `docs/SPIKES.md#3-spike-progression-roadmap` | 26 | 0 | 5 | 0 | 21 |
| 5 | `docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture` | 25 | 2 | 6 | 2 | 15 |
| 6 | `docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine` | 13 | 3 | 0 | 0 | 10 |
| | **Total** | **289** | **13** | **130** | **30** | **116** |

Under the strict reading of §1.1 above, clusters 2 and 3 move wholly to `vacuous` and the
totals become 7 `justified` / 126 `understated` / 4 `misaimed` / 60 `false` / 96 `vacuous`.

---

## 3. Cluster 1 — `X86_64.md#2-binary-instruction-encoding` (129 read)

### 3.1 The cited section, in full

```
## 2. Binary Instruction Encoding

An x86-64 instruction consists of up to 15 bytes formatted as follows:

    +-------------------+------------+---------+--------+-----+--------------+-----------+
    | Legacy Prefixes   | REX Prefix | Opcode  | ModR/M | SIB | Displacement | Immediate |
    | (0-4 bytes)       | (0-1 byte) | (1-3 B) | (0-1B) |(0-1)| (0,1,2,4,8 B)| (0,1,2,4B)|
    +-------------------+------------+---------+--------+-----+--------------+-----------+
```

One sentence and a fenced box naming seven slot *positions and widths*. No opcode value, no
bit layout within any slot, no byte order, no register numbering, no sign-extension rule.

### 3.2 `justified` — 2

Both are the same shape: a total function from an instruction to a byte string, with no
content beyond that.

```
/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Binary encoder forwarding to the modular X86_64Instruction typeclass. -/
def encodeX86_64Instr (instr : X86_64Instr) : ByteArray :=
  X86_64Instruction.encode instr
```
`Gasm/Targets/X86_64/Encoding.lean:24` (and `X86_64Instr.toBinary`,
`Gasm/Targets/X86_64/Instructions/Base.lean:535`). "An x86-64 instruction consists of up to 15
bytes" is exactly and entirely what these declarations assert. This is what a thin section
legitimately supports.

### 3.3 `understated` — 111

**(a) The seven field codecs (`Base.lean:103`–`:133`).** The section names the slots; the code
states the bit layouts the section omits.

```
/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Constructs an 8-bit REX prefix byte from its 1-bit fields. -/
def makeRex (w : Bool) (r : Bool) (x : Bool) (b : Bool) : UInt8 :=
  0x40 ||| (if w then 8 else 0) ||| (if r then 4 else 0) ||| (if x then 2 else 0) ||| (if b then 1 else 0)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Constructs an 8-bit ModR/M byte from mod, reg, and rm fields. -/
def makeModRM (mod : UInt8) (reg : UInt8) (rm : UInt8) : UInt8 :=
  ((mod &&& 3) <<< 6) ||| ((reg &&& 7) <<< 3) ||| (rm &&& 7)
```

The section says `| REX Prefix | (0-1 byte) |`. The code says REX is `0x40` with W at bit 3, R
at bit 2, X at bit 1, B at bit 0; and that ModR/M is `mod:2 | reg:3 | rm:3`. Every one of
those facts is real, correct, and sourced from nothing in this repository. `parseRex`,
`isRex`, `extractModRM`, `makeSIB` and `extractSIB` are the same story. These are the
citations where the gap is *narrowest* and the remedy is clearest: eleven lines of prose under
§2 giving the REX/ModR/M/SIB bit layouts would convert seven `understated` citations to
`justified` and would be worth writing.

**(b) Eleven byte-level helpers (`Base.lean:138`–`:246`).** `readUInt16LE`, `readUInt32LE`,
`uint64ToLittleEndian`, `signExtend8To64`, `signExtendUInt32To64` and siblings. §2 gives
displacement and immediate *widths* (`0,1,2,4,8 B`) and says nothing about endianness or
sign-extension — the two facts these declarations exist to encode.

**(c) Eighty-nine instruction-form smart constructors.** The dominant population of the
cluster, and structurally the most interesting, because the *correct* citation is already
present in the same file a few lines up:

```
/- REF: intel-sdm#vol=2;instr=AND;part=description -/
structure AndR64R64 where ...

/- REF: intel-sdm#vol=2;instr=AND;part=operation -/
instance : X86_64Instruction AndR64R64 where ...

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- AND reg64, reg64 helper. -/
def and_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨AndR64R64.mk dst src⟩
```
`Gasm/Targets/X86_64/Instructions/And.lean:27`, `:34`, `:100`.

The declaration commits to a specific instruction form and operand typing; §2 names no
instruction. Note that the *encoding* — the opcode bytes — is not here at all: it lives in the
`instance`, which cites Intel correctly. So the docs audit's framing ("the largest cluster is
opcode encodings landing on a generic diagram") is slightly off: the opcodes are properly
cited. What lands on the diagram is the ergonomic wrapper layer. This is a milder defect than
advertised, and its remedy is mechanical — retarget each `foo_r64` helper to the same
`intel-sdm#vol=2;instr=FOO` slug its own structure already uses.

**(d) Two fuzzer properties** (`StabilityFuzzer.lean:105` `mutPrependRex`, `:185`
`checkStability`) — on-topic (REX prefix parsing, encode/decode roundtrip), thinner in the
doc than in the code.

### 3.4 `misaimed` — 2

`Disassembler.lean:65` `disassembleToLean` and `:72` `disassembleToLeanModule`. These decode
bytes; the decoder has a real home at `docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization`,
which `andTryDecode` and the whole `*.tryDecode` family already cite correctly.

### 3.5 `false` — 14

The section describes a binary byte layout. These declarations produce **text**, parse CLI
arguments, or concern a different subject entirely.

```
/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Formats a UInt64 as a hexadecimal string literal for Lean source code. -/
def formatHex64 (v : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 v.toNat)
  s!"0x{s}"
```
`Base.lean:294`. Also `formatHex8`, `formatHex32`, `formatDisp8`, `formatDisp32` (NASM
disassembly text), the `ToString AnyX86_64Instruction` instance (`Base.lean:94`, which
delegates to `toNASM`), `Disassembler.lean:27`/`:33` (which emit Lean source, one of them
literally `"import Lean\n" ++ ...`), `StabilityFuzzer.lean:28`/`:54` (hex diagnostic strings),
and:

```
/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CLI Driver for x86-64 Hardware Semantic Fuzzer. -/
def main (args : List String) : IO UInt32 := do
  let mut iterations : Nat := 150
```
`SemanticsFuzzerCLI.lean:22`.

The cross-domain pair is the sharpest:

```
/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- The byte mask selecting exactly the `methodTokenBytes m` bytes out of such a 64-bit load, so a
    shorter token is compared against only its own bytes and not whatever follows it in the buffer. -/
def methodTokenMask (m : Stdlib.Http11.Method) : UInt64 :=
  (methodTokenBytes m).foldr (fun _ acc => (acc <<< 8) ||| 0xFF) 0
```
`Spikes/Spike4HttpServer/Spec.lean:195` (and `methodTokenWord` at `:188`). This is HTTP
request-line parsing. Its two immediate neighbours in the same file both cite
`docs/STDLIB_HTTP11.md#21-request-line`, correctly. The x86-64 anchor was reached for because
the doc comment mentions `mov r64, [mem]`.

Finally `Mov.lean:627`, a state-transition soundness theorem about sign-extending an imm32
into a 64-bit memory store, cited to a section about byte layout.

---

## 4. Cluster 2 — `X86_64.md#1-machine-state-model-sub-register-aliasing` (57 read)

The heading has **zero body lines**: `## 1.` at line 7, a blank line, then `### 1.1` at line 9.
Under the charitable reading, §1.1 contributes a 9-row GPR alias table and a zero-extension
invariant. That is the whole of the section's content: **general-purpose registers**.

### 4.1 The decisive fact

`docs/TARGETS/X86_64.md` contains the substring `flag` exactly once, in the word "flagged", in
a `**Status**` note about memory ordering. The tokens `ZF`, `SF`, `CF`, `OF`, `PF`, `AF`,
`EFLAGS` and `RFLAGS` occur **zero times** in the file.

Fourteen declarations encoding exact EFLAGS bit positions cite it.

```
/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Bitmask for all 6 standard arithmetic status flags (CF: bit 0, PF: bit 2, AF: bit 4, ZF: bit 6, SF: bit 7, OF: bit 11). -/
def arithmeticStatusMask : UInt64 := ...
```
`Gasm/Targets/X86_64/Registers.lean:142`. Also `zf` (bit 6), `sf` (bit 7), `cf` (bit 0), `of_`
(bit 11), `computeParity8`, `computeAuxCarry`, and the seven `setFlags*64` transformers.

Fifteen lines above, in the same file, the correct source is already in use:

```
/- REF: intel-sdm#vol=1;sec=3.4;part=34-basic-program-execution-registers -/
/-- Updates 64-bit general-purpose register value. -/
def X86_64MachineState.setGpr64 (s : X86_64MachineState) (r : Reg64) (val : UInt64) : X86_64MachineState := ...

/- REF: docs/TARGETS/X86_64.md#11-general-purpose-registers-gprs-32-bit-zero-extension -/
/-- Updates 32-bit sub-register with mandatory 64-bit hardware zero-extension. -/
def X86_64MachineState.setGpr32 (s : X86_64MachineState) (r : Reg32) (val : UInt32) : X86_64MachineState := ...
```

Note the second one: it cites **§1.1**, the subsection where the content actually is. So the
same file demonstrates, four declarations apart, both the correct pattern and the
anchor-of-convenience. The `setGpr32` citation is the single best citation found in this
review's x86-64 reading — the zero-extension invariant it depends on is stated verbatim in the
section it names.

### 4.2 Other `false` findings in this cluster — 27 more

- **`Semantics.lean`, 13 citations.** The interpreter: `stepX86_64`, `instructionAtRip`,
  `indexInstructions`, `runProgramTraceWithLoops`, `runProgramWithLoopsIntercept`,
  `initMachineState`, `callSubroutine`, plus the `ExternalCallInterceptor` class and two
  indexing-equivalence theorems. Fuel-bounded execution, RIP indexing and external-call
  interception are not sub-register aliasing.
- **`Spike2Fibonacci/Windows/LoopInvariant.lean`, 7 citations** — bit-6-clear lemmas for
  `computeParity8`/`computeAuxCarry`, and two run-to-completion fuel lemmas.
- **`Spike3SortLines/TraceStepLemmas.lean`, 4 citations** — trace-step lemmas for
  `runProgramTraceWithLoops`.
- **`SemanticsFuzzer.lean:81` `formatFlagDiff`, `:100` `verifyInstructionSemantics`**, plus a
  hardware-safety note at `:66`.

The mechanism is visible in the title: "Machine State Model **&** Sub-Register Aliasing" is a
broad enough phrase to feel like a home for anything touching `X86_64MachineState`, while the
body is narrow. A title that overpromises relative to its body is what makes an
anchor-of-convenience attractive.

### 4.3 `misaimed` — 9, including one layering inversion

Eight are memory operations (`write8`, `write64`, `push64`, `pop64`, `readString`, the sealed
`X86_64Memory` note, and the `Inhabited` default carrying `rip := 0x401000, flags := 0x202`) —
`docs/MEMORY_HOOK.md` and `docs/STACK_DISCIPLINE.md` are the real homes and are cited by name
in several of those declarations' own doc comments.

The ninth is the layering defect the docs audit flagged, and it is real:

```
/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Target register model parameterized by architecture and bit width. -/
structure Register (Arch : Type) (width : Nat) where
  id : Nat
```
`Gasm/Core/CFG.lean:24`. An architecture-*parameterised* structure in `Gasm/Core/` deriving its
justification from an x86-64-specific target document. Whatever the citation's adequacy, a
target document cannot be the source of an arch-generic core type without inverting the
dependency the whole `TargetArch` abstraction exists to maintain.

### 4.4 `understated` — 4, and a partial disagreement with the docs audit

```
/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- 16-bit word. -/
@[reducible] def Word := UInt16
```
`Gasm/Core/Types.lean:33`, with `QWord`, `DWord` and `Byte` alongside.

The docs audit lists these as landing on an empty heading. That is true of §1's own body, but
§1.1's table does carry a `| 64-bit | 32-bit | 16-bit | 8-bit Low |` column ladder, so the
width correspondence is not wholly unsourced — `understated`, not `vacuous`. The stronger
objection to these four is the same layering inversion as `Register` above: they are
target-independent width names in `Gasm/Core/`, and an x86-64 register-aliasing table is not
where a repository-wide width vocabulary should be defined.

### 4.5 `justified` — 3

`Registers.lean:27` (`structure X86_64` / `inductive Reg64` — §1.1's table enumerates exactly
these sixteen registers and their aliases), and `SemanticsFuzzer.lean:52`/`:59`
(`allRegs64`/`allRegs32`).

---

## 5. Cluster 3 — `WINDOWS.md#1-microsoft-x64-calling-convention` (39 read)

§1's own body is one sentence. §1.1 (register allocation), §1.2 (shadow space and alignment,
with two stack-layout diagrams) and §1.3 (red-zone prohibition) carry the content. The docs
audit is right that this is a *retargeting* defect and not a missing-content defect — but only
for a minority of the cluster. For most of it the content is not in §1.1–1.3 either; it is in
§2 or §3 of the same file.

### 5.1 `justified` — 3, and the audit's example holds up

```
/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Implementation of MS x64 Fastcall calling convention discipline for x86-64. -/
instance : AbiDiscipline X86_64 WindowsFastcall where
  callerSavedRegs      := [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨8⟩, ⟨9⟩, ⟨10⟩, ⟨11⟩] -- RAX, RCX, RDX, R8-R11
  calleeSavedRegs      := [⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨12⟩, ⟨13⟩, ⟨14⟩, ⟨15⟩] -- RBX, RSP, RBP, RSI, RDI, R12-R15
  shadowSpaceRequired  := 32
  stackAlignment       := 16
  argumentRegisters    := [⟨1⟩, ⟨2⟩, ⟨8⟩, ⟨9⟩] -- RCX, RDX, R8, R9
  returnRegister       := ⟨0⟩ -- RAX
```
`Gasm/Targets/Windows/ABI.lean:34`. Every field is stated verbatim in §1.1 or §1.2:
"Caller-Saved Scratch: `RAX`, `RCX`, `RDX`, `R8`–`R11`"; "Callee-Saved Non-Volatile Registers:
`RBX`, `RBP`, `RDI`, `RSI`, `RSP`, `R12`–`R15`"; "First 4 Arguments: `RCX`, `RDX`, `R8`, `R9`";
"Return Value: `RAX`"; "**MUST allocate at least 32 bytes**"; "$RSP \equiv 0 \pmod{16}$". This
citation is fully adequate, and it shares an anchor with the worst instances in this review —
exactly the calibration point the review brief asked for. `structure WindowsFastcall` and
`popReturnAddress` (justified by §1.2's callee-view diagram placing the return address at
`[RSP + 0]`) round out the three.

### 5.2 `false` — 15

The four `EnvironmentLoader` instances are the clearest illustration in the whole review of how
an anchor-of-convenience forms, because the correct citation is **three lines above them**:

```
/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Typeclass defining how an abstract environment `Env` is loaded into a machine's initial execution state. -/
class EnvironmentLoader (Env : Type) where
  loadEnvironment : WindowsExecutable → Env → X86_64MachineState

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Default loader instance for standalone executables with closed/empty environment. -/
instance : EnvironmentLoader Unit where
  loadEnvironment exe _ := exe.load

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Loader instance for CLI utilities and filter programs taking dynamic stdin streams. -/
instance : EnvironmentLoader ByteArray where
  loadEnvironment exe stdin := exe.loadWithStdin stdin
```
`Gasm/Core/Verification.lean:47`–`:61`. The class carries the right citation; its four
instances drift to a calling-convention section that has nothing to do with them. As with
`Gasm/Core/CFG.lean`, these are `Gasm/Core/` declarations pointing at a target document.

The rest: `win32Intercept`/`win32CallIntercept` (`Win32API.lean:278`, `:300`), five
`HardwareHarness.lean` declarations covering result decoding and oracle-integrity notes, the
`Dispatcher.lean:38` interceptor instance, and three `Spike3SortLines/Windows/InterceptLemmas.lean`
lemmas about IAT-slot alignment and the Linux syscall sentinel.

### 5.3 `misaimed` — 17, and most of them want §2/§3, not §1.1

Nine in `Win32API.lean` and six in `Linker.lean` are PE/COFF import-table and section-layout
work whose home is §3 ("PE32+ Binary Header Loader Invariants"). `findIatIndex`
(`Win32API.lean:270`) is the plainest: §3 names the Import Address Table data directory
explicitly. `VirtualAllocDef`/`VirtualFreeDef` bind to `"KERNEL32.dll"`, which §3 names and §1
does not. And:

```
/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Builds the .text bytecode for test execution using the exact computed section layout. -/
def buildTestText (layout : SectionLayout) (testCases : List (X86_64MachineState × ByteArray)) : ByteArray := Id.run do
  ...
  let imageBase : UInt64 := 0x140000000
```
`HardwareHarness.lean:88`. `0x140000000` is stated in §3 ("Default Image Base: `0x140000000`"),
not in §1.

So: the docs audit's "39 of 43 land on the parent rather than §1.1–1.3" is arithmetically
right but diagnostically incomplete. Retargeting to §1.1 would fix roughly seven citations.
Seventeen want a different top-level section, and fifteen want a different document.

---

## 6. Cluster 4 — `SPIKES.md#3-spike-progression-roadmap` (26 read)

### 6.1 This cluster's cause is a missing document

All 26 citations come from `Spikes/Spike2Fibonacci/**`. Not one comes from anywhere else.

`docs/SPIKES/` contains `SPIKE3_SORT_LINES.md`, `SPIKE4_HTTP_SERVER.md`, `SPIKE5_GZIP.md` and
`SPIKE8_MULTITHREADING.md`. There is no `SPIKE2_*.md`. Spike 1 at least has `docs/SPIKES.md` §2,
which includes an "Architectural Capabilities Forced by Spike 1" table naming its instructions,
ABI obligations and PE structures. Spike 2 has one line, inside a fenced ASCII box:

```
| Spike 2: Recursive & Iterative Fibonacci (Pure Control Flow, Memory & Trace Equivalence)          |
```

That is the entire specification available to a spike with a symbolic program, two linkers,
three emitters, a Windows and a Linux target, and a loop-invariant proof file.

**This is a missing-document finding, not a bad-citation finding.** Retargeting these 26
citations is impossible because there is nowhere to retarget them to. The remedy is to author
`docs/SPIKES/SPIKE2_FIBONACCI.md`. **Status**: no such document exists in the tree; this review
proposes one and does not write it.

### 6.2 `understated` — 5

`Spec.lean:29` `fibNat`, `:36` `fibIterLoop`, `:43` `fibIter`, `:48` `fibIterLoop_invariant`,
`:67` `fibIter_eq_fibNat`. The box line does name "Recursive & Iterative Fibonacci" and "Trace
Equivalence", so the *existence* of a recursive definition, an iterative one and an equivalence
between them is genuinely gestured at. What it does not state is the recurrence, the base
cases, or which of `F(0) = 0` / `F(0) = 1` this repository uses — the one fact a reader
checking `fibNat` would need.

### 6.3 `false` — 21

```
/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
def fibonacciSpec : TraceM AnyEvent Unit := do
  for i in [0:90] do
    ...
```
`Spikes/Spike2Fibonacci/Spec.lean:93`. The spike's own specification — the artifact every
equivalence theorem in Spike 2 is stated against — cites a roadmap picture. The constant `90`
appears nowhere in `docs/`. Neither does the output format that
`formattedFibonacciWindowsOutput` (`:77`) and `formattedFibonacciWasmOutput` (`:85`) fix, and
against which the host-execution check compares real stdout byte for byte.

The other sixteen are the symbolic programs (`Windows/Program.lean:47`,
`Linux/Program.lean:47`), the assembled instruction lists, the linkers, the executables, the
three `main` emitters and the test driver. A section that orders eight spikes relative to one
another says nothing about any of them.

---

## 7. Cluster 5 — `SPIKE3_SORT_LINES.md#1-overview-high-level-architecture` (25 read)

§1 is one 52-word sentence plus an 8-line mermaid fence. The docs audit's "75% mermaid" is
accurate. Two further facts matter more than the ratio:

1. **The diagram is entirely Win32.** Its edges are `Win32 ReadFile`, `Win32 WriteFile`,
   `Win32 ExitProcess`, and its buffer node is `[RSP + 0x60]` — a Windows stack offset.
2. **The document never mentions Linux, ELF, Wasm or WASI.** A case-insensitive search for all
   four returns nothing. The file's title is "Verified Stdin Lexicographical Sort & Windows
   PE64 Executable".

Eleven of the 25 citations come from `Spike3SortLines/Linux/**` and `Spike3SortLines/Wasm/**`.
Those targets have no coverage anywhere in this document — a second, smaller instance of the
missing-document finding, this time a missing *section* in an existing document.

`Wasm/Program.lean:46` is the sharpest: its doc comment lays out a WASI linear-memory map
(`Offset 0x00: stdin ciovec (bufPtr=0x100, bufLen=512)`) and cites a diagram whose only memory
reference is a Windows stack displacement.

### 7.1 A correction to the docs audit, and a clean retargeting

The audit states that neither `crlfBytes` nor the fruit list appears anywhere in §1. Both true.
But `crlfBytes` *is* documented — one section down:

```
/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
def crlfBytes : ByteArray := "\r\n".toUTF8
```
`Windows/Program.lean:51` and `Linux/Program.lean:51`, against §3.1: "Lines are delimited by
newline characters (`\n` / ASCII `0x0A` or `\r\n` / ASCII `0x0D 0x0A`)." These two are
`misaimed` with an exact retarget available (`#31-line-record-representation`), not unsourced.

The fruit list genuinely is unsourced. `cherry`, `apple` and `banana` appear nowhere in
`docs/`, in any file:

```
/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
def defaultInputLines : List String := ["cherry", "apple", "banana"]
```
`Spec.lean:97`, plus the three `defaultSampleInput` byte arrays that encode the same three
words with CRLF separators. These are test fixtures rather than specification, which is a fair
mitigation — but Law 1 admits no fixture exemption, and the honest fix is either a fixture
subsection in the spike document or a citation that does not overclaim.

**Counts**: 2 `justified` (`Spec.lean:72` `readAllLines` and `:83`, the sort specification —
both squarely described by the sentence and the diagram's five steps), 6 `understated` (the
Windows target's linker/emitter/test declarations, which the diagram names only as pictures),
2 `misaimed` (`crlfBytes` ×2), 15 `false`.

---

## 8. Cluster 6 — `SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine` (13 read)

### 8.1 The docs audit is stale here — this section was already fixed

The audit describes §2 as "a section whose body *is* `inductive GzipMode` / `structure
GzipConfig`, copied verbatim from the tree". That was true before commit `cc1e997`
(*docs(honesty): disclose Spike 4's invented WASI socket API; refresh three stale ledgers*).
The prior revision's body is confirmable with `git show cc1e997^:docs/SPIKES/SPIKE5_GZIP.md`
and was exactly the transcribed declarations. The current body opens:

```
**Status** (corrected 2026-08-28): this section used to transcribe `GzipMode`, `GzipConfig` and
the three signatures below verbatim from the tree. That is Law 12's unlinked twin — a second
encoding of one fact, adding no information because it *was* the code — and it had already
drifted [...] The declarations are cited rather than copied now, so that drift cannot recur.
```

The audit read a pre-`cc1e997` tree. Cluster 6 as characterised no longer exists.

### 8.2 `justified` — 3, and these are the best citations in the review

Against the current body, `Spec.lean:32` `GzipMode`, `:39` `GzipConfig` and `:47`
`parseGzipFlags` are fully justified. §2 states that `GzipMode` is a two-constructor enum
`Compress`/`Decompress`; that `parseGzipFlags` recognises `-d`, `--decompress`, `-dc` and
`-cd`; that `GzipConfig` carries the mode plus `keepSource` and `level`; and that both derive
`DecidableEq`/`Repr`/`Inhabited`, with a reason (it is what lets the equivalence theorems
decide trace equality). Every one of those is checkable against the code, and none of it is a
transcription. This is the shape the other five clusters should be measured against.

### 8.3 `false` — 10, and a second missing-section finding

All ten are in `Spikes/Spike5Gzip/Linux/**`: two `main` emitters and eight ELF
link/instruction/executable declarations, citing "Monadic Specification & CLI State Machine".

The cause is again structural. `SPIKE5_GZIP.md` §4 is "Dual-Target Architectural Realization",
with §4.1 (`x8664-windows-kernel32dll`) and §4.2 (`webassembly-wasi-wasisnapshotpreview1`).
The Windows and Wasm targets cite those two subsections correctly — 10 and 8 citations
respectively. **There is no §4.3 for Linux**, and the document mentions neither Linux nor ELF
anywhere. The Linux target, having no home, took §2. Same failure mode as Spike 3's Linux and
Wasm targets, and the same remedy: a section, not a retarget.

---

## 9. Is the `sockListen` shape — a citation that is *false*, not merely empty — isolated?

No. It is the most conspicuous instance because the invented API was disclosed, but the shape
recurs across every cluster:

| Instance | Declaration asserts | Cited section describes |
| :--- | :--- | :--- |
| `Registers.lean:142` `arithmeticStatusMask` | six EFLAGS bit positions | GPR sub-register aliasing (the file never says "flag") |
| `Verification.lean:51`–`:66` `EnvironmentLoader` ×4 | loading stdin/args/requests into a machine state | MS x64 register and stack discipline |
| `Spec.lean:195` `methodTokenMask` | HTTP method token masking | x86-64 instruction byte layout |
| `Spec.lean:93` `fibonacciSpec` | the 90-value Fibonacci trace specification | the ordering of eight spikes |
| `Base.lean:294` `formatHex64` | hex string formatting for Lean source | binary instruction encoding |

One structural note on the `sockListen` remedy, offered as an observation and not a request:
the disclosure landed as a new `### 2.3` *under* `## 2. Syscall Signatures`. That parent
heading's own body remains empty, and the seven citations still name the parent. Whoever owns
that fix may want to retarget them to `#23-...` so the citations reach the subsection that
now does the justifying.

---

## 10. Recommendation on the proposed prose-floor gate

A prose-floor check on cited anchors was proposed: reject a section with fewer than N
non-fence, non-diagram body lines. **Status**: not built, and this review recommends it not be
built in that form. **Do not build it** was the instruction and nothing here is built; the
numbers below come from measuring the tree, not from adding a gate to it.

### 10.1 It would catch five of the six clusters

Own-body prose lines, counting only non-blank lines outside fenced blocks and excluding
ASCII-art and table rows:

| Anchor | Prose lines | Caught at N=4? |
| :--- | --: | :--- |
| `X86_64.md#1-machine-state-model...` | 0 | yes |
| `X86_64.md#2-binary-instruction-encoding` | 1 | yes |
| `WINDOWS.md#1-microsoft-x64-calling-convention` | 1 | yes |
| `SPIKE3_SORT_LINES.md#1-overview...` | 1 | yes |
| `SPIKES.md#3-spike-progression-roadmap` | 3 | yes (missed at N=3) |
| `SPIKE5_GZIP.md#2-monadic-specification...` | 13 | no — correctly passes |

The separation looks clean: 0, 1, 1, 1, 3 for the defective anchors against 13 for the one
good one.

### 10.2 It would false-positive on a third of the corpus, including the best anchors

Applied to all 1,933 path-anchor citations in the tree:

| Floor | Anchors failing | Citations failing |
| --: | --: | --: |
| N=1 | 22 | 215 |
| N=2 | 46 | 507 |
| N=3 | 50 | 536 |
| N=4 | 59 | 662 |
| N=5 | 70 | 739 |

At N=4 the gate flags 59 anchors to catch 5 — about 8% precision. Worse, the flagged set
includes the anchors this review found *most* adequate:

- **`docs/TARGETS/X86_64.md#11-general-purpose-registers-gprs-32-bit-zero-extension`**
  (prose = 1). This is the anchor `setGpr32` cites, identified in §4.1 above as the best
  x86-64 citation in the tree. Its content is a nine-row alias table, which a "non-diagram
  lines" filter discards.
- **`docs/STDLIB_PNG.md#32-color-types-bit-depth-matrix`** (prose = 0, 10 citations). Its body
  is a five-row matrix of PNG colour types, allowed bit depths and channel counts. That matrix
  *is* the specification.
- **`docs/TARGETS/LINUX.md#31-elf64-layout-header-structure`** (prose = 0, 24 citations). Its
  body is an ASCII box — and this is the argument that settles it. Compare the two boxes:

```
X86_64.md §2:  | Legacy Prefixes   | REX Prefix | Opcode  | ModR/M | SIB | ...
               | (0-4 bytes)       | (0-1 byte) | (1-3 B) | (0-1B) |(0-1)| ...

LINUX.md §3.1: |   e_type: ET_EXEC (0x0002)                                      |
               |   e_machine: EM_X86_64 (0x003E)                                 |
               |   e_ident: Magic (\x7fELF), ELFCLASS64, ELFDATA2LSB, EV_CURRENT |
```

Identical *form*. One names slot positions and widths and justifies almost none of its 129
citations; the other carries the actual constant values an emitter must write and justifies its
24. No line-shape or line-count rule distinguishes them, in either direction.

A related limitation: `SPIKES.md#3`'s three prose lines are a note about Spike 8's ordering
relative to Spikes 6 and 7 — text with no bearing on any of the 26 citations that land there.
A floor measures volume; adequacy is about relevance. Those are different properties, and the
gate would be measuring the wrong one.

### 10.3 What is worth building instead

**A bare-container check.** Counting *all* non-blank own-body lines — keeping tables, fences
and ASCII art, and asking only whether the heading has anything under it at all before the next
heading — the tree yields:

| Floor | Anchors failing | Citations failing |
| --: | --: | --: |
| 0 body lines | 10 | 138 |
| < 2 body lines | 14 | 196 |

"A cited heading with literally nothing beneath it" is a bright line no legitimate anchor needs
to cross, the false-positive rate is near zero, and 138 citations is a tractable backlog rather
than a third of the corpus. It catches cluster 2 outright (57 citations, zero body lines) and,
at the two-line threshold, cluster 3 as well (39) — 96 of this review's 289. It also catches
`docs/TARGETS/WASI.md#2-syscall-signatures` (12 citations, zero body lines), which is the
`sockListen` parent discussed in §9.

It catches none of clusters 1, 4 or 5, and that is the honest finding: those anchors have
bodies. Their bodies just do not say what the citing code needs. **No mechanical check reaches
that; only a reader does.** Which is the argument for §11.

A second non-blocking artifact would earn its keep: a ranked report of cited anchors by
citations-per-body-line, published rather than enforced, as a standing worklist for the review
obligation below. `X86_64.md#2` at 129 citations onto 8 body lines would sit at the top of it,
where it belongs.

---

## 11. Recommendation on the review protocol

The gap this review closes existed because no reviewer was ever asked to do this work.
`docs/REVIEW.md` §4.2 currently obliges reviewers to derive theorems from specs and to hunt
domain gaps — both of which presuppose that the cited section *is* the spec. Nothing asks
whether it is.

Proposed addition to `docs/REVIEW.md` §4.2, as a third subsection alongside A and B.
**Status**: proposed text only; this review does not edit `docs/REVIEW.md`, and the wording is
for the owner to rule on.

> #### C. Citation Adequacy Audit
>
> `scripts/check_refs.py` proves that a cited anchor *resolves*. It cannot prove that the cited
> section *justifies* the declaration, and no other gate does either. That half is the
> reviewer's, and it is not discharged by observing that CI is green.
>
> For every declaration under review, the reviewer MUST read the cited section — not its
> heading, its body — and classify the citation as one of:
>
> - `justified` — the section states something the declaration depends on;
> - `understated` — the section is on-topic but states strictly less than the declaration
>   commits to (record what is missing);
> - `misaimed` — the justifying content exists elsewhere in the same document (record the
>   correct anchor);
> - `false` — the section describes something else, or contradicts the declaration;
> - `vacuous` — the cited heading has no body.
>
> Reviewers MUST report `justified` counts alongside the others. A citation audit that finds
> only defects has not calibrated itself against the document, and the same anchor routinely
> carries both good and bad citations.
>
> Three rules make the audit cheap enough to actually perform:
>
> 1. **Read the neighbours.** The correct citation is very often already present within a few
>   declarations in the same file. Where it is, the finding is `misaimed` and the fix is
>   mechanical.
> 2. **Distinguish a bad citation from a missing document.** Where a cluster of citations has
>   nowhere correct to point, the finding is a specification gap and the remedy is Law 5's:
>   author the design document before touching the citations. Report it as such rather than as
>   a citation defect.
> 3. **Layering is part of adequacy.** A declaration in `Gasm/Core/` citing a
>   `docs/TARGETS/` document is a defect independent of whether the section's content fits,
>   because it inverts the dependency the target abstraction exists to maintain.
>
> Reviewers MUST include a **Citation Adequacy Table**:
>
> | Declaration (path:line) | Cited anchor | Class | What the section states vs. what the declaration needs |
> | :--- | :--- | :--- | :--- |
>
> Scope: every declaration whose theorem is under review, plus — for a review touching a
> document — every citation landing on the sections that document changed.

One further protocol note, from the calibration this review needed: the counts in a docs audit
are reliable, but its *characterisations* age. Cluster 6's defect had been repaired before this
review began, and cluster 1's was materially different from its description (the opcode
encodings are correctly cited to Intel; it is the constructor wrappers that drift). A
citation-adequacy finding should be re-verified against the tree at the moment it is acted on.

---

## 12. Summary of structural findings

Three of the six clusters are not citation defects at all:

1. **Spike 2 has no design document.** All 26 citations in cluster 4 come from
   `Spikes/Spike2Fibonacci/**` and there is nowhere correct for them to point.
   **Status**: `docs/SPIKES/SPIKE2_FIBONACCI.md` does not exist.
2. **Spike 3's document covers only the Windows target.** Eleven of cluster 5's 25 citations
   come from its Linux and Wasm targets, which `SPIKE3_SORT_LINES.md` does not mention.
3. **Spike 5's document has no Linux section.** All ten of cluster 6's remaining defects are
   the Linux target citing §2 because §4 offers it no subsection. Its Windows and Wasm
   siblings cite §4.1 and §4.2 correctly.

And one that is a layering defect wearing a citation defect's clothes: five declarations in
`Gasm/Core/` (`CFG.lean`'s `Register`, `Types.lean`'s four width aliases) and four more
(`Verification.lean`'s `EnvironmentLoader` instances) draw their justification from
`docs/TARGETS/` documents. Fixing the citation without fixing the direction of the dependency
would only hide it.
