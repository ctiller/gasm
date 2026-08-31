# Proved Macro Assembler and Small Compiler

## Execution and contracts

A macro `Segment` is a named straight-line fragment of target-native instructions. Its
`localSound` field proves a pre/postcondition for a fold of instruction `step` functions. This fold
does not model instruction lookup, dispatch, fault stopping, termination, or fuel. Consequently a
segment is local instruction-step evidence only: it cannot establish platform execution,
admissibility, or whole-function correctness without a separate target-owned refinement theorem.

`Segment.then` composes two fragments. The composed postcondition existentially exposes the state
between them, which lets a later proof use facts established by the first fragment. `runLocalSteps_append`
is the execution theorem that justifies concatenating their instruction lists.

## Explicit footprints

Every x86-64 segment declares:

- general-purpose registers it may clobber, with a proof that every other GPR is preserved;
- whether flags, memory, and RIP are `preserved` or `unspecified`;
- a semantic precondition and postcondition.

`unspecified` is intentional: it prevents a caller from silently depending on a fact the macro did
not promise. Arithmetic primitives currently promise their result register and memory preservation,
while treating flags as unspecified at the macro API even though the underlying instruction model
computes them.

## Composition

Use `first.then second` for one combined proved segment, or keep a `Program` (`List Segment`) when
you want to inspect, select, or replace individual implementations. `assemble` erases proof wrappers
to the same ordinary instruction-list type used by hand-authored Gasm programs.

## Building blocks

The initial x86-64 library contains proved register-to-register `mov`, 64-bit constant loading,
and register `add`, `sub`, and `and`. These are deliberately small primitives. Larger macros should
be assembled from them and expose domain-specific postconditions.

## Macro programs

`MacroAssembler.Program` is a list of proved fragments. It is an authoring form, not a mandatory
whole-program representation. A caller can expand it immediately, compose it with library macros,
or add a custom `Segment` carrying a local proof.

## Portable source language

`Gasm.Compiler.Word` is target-independent. Its first supported subset has four 64-bit inputs,
constants, and one `add`, `sub`, or bitwise `and`. The restriction is explicit and total. Arbitrary
Lean functions are not reflectable after elaboration, so unsupported constructs are not silently
accepted or assigned guessed semantics.

## Lean functions

`Word.Function` contains:

1. an ordinary Lean function `Args → UInt64`;
2. a reifiable `Expr` in the supported subset;
3. a proof that the function and expression agree for every input.

`Function.ofExpr` supplies the proof automatically when the expression itself is the desired API.
For a separately named Lean function, the user provides what is usually a small `rfl` or simplifier
proof. This proof is the honest boundary between Lean source and compiler input.

## Portable macro IR

`compileExpr` lowers source expressions to portable accumulator operations. `compileExpr_correct`
and `compileFunction_correct` prove that this stage preserves the Lean function's result. No ABI,
register name, instruction encoding, or target state appears in this IR.

## x86-64 backend

The `MicrosoftX64` backend maps four inputs to RCX, RDX, R8, and R9, returns through RAX, and uses
R10 as a scratch register. It is deliberately not named as a generic x86-64 ABI. `compileMacros`
returns proved fragments; `compileAssembly` returns normal Gasm x86 instructions.
`compileAssembly_correct` proves the final RAX value for the local instruction-step fold.

The present backend intentionally does not emit a `ret`; its output is a composable body segment.
The surrounding hand-written or generated routine chooses its terminator and ABI wrapper.

## Frontend certificates

`MicrosoftX64.lower` is the preferred bulk entry point. It returns a `LocalCertificate source`
containing the portable operations, proved macros, native instructions, serialized code bytes, and
equations tying each representation to the next. Its reusable theorem says that the local step fold
puts `source.fn` in RAX. It packages memory preservation and preservation of every GPR outside the
declared RAX/R10 clobber set; flags remain explicitly unspecified.

This supports the precise claim that a compiled body has verified local lowering because the generic
compiler theorem constructed its certificate. It does not yet support the stronger claim that the
body is platform-execution correct merely because the compiler was used. The compiler is a
proof-producing frontend, not a proof authority. `LocalCertificate` has no binary-emission operation
and is not a second `VerifiedProgram`.

The current expression grammar has no control-transfer constructors. Rather than infer this from RIP
arithmetic, the target-owned `ControlFlowFree` predicate explicitly admits the ordinary instruction
constructors available to macros, and `assemble_controlFlowFree` proves structurally that every emitted
instruction has that classification. A call or jump remains a control transfer even when its target
equals fallthrough, while an ordinary instruction fault does not change its classification. Successful
ordinary-step advancement belongs in the later platform bridge, with faults as explicit outcomes.
When control forms are added, selected lowering cases must construct
the core typed-CFG destination-precondition and ghost-world/obligation-transfer certificates; indirect
cases must additionally prove closed target-set resolution. Unselected features impose no obligation.

## Platform handoff

The frontend deliberately defines no artifact-connection record: a client-chosen artifact extractor
would be forgeable. Extraction, placement, artifact identity, and the final connection predicate must
be target-owned and must discharge the corresponding field of the sole platform-parameterized core
`VerifiedProgram`. That core remains the final composition and emission authority.

## Platform execution bridge

`ContextualStraightLinePlacement` connects every locally executed body prefix to production x86
indexed lookup inside a larger instruction stream. Along with an initially fault-free state and
`RuntimeSilentOn` evidence for the selected runtime, `runProgramOutcomeLoop_prefix` proves
that the production explicit-outcome evaluator consumes exactly the body's instruction count and
then resumes a caller-provided continuation from the same fallthrough state as `runLocalSteps`.

Selected-call proofs use the parallel `SelectedAfterEach` law and
`selectedPrefixOfSafeSequential`.  The law is quantified over symbolic instruction-list prefixes;
the opaque bridge constructs the exact `ProductionPrefix.SelectedPrefix` constructor spine once.
Clients therefore retain every lookup, safety, selector, and silence obligation without embedding
another deeply nested proof over closed intermediate machine states.

This theorem deliberately does not turn falling off an isolated body into successful function
termination: the current body has no `RET`. Placement and runtime silence are artifact/platform
facts, while instruction fault preservation and successful sequential advancement are proved once
for the target-owned `ControlFlowFree` constructors. Future selected control forms use typed-edge
certificates instead of this straight-line bridge. Native platform profiles still have empty public
boundary semantics, so publication as a real `PublishedBoundary` remains staged on target-owned
callable export manifests and entry semantics.

## Eventful production segments

`Gasm.Targets.X86_64.ProductionPrefix` is a deliberately narrow, target-owned certificate for a
safe prefix of the existing `runProgramOutcomeLoop`; it is not a second evaluator. Every
constructor carries an exact `instructionAtRipIndexed` fetch. Ordinary steps require the existing
constructor-derived `SequentialInstruction`, explicit runtime silence, and an explicit nonfaulting
step. Direct and conditional branches retain the closed `DirectJumpEncoding` or
`ConditionalJumpEncoding` evidence; the two JCC constructors separately retain whether the
target-owned condition was selected, so a taken and fallthrough path cannot be swapped silently.

Selected host transitions are restricted to the closed x86 CALL and SYSCALL encodings. They require
the exact `ExternalCallInterceptor.interceptCall` result after the pure instruction step and an
explicit nonfaulting hooked state. An interceptor event is accumulated using the production reverse
accumulator. `ProductionPrefix.run`, its composition theorem, and its event-delta theorem therefore
state exact production-runner continuation, total consumed fuel, final machine state, final reverse
accumulator, and chronological event append. `InvariantLoopStep.iterate` exposes the same relation
for a caller-proved loop invariant without creating a graph, artifact, ABI, or authority layer.

A terminal selected host transition uses `SelectedProcessExitStep`. It retains the closed
CALL/SYSCALL classification, exact fetch and selection, a fault-free raw CPU step, the exact
interceptor result, and the resulting typed process-exit state. Consequently an ordinary
instruction which merely reaches an address watched by an interceptor, or an interceptor which
overwrites an existing CPU fault, cannot supply process-exit authority.

This is a prefix/continuation law, not an artifact certificate or a termination claim. It does not
prove that the indexed stream is a final artifact, that a function returns, or that a native outcome
is admissible. Return, halt, fault, and fuel exhaustion remain the unchanged production runner's
explicit continuation outcomes. Unselected instruction forms, unselected host boundaries, and
ordinary paths do not acquire interceptor or loop obligations.

### Decimal extraction and write passes

`Gasm.Targets.X86_64.DecimalSegments` selects the exact DIV/PUSH and POP/store loop bodies used by
native decimal formatters. Each taken or fallthrough theorem constructs a `ProductionPrefix` from
lookups in the caller's final instruction index, the real instruction steps, explicit nonfaulting
facts, runtime silence, and the encoded JNE back-target equation. Stack and output bounds are
separate non-wrapping frame premises even though the current machine memory cell is total.

The placement evidence is intentionally replaceable: relayout regenerates indexed lookup and
branch-target facts without changing the selected pass relation. The module is not an artifact,
execution, export, or `VerifiedProgram` certificate. Portable decimal-schedule correctness and
bounded multi-pass composition remain separate layers.

`Gasm.Targets.X86_64.DecimalMacro` moves the stable decimal invariant one step farther away from
layout. `MachineData` omits RIP, while `ExtractionPoint` and `WritePoint` give every local
instruction and fallthrough boundary a nominal coordinate. `LinkedLayout` is the single final-link
refinement: it assigns injective addresses and proves exact production lookup, serialized bytes,
whole-text coverage/non-wrapping, and every ordinary successor address. The extraction/write
specializations additionally prove the selected rel8 JNE's taken target and false fallthrough.
Relayout replaces only this refinement. Runtime-only selector/interceptor facts remain indexed by
the reachable state; `toSelectedPass` combines those facts with the linked layout and existing
safety laws to construct the accepted `DecimalSchedule` pass rather than a parallel execution API.

This first symbolic-PC slice deliberately selects no RIP-as-data instruction, CALL/return-address
behavior, external call, or syscall. Selecting one later requires its own semantic, ABI/return,
interceptor/event, and obligation-transfer evidence. The relative branch is selected now, so its
two address refinements are mandatory rather than inferred from a coincidental dynamic RIP.

## Microsoft x64 staged platform adapter

`MicrosoftX64StraightLinePlacement` indexes the compiler's `LocalCertificate` by an exact Windows
x86-64 artifact, runtime, initial state, and body base. Its lookup law is stated against the artifact's
production index, while initial safety and runtime silence remain outside the compiler certificate.
`LocalCertificate.runProgramOutcomeLoop_prefix` instantiates the contextual runner theorem;
`fallthroughResult` and the fallthrough frame corollaries reuse the compiler's generic result,
GPR, memory, and input-preservation proofs at the reached state. Final byte connection remains the
separate target-owned `Platform.artifactConnected` premise used by core composition.

This is intentionally an adapter input, not a `ProgramBehaviorCertificate`, `VerifiedExportSet`, or
`VerifiedProgram`. Once native target profiles acquire real callable export manifests and boundary
semantics, the same staged evidence can feed `ContextBoundaryRealization` and `PublishedBoundary`.

## Placement construction

Consumers need not prove contextual indexed lookup separately for every body decomposition.
`IndexedLayoutCertificate` states the final linker's global resolution law once, while
`ContiguousInstructionSubsequence` proves that the body index beginning at its selected base is
included in that final index. `ContextualStraightLinePlacement.ofSubsequence` combines those facts
with the body's constructor-derived ordinary classification and entry RIP.

The construction derives prefix RIP from encoded instruction sizes and proves membership through
the target indexer's append law. A differential relayout therefore regenerates only final layout
resolution and subsequence inclusion; the symbolic/local compiler proof remains reusable. The linker
is expected to derive `IndexedLayoutCertificate` from its injective, aligned address assignment.
`ContiguousInstructionSubsequence.ofDecomposition` supplies the complementary linker-facing
constructor directly from `beforeCode ++ code ++ afterCode` and the encoded prefix span, so consumers
do not prove index membership manually.

`selectedPrefixOfSafeSequentialSubsequence` is the selected-call specialization of the same split.
Local proofs retain a symbolic `bodyBase`; one opaque index-level theorem combines them with a
caller-supplied `IndexedLayoutCertificate` and subsequence inclusion.  This avoids separately
normalizing a large closed instruction index at every sequential program counter.  This theorem
does not establish linked-text bytes or text-wide non-wrapping. Branch and host-transition
constructors remain explicit and must be appended with their exact target/runtime evidence.

`SelectedSequentialStepEvidence` is the consumer-facing bundled form of the same law. It lets a
fixed pass enumerate each reached ordinary step once instead of traversing the code separately for
lookup, selection, silence, and safety. `DecimalMacroSelectedPrefix` is the concrete 7/5 consumer:
it builds the six/four ordinary steps through the opaque bridge, appends the JNE taken/fallthrough
constructor explicitly, and returns the existing `extractionFinal`/`writeFinal` state.

This initial straight-line slice therefore supplies instruction realization, local ABI realization,
and an exact byte boundary, but does not claim whole-function callability merely from its RAX theorem.
A platform composition must still establish the core entry/exit, stack, obligation-world, placement,
and final-artifact contracts before emission.

## Choosing the authoring level

The same function may be consumed at any of four levels:

```lean
open Gasm.Compiler.Word

def addFirstTwo : Function where
  fn := fun a => a.a0 + a.a1
  body := .binary .add (.arg .a0) (.arg .a1)
  implements := by intro; rfl

def portable := compileExpr addFirstTwo.body
def macros := MicrosoftX64.compileMacros addFirstTwo
def instructions := MicrosoftX64.compileAssembly addFirstTwo
def compiled := MicrosoftX64.lower addFirstTwo

example (s) :
    (MacroAssembler.runLocalSteps compiled.instructions s).gprs .rax =
      addFirstTwo.fn (MicrosoftX64.argsOfState s) :=
  compiled.localResult s
```

Hand-written instructions remain available throughout, and generated assembly has the ordinary target
instruction type. Editing a generated macro or instruction list invalidates its original certificate.
Supported modification means composing proved segments and then generating a fresh certificate for
the resulting sequence.

## Target variations

The portable `Expr` and `Op` layers deliberately contain no x86 concepts. The Microsoft x64 backend
is the first proved reference backend. An AArch64 backend should independently define native
segments and footprints (including NZCV rather than x86 RFLAGS), map arguments to X0-X3, return in
X0, and prove its lowering against `AArch64Instruction.step`. This keeps the portable compiler shared
without weakening target-specific contracts into a misleading lowest common denominator.

## Typed control-flow compiler frontend

`Gasm.Compiler.TypedCFG` is the first bulk control-flow frontend. A `SourceScope` declares a finite
`Fin n` block index, one dependent `BlockEntry` contract per index, and injective nominal block IDs
before any body is supplied. `SourceRef` retains that exact scope and index; it has no text label,
raw offset, address, or post-hoc entry choice.

A total `ProgramPlan` supplies exactly one `BlockPlan` for every declaration. A body plan is already-
lowered logical body data ending in typed JMP, JCC, RET, process-exit, or halt. JMP and JCC retain the
existing core edge contracts and exact target-entry equalities; JCC keeps its true and false refs in
their original orientation. This initial interface is deliberately named a plan rather than an
execution/compiler certificate: it contains no theorem connecting an instruction payload to target
operational semantics. Handwritten macro lowering and later word-compiler lowering can both produce
this same logical interface once they carry the appropriate local proofs.

`ProgramPlan.lowerDefinitions` is a total structural function into the existing
`RecursiveCFGBuilder.Definitions`, and `ProgramPlan.lower` delegates sealing to `sealDefinitions`.
The correspondence theorems preserve source index, nominal BlockId, dependent entry contract,
terminator constructor, target indices, and JCC polarity. Each sealed exact-definition ref is the
same-index lowered source block, providing the blockwise handoff for later differential proofs.
Injective BlockId remapping commutes with generated blocks. No alternate CFG, CALL/indirect or
exception semantics, instruction layout, byte identity, native execution, artifact, ABI, or
`VerifiedProgram` authority is introduced.

## Next control-flow slice

## Operational CFG realization

`EmittedBasicBlock` binds a `BasicBlock` to an exact contiguous instruction slice in one final
artifact index. Its ordinary prefix is refined through the shared macro runner, while the emitted
terminator is looked up and executed by the production evaluator. `RealizesAt` connects that exact
host-aware transition to the dependent body result and excludes divide/memory faults.

`OperationalCFGRealization` owns the artifact-global layout law and a realization for every graph
block once. Logical `Step.fromBody` remains useful for local contract composition, but cannot by
itself establish production reachability; final behavior proofs consume the operational realization.

For the initial pure-block slice, `ConservativeGhostFrame` preserves typestate, stack depth,
permissions, obligations, causal time, and event history exactly. Authority-changing blocks must
instead receive an ABI/obligation-owned transition certificate in a later extension.
`TerminatorRealization` is closed over actual x86 instruction families: direct and conditional
branches bind destinations and flag predicates, RET binds its zero-pop logical form and concrete RSP
effect, Linux syscall exit binds the ABI exit-code register, and HLT is distinct from syscall exit.
Pure JMP/Jcc/RET/HLT transitions additionally require runtime silence, so an interceptor cannot
smuggle effects through a conservative ghost frame. Every constructor carries the exact host-aware
production transition and event result; divide/memory faults cannot realize typed control flow.
Windows `ExitProcess` is intentionally not a constructor yet: its production hook returns normally
after a linked IAT call, so it needs a profile-owned provider/IAT and returned-outcome realization.

The first symbolic-control-flow slice is implemented by `Gasm.Core.CFGBuilder`. `BlockRef` retains
the exact supplied `BasicBlock` definition, whose complete dependent entry contract contains the
nominal `BlockId`; text labels and machine addresses never participate. Interning is exact block
membership, not merely equality of entries, so a resident block with the same ID and entry but a
different body cannot discharge the reference. `DirectTerminator.jmpToBlock` accepts the target
`BasicBlock` value and retains the ordinary core `BlockEdge`, including destination precondition and
ghost-world transfer. Cloning/inlining requires constructing a block with a distinct ID.

`Builder.intern` is deliberately finite and acyclic: a new block's direct targets must already occur
in the block table, while RET, process exit, and halt impose no target-closure proof. Every public
`Builder` also carries an inductive `BuildHistory`, so direct record construction cannot bypass that
ordering with a self- or mutually-recursive table. `Builder.finalize`
derives the existing `TypedControlFlowGraph` fields (`entryInGraph`, `uniqueIds`, and
`targetsInGraph`); it creates neither a parallel graph nor an execution/emission authority.
`Builder.mapId` transports the symbolic proof through an injective identity embedding, and
`Builder.sum` / `Builder.finAppend` compose independent scopes with proved collision-free `Sum` and
`Fin` injections. Byte layout remains entirely deferred to the linker and operational realization.

### Instruction-relative authoring

`Gasm.Targets.X86_64.MacroAssembler.ControlPoints` supports requests such as “back K instructions”
without making the numeric offset proof authority. Its single generic `OrderedPoint` / `Scope`
kernel is parameterized by item type, nominal point ID, and a concrete target payload. Every point
stores `code = before ++ after`, a nonempty suffix proving the point precedes the current boundary,
and its derived distance; the scope makes point IDs and distances unique. `markThenAppend` marks the
current boundary with a payload and appends a nonempty item suffix. Generic mapping and `Sum`
composition remap nominal point IDs collision-free and transport payloads without introducing an
abstract binding relation.

`resolveBack` is fallible. Zero is rejected as the current boundary, and an instruction distance
without a typed mark is rejected instead of being treated as permission to enter a block interior.
A successful result carries exact scope membership and the stored target payload. The Nat query is
not passed to an edge constructor and is discarded after resolution.

The acyclic binding instantiates the payload with an exact `BlockRef` plus intrinsic membership in
the selected `CFGBuilder.Builder` table. Its thin JMP/JCC functions desugar only to the existing
`DirectTerminator` and require the existing typed edges and exact target-entry equalities. A fresh
current block ID is distinct from every resolved target, so this binding cannot create a self loop.
The recursive binding instead uses exactly a same-scope `RecursiveCFGBuilder.DeclRef`; it desugars
to the existing `RecursiveTerminator`, permitting forward, self, and mutual edges because the later
finite seal proves table closure. JCC retains both oriented static targets while runtime selection
activates only the applicable edge contract. Recursive component composition maps point, block, and
declaration identities through collision-free `Sum`; foreign-scope refs remain uninhabitable.

Once relative syntax is resolved, later insertion or composition preserves the symbolic point and
target rather than reinterpreting its old number. Differential relayout need regenerate only
layout/relocation evidence. This logical binding does not prove an emitted address, establish that
an arbitrary instruction boundary is a native block entry, or add linker, execution, artifact, or
`VerifiedProgram` authority; those remain target/linker placement obligations.

### Finite recursive CFG authoring

`Gasm.Core.RecursiveCFGBuilder` adds the declaration-first path needed by compilers for forward
edges, self loops, and mutually recursive JMP/JCC graphs. A finite `Scope` enumerates each index
exactly once, assigns its exact dependent `BlockEntry`, and requires nominal block IDs to be
injective. `Scope.fin` supplies the ordinary generated `Fin n` form. A pre-seal `DeclRef` contains
only an index in one exact scope; it is deliberately not a `BlockRef`, because no body definition
exists yet and entry equality must not masquerade as exact-definition identity.

`Definitions` is a total dependent function over every declaration index. Exactly-one definition is
therefore structural, not a caller-maintained list invariant. Its `RecursiveTerminator` accepts only
same-scope declaration refs and retains the existing `BlockEdge` or `ConditionalBlockEdge`; JCC
publishes both static successors while the core edge activates only the runtime-selected entry
premise. Dangling or foreign-scope references cannot inhabit the expected type.

`Definitions.toGraph` simultaneously generates the finite `BasicBlock` table and proves entry
membership, unique IDs, and closure of every selected target, returning only the existing
`TypedControlFlowGraph`. `sealDefinitions` additionally returns exact post-seal `BlockRef`s to the
generated definitions. Neither result claims execution, layout, artifact identity, or program
authority.

Injective BlockId remapping reuses every body and has an exact generated-block correspondence
theorem. `Scope.sum` and `Definitions.sum` compose closed independent components through collision-
free `Sum` identities, with exact left/right definition correspondence. Such composition preserves
each side's old targets; cross-component mutual recursion must instead be authored from the start
against the combined declaration scope. The generic instruction-relative kernel binds same-scope
declaration refs without weakening this rule.

CALL/indirect forms remain unselected and therefore add no obligations in this slice. When added,
CALL must carry return-continuation, ABI, obligation-transfer, and
exceptional/cancellation contracts, while indirect edges must carry closed target-set resolution.
The existing “back five instructions” form resolves immediately to a typed control-point identity;
adapting such a point to a recursive declaration remains separate, and a raw `Nat` never authorizes
entry into a block interior. The linker later proves that each encoded displacement resolves to the
symbolic target.

### Typed direct-jump linking

`Gasm.Targets.X86_64.CFGLinker` connects the first selected symbolic JMP form to a concrete linked
text image. `ClosedCFGLayout` is indexed by the existing closed typed CFG and retains exact block
definitions. It requires aligned, unique starts, non-overlapping half-open encoded ranges, global
indexed lookup, and inclusion of every emitted instruction boundary; address injectivity alone is
not a layout certificate. The complete text and every emitted block range must fit inside the same
non-wrapping `[base, base + encoded span)` interval. A boundary-to-byte extraction law connects each
modular instruction address to its exact serialized bytes, so below-base truncating subtraction or
wrapped aliases cannot justify relocation.

`checkedRel32ForSize` is explicitly fallible and measures displacement from the exact
`source + instructionSize` next RIP. It rejects zero or violated target-block alignment,
next-instruction address wrap, and every mathematical displacement outside the signed 32-bit interval
before conversion. `checkedRel32` preserves the direct-JMP API as the five-byte specialization. These
are link-time errors, not runtime faults or outcomes. A selected direct symbolic JMP alone adds
`DirectJumpRelocation`: exact target-definition membership, the checked displacement,
exact five emitted bytes, production decoding and source/target lookup, and the concrete destination.
`DirectJumpRelocation.connect` carries the existing typed edge's destination contract and ghost-world
transfer into a layout-indexed connection which retains the source-terminator placement,
target-definition start, and exact `bytes = text.bytesAt sourceAddress 5` identities. It proves
neither whole-program termination nor platform
admissibility, and creates no artifact or emission authority. Straight-line and other unselected
forms acquire no relocation premise. After differential relayout, the CFG and edge proofs remain
valid; only layout and relocation evidence is regenerated.

### Typed conditional branching

`DirectTerminator.jccToBlocks` accepts the true and false `BasicBlock` values themselves. The
frontend retains both exact definitions, both existing core `ConditionalBlockEdge`s, and exact
entry identities. Both definitions must already be interned, so `BuildHistory` remains finite and
acyclic; injective remapping and collision-free composition transport both memberships. Static CFG
closure publishes both possible successors, while `ConditionalBlockEdge.activate` and the core
selected-edge relation require the entry contract only for the runtime-selected path. Blocks using
JMP, RET, exit, or halt acquire no conditional-branch premise.

This frontend step does not yet choose a concrete JCC encoding. The narrow x86 linker form uses one
near-JCC rel32 target and one proved fallthrough target; arbitrary placement requires a later proved
JCC-plus-JMP terminator sequence rather than pretending a single JCC has two displacements.

### Typed conditional-branch linking

`ConditionalJumpRelocation` realizes that narrow x86 shape against the same non-wrapping
`ClosedCFGLayout`: the true block is the one checked rel32 destination and the false block must begin
at exactly `sourceAddress + 6`. `checkedNearJccRel32` is the six-byte specialization of the
size-aware checker, so a successful relocation both computes the taken displacement from that next
RIP and proves that the source-plus-six fallthrough address does not wrap. `nearJccInstruction` is
partial over the existing sealed
`ConditionalJumpEncoding` kinds; conditions for which only a short encoding is currently admitted
are rejected rather than silently narrowed. The connection retains the exact source terminator,
both target definitions and starts, the condition-kind agreement, exact linked bytes, production
decode and all three lookups, and state-parametric taken/fallthrough destination laws.

`ConditionalJumpRelocation.toTerminatorRealization` contributes only those static facts to the
existing one-step `TerminatorRealization.conditional`. Runtime silence, the actual host-aware
transition and event result, nonfaulting state, and the dynamic condition relation remain explicit
operational/profile premises. This proves neither a whole branch execution nor termination. Blocks
without a selected JCC acquire no conditional relocation obligation.

## AArch64 macro segments

`Gasm.Targets.AArch64.MacroAssembler` is a target-owned, closed straight-line kernel for a small
64-bit AArch64 subset. Its operand type is `Fin 31`, so selected MOV/register and logical forms can
name only X0--X30. Encoding value 31 is not admitted: those encodings mean XZR for this instruction
class while the broader machine register type can also denote SP. MOV-wide lanes are `Fin 4`, not
masked caller integers. The selected constructors are MOV register, MOVZ/MOVK, and ADD/SUB/AND
shifted-register forms fixed to `LSL #0`, with flags and logical inversion disabled.

`runLocalSteps` folds only the constructor-local semantic steps. Its laws prove PC advancement by
four per instruction, preservation of fault and termination fields, memory, SP, and NZCV, and every
GPR outside the structurally declared clobber list. `Segment.then` is list composition; its code,
clobbers, instructions, bytes, and frame laws are consequently derived compositionally. Emitted
instructions are the structural map of the closed constructors and serialized bytes are computed
directly from exactly that list. Constant materialization is deliberately the total four-word form:
MOVZ lane 0 followed by MOVK lanes 1, 2, and 3.

These are local instruction-step facts only. They do not perform production lookup, fault stopping,
fuel accounting, host interception, or termination; they establish no ABI, callable export,
admissibility, artifact connection, `VerifiedExportSet`, or `VerifiedProgram` authority. A later
target/linker bridge must connect selected instructions and exact bytes to those authorities.

## AArch64 AAPCS64 backend

`Gasm.Compiler.Word.AArch64AAPCS64` lowers the portable four-argument Word source language through
its portable `Op` plan into proved AArch64 macro segments, exact selected instructions, and exact
serialized bytes. It selects the AAPCS64 integer registers X0--X3 for the source language's four
inputs, X0 for the result, and caller-saved X9 as its one scratch register. AAPCS64 provides more
integer argument registers; they are intentionally outside this source subset. In a binary body the
right atom is captured in X9 before X0 is overwritten, preserving the original X0 argument for
either operand.

The backend certificate is local body evidence only. It has no RET or stack frame and makes no
callable-export, OS, lookup/fuel, platform-execution, artifact-connection, `VerifiedExportSet`, or
`VerifiedProgram` claim. X0 is both the first input and result, so input preservation applies to
the unmodified X1--X3 inputs; X0 and X9 form the conservative declared clobber set.

## Lean Word reification

`Gasm.Compiler.Word.LeanReify` provides `#word_reify original as generated`, a deliberately narrow
entry point from ordinary Lean declarations into the portable Word frontend. The original must be a
reducible declaration with exactly four explicit `UInt64` arguments and a `UInt64` result. Its
kernel-visible body may be one argument, one `UInt64` literal, or exactly one addition, subtraction,
or bitwise AND whose operands are arguments or literals. Operand order is preserved. Nested
operations, local `let` bindings, conditionals, comparisons, shifts, multiplication, division,
wrappers, and all other applications are rejected rather than normalized into a larger language.

The generated `Word.Function.fn` calls the original declaration on `Args.a0` through `Args.a3`; it
is not merely `Function.ofExpr`. Its `body` is the structurally reified `Word.Expr`, and its
`implements` field is a normal proof term which must elaborate and pass the Lean kernel. The command
is therefore syntax and proof-term production, not a proof authority or evaluator. It creates no
backend certificate, platform execution claim, artifact connection, export, or `VerifiedProgram`.
The unchanged Microsoft x64 and AArch64 AAPCS64 lowerers consume the generated `Word.Function` and
derive their existing local certificates in the ordinary way.

This exact grammar boundary is intentional. The command remains the stable frontend for the tiny
straight-line IR. Structured `let`, comparison, and conditional forms use the separate reifier
below; the tiny command is not silently broadened or reinterpreted.

## Structured Word source language

`Gasm.Compiler.Word.Structured` is the typed semantic source layer for growing beyond straight-line
leaf expressions. Its sorts are `word` (`UInt64`) and `bool`; typed de Bruijn membership makes local
variables intrinsically scoped. Expressions include literals, variables, wrapping word
addition/subtraction, bitwise AND, word equality, unsigned less-than, Boolean negation, typed
`letE`, and typed `ite`. A total structural evaluator interprets every well-typed expression in a
typed environment. The initial environment is fixed to the same four Word arguments used by the
existing leaf compiler.

The primitive comparison basis is intentionally small: equality, unsigned less-than, and Boolean
negation. Inequality, unsigned less-than-or-equal, greater-than, and greater-than-or-equal are
ordinary derived expressions with evaluator equations. Signed comparison requires a future signed
representation or type. Eager or short-circuit Boolean conjunction/disjunction, recursion, effects,
memory, pointers, and exceptions are not selected.

`Structured.Function result` connects an ordinary Lean function over `Word.Args` to a typed body by
a kernel-checked equality for every input. `WordFunction` selects Word results for eventual machine
lowering. `BoolFunction` is semantic source data useful for conditions but is not callable or
exportable through the current backends.

This layer does not replace or reinterpret the existing `Word.Expr`: that smaller IR remains the
current proved straight-line leaf/backend language. Structured leaves may later be related to
certified `Word.Function` payloads, while branches lower through the nominal typed-CFG frontend only
when target-owned leaf and condition realizations are supplied. This module itself provides no
flags, register, instruction, CFG, execution, ABI, artifact, export, or `VerifiedProgram` claim.

## Structured Lean Word reification

`Gasm.Compiler.Word.StructuredLeanReify` provides
`#structured_word_reify original as generated`. It accepts exactly four explicit `UInt64`
arguments and a `UInt64` result. The stored kernel body is inspected without general reduction or
helper unfolding. Supported terms are argument and local variables, exact `UInt64` literals, the
selected wrapping addition/subtraction and bitwise-AND instances, exact UInt64 Boolean equality,
`decide` applied to exact UInt64 unsigned less-than, `Bool.not`, structural `let`, and typed Boolean
`if`. Unsupported terms are rejected with their first unmatched term and inferred type. The
generated call embeds the already-resolved constant identity hygienically; it is not looked up again
relative to the namespace containing the generated declaration.

Local bindings are preserved as `Expr.letE`; the frontend extends the intrinsic context and emits
the corresponding typed de Bruijn reference. It neither substitutes nor duplicates a let RHS.
Operator instances, operand order, comparison orientation, and true/false branch polarity are
matched structurally. A helper call or overloaded lookalike is not accepted because it happens to
compute the same value. The generated `Structured.WordFunction.fn` invokes the exact original
declaration, while `body` contains the reified structured expression and `implements` is a normal
kernel-checked proof. Existing declaration collisions fail during ordinary command elaboration;
the command never replaces a prior generated definition.

Reification establishes only source-expression correspondence. It creates no CFG plan, assignment,
leaf or condition realization, target certificate, execution theorem, artifact, export, or
`VerifiedProgram`. The reified expression and its `implements` theorem can remain fixed while later
CFG assignments or hand-optimized target blocks are replaced, provided the replacement re-proves
the properties selected by its consumers.

## Structured Word CFG plans

`Gasm.Compiler.Word.StructuredCFG` lowers the first selected finite conditional shape through the
existing acyclic `CFGBuilder`. A stable symbolic `Plan` is indexed by its exact structured source
expression. Its nominal `NodeId` roles, postorder list, root, child roles, and true/false polarity do
not contain blocks, instructions, strings, or addresses. The leaf constructor requires a structural
`NoIte` witness. The branch constructor accounts definitionally for exactly one source `ite` and
requires a branch-free condition plus recursively complete true and false plans. A branch hidden
inside `letE` is therefore rejected: supporting it requires a later proved continuation-duplication
transformation, not silent treatment as a leaf.

Exact implementations are selected separately by a dependent `Assignment` aligned with precisely
the plan's finite postorder roles. It retains one exact `DirectBlock` per selected role and proves
nominal block-ID uniqueness only across those blocks; roles outside the plan impose no block, ID, or
proof obligation. `RealizesLeaf` supplies caller-owned
evidence, an input/output logical relation to its exact source leaf, and an exhaustive target-free
law admitting only RET, exit, or halt in the current direct frontend. `RealizesCondition` supplies
the exact actual JCC, both existing `ConditionalBlockEdge`s and child definitions in true/false
order, plus a target-owned theorem relating the actual `ConditionCode.holds` predicate to portable
Bool evaluation. The generic adapter never derives flags, edges, entry/world transfer, or payload
correctness from portable syntax.

Lowering recursively builds false and true children, appends their collision-free tables, interns
the exact JCC parent last, and calls only `Builder.finalize`. Symbolic source/root, unique-role,
postorder, topology, and polarity facts depend only on `Plan`; exact block membership,
`BuildHistory`, closure, and final graph definitions depend on the chosen finite assignment and
pointwise realizations. Consequently a later generated or hand-optimized block can replace one
assignment while the stable source topology remains reusable, provided the replacement proves every
logical, edge/world, frame, clobber, and footprint property selected by its consumers.

This first plan duplicates continuations into finite leaves and may grow code size. It claims no
optimization, whole-expression execution, instruction/flag semantics, ABI, layout, artifact,
export, or `VerifiedProgram` authority. Loops, recursion, CALL, indirect and exceptional edges,
memory, and pointer representations remain unselected.

## Automatic structured decision plans

`Gasm.Compiler.Word.StructuredPlanCompiler` removes the manual topology step for the first explicit
decision-tree grammar. Recognition accepts a branch-free leaf, or an `ite` whose condition is
branch-free and whose two arms are recursively accepted trees. Its dependent result remains indexed
by the exact original `Structured.Expr`; it cannot attach a convenient but unrelated topology to a
source declaration. An `ite` hidden under a `letE` or inside a condition is rejected. The frontend
does not normalize, duplicate, or eagerly evaluate that source construct.

Plan roles are generated nominally rather than from strings or numeric offsets. Each branch maps
the false and true child roles through distinct injections into a `Sum`-tagged scope and reserves
`none` as its fresh parent identity. The generic injective role-remapping theorem preserves the
source, topology, and branch polarity. Existing `Plan.uniqueRoles` and `Plan.root_mem` then provide
collision freedom and root selection for every generated tree.

The output is only the existing stable symbolic `StructuredCFG.Plan`. It assigns no block and
proves no leaf implementation, condition flags, edge/world transfer, CFG execution, layout,
artifact, or `VerifiedProgram` property. Generated and hand-optimized blocks remain independently
replaceable through `Assignment` and `Realizes`; changing an implementation does not require
reconstructing the generated source topology.

## Structured straight-line plans

`Gasm.Compiler.Word.StructuredStraightLine` is the first bulk leaf compiler for the structured
source. It accepts exactly Word variables and constants, wrapping add/subtract/bitwise-and, and
Word-valued structural lets. Boolean bindings, comparisons, conditionals, effects, and recursion
are rejected rather than normalized into a misleading straight-line leaf.

The generated portable code is intrinsically temporary-safe. Operands are one of the four inputs,
an exact constant, or a structurally scoped temporary already introduced by an earlier `emit`; a forward or
dangling temporary reference cannot be constructed. Each operand, instruction, and result is
indexed by its exact `Args -> UInt64` denotation. The total local interpreter executes the explicit
temporary plan, and `compile_correct` proves for every input that its result equals the original
`Structured.Expr.eval`. Structural lets share their generated result instead of duplicating the
right-hand-side computation. `compileFunction_correct` then composes that theorem with the existing
reifier's `WordFunction.implements` proof, tying the plan to the exact named Lean declaration.

These semantic indices are portable logical identities, not registers or SPIR-V physical IDs. The
plan chooses no ISA, register allocation, spills, flags, ABI, CFG block, layout, artifact, or
`VerifiedProgram` evidence. Later x86-64, AArch64, and SPIR-V selectors may realize the same plan;
handwritten optimized leaves may instead prove the same source/result and selected frame contracts.
Target realization and differential replacement remain separate proof-producing layers.

## Structured AArch64 bounded backend

`Gasm.Compiler.Word.StructuredStraightLineAArch64` is the first target realization of those
portable straight-line plans. It selects AAPCS64 X0--X3 as the four source inputs, X0 as the
result, X9--X15 as seven stable creation-order temporaries, and X16/X17 as operand scratch
registers. `Fits` is an explicit structural resource premise: a program needing more than seven
simultaneously assigned temporaries is rejected. Register reuse, spilling, scheduling, and
instruction selection optimization remain later, independently proved passes.

The backend lowers through the target-owned AArch64 macro segments. Its `LocalCertificate` retains
the exact structured `WordFunction`, selection witness, portable code, macro instructions,
production instructions, serialized bytes, result theorem, PC advance, declared clobbers, and
frame preservation. It is deliberately local evidence. It does not provide lookup, host-runtime
silence, a process outcome, platform admission, artifact identity, or `VerifiedProgram` authority.
That factorization is the optimization seam: an optimized or handwritten body can replace the
generated body by proving the same selected logical and frame properties, while placement and bytes
are regenerated for the replacement.

## AArch64 platform execution bridge

`Gasm.Targets.AArch64.MacroAssembler.PlatformBridge` connects admitted macro instructions to the
production AArch64 outcome runner. The macro step uses the exact production existential instruction
wrapper, which seals host input queues, but still performs no lookup, interception, stopping, fuel,
or outcome classification by itself.

`ContextualStraightLinePlacement` supplies exact final-index lookup at every reached instruction
position. `RuntimeSilentOn` separately supplies the selected platform/profile fact that no interior
successor is reinterpreted as a host call. Given those facts plus safe/running entry state,
`runAArch64OutcomeLoop_prefix` proves that the real runner consumes exactly the body instruction
count, emits no events, reaches the local-fold state, and resumes the caller's unchanged
continuation fuel and event accumulator. The theorem does not claim the continuation terminates or
is admissible. Relayout invalidates placement and runtime-silence evidence, while the source and
local compiler proofs remain reusable.

## Verified compiler-bulk spike

`Spikes.CompilerBulk.AArch64Linux` is the completion gate for this slice. It starts with the named
Lean function `bulkExit`, structurally reifies its nested lets, compiles the selected word fragment
to nineteen AArch64 instructions, and proves that the generated body returns 42 in X0. A handwritten
two-instruction tail selects Linux `exit` in X8 and executes `svc #0`.

The spike proves exact placement and runtime silence for the generated prefix, uses the contextual
prefix theorem at the platform's 50,000-step proof budget, classifies the real exit event, connects
the exact serialized instructions to an ELF artifact, and builds the existing artifact, provider,
entry, admissibility, and behavior certificates. `verifiedProgram` is composed through the sole
platform `VerifiedProgram.compose` authority. `Emit` emits only through `emitVerifiedProgram`, and
`Test` checks production semantics then runs the emitted ELF with QEMU when available. Thus the
claim “this function is verified because this compiler was used” is demonstrated end-to-end for
this selected bounded fragment, not generalized to unsupported Lean.

## Differential certificate transport

Optimization and hand adjustment should support property-relative transport: a proved baseline `X`,
a certified delta relating it to `Y`, and a theorem that the delta preserves selected dimensions of a
certificate together derive those dimensions for `Y`. A delta records changed and unchanged blocks,
entry/exit and observable refinement, clobber/frame changes, ghost obligations, control and exceptional
edges, symbolic-block correspondence, and final relocation/byte correspondence. Consumers explicitly
select the dimensions they transport; functional equivalence alone says nothing about timing, memory
ordering, ABI preservation, cancellation, or target closure.

The baseline-to-transformed block mapping must preserve nominal identity and state whether each block
is shared or cloned. Symbolic CFG proofs can then survive layout changes while displacement and exact
byte proofs are regenerated. Differential transport derives ordinary certificates only; it is neither
an emission path nor an authority parallel to `VerifiedExportSet` and `VerifiedProgram`.

## Proof-directed local blocks

`Gasm.Targets.X86_64.LocalBlockDischarge` packages reusable local contracts over the canonical exact
`SelectedPrefix.Cutpoint` evidence. A contract explicitly names its entry predicate and its exit relation
over the initial and final machine states, reverse event accumulators, ghost state, chronological
event delta, and a caller-selected logical result. That result and the ghost transition classify a
proof phase only; they do not claim a native success, failure, cancellation, or terminal outcome.
Such a claim additionally requires the applicable production outcome/terminator evidence. Contracts
are explicit and are not inferred through typeclass search.

A `LocalBlockRun` is indexed by the selection policy and exact artifact instruction index. Its
operational field is the shared `SelectedPrefix.Cutpoint`, retaining the real selected prefix and therefore every instruction lookup,
classification, interceptor transition, safety premise, fuel count, final state, and event delta.
The reverse-accumulator law retains the event observation even when that emitted delta is empty; no
pilot may erase an explicit empty-event observation merely because it carries no payload.
Its continuation theorem rewrites the production runner to the unchanged caller continuation; it
does not claim termination or admissibility. Changing the placed instruction index cannot reuse the
certificate, so differential code replacement must regenerate placement/execution evidence.
Symbolic body identity remains in the typed CFG; this operational wrapper does not introduce a
forgeable phantom body tag.

`LocalBlockDischarge` proves the same fixed contract for every admitted entry. Contract refinement
can strengthen entry requirements or project/weaken exit properties without changing the selected
artifact index. `LocalBlockRun.then` applies a second discharge to the first run's exact final
machine/event/ghost state. `SequentialLocalBlockRuns` retains both witnesses and composes their
selected prefixes and fuel, preventing an existentially reselected middle state from satisfying an
unrelated continuation contract.

This is the implementation-hole layer for bidirectional proof construction: forward analysis
derives the strongest useful abstract and ghost facts, backward analysis derives the weakest target
requirements, and their explicit meet at named block/join/loop contracts admits a generated or
handwritten local body. Iteration may tighten either side without changing abstract instruction
positions; linker placement remains later. CFG closure, link placement, artifact identity,
exports, and the sole `VerifiedProgram` authority remain separate.
