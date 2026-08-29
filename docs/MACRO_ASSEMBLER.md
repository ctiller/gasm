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
