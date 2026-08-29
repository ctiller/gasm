/-
Copyright 2026 Craig Tiller

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Gasm.Compiler.Word
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.X86_64.MacroAssembler

namespace Gasm.Compiler.Word.MicrosoftX64

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Gasm.Targets.X86_64.Assembler

/- REF: docs/MACRO_ASSEMBLER.md#x86-64-backend -/
def argReg : Arg → Reg64
  | .a0 => .rcx
  | .a1 => .rdx
  | .a2 => .r8
  | .a3 => .r9

/- REF: docs/MACRO_ASSEMBLER.md#x86-64-backend -/
def argsOfState (s : X86_64MachineState) : Args where
  a0 := s.gprs .rcx
  a1 := s.gprs .rdx
  a2 := s.gprs .r8
  a3 := s.gprs .r9

/- REF: docs/MACRO_ASSEMBLER.md#x86-64-backend -/
def lowerAtom (dst : Reg64) : Atom → Segment
  | .arg index => mov dst (argReg index)
  | .const value => loadImm dst value

/- REF: docs/MACRO_ASSEMBLER.md#x86-64-backend -/
def lowerCombine (op : BinOp) : Segment :=
  match op with
  | .add => add .rax .r10
  | .sub => sub .rax .r10
  | .bitAnd => and .rax .r10

/- REF: docs/MACRO_ASSEMBLER.md#x86-64-backend -/
def lowerOp : Op → Program
  | .load value => [lowerAtom .rax value]
  | .combine op rhs => [lowerAtom .r10 rhs, lowerCombine op]

/- REF: docs/MACRO_ASSEMBLER.md#x86-64-backend -/
/-- Compile to proved x86 macro fragments. Clients may edit or combine this list before expansion. -/
def compileMacros (f : Function) : Program :=
  (compileExpr f.body).flatMap lowerOp

/- REF: docs/MACRO_ASSEMBLER.md#x86-64-backend -/
/-- Compile all the way to ordinary assembly instructions. This output has the same type as
    hand-written Gasm assembly, so generated and manual code remain a per-call-site choice. -/
def compileAssembly (f : Function) : List X86_64Instr :=
  assemble (compileMacros f)

/- REF: docs/MACRO_ASSEMBLER.md#x86-64-backend -/
private theorem lowerAtom_correct (dst : Reg64) (atom : Atom) (s : X86_64MachineState) :
    (runLocalSteps (lowerAtom dst atom).code s).gprs dst = atom.eval (argsOfState s) := by
  cases atom with
  | arg index =>
    cases index <;> exact (lowerAtom dst (.arg _)).localSound s trivial
  | const value => exact (lowerAtom dst (.const value)).localSound s trivial

/- REF: docs/MACRO_ASSEMBLER.md#x86-64-backend -/
private theorem lowerAtom_preservesInput (dst : Reg64)
    (hdst : dst ≠ .rcx ∧ dst ≠ .rdx ∧ dst ≠ .r8 ∧ dst ≠ .r9)
    (atom : Atom) (s : X86_64MachineState) :
    argsOfState (runLocalSteps (lowerAtom dst atom).code s) = argsOfState s := by
  have hclob : (lowerAtom dst atom).contract.clobberedGprs = [dst] := by
    cases atom <;> rfl
  apply Args.ext
  · apply (lowerAtom dst atom).preservesGpr
    rw [hclob]; simpa using Ne.symm hdst.1
  · apply (lowerAtom dst atom).preservesGpr
    rw [hclob]; simpa using Ne.symm hdst.2.1
  · apply (lowerAtom dst atom).preservesGpr
    rw [hclob]; simpa using Ne.symm hdst.2.2.1
  · apply (lowerAtom dst atom).preservesGpr
    rw [hclob]; simpa using Ne.symm hdst.2.2.2

/- REF: docs/MACRO_ASSEMBLER.md#x86-64-backend -/
private theorem lowerAtom_preservesRax (atom : Atom) (s : X86_64MachineState) :
    (runLocalSteps (lowerAtom .r10 atom).code s).gprs .rax = s.gprs .rax := by
  apply (lowerAtom .r10 atom).preservesGpr
  have hclob : (lowerAtom .r10 atom).contract.clobberedGprs = [.r10] := by
    cases atom <;> rfl
  rw [hclob]
  simp

/- REF: docs/MACRO_ASSEMBLER.md#frontend-certificates -/
private theorem lowerAtom_preservesGpr (dst r : Reg64) (h : r ≠ dst)
    (atom : Atom) (s : X86_64MachineState) :
    (runLocalSteps (lowerAtom dst atom).code s).gprs r = s.gprs r := by
  apply (lowerAtom dst atom).preservesGpr
  have hclob : (lowerAtom dst atom).contract.clobberedGprs = [dst] := by
    cases atom <;> rfl
  rw [hclob]
  simpa using h

/- REF: docs/MACRO_ASSEMBLER.md#frontend-certificates -/
private theorem lowerAtom_preservesMemory (dst : Reg64) (atom : Atom)
    (s : X86_64MachineState) :
    (runLocalSteps (lowerAtom dst atom).code s).memory = s.memory := by
  apply (lowerAtom dst atom).preservesMemory
  cases atom <;> rfl

/- REF: docs/MACRO_ASSEMBLER.md#x86-64-backend -/
private theorem lowerCombine_correct (op : BinOp) (s : X86_64MachineState) :
    (runLocalSteps (lowerCombine op).code s).gprs .rax =
      op.eval (s.gprs .rax) (s.gprs .r10) := by
  cases op with
  | add => exact (add .rax .r10).localSound s trivial
  | sub => exact (sub .rax .r10).localSound s trivial
  | bitAnd => exact (and .rax .r10).localSound s trivial

/- REF: docs/MACRO_ASSEMBLER.md#frontend-certificates -/
private theorem lowerCombine_preservesGpr (op : BinOp) (r : Reg64) (h : r ≠ .rax)
    (s : X86_64MachineState) :
    (runLocalSteps (lowerCombine op).code s).gprs r = s.gprs r := by
  apply (lowerCombine op).preservesGpr
  cases op <;> change r ∉ [.rax] <;> simpa using h

/- REF: docs/MACRO_ASSEMBLER.md#frontend-certificates -/
private theorem lowerCombine_preservesMemory (op : BinOp) (s : X86_64MachineState) :
    (runLocalSteps (lowerCombine op).code s).memory = s.memory := by
  apply (lowerCombine op).preservesMemory
  cases op <;> rfl

/- REF: docs/MACRO_ASSEMBLER.md#x86-64-backend -/
/-- End-to-end backend correctness against the concrete target instruction semantics. -/
theorem compileAssembly_correct (f : Function) (s : X86_64MachineState) :
    (runLocalSteps (compileAssembly f) s).gprs .rax = f.fn (argsOfState s) := by
  rw [f.implements]
  cases hbody : f.body with
  | atom value =>
    simpa [compileAssembly, compileMacros, compileExpr, lowerOp, assemble, hbody, Expr.eval] using
      lowerAtom_correct .rax value s
  | binary op lhs rhs =>
    simp only [compileAssembly, compileMacros, compileExpr, lowerOp, assemble, hbody,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_append,
      runLocalSteps_append]
    let s1 := runLocalSteps (lowerAtom .rax lhs).code s
    let s2 := runLocalSteps (lowerAtom .r10 rhs).code s1
    rw [lowerCombine_correct]
    rw [lowerAtom_correct .r10 rhs s1, lowerAtom_preservesRax rhs s1,
      lowerAtom_correct .rax lhs s]
    rw [lowerAtom_preservesInput .rax (by decide) lhs s]
    rfl

/- REF: docs/MACRO_ASSEMBLER.md#frontend-certificates -/
theorem compileAssembly_preservesGpr (f : Function) (s : X86_64MachineState) (r : Reg64)
    (hresult : r ≠ .rax) (hscratch : r ≠ .r10) :
    (runLocalSteps (compileAssembly f) s).gprs r = s.gprs r := by
  cases hbody : f.body with
  | atom value =>
    simpa [compileAssembly, compileMacros, compileExpr, lowerOp, assemble, hbody] using
      lowerAtom_preservesGpr .rax r hresult value s
  | binary op lhs rhs =>
    simp only [compileAssembly, compileMacros, compileExpr, lowerOp, assemble, hbody,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_append,
      runLocalSteps_append]
    rw [lowerCombine_preservesGpr op r hresult,
      lowerAtom_preservesGpr .r10 r hscratch,
      lowerAtom_preservesGpr .rax r hresult]

/- REF: docs/MACRO_ASSEMBLER.md#frontend-certificates -/
theorem compileAssembly_preservesMemory (f : Function) (s : X86_64MachineState) :
    (runLocalSteps (compileAssembly f) s).memory = s.memory := by
  cases hbody : f.body with
  | atom value =>
    simpa [compileAssembly, compileMacros, compileExpr, lowerOp, assemble, hbody] using
      lowerAtom_preservesMemory .rax value s
  | binary op lhs rhs =>
    simp only [compileAssembly, compileMacros, compileExpr, lowerOp, assemble, hbody,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_append,
      runLocalSteps_append]
    rw [lowerCombine_preservesMemory, lowerAtom_preservesMemory,
      lowerAtom_preservesMemory]

/- REF: docs/MACRO_ASSEMBLER.md#frontend-certificates -/
theorem compileAssembly_controlFlowFree (f : Function) (i : X86_64Instr)
    (hi : i ∈ compileAssembly f) : ControlFlowFree i := by
  exact assemble_controlFlowFree (compileMacros f) i hi

/- REF: docs/MACRO_ASSEMBLER.md#frontend-certificates -/
/-- Proof-producing frontend output. It certifies lowering, instruction expansion, and the local
    ABI body facts, but deliberately carries no emission capability and is not a `VerifiedProgram`. -/
structure LocalCertificate (source : Function) where
  portable : List Op
  macros : Program
  instructions : List X86_64Instr
  codeBytes : ByteArray
  portable_eq : portable = compileExpr source.body
  macros_eq : macros = compileMacros source
  instructions_eq : instructions = assemble macros
  codeBytes_eq : codeBytes = serializeInstructions instructions
  localResult : ∀ s, (runLocalSteps instructions s).gprs .rax = source.fn (argsOfState s)
  preservesInputs : ∀ s,
    argsOfState (runLocalSteps instructions s) = argsOfState s
  preservesMemory : ∀ s, (runLocalSteps instructions s).memory = s.memory
  clobberedGprs : List Reg64
  clobberedGprs_eq : clobberedGprs = [.rax, .r10]
  preservesGpr : ∀ s r, r ∉ clobberedGprs →
    (runLocalSteps instructions s).gprs r = s.gprs r
  flags : FieldEffect
  flags_eq : flags = .unspecified
  controlFlowFree : ∀ i ∈ instructions, ControlFlowFree i

/- REF: docs/MACRO_ASSEMBLER.md#frontend-certificates -/
/-- Generate all feature-applicable local frontend evidence. Platform execution and final-artifact
    premises remain the responsibility of the target-owned `VerifiedProgram` adapter. -/
def lower (source : Function) : LocalCertificate source where
  portable := compileExpr source.body
  macros := compileMacros source
  instructions := compileAssembly source
  codeBytes := serializeInstructions (compileAssembly source)
  portable_eq := rfl
  macros_eq := rfl
  instructions_eq := rfl
  codeBytes_eq := rfl
  localResult := compileAssembly_correct source
  preservesInputs := by
    intro s
    apply Args.ext <;> apply compileAssembly_preservesGpr <;> decide
  preservesMemory := compileAssembly_preservesMemory source
  clobberedGprs := [.rax, .r10]
  clobberedGprs_eq := rfl
  preservesGpr := by
    intro s r h
    simp only [List.mem_cons, not_or] at h
    exact compileAssembly_preservesGpr source s r h.1 h.2.1
  flags := .unspecified
  flags_eq := rfl
  controlFlowFree := compileAssembly_controlFlowFree source

end Gasm.Compiler.Word.MicrosoftX64
