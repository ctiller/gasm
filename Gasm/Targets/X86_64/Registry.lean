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

import Lean
import Gasm.Targets.X86_64.Instructions
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.RoundtripGate
import Gasm.Targets.X86_64.MemoryFrame

-- LOUD INVARIANT (see also the import-closure comment atop Instructions.lean): the `run_cmd`
-- audit below can only see `X86_64Instruction` instances reachable through THIS file's import
-- graph — it is not a filesystem scan of Instructions/*.lean. Importing the umbrella
-- `Gasm.Targets.X86_64.Instructions` (which itself imports every Instructions/*.lean submodule)
-- makes that graph match "every instruction file that exists", PROVIDED every new
-- Instructions/<Foo>.lean is added to that umbrella's import list. A new instruction file that is
-- never imported anywhere in this closure is invisible to the audit — it will not be flagged as
-- missing, because the audit never learns it exists. This is a residual, undetected gap: closing
-- it fully would need the audit to independently enumerate Instructions/*.lean from disk and
-- cross-check against the import graph, which this file does not yet do.
namespace Gasm.Targets.X86_64.Registry

open Lean Meta
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.RoundtripGate

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Every `roundtripCases` witness across every instruction family, lifted into the open
    existential wrapper — the concatenation of every `RoundtripGate/*.lean` shard's own family
    list. This is the single source of truth `RoundtripTests.lean` and `SemanticsFuzzer.lean`
    derive their instruction suites from, instead of maintaining separate hand-written lists that
    can (and, before this change, did) silently drift from what the decoder actually supports. -/
def allEncodableInstructions : List AnyX86_64Instruction :=
  addFamilyCases ++ subFamilyCases ++ movFamilyCases ++ leaFamilyCases ++ cmpFamilyCases ++
  jccFamilyCases ++ pushFamilyCases ++ popFamilyCases ++ divFamilyCases ++ imulFamilyCases ++
  andFamilyCases ++ orFamilyCases ++ xorFamilyCases ++ notFamilyCases ++ negFamilyCases ++
  shiftFamilyCases ++ testFamilyCases ++ xchgFamilyCases ++ cmovFamilyCases ++ callFamilyCases ++
  retFamilyCases ++ inFamilyCases ++ outFamilyCases ++ hltFamilyCases ++ syscallFamilyCases

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Hand-maintained manifest of every concrete type this file's `run_cmd` audit below expects to
    find an `X86_64Instruction` instance for. Every `RoundtripGate/*.lean` shard's family list
    above must be built from exactly these types' `roundtripCases` (and vice versa) — this is
    checked against the live environment, not merely asserted, so drift is a build failure rather
    than a review finding. -/
def expectedInstructionTypes : List Name := [
  -- Base.lean's own open existential wrapper instance (registered, but contributes no cases of
  -- its own — see its `roundtripCases := []`).
  ``AnyX86_64Instruction,
  -- Add
  ``AddR64R64, ``AddR64Imm8, ``AddRspImm8, ``AddRspImm32, ``AddR64Imm32,
  -- Sub
  ``SubRspImm8, ``SubR64R64, ``SubR64Imm8, ``SubRspImm32, ``SubR64Imm32,
  -- Mov / Movzx
  ``MovR32Imm32, ``MovR64Imm64, ``MovR64R64, ``MovRspDispByte, ``MovRspDispImm32,
  ``MovRspDispImm64, ``MovMem8Reg8, ``MovMem64DispReg64, ``MovMem64DispImm32,
  ``MovReg64Mem64Disp, ``MovzxR64Mem8, ``MovReg32RspDisp32,
  -- Lea
  ``LeaRipRel, ``LeaRspDisp, ``LeaRspDisp32,
  -- Cmp
  ``CmpR64R64, ``CmpR64Imm8, ``CmpR64Imm32,
  -- Jcc / Jmp
  ``JmpRel8, ``JmpRel32, ``JeRel8, ``JeRel32, ``JneRel8, ``JneRel32, ``JlRel8, ``JleRel8,
  ``JgRel8, ``JgeRel8, ``JgeRel32, ``JbRel8, ``JaeRel8, ``JaeRel32, ``JaRel8, ``JbeRel8,
  ``JleRel32, ``JbRel32, ``JaRel32,
  -- Push / Pop
  ``PushR64, ``PopR64,
  -- Div / Imul
  ``DivR64, ``ImulR64R64,
  -- And / Or / Xor
  ``AndR64Imm8, ``AndR64R64, ``OrR64R64, ``OrR64Imm8, ``OrR64Imm32, ``XorR32R32,
  -- Not / Neg
  ``NotR64, ``NegR64,
  -- Shift
  ``ShlR64Imm8, ``ShrR64Imm8, ``SarR64Imm8, ``ShlR64Cl, ``ShrR64Cl,
  -- Test / Xchg
  ``TestR64R64, ``TestR64Imm32, ``XchgR64R64,
  -- Cmov
  ``CmoveR64R64, ``CmovneR64R64, ``CmovlR64R64, ``CmovleR64R64, ``CmovgR64R64, ``CmovgeR64R64,
  ``CmovbR64R64, ``CmovaeR64R64,
  -- Call / Ret
  ``CallRipRel, ``CallRel32, ``RetOp,
  -- In / Out / Hlt
  ``InAlImm8, ``InAlDx, ``InEaxImm8, ``InEaxDx,
  ``OutImm8Al, ``OutDxAl, ``OutImm8Eax, ``OutDxEax,
  ``HltOp,
  -- Syscall
  ``SyscallOp
]

-- Elaboration-time environment audit (docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate).
-- Walks every registered typeclass instance in the whole environment
-- (`Lean.Meta.instanceExtension`), keeps the ones whose inferred type has head constant
-- `X86_64Instruction`, and extracts the concrete instantiated type's name from each. Compares
-- that live set against `expectedInstructionTypes` and fails the build — naming the exact
-- symmetric difference — if a new `instance : X86_64Instruction Foo` was added without a
-- matching manifest entry (and, by construction, without a `RoundtripGate` case list), or if a
-- manifest entry's instance no longer exists. This is the "acceptable fallback" audit design (a
-- hand-maintained name list checked against the live environment) rather than a bespoke
-- `@[x86_instr]` attribute — it needs no custom attribute infrastructure, and the API used
-- (`Lean.Meta.instanceExtension`) is ordinary, stable Lean 4 metaprogramming. `run_cmd` is a
-- command, not a declaration, so it cannot itself carry a `/- REF -/` citation (check_refs.py
-- only pairs citations with `inductive|structure|def|class|instance|theorem|lemma|axiom|opaque`
-- declarations) — traceability for this file is carried by `allEncodableInstructions` and
-- `expectedInstructionTypes` above instead.
run_cmd do
  let env ← Lean.getEnv
  let insts := Lean.Meta.instanceExtension.getState env
  let liveNames ← Lean.Elab.Command.liftTermElabM do
    let mut found : List Name := []
    for (_, entry) in insts.instanceNames.toList do
      let ty ← Lean.Meta.inferType entry.val
      if ty.isAppOf ``X86_64Instruction then
        if let some tyName := ty.getAppArgs[0]!.constName? then
          found := tyName :: found
    pure found
  let sortByName (l : List Name) : List Name :=
    (l.eraseDups).toArray.qsort (fun a b => a.toString < b.toString) |>.toList
  let live := sortByName liveNames
  let expected := sortByName expectedInstructionTypes
  if live != expected then
    let missing := expected.filter (fun n => !live.contains n)
    let stale := live.filter (fun n => !expected.contains n)
    throwError s!"X86_64Instruction registry audit failed.\n\
      Missing from the live environment (stale `expectedInstructionTypes` entries, or the \
      matching instance was deleted): {missing}\n\
      Present in the live environment but not in `expectedInstructionTypes` (a new \
      `instance : X86_64Instruction Foo` was added without registering `Foo` here and adding a \
      RoundtripGate case list for it): {stale}"
  -- Non-emptiness floor: an empty `roundtripCases` list is otherwise legal Lean (it type-checks,
  -- `decodesOk.all` over `[]` is vacuously `true`), which makes "shrink the list to nothing" the
  -- path of least resistance for silencing a red gate rather than fixing the underlying bug. Fail
  -- the build if any family contributes zero cases, or if the aggregate registry is implausibly
  -- small for ~79 registered instruction types.
  let familyCounts : List (String × Nat) := [
    ("add", addFamilyCases.length), ("sub", subFamilyCases.length), ("mov", movFamilyCases.length),
    ("lea", leaFamilyCases.length), ("cmp", cmpFamilyCases.length), ("jcc", jccFamilyCases.length),
    ("push", pushFamilyCases.length), ("pop", popFamilyCases.length), ("div", divFamilyCases.length),
    ("imul", imulFamilyCases.length), ("and", andFamilyCases.length), ("or", orFamilyCases.length),
    ("xor", xorFamilyCases.length), ("not", notFamilyCases.length), ("neg", negFamilyCases.length),
    ("shift", shiftFamilyCases.length), ("test", testFamilyCases.length),
    ("xchg", xchgFamilyCases.length), ("cmov", cmovFamilyCases.length),
    ("call", callFamilyCases.length), ("ret", retFamilyCases.length),
    ("in", inFamilyCases.length), ("out", outFamilyCases.length), ("hlt", hltFamilyCases.length),
    ("syscall", syscallFamilyCases.length)
  ]
  let empties := familyCounts.filter (fun p => p.2 == 0)
  if !empties.isEmpty then
    throwError s!"X86_64Instruction registry audit failed: empty roundtripCases family list(s) \
      (every family must contribute at least one case): {empties.map Prod.fst}"
  let totalCases := allEncodableInstructions.length
  let sumFamilyCases := (familyCounts.map Prod.snd).foldl (· + ·) 0
  if totalCases != sumFamilyCases then
    throwError s!"X86_64Instruction registry audit failed: allEncodableInstructions has {totalCases} cases, \
      but the sum of all familyCounts is {sumFamilyCases} — a family was dropped from allEncodableInstructions!"
  if totalCases < expectedInstructionTypes.length then
    throwError s!"X86_64Instruction registry audit failed: allEncodableInstructions has only \
      {totalCases} cases total, fewer than the {expectedInstructionTypes.length} registered \
      instruction types — at least one family's roundtripCases is implausibly small."

end Gasm.Targets.X86_64.Registry
