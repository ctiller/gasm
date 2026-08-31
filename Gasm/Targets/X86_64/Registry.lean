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
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.InstructionCensus
import Gasm.Targets.X86_64.RoundtripGate
import Gasm.Targets.X86_64.MemoryFrame

-- LOUD INVARIANT (see also the import-closure comment atop Instructions.lean):
-- `InstructionCensus.concreteForms` is the one semantic population census used by this registry,
-- the family/dispatch audits, and the memory-frame audit.  The filesystem gate independently
-- requires every recursively nested Instructions/**/*.lean module to be umbrella-reachable, so
-- the compiled census cannot be bypassed by leaving a source module outside the import closure.
namespace Gasm.Targets.X86_64.Registry

open Lean Meta
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.RoundtripGate
open Gasm.Targets.X86_64.InstructionCensus

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

-- Elaboration-time registry audit.  Classification and all production shape rejection happen in
-- the shared reducing compiled census.  Exact witness population is then checked by
-- `FamilyPipelineAudit`; this command makes the same census an ordinary Registry build dependency
-- and rejects an accidentally empty instruction universe here rather than relying on that later
-- consumer.
run_cmd do
  let env ← Lean.getEnv
  let forms ← Lean.Elab.Command.liftTermElabM <| concreteForms env
  if forms.isEmpty then
    throwError "X86_64Instruction registry audit found no concrete instruction forms"

end Gasm.Targets.X86_64.Registry
