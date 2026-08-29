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

import Gasm.Targets.X86_64.Decoder
import Gasm.Targets.X86_64.RoundtripGate.Add
import Gasm.Targets.X86_64.RoundtripGate.And
import Gasm.Targets.X86_64.RoundtripGate.Call
import Gasm.Targets.X86_64.RoundtripGate.Cmov
import Gasm.Targets.X86_64.RoundtripGate.Cmp
import Gasm.Targets.X86_64.RoundtripGate.Div
import Gasm.Targets.X86_64.RoundtripGate.Hlt
import Gasm.Targets.X86_64.RoundtripGate.Imul
import Gasm.Targets.X86_64.RoundtripGate.In
import Gasm.Targets.X86_64.RoundtripGate.Jcc
import Gasm.Targets.X86_64.RoundtripGate.Lea
import Gasm.Targets.X86_64.RoundtripGate.Mov
import Gasm.Targets.X86_64.RoundtripGate.Neg
import Gasm.Targets.X86_64.RoundtripGate.Not
import Gasm.Targets.X86_64.RoundtripGate.Or
import Gasm.Targets.X86_64.RoundtripGate.Out
import Gasm.Targets.X86_64.RoundtripGate.Pop
import Gasm.Targets.X86_64.RoundtripGate.Push
import Gasm.Targets.X86_64.RoundtripGate.Ret
import Gasm.Targets.X86_64.RoundtripGate.Shift
import Gasm.Targets.X86_64.RoundtripGate.Sub
import Gasm.Targets.X86_64.RoundtripGate.Syscall
import Gasm.Targets.X86_64.RoundtripGate.Test
import Gasm.Targets.X86_64.RoundtripGate.Xchg
import Gasm.Targets.X86_64.RoundtripGate.Xor

-- STAGE B — this file is exactly the full-fan-in module required by
-- `docs/TARGETS/X86_64.md` Stage B: "isolate dispatch exhaustiveness into one separate
-- module that is *allowed* to have full fan-in, proving that the dispatcher agrees with the
-- per-family decoders." Every other Stage B module (each `Instructions/<Family>.lean`'s
-- `tryDecode`, each `RoundtripGate/<Family>.lean` shard) depends on at most its own family plus
-- `RoundtripGate.Common` — deliberately narrow, so editing one family doesn't invalidate another.
-- THIS file is the one deliberate exception: it imports `Decoder.lean` (which imports every
-- family, since the thin dispatcher must be able to route to any of them) and every
-- `RoundtripGate/<Family>.lean` shard, so editing *any* family's `Instructions/<Family>.lean`
-- will invalidate this file too. That is expected and correct, not a regression Stage B failed to
-- fix — dispatch-reachability is inherently a global property (does the dispatcher route every
-- registered instruction to the right family?), so the one module that states it must see every
-- family. Confining that unavoidable fan-in to this single, otherwise-inert file (it is proved,
-- not consumed — nothing downstream imports `DispatchExhaustive.lean`) is what keeps it from
-- reintroducing the pre-Stage-B cascade: editing `Instructions/Add.lean` still invalidates this
-- file, but no longer invalidates the 24 *other* families' `RoundtripGate/<Family>.lean` shards,
-- which is the property `docs/TARGETS/X86_64.md` measures.
namespace Gasm.Targets.X86_64.RoundtripGate

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Dispatch-reachability for the ADD family: the thin registry-driven dispatcher
    (`decodeX86_64Instr`, which tries `Decoder.allTryDecoders` in order) agrees with `addTryDecode`
    on every ADD witness — i.e. no earlier entry in `allTryDecoders` shadows or misroutes an ADD
    encoding before `addTryDecode` gets a chance to claim it. Proved the same way as the per-family
    roundtrip gates: `decodesOk`, instantiated with the real dispatcher instead of the family's own
    `tryDecode`, checked exhaustively over that family's finite `roundtripCases` witness list. -/
theorem addFamily_dispatchReachable : addFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem andFamily_dispatchReachable : andFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem callFamily_dispatchReachable : callFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem cmovFamily_dispatchReachable : cmovFamilyCases.all (decodesOk decodeX86_64Instr) = true := by
  set_option maxRecDepth 8000 in decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem cmpFamily_dispatchReachable : cmpFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem divFamily_dispatchReachable : divFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem hltFamily_dispatchReachable : hltFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem imulFamily_dispatchReachable : imulFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem inFamily_dispatchReachable : inFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem jccFamily_dispatchReachable : jccFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem leaFamily_dispatchReachable : leaFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem movFamily_dispatchReachable : movFamilyCases.all (decodesOk decodeX86_64Instr) = true := by
  set_option maxRecDepth 8000 in decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem negFamily_dispatchReachable : negFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem notFamily_dispatchReachable : notFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem orFamily_dispatchReachable : orFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem outFamily_dispatchReachable : outFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem popFamily_dispatchReachable : popFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem pushFamily_dispatchReachable : pushFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem retFamily_dispatchReachable : retFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem shiftFamily_dispatchReachable : shiftFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem subFamily_dispatchReachable : subFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem syscallFamily_dispatchReachable : syscallFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem testFamily_dispatchReachable : testFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem xchgFamily_dispatchReachable : xchgFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
theorem xorFamily_dispatchReachable : xorFamilyCases.all (decodesOk decodeX86_64Instr) = true := by decide

end Gasm.Targets.X86_64.RoundtripGate
