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
import Gasm.Core.Types
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Decoder

namespace Gasm.Targets.X86_64.RoundtripGate

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Byte-level roundtrip equality relation shared by every per-family gate theorem.
    `AnyX86_64Instruction` (an open existential over a hidden concrete type) has no general
    `DecidableEq` instance to drive a `List.all` over a mixed-family list, so this checks the
    conjunction the design doc specifies instead: (a) decoding the encoded bytes succeeds, (b) the
    decoded length equals the encoded byte count, (c) re-encoding the decoded instruction reproduces
    the original bytes exactly, and (d) the `toLean` renderings of the decoded and original
    instructions match — guarding against a same-bytes-different-structure misdecode (the class of
    bug the 0x8B REX.W soundness fix addressed). -/
def decodesOk (i : AnyX86_64Instruction) : Bool :=
  let encoded := X86_64Instruction.encode i
  match decodeX86_64Instr encoded 0 with
  | .error _ => false
  | .ok (decoded, len) =>
    len == encoded.size &&
    X86_64Instruction.encode decoded == encoded &&
    X86_64Instruction.toLean decoded == X86_64Instruction.toLean i

end Gasm.Targets.X86_64.RoundtripGate
