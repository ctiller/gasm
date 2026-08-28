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

import Gasm.Targets.X86_64.RoundtripGate.Common
import Gasm.Targets.X86_64.RoundtripGate.Add
import Gasm.Targets.X86_64.RoundtripGate.Sub
import Gasm.Targets.X86_64.RoundtripGate.Mov
import Gasm.Targets.X86_64.RoundtripGate.Lea
import Gasm.Targets.X86_64.RoundtripGate.Cmp
import Gasm.Targets.X86_64.RoundtripGate.Jcc
import Gasm.Targets.X86_64.RoundtripGate.Push
import Gasm.Targets.X86_64.RoundtripGate.Pop
import Gasm.Targets.X86_64.RoundtripGate.Div
import Gasm.Targets.X86_64.RoundtripGate.Imul
import Gasm.Targets.X86_64.RoundtripGate.And
import Gasm.Targets.X86_64.RoundtripGate.Or
import Gasm.Targets.X86_64.RoundtripGate.Xor
import Gasm.Targets.X86_64.RoundtripGate.Not
import Gasm.Targets.X86_64.RoundtripGate.Neg
import Gasm.Targets.X86_64.RoundtripGate.Shift
import Gasm.Targets.X86_64.RoundtripGate.Test
import Gasm.Targets.X86_64.RoundtripGate.Xchg
import Gasm.Targets.X86_64.RoundtripGate.Cmov
import Gasm.Targets.X86_64.RoundtripGate.Call
import Gasm.Targets.X86_64.RoundtripGate.Ret
import Gasm.Targets.X86_64.RoundtripGate.In
import Gasm.Targets.X86_64.RoundtripGate.Out
import Gasm.Targets.X86_64.RoundtripGate.Hlt
import Gasm.Targets.X86_64.RoundtripGate.Syscall

-- Thin aggregator (docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate):
-- importing every per-family RoundtripGate/*.lean shard forces all of their
-- `<family>_roundtripGate` theorems to elaborate whenever this module (transitively, `Gasm`) is
-- built. There is no declaration here beyond the imports — this file's only job is to be the
-- single place a new shard must be wired into so its gate actually runs.
