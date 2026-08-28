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

import Gasm.Targets.X86_64.MemoryFrame.Common
import Gasm.Targets.X86_64.MemoryFrame.Mov
import Gasm.Targets.X86_64.MemoryFrame.Push
import Gasm.Targets.X86_64.MemoryFrame.Pop
import Gasm.Targets.X86_64.MemoryFrame.Call
import Gasm.Targets.X86_64.MemoryFrame.Ret
import Gasm.Targets.X86_64.MemoryFrame.Add
import Gasm.Targets.X86_64.MemoryFrame.Sub
import Gasm.Targets.X86_64.MemoryFrame.And
import Gasm.Targets.X86_64.MemoryFrame.Or
import Gasm.Targets.X86_64.MemoryFrame.Xor
import Gasm.Targets.X86_64.MemoryFrame.Not
import Gasm.Targets.X86_64.MemoryFrame.Neg
import Gasm.Targets.X86_64.MemoryFrame.Shift
import Gasm.Targets.X86_64.MemoryFrame.Test
import Gasm.Targets.X86_64.MemoryFrame.Xchg
import Gasm.Targets.X86_64.MemoryFrame.Cmp
import Gasm.Targets.X86_64.MemoryFrame.Cmov
import Gasm.Targets.X86_64.MemoryFrame.Jcc
import Gasm.Targets.X86_64.MemoryFrame.Div
import Gasm.Targets.X86_64.MemoryFrame.Imul
import Gasm.Targets.X86_64.MemoryFrame.Lea
import Gasm.Targets.X86_64.MemoryFrame.In
import Gasm.Targets.X86_64.MemoryFrame.Out
import Gasm.Targets.X86_64.MemoryFrame.Hlt
import Gasm.Targets.X86_64.MemoryFrame.Syscall

-- Thin aggregator, mirroring RoundtripGate.lean's own header comment: importing every
-- per-family MemoryFrame/*.lean shard forces all 88 registered instruction forms' (14
-- memory-touching + 74 register-only) writesWithin/readsWithin connection theorems
-- (docs/MEMORY_HOOK.md §3.3, Law 12) to elaborate whenever this module (transitively, Gasm) is
-- built. There is no declaration here beyond the imports.
