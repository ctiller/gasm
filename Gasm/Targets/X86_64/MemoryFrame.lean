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

-- Thin aggregator, mirroring RoundtripGate.lean's own header comment: importing every
-- per-family MemoryFrame/*.lean shard forces all 14 memory forms' writesWithin/readsWithin
-- connection theorems (docs/MEMORY_HOOK.md §3.3, Law 12) to elaborate whenever this module
-- (transitively, Gasm) is built. There is no declaration here beyond the imports.
