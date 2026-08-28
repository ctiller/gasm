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
import Gasm.Targets.X86_64.MemoryFrame.Common
import Gasm.Targets.X86_64.Instructions.Syscall

namespace Gasm.Targets.X86_64.MemoryFrame

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

-- SYSCALL is register-only (`memAccesses _ := []`): the pure model step only advances RIP to the
-- simulated kernel entry point and records the return address/flags in RCX/R11 -- it never
-- touches `.memory`. See MemoryFrame/Add.lean's header comment for the batch-lemma-instantiation
-- rationale (identical here).

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem SyscallOp.writesWithin (i : SyscallOp) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem SyscallOp.readsWithin (i : SyscallOp) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64, hrip, hgprs, hflags, hstdin,
        hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

end Gasm.Targets.X86_64.MemoryFrame
