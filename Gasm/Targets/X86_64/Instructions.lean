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
-- True umbrella: every Instructions/*.lean submodule is imported here so that anything importing
-- this file (in particular Registry.lean, transitively through RoundtripGate.lean) sees every
-- registered `X86_64Instruction` instance in the environment. This narrows — though does not by
-- itself eliminate — the import-closure hole the registry audit is otherwise blind to: an
-- instruction file that exists on disk but is imported nowhere is invisible to a whole-program
-- environment walk, since Lean only sees declarations reachable through the current file's
-- import graph, not every `.lean` file Lake happens to compile as part of the library glob. Adding
-- a new Instructions/<Foo>.lean file MUST add an `import` line here (in addition to giving it a
-- RoundtripGate/<Foo>.lean shard and an `expectedInstructionTypes` entry in Registry.lean) or its
-- instance(s) will silently not be audited, registered, or gated.
--
-- B1 iteration 2 (build-perf: Instructions.lean aggregator sharding): this file is now
-- intentionally import-only. `X86_64Instr`, the `TargetArch X86_64` instance, and
-- `X86_64Instr.toBinary` used to live here, forcing every consumer that only needed those three
-- declarations (not whole-registry visibility) to transitively depend on all 21
-- Instructions/*.lean submodules. They now live in `Instructions/Base.lean` instead — a module
-- every instruction file (and therefore this umbrella) already imports, so moving them does not
-- add any new dependency, but it lets a consumer that needs only `X86_64Instr`/`TargetArch X86_64`
-- import `Instructions.Base` directly instead of this file's own forward closure (this umbrella +
-- its 21 submodules = 33 modules per `scripts/build_baseline.md` §3, vs `Instructions.Base`'s 11
-- — a 22-module reduction per such consumer). 56 is this umbrella's *fan-in* (how many other
-- modules transitively import it), not its forward closure; see `scripts/build_baseline.md` §7.1
-- for the measured cascade-size delta this restructuring actually produces. Only `Registry.lean`
-- (which needs the whole-environment audit) and `Decoder.lean` (which already imports every
-- individual instruction submodule directly to construct decoded instances) still import this
-- umbrella.
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Instructions.Cmov
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Div
import Gasm.Targets.X86_64.Instructions.Imul
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Neg
import Gasm.Targets.X86_64.Instructions.Not
import Gasm.Targets.X86_64.Instructions.Or
import Gasm.Targets.X86_64.Instructions.Pop
import Gasm.Targets.X86_64.Instructions.Push
import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.Instructions.Shift
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.Instructions.Test
import Gasm.Targets.X86_64.Instructions.Xchg
import Gasm.Targets.X86_64.Instructions.Xor
