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
import Gasm.Core.Arch
import Gasm.Core.Permissions
import Gasm.Core.Obligations

namespace Gasm.Core

/- REF: docs/API_STATE_MODELS.md#1-the-composed-state-model-zero-cost-proof-erasure -/
/-- Composite verification state bundling target-native machine state, stack depth, typestate, capabilities, and causality. -/
structure ComposedState (Arch : Type) [TargetArch Arch] (ApiStateType : Type) where
  machine      : TargetArch.MachineState Arch
  stackDepth   : Nat
  api          : ApiStateType
  perms        : MemoryPermissions Arch
  obligations  : List ObligationToken
  causalClock  : VectorClock
  eventHistory : EventTag → VectorClock

end Gasm.Core
