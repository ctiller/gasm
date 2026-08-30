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

import Spikes.Spike3SortLines.NativeOutcome

/-! Explicit operational probes for the bounded native Spike 3 artifact.  These are regression
    observations, deliberately not theorems and not substitutes for the universal runtime-boundary
    proofs in `NativeOutcome`. -/

namespace Spikes.Spike3SortLines

#eval emittedSpike3ResourceFailure (runSpike3LinuxWithGrant noNativeArenaGrant ByteArray.empty 30)
#eval (runSpike3LinuxWithGrant spike3NativeReservationGrant ByteArray.empty 200).events
#eval emittedSpike3ResourceFailure (runSpike3WindowsWithGrant noNativeArenaGrant ByteArray.empty 30)
#eval (runSpike3WindowsWithGrant spike3NativeReservationGrant ByteArray.empty 220).events

end Spikes.Spike3SortLines
