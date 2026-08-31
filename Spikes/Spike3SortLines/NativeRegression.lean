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
import Spikes.Spike3SortLines.StableSortRegression

/-! Explicit operational probes for the bounded native Spike 3 artifact.  These are regression
    observations, deliberately not theorems and not substitutes for the universal runtime-boundary
    proofs in `NativeOutcome`. -/

namespace Spikes.Spike3SortLines

open Gasm.Effects

/-- An interior CR is data; only a CR immediately followed by LF is trimmed.  This regression
    prevents the native streamers from reintroducing their former standalone-CR delimiter path. -/
def nativeInteriorCrInput : ByteArray := "a\rb\n".toUTF8

def nativeInteriorCrExpected : List AnyEvent :=
  [AnyEvent.of (ConsoleEvent.out "a\rb"),
   AnyEvent.of (ConsoleEvent.out "\r\n"),
   AnyEvent.of (ProcessEvent.exit 0)]

/-- Literal operational probes remain outside the proof surface.  They exercise rejected and
    sufficient reservations with the same empty stdin on both native targets, plus the shared
    arbitrary-byte CRLF boundary contract. -/
def nativeResourceRegressionPassed : Bool :=
  emittedSpike3ResourceFailure (runSpike3LinuxWithGrant noNativeArenaGrant ByteArray.empty 30) &&
  ((runSpike3LinuxWithGrant spike3NativeReservationGrant ByteArray.empty 200).events ==
    [AnyEvent.of (ProcessEvent.exit 0)]) &&
  emittedSpike3ResourceFailure (runSpike3WindowsWithGrant noNativeArenaGrant ByteArray.empty 30) &&
  ((runSpike3WindowsWithGrant spike3NativeReservationGrant ByteArray.empty 220).events ==
    [AnyEvent.of (ProcessEvent.exit 0)]) &&
  ((runSpike3LinuxWithGrant spike3NativeReservationGrant nativeInteriorCrInput 5000).events ==
    nativeInteriorCrExpected) &&
  ((runSpike3WindowsWithGrant spike3NativeReservationGrant nativeInteriorCrInput 5000).events ==
    nativeInteriorCrExpected)

end Spikes.Spike3SortLines

/-- Explicit executable regression target for bounded native resource outcomes. -/
def main : IO UInt32 := do
  if Spikes.Spike3SortLines.nativeResourceRegressionPassed &&
      Spikes.Spike3SortLines.taggedStableSortRegressionPassed then
    IO.println "[PASS] Spike 3 native resource outcomes and tagged stable sort"
    return 0
  else
    IO.eprintln "[FAIL] Spike 3 native resource outcomes or tagged stable sort"
    return 1
