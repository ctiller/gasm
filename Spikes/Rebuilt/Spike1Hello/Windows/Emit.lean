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

import Spikes.Rebuilt.Spike1Hello.Windows.Certificate

open Spikes.Rebuilt.Spike1Hello.Windows.Certificate

def main (args : List String) : IO UInt32 := do
  let output := args.headD "rebuilt_spike1_hello.exe"
  let bytes := emitVerified verifiedArtifact
  IO.FS.writeBinFile output bytes
  IO.println s!"Emitted {bytes.size} certificate-gated bytes to {output}"
  pure 0
