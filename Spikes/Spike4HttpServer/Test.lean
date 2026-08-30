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
import Spikes.Spike4HttpServer.Equivalence

open Gasm.Core.Platform
open Spikes.Spike4HttpServer

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#whole-program-certificates -/
/- Smoke-test final serialization through the sole universal authority. The load-bearing
   arbitrary-environment proofs live in `Equivalence`; the closed probes here are supplemental. -/
def main : IO UInt32 := do
  let windows ← IO.ofExcept (emitVerifiedProgram spike4VerifiedWindowsProgram)
  let linux ← IO.ofExcept (emitVerifiedProgram spike4VerifiedLinuxProgram)
  let wasi ← IO.ofExcept (emitVerifiedProgram spike4VerifiedWasiProgram)
  IO.FS.writeBinFile "spike4_http.exe" windows
  IO.FS.writeBinFile "spike4_http_linux" linux
  IO.FS.writeBinFile "spike4_http.wasm" wasi
  if spike4RuntimeRegressionRequests.all spike4RuntimeAgreementOnAllTargets then
    IO.println "[+] Spike 4 verified artifacts emitted; supplemental request probes agree."
    return 0
  else
    IO.println "[!] Spike 4 supplemental request probe failed."
    return 1
