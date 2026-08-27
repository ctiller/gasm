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
import Gasm.Core.Verification
import Gasm.Targets.WASI.ABI
import Spikes.Spike4HttpServer.Spec
import Spikes.Spike4HttpServer.Windows.Program
import Spikes.Spike4HttpServer.Wasm.Program
import Spikes.Spike4HttpServer.Equivalence

open Gasm.Core.Verification
open Gasm.Targets.WASI
open Spikes.Spike4HttpServer

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#4-semantic-trace-equivalence-verifiedprogram-contract -/
/-- CLI Test Target for Dual-Target Spike 4 HTTP 1.1 Server (x86_64 Windows & WebAssembly). -/
def main : IO UInt32 := do
  IO.println "[*] ==================================================================="
  IO.println "[*] SPIKE 4: Dual-Target HTTP 1.1 Server Verification Suite"
  IO.println "[*] ==================================================================="

  -- 1. Verify VerifiedProgram Windows Contract & Binary Emission
  IO.println "[*] [1/4] Verifying x86_64 Windows VerifiedProgram Contract..."
  let winExeBytes := emitVerifiedExecutable spike4WindowsVerifiedProgram
  let winExePath := "spike4_http.exe"
  IO.FS.writeBinFile winExePath winExeBytes
  IO.println s!"[+] Windows PE32+ binary generated: {winExePath} ({winExeBytes.size} bytes)"

  -- 2. Verify VerifiedWasmProgram Contract & Binary Emission
  IO.println "[*] [2/4] Verifying WebAssembly VerifiedWasmProgram Contract..."
  let wasmBytes ← IO.ofExcept (emitVerifiedWasmBinary spike4WasmVerifiedProgram)
  let wasmText := emitVerifiedWasmText spike4WasmVerifiedProgram
  let wasmPath := "spike4_http.wasm"
  let watPath := "spike4_http.wat"
  IO.FS.writeBinFile wasmPath wasmBytes
  IO.FS.writeFile watPath wasmText
  IO.println s!"[+] WebAssembly binary generated: {wasmPath} ({wasmBytes.size} bytes)"
  IO.println s!"[+] WebAssembly WAT text generated: {watPath}"

  -- 3. Verify Constructive Multi-Route Equivalence Theorems across Windows & WASM
  IO.println "[*] [3/4] Verifying Constructive Multi-Route Trace Equivalence Theorems..."
  if windowsTraceRoot == modelTraceRoot && wasmTraceRoot == modelTraceRoot then
    IO.println "[+] Route [/] (Root 200 OK): Windows and WASM traces 100% equivalent to Spec."
  else
    IO.println "[!] FAIL: Route [/] trace mismatch!"
    return 1

  if windowsTraceStatus == modelTraceStatus && wasmTraceStatus == modelTraceStatus then
    IO.println "[+] Route [/status] (Status JSON 200 OK): Windows and WASM traces 100% equivalent to Spec."
  else
    IO.println "[!] FAIL: Route [/status] trace mismatch!"
    return 1

  if windowsTrace404 == modelTrace404 && wasmTrace404 == modelTrace404 then
    IO.println "[+] Route [/unknown] (404 Not Found): Windows and WASM traces 100% equivalent to Spec."
  else
    IO.println "[!] FAIL: Route [/unknown] 404 trace mismatch!"
    return 1

  -- 4. Verify HTTP Response Routing Logic
  IO.println "[*] [4/4] Verifying HTTP Routing & Serialization Invariants..."
  let rootReq := "GET / HTTP/1.1\r\nHost: localhost:8080\r\n\r\n"
  let statusReq := "GET /status HTTP/1.1\r\nHost: localhost:8080\r\n\r\n"
  let notFoundReq := "GET /unknown HTTP/1.1\r\nHost: localhost:8080\r\n\r\n"

  let rootResp := handleRawRequest rootReq
  let statusResp := handleRawRequest statusReq
  let notFoundResp := handleRawRequest notFoundReq

  let expectedRoot := formatResponse (routeRequest { method := "GET", path := "/", version := "HTTP/1.1" })
  let expectedStatus := formatResponse (routeRequest { method := "GET", path := "/status", version := "HTTP/1.1" })
  let expected404 := formatResponse { statusCode := 404, statusText := "Not Found", contentType := "text/plain", body := "404 Not Found\r\n" }

  if rootResp != expectedRoot then
    IO.println s!"[!] FAIL: Root endpoint response malformed:\n{rootResp}"
    return 1

  if statusResp != expectedStatus then
    IO.println s!"[!] FAIL: Status endpoint response malformed:\n{statusResp}"
    return 1

  if notFoundResp != expected404 then
    IO.println s!"[!] FAIL: 404 endpoint response malformed:\n{notFoundResp}"
    return 1

  IO.println "[+] HTTP / 200 OK text/plain verified."
  IO.println "[+] HTTP /status 200 OK application/json verified."
  IO.println "[+] HTTP /unknown 404 Not Found verified."

  IO.println "[*] ==================================================================="
  IO.println "[+] ALL SPIKE 4 DUAL-TARGET HTTP SERVER VERIFICATION CHECKS PASSED!"
  IO.println "[*] ==================================================================="
  return 0
