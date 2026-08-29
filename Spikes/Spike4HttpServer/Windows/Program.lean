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
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Targets.X86_64.Instructions.Shift
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Push
import Gasm.Targets.X86_64.Instructions.Pop
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.Windows.PEFormat
import Gasm.Targets.Windows.Linker
import Spikes.Spike4HttpServer.Spec
import Spikes.Spike4HttpServer.Runtime

namespace Spikes.Spike4HttpServer.Windows

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.Windows
open Gasm.Targets.Windows.Linker
open Spikes.Spike4HttpServer

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- Response bytes for HTTP root endpoint "/" -/
def respRootBytes : ByteArray :=
  (formatResponse (routeRequest { method := "GET", path := "/", version := "HTTP/1.1" })).toUTF8

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- Response bytes for HTTP status endpoint "/status" -/
def respStatusBytes : ByteArray :=
  (formatResponse (routeRequest { method := "GET", path := "/status", version := "HTTP/1.1" })).toUTF8

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- Response bytes for 404 Not Found -/
def resp404Bytes : ByteArray :=
  (formatResponse { statusCode := 404, statusText := "Not Found", contentType := "text/plain", body := "404 Not Found\r\n" }).toUTF8

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- Response bytes for 400 Bad Request, taken from the model's own `badRequestResponse` so the
    lowering cannot drift from what `Spec.handleRawRequest` emits on a rejected request line. -/
def resp400Bytes : ByteArray :=
  (formatResponse badRequestResponse).toUTF8

def resp414Bytes : ByteArray :=
  (formatResponse requestResourceExhaustedResponse).toUTF8

/- REF: windows-winsock2-send#parameters -/
/-- Offsets in the combined .rdata payload for response strings. -/
def respRootOffset : Nat := 0

/- REF: windows-winsock2-send#parameters -/
def respStatusOffset : Nat := respRootBytes.size

/- REF: windows-winsock2-send#parameters -/
def resp404Offset : Nat := respStatusOffset + respStatusBytes.size

/- REF: windows-winsock2-send#parameters -/
def resp400Offset : Nat := resp404Offset + resp404Bytes.size

def resp414Offset : Nat := resp400Offset + resp400Bytes.size

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#31-x8664-windows-ws232dll -/
def rdataPayload : ByteArray :=
  respRootBytes ++ respStatusBytes ++ resp404Bytes ++ resp400Bytes ++ resp414Bytes

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#31-x8664-windows-ws232dll -/
/-- Symbolic Windows x86-64 entry point for the proof-connected Spike 4 runtime ABI.
    It reserves the mandatory 32-byte Windows x64 shadow space and invokes the one imported
    verified request component once for each lifecycle phase (listen, accept, receive, respond,
    close). Socket state, bounded scratch storage, parsing, routing, and request-scope recovery are
    owned by the selected runtime profile, not duplicated in this ISA wrapper. -/
def spike4SymbolicProgram : List SymbolicInstr := [
  -- The selected OS + Gasm-runtime profile owns the request lifecycle.  Five explicit phases
  -- make the resource scope and its recovery boundary visible while keeping parsing/routing in
  -- the separately verified component rather than duplicating it in each ISA lowering.
  instr (sub_rsp32 32),
  instr (mov_r32 .r9d 0), call_import gasmHttpParserSymbol,
  instr (mov_r32 .r9d 1), call_import gasmHttpParserSymbol,
  instr (mov_r32 .r9d 2), call_import gasmHttpParserSymbol,
  instr (mov_r32 .r9d 3), call_import gasmHttpParserSymbol,
  instr (mov_r32 .r9d 4), call_import gasmHttpParserSymbol
]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#31-x8664-windows-ws232dll -/
def spike4DllImports : List (String × List String) := [
  (gasmHttpRuntimeDll, [gasmHttpParserSymbol])
]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#31-x8664-windows-ws232dll -/
def spike4DataItems : List (String × ByteArray) := [
  ("rdata_base", ByteArray.empty)
]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#31-x8664-windows-ws232dll -/
def spike4LinkedProgram : LinkedWindowsProgram :=
  linkWindowsProgramMultiDll spike4SymbolicProgram spike4DataItems spike4DllImports

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#31-x8664-windows-ws232dll -/
def spike4Executable : WindowsExecutable :=
  spike4LinkedProgram.executable

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#31-x8664-windows-ws232dll -/
def spike4Instructions : List X86_64Instr :=
  spike4LinkedProgram.instructions

def lifecyclePhaseInstructions (phase : Nat) (displacement : Int32) : List X86_64Instr :=
  [mov_r32 .r9d phase.toUInt32, call_rip displacement]

theorem spike4Instructions_phases : spike4Instructions =
    [sub_rsp32 32] ++ lifecyclePhaseInstructions 0 8173 ++
      lifecyclePhaseInstructions 1 8161 ++ lifecyclePhaseInstructions 2 8149 ++
      lifecyclePhaseInstructions 3 8137 ++ lifecyclePhaseInstructions 4 8125 := rfl

end Spikes.Spike4HttpServer.Windows
