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
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Instructions.Syscall
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.Linux.ELFFormat
import Gasm.Targets.Linux.Linker
import Spikes.Spike4HttpServer.Spec
import Spikes.Spike4HttpServer.Runtime

namespace Spikes.Spike4HttpServer.Linux

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.Linux
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

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Offsets in the combined .rodata payload for response strings. -/
def respRootOffset : Nat := 0

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
def respStatusOffset : Nat := respRootBytes.size

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
def resp404Offset : Nat := respStatusOffset + respStatusBytes.size

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
def resp400Offset : Nat := resp404Offset + resp404Bytes.size

def resp414Offset : Nat := resp400Offset + resp400Bytes.size

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
def rdataPayload : ByteArray :=
  respRootBytes ++ respStatusBytes ++ resp404Bytes ++ resp400Bytes ++ resp414Bytes

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#1-high-level-architecture-protocol-state-machine -/
/-- Symbolic Linux x86-64 entry point for the proof-connected Spike 4 runtime ABI.
    The five calls use the profile-owned Gasm runtime entry and identify the listen, accept,
    receive, respond, and close phases in `r10`. Socket state, bounded scratch storage, parsing,
    routing, and request-scope recovery are supplied by that selected runtime profile. -/
def spike4SymbolicProgram : List SymbolicInstr := [
  -- Five explicit request-scope phases provided by the selected Gasm runtime.
  instr (xor_r32 .r10d .r10d),
  instr (mov_r32 .eax gasmHttpLinuxSyscall.toUInt32), instr syscall_op,
  instr (mov_r32 .r10d 1),
  instr (mov_r32 .eax gasmHttpLinuxSyscall.toUInt32), instr syscall_op,
  instr (mov_r32 .r10d 2),
  instr (mov_r32 .eax gasmHttpLinuxSyscall.toUInt32), instr syscall_op,
  instr (mov_r32 .r10d 3),
  instr (mov_r32 .eax gasmHttpLinuxSyscall.toUInt32), instr syscall_op,
  instr (mov_r32 .r10d 4),
  instr (mov_r32 .eax gasmHttpLinuxSyscall.toUInt32), instr syscall_op
]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#1-high-level-architecture-protocol-state-machine -/
/-- Linked binary program artifact for Linux Spike 4. -/
def spike4Linked : LinkedLinuxProgram :=
  linkLinuxProgramStatic spike4SymbolicProgram [
    ("rdata_base", rdataPayload)
  ]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#1-high-level-architecture-protocol-state-machine -/
/-- Lowered concrete machine instruction sequence for Linux Spike 4. -/
def spike4Instructions : List X86_64Instr :=
  spike4Linked.instructions

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#1-high-level-architecture-protocol-state-machine -/
/-- Standard executable layout descriptor for Linux Spike 4. -/
def spike4Executable : LinuxExecutable :=
  spike4Linked.executable

end Spikes.Spike4HttpServer.Linux
