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

/- REF: windows-winsock2-send#parameters -/
/-- Offsets in the combined .rdata payload for response strings. -/
def respRootOffset : Nat := 0

/- REF: windows-winsock2-send#parameters -/
def respStatusOffset : Nat := respRootBytes.size

/- REF: windows-winsock2-send#parameters -/
def resp404Offset : Nat := respStatusOffset + respStatusBytes.size

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#31-x8664-windows-ws232dll -/
def rdataPayload : ByteArray :=
  respRootBytes ++ respStatusBytes ++ resp404Bytes

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#31-x8664-windows-ws232dll -/
/-- Symbolic program definition for Spike 4 x86_64 Windows HTTP 1.1 Server.
    Stack Layout (total 608 bytes allocated, maintaining (RSP - 608) % 16 == 0):
      [RSP + 0x00..0x1F] : shadow space (32 bytes)
      [RSP + 0x20..0x27] : server socket descriptor (8 bytes)
      [RSP + 0x28..0x2F] : client socket descriptor (8 bytes)
      [RSP + 0x30..0x3F] : sockaddr_in buffer (16 bytes)
      [RSP + 0x40..0xBF] : HTTP request recv buffer (128 bytes)
      [RSP + 0xC0..0x258] : WSADATA buffer (408 bytes)
-/
def spike4SymbolicProgram : List SymbolicInstr := [
  -- 1. Setup 608-byte stack frame (accommodates 408-byte WSADATA + 128-byte recv + locals + shadow space)
  instr (sub_rsp32 608),

  -- 2. WSAStartup(0x0202, lpWSAData = RSP + 0xC0)
  instr (mov_r32 .ecx 0x0202),
  instr (lea_rsp .rdx 0xC0),
  call_import "WSAStartup",

  -- 3. socket(af = AF_INET (2), type = SOCK_STREAM (1), protocol = IPPROTO_TCP (6))
  instr (mov_r32 .ecx 2),
  instr (mov_r32 .edx 1),
  instr (mov_r32 .r8d 6),
  call_import "socket",
  instr (mov_mem64_disp .rsp 0x20 .rax), -- Save server socket

  -- 4. Setup sockaddr_in at RSP + 0x30
  -- sin_family = 2 (AF_INET), sin_port = htons(8080) = 0x1F90, sin_addr = 0 (INADDR_ANY = 0.0.0.0)
  -- Storing 0x00000000901F0002 via RAX ensures bytes [RSP+0x30..0x37] = 02 00 1F 90 00 00 00 00
  instr (mov_r64_imm64 .rax 0x901F0002),
  instr (mov_mem64_disp .rsp 0x30 .rax),
  instr (mov_mem64_disp_imm .rsp 0x38 0), -- Zero out remaining 8 bytes (sin_zero)

  -- 5. bind(server_fd, name = RSP + 0x30, namelen = 16)
  instr (mov_reg64_mem64_disp .rcx .rsp 0x20),
  instr (lea_rsp .rdx 0x30),
  instr (mov_r32 .r8d 16),
  call_import "bind",

  -- 6. listen(server_fd, backlog = 5)
  instr (mov_reg64_mem64_disp .rcx .rsp 0x20),
  instr (mov_r32 .edx 5),
  call_import "listen",

  -- 7. Accept loop (runs indefinitely)
  label "accept_loop",
  instr (mov_reg64_mem64_disp .rcx .rsp 0x20),
  instr (xor_r32 .edx .edx),
  instr (xor_r32 .r8d .r8d),
  call_import "accept",
  instr (mov_mem64_disp .rsp 0x28 .rax), -- Save client socket

  -- 8. recv(client_fd, buf = RSP + 0x40, len = 128, flags = 0)
  instr (mov_reg64_mem64_disp .rcx .rsp 0x28),
  instr (lea_rsp .rdx 0x40),
  instr (mov_r32 .r8d 128),
  instr (xor_r32 .r9d .r9d),
  call_import "recv",

  -- 9. Inspect received HTTP request line at RSP + 0x40
  -- Check if path is "/status" (at offset 4: "GET /status...")
  instr (lea_rsp .rsi (0x40 + 4)),
  instr (mov_reg64_mem64_disp .rax .rsi 0),
  instr (mov_r64_imm64 .rdx 0xFFFFFFFFFF),
  instr (and_r64 .rax .rdx),
  instr (mov_r64_imm64 .rcx 0x746174732F), -- "/stat"
  instr (cmp_r64 .rax .rcx),
  je_label "send_status",

  -- Check root endpoint: "/ " (0x202F)
  instr (mov_reg64_mem64_disp .rax .rsi 0),
  instr (mov_r64_imm64 .rdx 0xFFFF),
  instr (and_r64 .rax .rdx),
  instr (mov_r64_imm64 .rcx 0x202F), -- "/ "
  instr (cmp_r64 .rax .rcx),
  je_label "send_root",

  -- Check root endpoint alternative: "/\r" (0x0D2F)
  instr (mov_r64_imm64 .rcx 0x0D2F),
  instr (cmp_r64 .rax .rcx),
  je_label "send_root",

  -- Default: send 404
  label "send_404",
  lea_data .rdx "rdata_base",
  instr (add_r64_imm32 .rdx resp404Offset.toUInt32),
  instr (mov_r32 .r8d resp404Bytes.size.toUInt32),
  jmp_label "do_send",

  label "send_root",
  lea_data .rdx "rdata_base",
  instr (add_r64_imm32 .rdx respRootOffset.toUInt32),
  instr (mov_r32 .r8d respRootBytes.size.toUInt32),
  jmp_label "do_send",

  label "send_status",
  lea_data .rdx "rdata_base",
  instr (add_r64_imm32 .rdx respStatusOffset.toUInt32),
  instr (mov_r32 .r8d respStatusBytes.size.toUInt32),

  label "do_send",
  -- 10. send(client_fd, buf = RDX, len = R8, flags = 0)
  instr (mov_reg64_mem64_disp .rcx .rsp 0x28),
  instr (xor_r32 .r9d .r9d),
  call_import "send",

  -- 11. closesocket(client_fd)
  instr (mov_reg64_mem64_disp .rcx .rsp 0x28),
  call_import "closesocket",

  -- 12. Loop back to accept next connection
  jmp_near_label "accept_loop"
]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#31-x8664-windows-ws232dll -/
def spike4DllImports : List (String × List String) := [
  ("KERNEL32.dll", [
    "GetStdHandle",
    "ReadFile",
    "WriteFile",
    "ExitProcess",
    "VirtualAlloc",
    "VirtualFree"
  ]),
  ("WS2_32.dll", [
    "WSAStartup",
    "socket",
    "bind",
    "listen",
    "accept",
    "recv",
    "send",
    "closesocket",
    "WSACleanup"
  ])
]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#31-x8664-windows-ws232dll -/
def spike4DataItems : List (String × ByteArray) := [
  ("rdata_base", rdataPayload)
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

end Spikes.Spike4HttpServer.Windows
