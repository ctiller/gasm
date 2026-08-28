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

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Offsets in the combined .rodata payload for response strings. -/
def respRootOffset : Nat := 0

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
def respStatusOffset : Nat := respRootBytes.size

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
def resp404Offset : Nat := respStatusOffset + respStatusBytes.size

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
def rdataPayload : ByteArray :=
  respRootBytes ++ respStatusBytes ++ resp404Bytes

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#1-high-level-architecture-protocol-state-machine -/
/-- Symbolic program definition for Spike 4 x86_64 Linux HTTP 1.1 Server.
    Stack Layout (total 208 bytes allocated, maintaining (RSP - 208) % 16 == 0):
      [RSP + 0x20..0x27] : server socket descriptor (8 bytes)
      [RSP + 0x28..0x2F] : client socket descriptor (8 bytes)
      [RSP + 0x30..0x3F] : sockaddr_in buffer (16 bytes)
      [RSP + 0x40..0xBF] : HTTP request recv buffer (128 bytes)
-/
def spike4SymbolicProgram : List SymbolicInstr := [
  -- 1. Setup 208-byte stack frame
  instr (sub_rsp 208),

  -- 2. socket(af = AF_INET (2), type = SOCK_STREAM (1), protocol = IPPROTO_TCP (6))
  instr (mov_r32 .edi 2),
  instr (mov_r32 .esi 1),
  instr (mov_r32 .edx 6),
  instr (mov_r32 .eax 41), -- SYS_socket
  instr syscall_op,
  instr (mov_mem64_disp .rsp 0x20 .rax), -- Save server socket

  -- 3. Setup sockaddr_in at RSP + 0x30
  -- sin_family = 2 (AF_INET), sin_port = htons(8080) = 0x1F90, sin_addr = 0 (INADDR_ANY = 0.0.0.0)
  instr (mov_r64_imm64 .rax 0x901F0002),
  instr (mov_mem64_disp .rsp 0x30 .rax),
  instr (mov_mem64_disp_imm .rsp 0x38 0), -- Zero out remaining 8 bytes (sin_zero)

  -- 4. bind(server_fd, name = RSP + 0x30, namelen = 16)
  instr (mov_reg64_mem64_disp .rdi .rsp 0x20),
  instr (lea_rsp .rsi 0x30),
  instr (mov_r32 .edx 16),
  instr (mov_r32 .eax 49), -- SYS_bind
  instr syscall_op,

  -- 5. listen(server_fd, backlog = 5)
  instr (mov_reg64_mem64_disp .rdi .rsp 0x20),
  instr (mov_r32 .esi 5),
  instr (mov_r32 .eax 50), -- SYS_listen
  instr syscall_op,

  -- 6. Accept loop (runs until connections exhausted)
  label "accept_loop",
  instr (mov_reg64_mem64_disp .rdi .rsp 0x20),
  instr (xor_r32 .esi .esi),
  instr (xor_r32 .edx .edx),
  instr (mov_r32 .eax 43), -- SYS_accept
  instr syscall_op,
  instr (mov_mem64_disp .rsp 0x28 .rax), -- Save client socket

  -- 7. recv/read(client_fd, buf = RSP + 0x40, count = 128)
  instr (mov_reg64_mem64_disp .rdi .rsp 0x28),
  instr (lea_rsp .rsi 0x40),
  instr (mov_r32 .edx 128),
  instr (mov_r32 .eax 0),  -- SYS_read
  instr syscall_op,

  -- 8. Inspect received HTTP request line at RSP + 0x40
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
  lea_data .rsi "rdata_base",
  instr (add_r64_imm32 .rsi resp404Offset.toUInt32),
  instr (mov_r32 .edx resp404Bytes.size.toUInt32),
  jmp_label "do_send",

  label "send_root",
  lea_data .rsi "rdata_base",
  instr (add_r64_imm32 .rsi respRootOffset.toUInt32),
  instr (mov_r32 .edx respRootBytes.size.toUInt32),
  jmp_label "do_send",

  label "send_status",
  lea_data .rsi "rdata_base",
  instr (add_r64_imm32 .rsi respStatusOffset.toUInt32),
  instr (mov_r32 .edx respStatusBytes.size.toUInt32),

  label "do_send",
  -- 9. send/write(client_fd, buf = RSI, count = RDX)
  instr (mov_reg64_mem64_disp .rdi .rsp 0x28),
  instr (mov_r32 .eax 1), -- SYS_write
  instr syscall_op,

  -- 10. close(client_fd)
  instr (mov_reg64_mem64_disp .rdi .rsp 0x28),
  instr (mov_r32 .eax 3), -- SYS_close
  instr syscall_op,

  -- 11. Loop back to accept next connection
  jmp_near_label "accept_loop"
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
