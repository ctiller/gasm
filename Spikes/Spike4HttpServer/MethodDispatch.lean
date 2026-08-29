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
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.Assembler
import Spikes.Spike4HttpServer.Spec

/-!
# Shared x86-64 HTTP method-token dispatch for Spike 4

The Windows and Linux lowerings run byte-identical request-line inspection code; the only thing
that differs between them is the surrounding syscall/import ABI. That duplication is exactly how
the `/stat`-prefix routing bug (`docs/SPIKES/SPIKE4_HTTP_SERVER.md`) came to exist in
two targets at once and be fixed twice, so the method-validation prologue lives here, generated
once from `Spikes.Spike4HttpServer.allHttpMethods` (itself derived from `Stdlib.Http11.Method`),
and is spliced into both programs.

Contract of the emitted sequence, entered with the request bytes at `[RSP + bufDisp]`:

* clobbers `RAX`, `RCX`, `RDX`, `RSI` -- all caller-saved under both the Win64 and SysV ABIs and
  all dead at this point in both programs (the `recv`/`read` return value in `RAX` has already been
  range-checked, and every later use of `RCX`/`RDX`/`RSI` reloads them);
* on a recognised method token, jumps to `path_at_<n>` for that method's path offset `n`, which
  `methodPathWindowInstrs` defines so as to leave `RSI` pointing at the request target and fall
  through to the caller's routing label;
* on an unrecognised token, falls off the end of `methodValidationInstrs` -- the caller must place
  its 400 Bad Request path immediately after.
-/

namespace Spikes.Spike4HttpServer

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- Label naming the path-window setup block for one method-token length. Methods of equal token
    length share a block (`GET`/`PUT`, `HEAD`/`POST`, `TRACE`/`PATCH`, `CONNECT`/`OPTIONS`). -/
def methodPathLabel (off : Nat) : String :=
  s!"path_at_{off}"

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- Method-token validation: loads the first eight request bytes and tests them, masked to each
    token's own length, against every `Stdlib.Http11.Method` token followed by the request line's
    mandatory SP. A match jumps to that method's path-window block; no match falls through, which
    is where the caller's 400 Bad Request path must sit.

    The masked compare is exact on the token *and* its delimiter, so no token can match a mere
    prefix of a longer word (`"GETX / ..."` fails the `GET ` test because byte 3 is `X`, not SP) --
    the failure mode `docs/SPIKES/SPIKE4_HTTP_SERVER.md` found in the route dispatch,
    not repeated here. Near (`rel32`) conditional jumps are used because the nine blocks together
    span far more than a `rel8` displacement. -/
def methodValidationInstrs (bufDisp : Nat) : List SymbolicInstr :=
  instr (lea_rsp .rsi bufDisp.toUInt8) ::
    allHttpMethods.flatMap (fun m =>
      [ instr (mov_reg64_mem64_disp .rax .rsi 0),
        instr (mov_r64_imm64 .rdx (methodTokenMask m)),
        instr (and_r64 .rax .rdx),
        instr (mov_r64_imm64 .rcx (methodTokenWord m)),
        instr (cmp_r64 .rax .rcx),
        je_near_label (methodPathLabel (methodPathOffset m)) ])

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- One block per distinct method-token length: point `RSI` at the request target (immediately
    after the token and its SP) and jump to the caller's routing label. -/
def methodPathWindowInstrs (bufDisp : Nat) (routeLabel : String) : List SymbolicInstr :=
  methodPathOffsets.flatMap (fun off =>
    [ label (methodPathLabel off),
      instr (lea_rsp .rsi (bufDisp + off).toUInt8),
      instr (sub_r64_imm8 .r10 off.toUInt8),
      jmp_near_label routeLabel ])

/-- Validates the portion of an HTTP/1.1 request line not covered by the method dispatcher.
    `R10` holds the received byte count and `RSI` points at the target.  The scanner never reads
    beyond that count: it requires an origin-form target, finds its sole terminating SP, and then
    requires exactly `HTTP/1.1\\r\\n` before handing the original target pointer to routing. -/
def requestLineValidationInstrs (routeLabel badLabel : String) : List SymbolicInstr :=
  [ label "validate_request_line",
    instr (cmp_r64_imm8 .r10 0),
    jle_near_label badLabel,
    instr (mov_r64 .rdi .rsi),
    instr (movzx_r64_mem8 .rax .rsi 0),
    instr (cmp_r64_imm8 .rax 0x2F),
    jne_near_label badLabel,
    label "scan_request_target",
    instr (cmp_r64_imm8 .r10 0),
    jle_near_label badLabel,
    instr (movzx_r64_mem8 .rax .rsi 0),
    instr (cmp_r64_imm8 .rax 0x20),
    je_near_label "validate_http_version",
    instr (cmp_r64_imm8 .rax 0x0D),
    je_near_label badLabel,
    instr (cmp_r64_imm8 .rax 0x0A),
    je_near_label badLabel,
    instr (add_r64_imm8 .rsi 1),
    instr (sub_r64_imm8 .r10 1),
    jmp_near_label "scan_request_target",
    label "validate_http_version",
    instr (add_r64_imm8 .rsi 1),
    instr (sub_r64_imm8 .r10 1),
    instr (cmp_r64_imm8 .r10 10),
    jb_near_label badLabel,
    instr (mov_reg64_mem64_disp .rax .rsi 0),
    instr (mov_r64_imm64 .rcx 0x312E312F50545448),
    instr (cmp_r64 .rax .rcx),
    jne_near_label badLabel,
    instr (movzx_r64_mem8 .rax .rsi 8),
    instr (cmp_r64_imm8 .rax 0x0D),
    jne_near_label badLabel,
    instr (movzx_r64_mem8 .rax .rsi 9),
    instr (cmp_r64_imm8 .rax 0x0A),
    jne_near_label badLabel,
    instr (mov_r64 .rsi .rdi),
    jmp_near_label routeLabel ]

end Spikes.Spike4HttpServer
