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
import Gasm.Core.Arch
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Push
import Gasm.Targets.X86_64.Instructions.Pop
import Gasm.Targets.X86_64.Instructions.Div
import Gasm.Targets.X86_64.Instructions.Imul
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Instructions.Or
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Targets.X86_64.Instructions.Not
import Gasm.Targets.X86_64.Instructions.Neg
import Gasm.Targets.X86_64.Instructions.Shift
import Gasm.Targets.X86_64.Instructions.Test
import Gasm.Targets.X86_64.Instructions.Xchg
import Gasm.Targets.X86_64.Instructions.Cmov
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.Instructions.In
import Gasm.Targets.X86_64.Instructions.Out
import Gasm.Targets.X86_64.Instructions.Hlt
import Gasm.Targets.X86_64.Instructions.Syscall

namespace Gasm.Targets.X86_64

open Gasm.Core
open Gasm.Targets.X86_64.Instructions

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Decodes a single x86-64 instruction from a ByteArray starting at the specified byte offset.
    Returns the decoded instruction AST and the number of bytes consumed. -/
def decodeX86_64Instr (bytes : ByteArray) (offset : Nat) : Except String (X86_64Instr × Nat) :=
  match readUInt8 bytes offset with
  | .error e => .error e
  | .ok b0 =>
    let (hasRex, rexW, rexR, _rexX, rexB, curOffset) :=
      if isRex b0 then
        let (w, r, x, b) := parseRex b0
        (true, w, r, x, b, offset + 1)
      else
        (false, false, false, false, false, offset)

    match readUInt8 bytes curOffset with
    | .error e => .error e
    | .ok opcode =>

      -- 1. Unconditional RET (0xC3)
      if opcode == 0xC3 then
        .ok (ret_op, (curOffset - offset) + 1)

      -- 2. PUSH r64 (0x50 .. 0x57)
      else if opcode >= 0x50 && opcode <= 0x57 then
        let regCode := opcode - 0x50
        let r := codeToReg64 regCode rexB
        .ok (push_r64 r, (curOffset - offset) + 1)

      -- 3. POP r64 (0x58 .. 0x5F)
      else if opcode >= 0x58 && opcode <= 0x5F then
        let regCode := opcode - 0x58
        let r := codeToReg64 regCode rexB
        .ok (pop_r64 r, (curOffset - offset) + 1)

      -- 4. JMP rel8 (0xEB)
      else if opcode == 0xEB then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok disp8 => .ok (jmp_rel8 disp8, (curOffset - offset) + 2)

      -- 5. JMP rel32 (0xE9)
      else if opcode == 0xE9 then
        match readInt32LE bytes (curOffset + 1) with
        | .error e => .error e
        | .ok disp32 => .ok (jmp_rel32 disp32, (curOffset - offset) + 5)

      -- 5b. CALL rel32 (0xE8)
      else if opcode == 0xE8 then
        match readInt32LE bytes (curOffset + 1) with
        | .error e => .error e
        | .ok disp32 => .ok (call_rel32 disp32, (curOffset - offset) + 5)

      -- 6. Short Conditional Jumps (0x70 .. 0x7F)
      else if opcode == 0x72 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok disp8 => .ok (jb_rel8 disp8, (curOffset - offset) + 2)
      else if opcode == 0x73 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok disp8 => .ok (jae_rel8 disp8, (curOffset - offset) + 2)
      else if opcode == 0x74 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok disp8 => .ok (je_rel8 disp8, (curOffset - offset) + 2)
      else if opcode == 0x75 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok disp8 => .ok (jne_rel8 disp8, (curOffset - offset) + 2)
      else if opcode == 0x7C then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok disp8 => .ok (jl_rel8 disp8, (curOffset - offset) + 2)
      else if opcode == 0x7D then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok disp8 => .ok (jge_rel8 disp8, (curOffset - offset) + 2)
      else if opcode == 0x7E then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok disp8 => .ok (jle_rel8 disp8, (curOffset - offset) + 2)
      else if opcode == 0x7F then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok disp8 => .ok (jg_rel8 disp8, (curOffset - offset) + 2)
      else if opcode == 0x76 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok disp8 => .ok (jbe_rel8 disp8, (curOffset - offset) + 2)
      else if opcode == 0x77 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok disp8 => .ok (ja_rel8 disp8, (curOffset - offset) + 2)

      -- 7. MOV reg, imm (0xB8 .. 0xBF)
      else if opcode >= 0xB8 && opcode <= 0xBF then
        let regCode := opcode - 0xB8
        if rexW then
          let dst := codeToReg64 regCode rexB
          match readUInt64LE bytes (curOffset + 1) with
          | .error e => .error e
          | .ok imm64 => .ok (mov_r64_imm64 dst imm64, (curOffset - offset) + 9)
        else
          let dst := codeToReg32 regCode rexB
          match readUInt32LE bytes (curOffset + 1) with
          | .error e => .error e
          | .ok imm32 => .ok (mov_r32 dst imm32, (curOffset - offset) + 5)

      -- 8. Two-byte Opcode Escape (0x0F)
      else if opcode == 0x0F then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok op2 =>
          if op2 == 0x05 then
            .ok (syscall_op, (curOffset - offset) + 2)
          else if op2 == 0x82 then
            match readInt32LE bytes (curOffset + 2) with
            | .error e => .error e
            | .ok disp32 => .ok (jb_rel32 disp32, (curOffset - offset) + 6)
          else if op2 == 0x83 then
            match readInt32LE bytes (curOffset + 2) with
            | .error e => .error e
            | .ok disp32 => .ok (jae_rel32 disp32, (curOffset - offset) + 6)
          else if op2 == 0x84 then
            match readInt32LE bytes (curOffset + 2) with
            | .error e => .error e
            | .ok disp32 => .ok (je_rel32 disp32, (curOffset - offset) + 6)
          else if op2 == 0x85 then
            match readInt32LE bytes (curOffset + 2) with
            | .error e => .error e
            | .ok disp32 => .ok (jne_rel32 disp32, (curOffset - offset) + 6)
          else if op2 == 0x87 then
            match readInt32LE bytes (curOffset + 2) with
            | .error e => .error e
            | .ok disp32 => .ok (ja_rel32 disp32, (curOffset - offset) + 6)
          else if op2 == 0x8D then
            match readInt32LE bytes (curOffset + 2) with
            | .error e => .error e
            | .ok disp32 => .ok (jge_rel32 disp32, (curOffset - offset) + 6)
          else if op2 == 0x8E then
            match readInt32LE bytes (curOffset + 2) with
            | .error e => .error e
            | .ok disp32 => .ok (jle_rel32 disp32, (curOffset - offset) + 6)
          else if op2 == 0xAF then
            match readUInt8 bytes (curOffset + 2) with
            | .error e => .error e
            | .ok modrmByte =>
              let (_, reg, rm) := extractModRM modrmByte
              let dst := codeToReg64 reg rexR
              let src := codeToReg64 rm rexB
              .ok (imul_r64 dst src, (curOffset - offset) + 3)
          else if op2 == 0xB6 then
            match readUInt8 bytes (curOffset + 2) with
            | .error e => .error e
            | .ok modrmByte =>
              let (mod, reg, rm) := extractModRM modrmByte
              let dstReg := codeToReg64 reg rexR
              if mod == 0 then
                if rm == 4 then
                  match readUInt8 bytes (curOffset + 3) with
                  | .error e => .error e
                  | .ok _sib =>
                    let basePtr := codeToReg64 4 rexB
                    .ok (movzx_r64_mem8 dstReg basePtr 0, (curOffset - offset) + 4)
                else
                  let basePtr := codeToReg64 rm rexB
                  .ok (movzx_r64_mem8 dstReg basePtr 0, (curOffset - offset) + 3)
              else if mod == 1 then
                if rm == 4 then
                  match readUInt8 bytes (curOffset + 3) with
                  | .error e => .error e
                  | .ok _sib =>
                    match readUInt8 bytes (curOffset + 4) with
                    | .error e => .error e
                    | .ok disp8 =>
                      let basePtr := codeToReg64 4 rexB
                      .ok (movzx_r64_mem8 dstReg basePtr disp8, (curOffset - offset) + 5)
                else
                  match readUInt8 bytes (curOffset + 3) with
                  | .error e => .error e
                  | .ok disp8 =>
                    let basePtr := codeToReg64 rm rexB
                    .ok (movzx_r64_mem8 dstReg basePtr disp8, (curOffset - offset) + 4)
              else
                .error "Unsupported mod field for 0F B6 MOVZX"
          else if op2 >= 0x40 && op2 <= 0x4F then
            match readUInt8 bytes (curOffset + 2) with
            | .error e => .error e
            | .ok modrmByte =>
              let (_, reg, rm) := extractModRM modrmByte
              let dst := codeToReg64 reg rexR
              let src := codeToReg64 rm rexB
              if op2 == 0x42 then .ok (cmovb_r64 dst src, (curOffset - offset) + 3)
              else if op2 == 0x43 then .ok (cmovae_r64 dst src, (curOffset - offset) + 3)
              else if op2 == 0x44 then .ok (cmove_r64 dst src, (curOffset - offset) + 3)
              else if op2 == 0x45 then .ok (cmovne_r64 dst src, (curOffset - offset) + 3)
              else if op2 == 0x4C then .ok (cmovl_r64 dst src, (curOffset - offset) + 3)
              else if op2 == 0x4D then .ok (cmovge_r64 dst src, (curOffset - offset) + 3)
              else if op2 == 0x4E then .ok (cmovle_r64 dst src, (curOffset - offset) + 3)
              else if op2 == 0x4F then .ok (cmovg_r64 dst src, (curOffset - offset) + 3)
              else .error s!"Unsupported CMOV opcode 0x0F 0x{String.ofList (Nat.toDigits 16 op2.toNat)}"
          else
            .error s!"Unsupported 2-byte opcode 0x0F 0x{String.ofList (Nat.toDigits 16 op2.toNat)}"

      -- 9. ADD r64, r64 (0x01)
      else if opcode == 0x01 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (_, reg, rm) := extractModRM modrmByte
          let dst := codeToReg64 rm rexB
          let src := codeToReg64 reg rexR
          .ok (add_r64 dst src, (curOffset - offset) + 2)

      -- 10. OR r64, r64 (0x09)
      else if opcode == 0x09 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (_, reg, rm) := extractModRM modrmByte
          let dst := codeToReg64 rm rexB
          let src := codeToReg64 reg rexR
          .ok (or_r64 dst src, (curOffset - offset) + 2)

      -- 11. AND r64, r64 (0x21)
      else if opcode == 0x21 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (_, reg, rm) := extractModRM modrmByte
          let dst := codeToReg64 rm rexB
          let src := codeToReg64 reg rexR
          .ok (and_r64 dst src, (curOffset - offset) + 2)

      -- 12. SUB r64, r64 (0x29)
      else if opcode == 0x29 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (_, reg, rm) := extractModRM modrmByte
          let dst := codeToReg64 rm rexB
          let src := codeToReg64 reg rexR
          .ok (sub_r64 dst src, (curOffset - offset) + 2)

      -- 13. XOR r32, r32 (0x31)
      else if opcode == 0x31 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (_, reg, rm) := extractModRM modrmByte
          let dst := codeToReg32 rm rexB
          let src := codeToReg32 reg rexR
          .ok (xor_r32 dst src, (curOffset - offset) + 2)

      -- 14. CMP r64, r64 (0x39)
      else if opcode == 0x39 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (_, reg, rm) := extractModRM modrmByte
          let dst := codeToReg64 rm rexB
          let src := codeToReg64 reg rexR
          .ok (cmp_r64 dst src, (curOffset - offset) + 2)

      -- 15. TEST r64, r64 (0x85)
      else if opcode == 0x85 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (_, reg, rm) := extractModRM modrmByte
          let dst := codeToReg64 rm rexB
          let src := codeToReg64 reg rexR
          .ok (test_r64 dst src, (curOffset - offset) + 2)

      -- 16. XCHG r64, r64 (0x87)
      else if opcode == 0x87 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (_, reg, rm) := extractModRM modrmByte
          let dst := codeToReg64 rm rexB
          let src := codeToReg64 reg rexR
          .ok (xchg_r64 dst src, (curOffset - offset) + 2)

      -- 17. MOV byte ptr [mem], reg8 (0x88)
      else if opcode == 0x88 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (mod, reg, rm) := extractModRM modrmByte
          let srcReg := codeToReg64 reg rexR
          if mod == 0 && rm == 4 then
            match readUInt8 bytes (curOffset + 2) with
            | .error e => .error e
            | .ok _sib =>
              let dstPtr := codeToReg64 4 rexB
              .ok (mov_mem8 dstPtr srcReg, (curOffset - offset) + 3)
          else if mod == 1 && rm == 5 then
            match readUInt8 bytes (curOffset + 2) with
            | .error e => .error e
            | .ok _disp =>
              let dstPtr := codeToReg64 5 rexB
              .ok (mov_mem8 dstPtr srcReg, (curOffset - offset) + 3)
          else if mod == 0 then
            let dstPtr := codeToReg64 rm rexB
            .ok (mov_mem8 dstPtr srcReg, (curOffset - offset) + 2)
          else
            .error "Unsupported mod field for 0x88 MOV"

      -- 18. MOV r64, r64 OR MOV [base + disp], srcReg (0x89)
      else if opcode == 0x89 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (mod, reg, rm) := extractModRM modrmByte
          if mod == 3 then
            let dst := codeToReg64 rm rexB
            let src := codeToReg64 reg rexR
            .ok (mov_r64 dst src, (curOffset - offset) + 2)
          else if mod == 0 then
            let srcReg := codeToReg64 reg rexR
            if rm == 4 then
              match readUInt8 bytes (curOffset + 2) with
              | .error e => .error e
              | .ok _sib =>
                let basePtr := codeToReg64 4 rexB
                .ok (mov_mem64_disp basePtr 0 srcReg, (curOffset - offset) + 3)
            else
              let basePtr := codeToReg64 rm rexB
              .ok (mov_mem64_disp basePtr 0 srcReg, (curOffset - offset) + 2)
          else if mod == 1 then
            let srcReg := codeToReg64 reg rexR
            if rm == 4 then
              match readUInt8 bytes (curOffset + 2) with
              | .error e => .error e
              | .ok _sib =>
                match readUInt8 bytes (curOffset + 3) with
                | .error e => .error e
                | .ok disp8 =>
                  let basePtr := codeToReg64 4 rexB
                  .ok (mov_mem64_disp basePtr disp8 srcReg, (curOffset - offset) + 4)
            else
              match readUInt8 bytes (curOffset + 2) with
              | .error e => .error e
              | .ok disp8 =>
                let basePtr := codeToReg64 rm rexB
                .ok (mov_mem64_disp basePtr disp8 srcReg, (curOffset - offset) + 3)
          else
            .error "Unsupported mod field for 0x89 MOV"

      -- 19. MOV dstReg64, [base + disp] (0x8B, REX.W=1) OR MOV dstReg32, [RSP + disp8] (0x8B, REX.W=0)
      -- NOTE: rexW is load-bearing here. Ignoring it previously caused 0x8B to always decode into
      -- the 64-bit MovReg64Mem64Disp structure even when REX.W=0, silently misdecoding a 32-bit
      -- zero-extending load (MovReg32RspDisp32) as a 64-bit one (wrong width, wrong semantics).
      else if opcode == 0x8B then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (mod, reg, rm) := extractModRM modrmByte
          if rexW then
            let dstReg := codeToReg64 reg rexR
            if mod == 0 then
              if rm == 4 then
                match readUInt8 bytes (curOffset + 2) with
                | .error e => .error e
                | .ok _sib =>
                  let basePtr := codeToReg64 4 rexB
                  .ok (mov_reg64_mem64_disp dstReg basePtr 0, (curOffset - offset) + 3)
              else
                let basePtr := codeToReg64 rm rexB
                .ok (mov_reg64_mem64_disp dstReg basePtr 0, (curOffset - offset) + 2)
            else if mod == 1 then
              if rm == 4 then
                match readUInt8 bytes (curOffset + 2) with
                | .error e => .error e
                | .ok _sib =>
                  match readUInt8 bytes (curOffset + 3) with
                  | .error e => .error e
                  | .ok disp8 =>
                    let basePtr := codeToReg64 4 rexB
                    .ok (mov_reg64_mem64_disp dstReg basePtr disp8, (curOffset - offset) + 4)
              else
                match readUInt8 bytes (curOffset + 2) with
                | .error e => .error e
                | .ok disp8 =>
                  let basePtr := codeToReg64 rm rexB
                  .ok (mov_reg64_mem64_disp dstReg basePtr disp8, (curOffset - offset) + 3)
            else
              .error "Unsupported mod field for 0x8B MOV"
          else
            -- 32-bit form: the only encodable pattern is MovReg32RspDisp32's fixed
            -- [RSP + disp8] SIB encoding (mod=1, rm=4, base=4), disp8 always present.
            if mod == 1 && rm == 4 then
              match readUInt8 bytes (curOffset + 2) with
              | .error e => .error e
              | .ok _sib =>
                match readUInt8 bytes (curOffset + 3) with
                | .error e => .error e
                | .ok disp8 =>
                  let dstReg32 := codeToReg32 reg rexR
                  .ok (mov_r32_rsp dstReg32 disp8, (curOffset - offset) + 4)
            else
              .error "Unsupported mod/rm field for 32-bit 0x8B MOV"

      -- 20. LEA (0x8D)
      -- NOTE: rexB is load-bearing for the mod=0/1/2, rm=4 (SIB, base field = 4) forms, exactly
      -- like the 0x8B and 0xC7 SIB-base-4 forms: that SIB base code is shared by RSP (rexB=false,
      -- the only base LeaRspDisp/LeaRspDisp32 can represent) and R12 (rexB=true). There is no
      -- "LEA reg, [R12+disp]" structure in this codebase to decode into, so rather than silently
      -- misdecoding an R12-based encoding as an RSP-based one (as this branch previously did),
      -- reject those bytes outright — silent misdecode is the one prohibited outcome here, not
      -- "not yet supported".
      else if opcode == 0x8D then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (mod, reg, rm) := extractModRM modrmByte
          let dst := codeToReg64 reg (if hasRex then rexR else false)
          if mod == 0 && rm == 5 then
            match readInt32LE bytes (curOffset + 2) with
            | .error e => .error e
            | .ok disp32 => .ok (lea_rip dst disp32, (curOffset - offset) + 6)
          else if mod == 0 && rm == 4 then
            if rexB then
              .error "Unsupported base register (R12 via REX.B) for 0x8D LEA SIB form"
            else
              match readUInt8 bytes (curOffset + 2) with
              | .error e => .error e
              | .ok _sib => .ok (lea_rsp dst 0, (curOffset - offset) + 3)
          else if mod == 1 && rm == 4 then
            if rexB then
              .error "Unsupported base register (R12 via REX.B) for 0x8D LEA SIB form"
            else
              match readUInt8 bytes (curOffset + 2) with
              | .error e => .error e
              | .ok _sib =>
                match readUInt8 bytes (curOffset + 3) with
                | .error e => .error e
                | .ok disp8 => .ok (lea_rsp dst disp8, (curOffset - offset) + 4)
          else if mod == 2 && rm == 4 then
            if rexB then
              .error "Unsupported base register (R12 via REX.B) for 0x8D LEA SIB form"
            else
              match readUInt8 bytes (curOffset + 2) with
              | .error e => .error e
              | .ok _sib =>
                match readInt32LE bytes (curOffset + 3) with
                | .error e => .error e
                | .ok disp32 => .ok (lea_rsp32 dst disp32, (curOffset - offset) + 7)
          else
            .error "Unsupported addressing mode for 0x8D LEA"

      -- 21. Shift Group (0xC1)
      else if opcode == 0xC1 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (_, reg, rm) := extractModRM modrmByte
          let dst := codeToReg64 rm rexB
          match readUInt8 bytes (curOffset + 2) with
          | .error e => .error e
          | .ok imm8 =>
            if reg == 4 then .ok (shl_r64_imm8 dst imm8, (curOffset - offset) + 3)
            else if reg == 5 then .ok (shr_r64_imm8 dst imm8, (curOffset - offset) + 3)
            else if reg == 7 then .ok (sar_r64_imm8 dst imm8, (curOffset - offset) + 3)
            else .error "Unsupported shift sub-opcode in 0xC1"

      -- 21b. Shift Group by CL (0xD3)
      else if opcode == 0xD3 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (_, reg, rm) := extractModRM modrmByte
          let dst := codeToReg64 rm rexB
          if reg == 4 then .ok (shl_r64_cl dst, (curOffset - offset) + 2)
          else if reg == 5 then .ok (shr_r64_cl dst, (curOffset - offset) + 2)
          else .error "Unsupported shift sub-opcode in 0xD3"

      -- 22. MOV byte ptr [rsp + disp], val (0xC6)
      -- NOTE: rexB is load-bearing here for the same reason as the 0x8D LEA SIB-base-4 forms
      -- above: MovRspDispByte can only represent an RSP base (rexB=false); an R12-based encoding
      -- (rexB=true) has no structure to decode into, so it is rejected rather than misdecoded.
      else if opcode == 0xC6 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (mod, _, rm) := extractModRM modrmByte
          if rm == 4 then
            if rexB then
              .error "Unsupported base register (R12 via REX.B) for 0xC6 MOV SIB form"
            else
              match readUInt8 bytes (curOffset + 2) with
              | .error e => .error e
              | .ok _sib =>
                if mod == 0 then
                  match readUInt8 bytes (curOffset + 3) with
                  | .error e => .error e
                  | .ok val => .ok (mov_rsp_byte 0 val, (curOffset - offset) + 4)
                else if mod == 1 then
                  match readUInt8 bytes (curOffset + 3) with
                  | .error e => .error e
                  | .ok disp8 =>
                    match readUInt8 bytes (curOffset + 4) with
                    | .error e => .error e
                    | .ok val => .ok (mov_rsp_byte disp8 val, (curOffset - offset) + 5)
                else
                  .error "Unsupported mod field for 0xC6 MOV"
          else
            .error "Unsupported non-RSP rm field for 0xC6 MOV"

      -- 23. MOV [mem], imm32 (0xC7)
      else if opcode == 0xC7 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (mod, _, rm) := extractModRM modrmByte
          -- NOTE: rexB is load-bearing when rm==4 (SIB, base field = 4). That SIB base code is
          -- shared by RSP (rexB=false, the fixed-RSP MovRspDispImm32/64 helpers, which never set
          -- REX.B) and R12 (rexB=true, the general MovMem64DispImm32, whose base register is
          -- derived via `codeToReg64 4 rexB` exactly like every other SIB-base-4 path in this
          -- decoder, rather than hardcoded). Ignoring rexB here previously canonicalized every
          -- SIB-base-4 write to the RSP helper even when the encoded base was actually R12 —
          -- silently discarding the true base register.
          if mod == 0 then
            if rm == 4 then
              match readUInt8 bytes (curOffset + 2) with
              | .error e => .error e
              | .ok _sib =>
                match readUInt32LE bytes (curOffset + 3) with
                | .error e => .error e
                | .ok imm32 =>
                  if rexB then
                    .ok (mov_mem64_disp_imm (codeToReg64 4 rexB) 0 imm32, (curOffset - offset) + 7)
                  else if rexW then
                    .ok (mov_rsp64 0 imm32, (curOffset - offset) + 7)
                  else
                    .ok (mov_rsp32 0 imm32, (curOffset - offset) + 7)
            else
              let basePtr := codeToReg64 rm rexB
              match readUInt32LE bytes (curOffset + 2) with
              | .error e => .error e
              | .ok imm32 =>
                .ok (mov_mem64_disp_imm basePtr 0 imm32, (curOffset - offset) + 6)
          else if mod == 1 then
            if rm == 4 then
              match readUInt8 bytes (curOffset + 2) with
              | .error e => .error e
              | .ok _sib =>
                match readUInt8 bytes (curOffset + 3) with
                | .error e => .error e
                | .ok disp8 =>
                  match readUInt32LE bytes (curOffset + 4) with
                  | .error e => .error e
                  | .ok imm32 =>
                    if rexB then
                      .ok (mov_mem64_disp_imm (codeToReg64 4 rexB) disp8 imm32, (curOffset - offset) + 8)
                    else if rexW then
                      .ok (mov_rsp64 disp8 imm32, (curOffset - offset) + 8)
                    else
                      .ok (mov_rsp32 disp8 imm32, (curOffset - offset) + 8)
            else
              let basePtr := codeToReg64 rm rexB
              match readUInt8 bytes (curOffset + 2) with
              | .error e => .error e
              | .ok disp8 =>
                match readUInt32LE bytes (curOffset + 3) with
                | .error e => .error e
                | .ok imm32 =>
                  .ok (mov_mem64_disp_imm basePtr disp8 imm32, (curOffset - offset) + 7)
          else
            .error "Unsupported mod field for 0xC7 MOV"

      -- 24. Group 1 Immediate DWord (0x81): ADD /0, OR /1, SUB /5, CMP /7
      else if opcode == 0x81 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (_, reg, rm) := extractModRM modrmByte
          let dst := codeToReg64 rm rexB
          match readUInt32LE bytes (curOffset + 2) with
          | .error e => .error e
          | .ok imm32 =>
            if reg == 0 then
              if dst == .rsp && !rexB then
                .ok (add_rsp32 imm32, (curOffset - offset) + 6)
              else
                .ok (add_r64_imm32 dst imm32, (curOffset - offset) + 6)
            else if reg == 1 then .ok (or_r64_imm32 dst imm32, (curOffset - offset) + 6)
            else if reg == 5 then
              if dst == .rsp && !rexB then
                .ok (sub_rsp32 imm32, (curOffset - offset) + 6)
              else
                .ok (sub_r64_imm32 dst imm32, (curOffset - offset) + 6)
            else if reg == 7 then .ok (cmp_r64_imm32 dst imm32, (curOffset - offset) + 6)
            else .error s!"Unsupported sub-opcode {reg} for 0x81"

      -- 25. Group 1 Immediate Byte (0x83)
      else if opcode == 0x83 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (_, reg, rm) := extractModRM modrmByte
          let dst := codeToReg64 rm rexB
          match readUInt8 bytes (curOffset + 2) with
          | .error e => .error e
          | .ok imm8 =>
            if reg == 0 then
              if dst == .rsp && !rexB then
                .ok (add_rsp imm8, (curOffset - offset) + 3)
              else
                .ok (add_r64_imm8 dst imm8, (curOffset - offset) + 3)
            else if reg == 1 then .ok (or_r64_imm8 dst imm8, (curOffset - offset) + 3)
            else if reg == 4 then .ok (and_r64_imm8 dst imm8, (curOffset - offset) + 3)
            else if reg == 5 then
              if dst == .rsp && !rexB then
                .ok (sub_rsp imm8, (curOffset - offset) + 3)
              else
                .ok (sub_r64_imm8 dst imm8, (curOffset - offset) + 3)
            else if reg == 7 then .ok (cmp_r64_imm8 dst imm8, (curOffset - offset) + 3)
            else .error s!"Unsupported sub-opcode {reg} for 0x83"

      -- 26. Group 3 Unary & Test (0xF7)
      else if opcode == 0xF7 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          let (_, reg, rm) := extractModRM modrmByte
          let dst := codeToReg64 rm rexB
          if reg == 0 then
            match readUInt32LE bytes (curOffset + 2) with
            | .error e => .error e
            | .ok imm32 => .ok (test_r64_imm32 dst imm32, (curOffset - offset) + 6)
          else if reg == 2 then .ok (not_r64 dst, (curOffset - offset) + 2)
          else if reg == 3 then .ok (neg_r64 dst, (curOffset - offset) + 2)
          else if reg == 6 then .ok (div_r64 dst, (curOffset - offset) + 2)
          else .error s!"Unsupported sub-opcode {reg} for 0xF7"

      -- 27. Indirect CALL [RIP + disp32] (0xFF /2)
      else if opcode == 0xFF then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok modrmByte =>
          if modrmByte == 0x15 then
            match readInt32LE bytes (curOffset + 2) with
            | .error e => .error e
            | .ok disp32 => .ok (call_rip disp32, (curOffset - offset) + 6)
          else
            .error "Unsupported modrm for 0xFF CALL"

      -- 28. IN AL, imm8 (0xE4)
      else if opcode == 0xE4 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok port => .ok (in_al_imm8 port, (curOffset - offset) + 2)

      -- 29. IN EAX, imm8 (0xE5)
      else if opcode == 0xE5 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok port => .ok (in_eax_imm8 port, (curOffset - offset) + 2)

      -- 30. OUT imm8, AL (0xE6)
      else if opcode == 0xE6 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok port => .ok (out_imm8_al port, (curOffset - offset) + 2)

      -- 31. OUT imm8, EAX (0xE7)
      else if opcode == 0xE7 then
        match readUInt8 bytes (curOffset + 1) with
        | .error e => .error e
        | .ok port => .ok (out_imm8_eax port, (curOffset - offset) + 2)

      -- 32. IN AL, DX (0xEC)
      else if opcode == 0xEC then
        .ok (in_al_dx, (curOffset - offset) + 1)

      -- 33. IN EAX, DX (0xED)
      else if opcode == 0xED then
        .ok (in_eax_dx, (curOffset - offset) + 1)

      -- 34. OUT DX, AL (0xEE)
      else if opcode == 0xEE then
        .ok (out_dx_al, (curOffset - offset) + 1)

      -- 35. OUT DX, EAX (0xEF)
      else if opcode == 0xEF then
        .ok (out_dx_eax, (curOffset - offset) + 1)

      -- 36. HLT (0xF4)
      else if opcode == 0xF4 then
        .ok (hlt_op, (curOffset - offset) + 1)

      else
        .error s!"Unsupported x86-64 opcode byte 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} at offset {curOffset}"

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Disassembles a complete ByteArray stream of x86-64 instructions until the buffer is exhausted. -/
def disassembleX86_64 (bytes : ByteArray) : Except String (List X86_64Instr) :=
  let rec loop (fuel : Nat) (offset : Nat) (acc : List X86_64Instr) : Except String (List X86_64Instr) :=
    match fuel with
    | 0 => Except.error "Disassembly fuel exhausted"
    | fuel + 1 =>
      if offset >= bytes.size then
        Except.ok acc
      else
        match decodeX86_64Instr bytes offset with
        | .error err => Except.error err
        | .ok (instr, len) =>
          if len == 0 then
            Except.error s!"Zero-length instruction encountered at offset {offset}"
          else
            loop fuel (offset + len) (acc ++ [instr])
  loop (bytes.size + 1) 0 []

/- REF: docs/TARGETS/TARGET_MODEL.md#1-vertical-slice-target-structure -/
instance : DisassemblableArch X86_64 where
  decodeInstr := decodeX86_64Instr
  disassemble := disassembleX86_64

end Gasm.Targets.X86_64
