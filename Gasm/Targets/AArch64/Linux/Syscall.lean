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
import Gasm.Effects.Inject
import Gasm.Effects.Console
import Gasm.Effects.Process
import Gasm.Effects.Network
import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.Instructions.System
import Gasm.Targets.AArch64.Semantics
import Gasm.Targets.AArch64.MemoryCell

namespace Gasm.Targets.AArch64.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Instructions

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def SYS_read : UInt64 := 63

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def SYS_write : UInt64 := 64

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def SYS_openat : UInt64 := 56

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def SYS_close : UInt64 := 57

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def SYS_mmap : UInt64 := 222

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def SYS_munmap : UInt64 := 215

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def SYS_socket : UInt64 := 198

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def SYS_accept : UInt64 := 202

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def SYS_bind : UInt64 := 200

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def SYS_listen : UInt64 := 201

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def SYS_exit : UInt64 := 93

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def SYS_exit_group : UInt64 := 94

private def getRegFin (s : AArch64MachineState) (i : Nat) : UInt64 :=
  if h : i < 31 then s.gprs ⟨i, h⟩ else 0

private def setRegFin (s : AArch64MachineState) (i : Nat) (v : UInt64) : AArch64MachineState :=
  if h : i < 31 then s.setGpr64 ⟨i, h⟩ v else s

/-- Reads a string from AArch64Memory starting at `bufAddr` for `count` bytes. -/
private def readStringFromMemory (m : AArch64Memory) (bufAddr : Address) (count : Nat) : String :=
  let rec loop (idx : Nat) (acc : List Char) : List Char :=
    match idx with
    | 0 => acc
    | idx + 1 =>
      let b := AArch64Mem.readByte m (bufAddr + idx.toUInt64)
      loop idx (Char.ofNat b.toNat :: acc)
  String.ofList (loop count [])

/-- Helper to write list of bytes into AArch64Memory. -/
private def writeBytesToMemory (bufAddr : Address) (bytes : List Byte) (m : AArch64Memory) : AArch64Memory :=
  let rec loop (addr : Address) (l : List Byte) (mem : AArch64Memory) : AArch64Memory :=
    match l with
    | [] => mem
    | b :: rest => loop (addr + 1) rest (AArch64Mem.writeByte mem addr b)
  loop bufAddr bytes m

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def sysWriteHook {Event : Type} [Inject ConsoleEvent Event] [Inject NetEvent Event] (s : AArch64MachineState) : AArch64MachineState × Option Event :=
  let fd := getRegFin s 0
  let bufAddr := getRegFin s 1
  let count := (getRegFin s 2).toNat
  let text := readStringFromMemory s.memory bufAddr count
  let nextPc := s.syscallReturnPc
  if fd == 1 then
    let s' := { (setRegFin s 0 count.toUInt64) with pc := nextPc }
    (s', some (Inject.inject (ConsoleEvent.out text)))
  else if fd == 2 then
    let s' := { (setRegFin s 0 count.toUInt64) with pc := nextPc }
    (s', some (Inject.inject (ConsoleEvent.err text)))
  else if fd >= 100 then
    let s' := { (setRegFin s 0 count.toUInt64) with pc := nextPc }
    (s', some (Inject.inject (NetEvent.send text)))
  else
    -- Invalid fd: return -EBADF (-9)
    let s' := { (setRegFin s 0 0xFFFFFFFFFFFFFFF7) with pc := nextPc }
    (s', none)

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def sysExitHook {Event : Type} [Inject ProcessEvent Event] (s : AArch64MachineState) : AArch64MachineState × Option Event :=
  let exitCode := (getRegFin s 0).toUInt32
  let s' := { s with pc := 0, fault := none, terminated := true, exitCode := exitCode }
  (s', some (Inject.inject (ProcessEvent.exit exitCode)))

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def sysReadHook {Event : Type} [Inject NetEvent Event] (s : AArch64MachineState) : AArch64MachineState × Option Event :=
  let fd := getRegFin s 0
  let nextPc := s.syscallReturnPc
  if fd == 0 then
    let bufAddr := getRegFin s 1
    let maxLen := (getRegFin s 2).toNat
    let avail := s.stdinBuffer.size
    let count := min maxLen avail
    let readBytes := s.stdinBuffer.extract 0 count
    let remaining := s.stdinBuffer.extract count avail
    let s' := { (setRegFin s 0 count.toUInt64) with
      pc := nextPc,
      stdinBuffer := remaining,
      memory := writeBytesToMemory bufAddr readBytes.toList s.memory
    }
    (s', none)
  else if fd >= 100 then
    let bufAddr := getRegFin s 1
    let requested := (getRegFin s 2).toNat
    match s.incomingRequests with
    | [] =>
      let s' := { (setRegFin s 0 0) with pc := nextPc }
      (s', none)
    | req :: rest =>
      let (delivered, incomingRequests') := recvDeliver req requested rest
      let count := delivered.size
      let s' := { (setRegFin s 0 count.toUInt64) with
        pc := nextPc,
        incomingRequests := incomingRequests',
        memory := writeBytesToMemory bufAddr (toByteList delivered) s.memory
      }
      (s', some (Inject.inject (NetEvent.recv (bytesToPayload delivered))))
  else
    let s' := { (setRegFin s 0 0xFFFFFFFFFFFFFFF7) with pc := nextPc }
    (s', none)

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def sysOpenatHook {Event : Type} (s : AArch64MachineState) : AArch64MachineState × Option Event :=
  let nextPc := s.syscallReturnPc
  let s' := { (setRegFin s 0 3) with pc := nextPc }
  (s', none)

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def sysCloseHook {Event : Type} [Inject NetEvent Event] (s : AArch64MachineState) : AArch64MachineState × Option Event :=
  let fd := getRegFin s 0
  let nextPc := s.syscallReturnPc
  if fd >= 100 then
    let s' := { (setRegFin s 0 0) with pc := nextPc }
    (s', some (Inject.inject (NetEvent.close fd.toNat)))
  else
    let s' := { (setRegFin s 0 0) with pc := nextPc }
    (s', none)

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def sysMmapHook {Event : Type} (s : AArch64MachineState) : AArch64MachineState × Option Event :=
  let nextPc := s.syscallReturnPc
  let s' := { (setRegFin s 0 0x70000000) with pc := nextPc }
  (s', none)

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def sysMunmapHook {Event : Type} (s : AArch64MachineState) : AArch64MachineState × Option Event :=
  let nextPc := s.syscallReturnPc
  let s' := { (setRegFin s 0 0) with pc := nextPc }
  (s', none)

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def sysSocketHook {Event : Type} (s : AArch64MachineState) : AArch64MachineState × Option Event :=
  let nextPc := s.syscallReturnPc
  let s' := { (setRegFin s 0 100) with pc := nextPc }
  (s', none)

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def sysBindHook {Event : Type} (s : AArch64MachineState) : AArch64MachineState × Option Event :=
  let nextPc := s.syscallReturnPc
  let s' := { (setRegFin s 0 0) with pc := nextPc }
  (s', none)

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def sysListenHook {Event : Type} [Inject NetEvent Event] (s : AArch64MachineState) : AArch64MachineState × Option Event :=
  let nextPc := s.syscallReturnPc
  let s' := { (setRegFin s 0 0) with pc := nextPc }
  (s', some (Inject.inject (NetEvent.listen 8080)))

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def sysAcceptHook {Event : Type} [Inject NetEvent Event] (s : AArch64MachineState) : AArch64MachineState × Option Event :=
  match s.incomingRequests with
  | [] =>
    let s_exit := { s with pc := 0 }
    (s_exit, none)
  | _ =>
    let nextPc := s.syscallReturnPc
    let s' := { (setRegFin s 0 101) with pc := nextPc }
    (s', some (Inject.inject (NetEvent.accept "127.0.0.1")))

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def linuxSyscallIntercept {Event : Type} [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event]
    (addr : Address) (s : AArch64MachineState) : Option (AArch64MachineState × Option Event) :=
  if addr == linuxSyscallEntry then
    let nr := s.getReg64 .x8
    if nr == SYS_read then some (sysReadHook s)
    else if nr == SYS_write then some (sysWriteHook s)
    else if nr == SYS_openat then some (sysOpenatHook s)
    else if nr == SYS_close then some (sysCloseHook s)
    else if nr == SYS_mmap then some (sysMmapHook s)
    else if nr == SYS_munmap then some (sysMunmapHook s)
    else if nr == SYS_socket then some (sysSocketHook s)
    else if nr == SYS_accept then some (sysAcceptHook s)
    else if nr == SYS_bind then some (sysBindHook s)
    else if nr == SYS_listen then some (sysListenHook s)
    else if nr == SYS_exit then some (sysExitHook s)
    else if nr == SYS_exit_group then some (sysExitHook s)
    else
      let nextPc := s.syscallReturnPc
      some ({ (setRegFin s 0 0xFFFFFFFFFFFFFFDA) with pc := nextPc }, none) -- -ENOSYS (-38)
  else none

end Gasm.Targets.AArch64.Linux
