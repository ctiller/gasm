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
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Syscall
import Gasm.Targets.X86_64.Semantics

namespace Gasm.Targets.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux x86-64 SYS_read syscall number (0). -/
def SYS_read : UInt64 := 0

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux x86-64 SYS_write syscall number (1). -/
def SYS_write : UInt64 := 1

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux x86-64 SYS_open syscall number (2). -/
def SYS_open : UInt64 := 2

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux x86-64 SYS_close syscall number (3). -/
def SYS_close : UInt64 := 3

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux x86-64 SYS_mmap syscall number (9). -/
def SYS_mmap : UInt64 := 9

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux x86-64 SYS_munmap syscall number (11). -/
def SYS_munmap : UInt64 := 11

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux x86-64 SYS_socket syscall number (41). -/
def SYS_socket : UInt64 := 41

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux x86-64 SYS_accept syscall number (43). -/
def SYS_accept : UInt64 := 43

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux x86-64 SYS_bind syscall number (49). -/
def SYS_bind : UInt64 := 49

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux x86-64 SYS_listen syscall number (50). -/
def SYS_listen : UInt64 := 50

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux x86-64 SYS_exit syscall number (60). -/
def SYS_exit : UInt64 := 60

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux x86-64 SYS_exit_group syscall number (231). -/
def SYS_exit_group : UInt64 := 231

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux sys_write hook: extracts buffer from memory, emits ConsoleEvent or NetEvent, and returns count in RAX. -/
def sysWriteHook {Event : Type} [Inject ConsoleEvent Event] [Inject NetEvent Event] (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let fd := s.gprs .rdi
  let bufAddr := s.gprs .rsi
  let count := (s.gprs .rdx).toNat
  let text := s.readString bufAddr count
  let nextRip := s.gprs .rcx
  if fd == 1 then
    let s' := { (s.setGpr64 .rax count.toUInt64) with rip := nextRip }
    (s', some (Inject.inject (ConsoleEvent.out text)))
  else if fd == 2 then
    let s' := { (s.setGpr64 .rax count.toUInt64) with rip := nextRip }
    (s', some (Inject.inject (ConsoleEvent.err text)))
  else if fd >= 100 then
    let s' := { (s.setGpr64 .rax count.toUInt64) with rip := nextRip }
    (s', some (Inject.inject (NetEvent.send text)))
  else
    -- Invalid fd: return -EBADF (-9)
    let s' := { (s.setGpr64 .rax 0xFFFFFFFFFFFFFFF7) with rip := nextRip }
    (s', none)

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux sys_exit hook: extracts exit code from RDI, halts machine state, and emits ProcessEvent. -/
def sysExitHook {Event : Type} [Inject ProcessEvent Event] (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let exitCode := (s.gprs .rdi).toUInt32
  let s' := { s with rip := 0, fault := some .halted }
  (s', some (Inject.inject (ProcessEvent.exit exitCode)))

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux sys_read hook: copies up to RDX bytes from stdinBuffer or incomingRequests and returns count in RAX. -/
def sysReadHook {Event : Type} [Inject NetEvent Event] (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let fd := s.gprs .rdi
  let nextRip := s.gprs .rcx
  if fd == 0 then
    let bufAddr := s.gprs .rsi
    let maxLen := (s.gprs .rdx).toNat
    let avail := s.stdinBuffer.size
    let count := min maxLen avail
    let readBytes := s.stdinBuffer.extract 0 count
    let remaining := s.stdinBuffer.extract count avail
    let s' := { (s.setGpr64 .rax count.toUInt64) with
      rip := nextRip,
      stdinBuffer := remaining,
      memory := X86_64Mem.writeBytes bufAddr readBytes.toList s.memory
    }
    (s', none)
  else if fd >= 100 then
    -- Short-read contract fix (`docs/READ_BINDER_CONTRACT.md`): honors RDX (the syscall's declared cap) instead of ignoring
    -- it and always delivering the whole queued logical request -- see Win32API.lean's
    -- `recvHook` for the full rationale; this is the Linux `sys_read`-on-socket analogue,
    -- built on the same `Gasm.Effects.splitBytes` primitive.
    let bufAddr := s.gprs .rsi
    let requested := (s.gprs .rdx).toNat
    match s.incomingRequests with
    | [] =>
      let s' := { (s.setGpr64 .rax 0) with rip := nextRip }
      (s', none)
    | req :: rest =>
      -- F1: shared delivery step -- see `Win32API.lean`'s `recvHook` and
      -- `Gasm.Effects.recvDeliver_lossless`.
      let (delivered, incomingRequests') := recvDeliver req requested rest
      let count := delivered.size
      let s' := { (s.setGpr64 .rax count.toUInt64) with
        rip := nextRip,
        incomingRequests := incomingRequests',
        memory := X86_64Mem.writeBytes bufAddr (toByteList delivered) s.memory
      }
      (s', some (Inject.inject (NetEvent.recv (bytesToPayload delivered))))
  else
    -- Invalid fd: return -EBADF (-9)
    let s' := { (s.setGpr64 .rax 0xFFFFFFFFFFFFFFF7) with rip := nextRip }
    (s', none)

/- REF: docs/TARGETS/LINUX.md#21-file-descriptor-state-machine -/
/-- Linux sys_open hook: returns a simulated open file descriptor in RAX. -/
def sysOpenHook {Event : Type} (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let nextRip := s.gprs .rcx
  let s' := { (s.setGpr64 .rax 3) with rip := nextRip }
  (s', none)

/- REF: docs/TARGETS/LINUX.md#21-file-descriptor-state-machine -/
/-- Linux sys_close hook: closes file descriptor or socket and returns 0 in RAX. -/
def sysCloseHook {Event : Type} [Inject NetEvent Event] (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let fd := s.gprs .rdi
  let nextRip := s.gprs .rcx
  if fd >= 100 then
    let s' := { (s.setGpr64 .rax 0) with rip := nextRip }
    (s', some (Inject.inject (NetEvent.close fd.toNat)))
  else
    let s' := { (s.setGpr64 .rax 0) with rip := nextRip }
    (s', none)

/- REF: docs/TARGETS/LINUX.md#22-memory-mapping-mmap-state-model -/
/-- Linux sys_mmap hook: returns simulated virtual memory address in RAX. -/
def sysMmapHook {Event : Type} (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let nextRip := s.gprs .rcx
  let s' := { (s.setGpr64 .rax 0x70000000) with rip := nextRip }
  (s', none)

/- REF: docs/TARGETS/LINUX.md#22-memory-mapping-mmap-state-model -/
/-- Linux sys_munmap hook: releases memory mapping and returns 0 in RAX. -/
def sysMunmapHook {Event : Type} (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let nextRip := s.gprs .rcx
  let s' := { (s.setGpr64 .rax 0) with rip := nextRip }
  (s', none)

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux sys_socket hook: creates simulated socket descriptor and returns 100 in RAX. -/
def sysSocketHook {Event : Type} (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let nextRip := s.gprs .rcx
  let s' := { (s.setGpr64 .rax 100) with rip := nextRip }
  (s', none)

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux sys_bind hook: binds socket to local address and returns 0 in RAX. -/
def sysBindHook {Event : Type} (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let nextRip := s.gprs .rcx
  let s' := { (s.setGpr64 .rax 0) with rip := nextRip }
  (s', none)

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux sys_listen hook: puts socket in listen mode and emits NetEvent.listen. -/
def sysListenHook {Event : Type} [Inject NetEvent Event] (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let nextRip := s.gprs .rcx
  let s' := { (s.setGpr64 .rax 0) with rip := nextRip }
  (s', some (Inject.inject (NetEvent.listen 8080)))

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux sys_accept hook: accepts connection and returns client socket in RAX. -/
def sysAcceptHook {Event : Type} [Inject NetEvent Event] (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  match s.incomingRequests with
  | [] =>
    let s_exit := { s with rip := 0 }
    (s_exit, none)
  | _ =>
    let nextRip := s.gprs .rcx
    let s' := { (s.setGpr64 .rax 101) with rip := nextRip }
    (s', some (Inject.inject (NetEvent.accept "127.0.0.1")))

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Pure Linux system call interceptor. -/
def linuxSyscallIntercept {Event : Type} [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event]
    (addr : Address) (s : X86_64MachineState) : Option (X86_64MachineState × Option Event) :=
  if addr == linuxSyscallEntry then
    match s.gprs .rax with
    | 0 => some (sysReadHook s)
    | 1 => some (sysWriteHook s)
    | 2 => some (sysOpenHook s)
    | 3 => some (sysCloseHook s)
    | 9 => some (sysMmapHook s)
    | 11 => some (sysMunmapHook s)
    | 41 => some (sysSocketHook s)
    | 43 => some (sysAcceptHook s)
    | 49 => some (sysBindHook s)
    | 50 => some (sysListenHook s)
    | 60 => some (sysExitHook s)
    | 231 => some (sysExitHook s)
    | _ =>
      let nextRip := s.gprs .rcx
      some ({ (s.setGpr64 .rax 0xFFFFFFFFFFFFFFDA) with rip := nextRip }, none) -- -ENOSYS (-38)
  else none

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Scoped Linux x86-64 external call interceptor helper dispatching Linux syscalls. -/
def linuxCallIntercept {Event : Type} [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event]
    (addr : Address) (s : X86_64MachineState) : Option (X86_64MachineState × Option Event) :=
  linuxSyscallIntercept addr s

end Gasm.Targets.Linux
