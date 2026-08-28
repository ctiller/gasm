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
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.Windows.Emitter

namespace Gasm.Targets.Windows

open Gasm.Core
open Gasm.Effects
open Gasm.Targets.X86_64

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Standard Win32 API function descriptor. -/
structure Win32Function where
  moduleName : String
  symbolName : String
  deriving DecidableEq, Repr, Inhabited

/- REF: windows-exitprocess#syntax -/
/-- Win32 ExitProcess API descriptor. -/
def ExitProcessDef : Win32Function := {
  moduleName := "KERNEL32.dll"
  symbolName := "ExitProcess"
}

/- REF: windows-getstdhandle#syntax -/
/-- Win32 GetStdHandle API descriptor. -/
def GetStdHandleDef : Win32Function := {
  moduleName := "KERNEL32.dll"
  symbolName := "GetStdHandle"
}

/- REF: windows-readfile#syntax -/
/-- Win32 ReadFile API descriptor. -/
def ReadFileDef : Win32Function := {
  moduleName := "KERNEL32.dll"
  symbolName := "ReadFile"
}

/- REF: windows-writefile#syntax -/
/-- Win32 WriteFile API descriptor. -/
def WriteFileDef : Win32Function := {
  moduleName := "KERNEL32.dll"
  symbolName := "WriteFile"
}

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Win32 VirtualAlloc API descriptor. -/
def VirtualAllocDef : Win32Function := {
  moduleName := "KERNEL32.dll"
  symbolName := "VirtualAlloc"
}

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Win32 VirtualFree API descriptor. -/
def VirtualFreeDef : Win32Function := {
  moduleName := "KERNEL32.dll"
  symbolName := "VirtualFree"
}

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Pops the 8-byte return address from stack and increments RSP by 8 upon API return. -/
def popReturnAddress (s : X86_64MachineState) : X86_64MachineState :=
  let (returnRip, s') := s.pop64
  { s' with rip := returnRip }

/- REF: windows-getstdhandle#return-value -/
/-- Win32 GetStdHandle call hook: returns standard output console pseudo-handle. -/
def getStdHandleHook {Event : Type} (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let handle := match (s.gprs .rcx).toUInt32 with
    | 0xFFFFFFF6 => 1 -- STD_INPUT_HANDLE (-10)
    | 0xFFFFFFF5 => 1 -- STD_OUTPUT_HANDLE (-11)
    | 0xFFFFFFF4 => 2 -- STD_ERROR_HANDLE (-12)
    | _          => 1
  let s' := (popReturnAddress s).setGpr64 .rax handle
  (s', none)

/- REF: windows-readfile#parameters -/
/-- Win32 ReadFile call hook: copies up to R8 bytes from s.stdinBuffer into memory at RDX, updates lpNumberOfBytesRead at R9, and returns 1 in RAX. -/
def readFileHook {Event : Type} (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let bufAddr := s.gprs .rdx
  let maxLen := (s.gprs .r8).toNat
  let lpRead := s.gprs .r9
  let avail := s.stdinBuffer.size
  let count := min maxLen avail
  let readBytes := s.stdinBuffer.extract 0 count
  let remaining := s.stdinBuffer.extract count avail
  let s_popped := popReturnAddress s
  -- Order matches the pre-hook code's `if` precedence exactly: the destination-buffer write
  -- wins on any overlap with the [lpRead, lpRead+4) count-output word (checked first in the
  -- original raw-lambda chain), so lpRead's word is written first and the buffer bytes second.
  let s'' := if lpRead == 0 then s_popped.memory else X86_64Mem.write .w32 lpRead count.toUInt64 s_popped.memory
  let s''' := X86_64Mem.writeBytes bufAddr readBytes.toList s''
  let s' := { (s_popped.setGpr64 .rax 1) with
    stdinBuffer := remaining,
    memory := s'''
  }
  (s', none)

/- REF: windows-writefile#parameters -/
/-- Win32 WriteFile call hook: extracts buffer from memory, updates lpNumberOfBytesWritten, and emits strongly-typed ConsoleEvent. -/
def writeFileHook {Event : Type} [Inject ConsoleEvent Event] (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let bufAddr := s.gprs .rdx
  let len := (s.gprs .r8).toNat
  let lpWritten := s.gprs .r9
  let text := s.readString bufAddr len
  let s_popped := popReturnAddress s
  let s' := { (s_popped.setGpr64 .rax 1) with
    memory := if lpWritten == 0 then s_popped.memory else X86_64Mem.write .w32 lpWritten len.toUInt64 s_popped.memory
  }
  (s', some (Inject.inject (ConsoleEvent.out text)))

/- REF: windows-exitprocess#parameters -/
/-- Win32 ExitProcess call hook: extracts exit code from RCX and emits ProcessEvent. -/
def exitProcessHook {Event : Type} [Inject ProcessEvent Event] (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let exitCode := (s.gprs .rcx).toUInt32
  (s, some (Inject.inject (ProcessEvent.exit exitCode)))

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Win32 VirtualAlloc call hook: returns simulated virtual memory page pointer in RAX. -/
def virtualAllocHook {Event : Type} (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let s_popped := popReturnAddress s
  let s' := s_popped.setGpr64 .rax 0x20000000
  (s', none)

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Win32 VirtualFree call hook: releases virtual memory pages and returns 1 in RAX. -/
def virtualFreeHook {Event : Type} (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let s_popped := popReturnAddress s
  let s' := s_popped.setGpr64 .rax 1
  (s', none)

/- REF: windows-winsock2-wsastartup#return-value -/
/-- Win32 WSAStartup call hook: initializes WinSock subsystem and returns 0 in RAX. -/
def wsaStartupHook {Event : Type} (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let s_popped := popReturnAddress s
  let s' := s_popped.setGpr64 .rax 0
  (s', none)

/- REF: windows-winsock2-socket#return-value -/
/-- Win32 socket call hook: creates socket descriptor and returns 100 in RAX. -/
def socketHook {Event : Type} (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let s_popped := popReturnAddress s
  let s' := s_popped.setGpr64 .rax 100
  (s', none)

/- REF: windows-winsock2-bind#return-value -/
/-- Win32 bind call hook: binds socket to local address and returns 0 in RAX. -/
def bindHook {Event : Type} (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let s_popped := popReturnAddress s
  let s' := s_popped.setGpr64 .rax 0
  (s', none)

/- REF: windows-winsock2-listen#return-value -/
/-- Win32 listen call hook: places socket in listening state and emits NetEvent.listen. -/
def listenHook {Event : Type} [Inject NetEvent Event] (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let s_popped := popReturnAddress s
  let s' := s_popped.setGpr64 .rax 0
  (s', some (Inject.inject (NetEvent.listen 8080)))

/- REF: windows-winsock2-accept#return-value -/
/-- Win32 accept call hook: accepts incoming client connection and returns client socket in RAX. -/
def acceptHook {Event : Type} [Inject NetEvent Event] (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  match s.incomingRequests with
  | [] =>
    let s_exit := { s with rip := 0 }
    (s_exit, none)
  | _ =>
    let s_popped := popReturnAddress s
    let s' := s_popped.setGpr64 .rax 101
    (s', some (Inject.inject (NetEvent.accept "127.0.0.1")))

/- REF: windows-winsock2-recv#parameters -/
/- REF: docs/READ_BINDER_CONTRACT.md#5-integration-with-law-11s-capability-mandate -/
/-- Win32 recv call hook: copies at most R8 (`len`, the syscall's declared cap) bytes from the
head of `s.incomingRequests` into buffer at RDX and emits NetEvent.recv with exactly what was
delivered. N2 fix (MODEL_DEBT.md §C1): the pre-N2 hook never read R8 at all and always wrote
the entire queued logical request regardless of the caller's declared cap -- the gap
`docs/READ_BINDER_CONTRACT.md` §5 names as making Spike 4's buffer/cap mismatch invisible to any
proof (see `Gasm/Effects/ReadBinderWiring.lean`). Delivery is now built on
`Gasm.Effects.splitBytes`: whenever the queued request already fits within the declared cap
(every existing spike), `count = req.size` and the request is consumed atomically exactly as
before; whenever it does not, this is a genuine short read -- the true, uncorrupted remainder is
requeued as the new head of `incomingRequests` rather than being written past `len` bytes into
memory. -/
def recvHook {Event : Type} [Inject NetEvent Event] (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let bufAddr := s.gprs .rdx
  let requested := (s.gprs .r8).toNat
  let s_popped := popReturnAddress s
  match s.incomingRequests with
  | [] =>
    let s' := s_popped.setGpr64 .rax 0
    (s', none)
  | req :: rest =>
    let (delivered, remaining) := splitBytes req.toUTF8.toList requested
    let count := delivered.length
    let deliveredArr := ByteArray.mk delivered.toArray
    let incomingRequests' :=
      match String.fromUTF8? (ByteArray.mk remaining.toArray) with
      | some r => if remaining.isEmpty then rest else r :: rest
      | none => rest
    let deliveredStr := (String.fromUTF8? deliveredArr).getD req
    let s' := { (s_popped.setGpr64 .rax count.toUInt64) with
      incomingRequests := incomingRequests',
      memory := X86_64Mem.writeBytes bufAddr delivered s_popped.memory
    }
    (s', some (Inject.inject (NetEvent.recv deliveredStr)))

/- REF: windows-winsock2-send#parameters -/
/-- Win32 send call hook: extracts response string from memory at RDX and emits NetEvent.send. -/
def sendHook {Event : Type} [Inject NetEvent Event] (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let bufAddr := s.gprs .rdx
  let len := (s.gprs .r8).toNat
  let text := s.readString bufAddr len
  let s_popped := popReturnAddress s
  let s' := s_popped.setGpr64 .rax len.toUInt64
  (s', some (Inject.inject (NetEvent.send text)))

/- REF: windows-winsock2-closesocket#parameters -/
/-- Win32 closesocket call hook: closes socket descriptor and emits NetEvent.close. -/
def closesocketHook {Event : Type} [Inject NetEvent Event] (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let sock := (s.gprs .rcx).toNat
  let s_popped := popReturnAddress s
  let s' := s_popped.setGpr64 .rax 0
  (s', some (Inject.inject (NetEvent.close sock)))

/- REF: windows-winsock2-wsacleanup#return-value -/
/-- Win32 WSACleanup call hook: terminates WinSock usage and returns 0 in RAX. -/
def wsaCleanupHook {Event : Type} (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let s_popped := popReturnAddress s
  let s' := s_popped.setGpr64 .rax 0
  (s', none)

/- REF: docs/TARGETS/WINDOWS.md#3-pe32-binary-header-loader-invariants -/
/-- Groups imported Win32 functions by module DLL name preserving order. -/
def groupImportsByDll (imports : List Win32Function) : List (String × List String) :=
  let rec loop (fns : List Win32Function) (acc : List (String × List String)) : List (String × List String) :=
    match fns with
    | [] => acc
    | fn :: rest =>
      match acc.find? (fun (dll, _) => dll == fn.moduleName) with
      | some (dll, _names) =>
        let acc' := acc.map (fun (d, ns) => if d == dll then (d, ns ++ [fn.symbolName]) else (d, ns))
        loop rest acc'
      | none =>
        loop rest (acc ++ [(fn.moduleName, [fn.symbolName])])
  loop imports []

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Dynamically identifies the 0-indexed IAT slot index at runtime by resolving relative to the 4KB-aligned IAT base. -/
def findIatIndex (s : X86_64MachineState) (addr : Address) : Option Nat :=
  if s.read64 addr != addr || addr % 8 != 0 then none
  else
    let iatBase := (addr >>> 12) <<< 12
    some ((addr - iatBase) / 8).toNat

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Pure Win32 API external call interceptor. -/
def win32Intercept {Event : Type} [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event]
    (addr : Address) (s : X86_64MachineState) : Option (X86_64MachineState × Option Event) :=
  match findIatIndex s addr with
  | some 0  => some (getStdHandleHook s)
  | some 1  => some (readFileHook s)
  | some 2  => some (writeFileHook s)
  | some 3  => some (exitProcessHook s)
  | some 4  => some (virtualAllocHook s)
  | some 5  => some (virtualFreeHook s)
  | some 7  => some (wsaStartupHook s)
  | some 8  => some (socketHook s)
  | some 9  => some (bindHook s)
  | some 10 => some (listenHook s)
  | some 11 => some (acceptHook s)
  | some 12 => some (recvHook s)
  | some 13 => some (sendHook s)
  | some 14 => some (closesocketHook s)
  | some 15 => some (wsaCleanupHook s)
  | _ => none

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Dynamic Windows x64 external call interceptor dispatching Win32 API calls across any dynamically placed .idata section. -/
def win32CallIntercept {Event : Type} [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event]
    (addr : Address) (s : X86_64MachineState) : Option (X86_64MachineState × Option Event) :=
  win32Intercept addr s

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Loads raw binary section buffers and binds Win32 IAT function import pointers into initial machine memory with dynamic layout. -/
def loadMemory (imageBase : Address) (sections : List (UInt32 × ByteArray)) (imports : List Win32Function) (idataRva : UInt32) : Address → Byte := fun a =>
  match sections.findSome? (fun (rva, bytes) =>
    let startAddr := imageBase + rva.toUInt64
    let endAddr := startAddr + bytes.size.toUInt64
    if a >= startAddr && a < endAddr then
      some (bytes.get! (a - startAddr).toNat)
    else none) with
  | some byte => byte
  | none =>
    let iatBase := imageBase + idataRva.toUInt64
    let dllImports := groupImportsByDll imports
    let rec findIatDll (curBase : Address) (dlls : List (String × List String)) : Option Byte :=
      match dlls with
      | [] => none
      | (_, fns) :: rest =>
        let rec findIatFn (idx : Nat) (fnList : List String) : Option Byte :=
          match fnList with
          | [] => none
          | _ :: frest =>
            let slotAddr := curBase + (idx * 8).toUInt64
            if a >= slotAddr && a < slotAddr + 8 then
              let offset := (a - slotAddr).toNat
              some ((slotAddr >>> ((offset * 8).toUInt64)).toUInt8)
            else findIatFn (idx + 1) frest
        match findIatFn 0 fns with
        | some byte => some byte
        | none =>
          let nextBase := curBase + ((fns.length + 1) * 8).toUInt64
          findIatDll nextBase rest
    match findIatDll iatBase dllImports with
    | some byte => byte
    | none => 0

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Constructs the initial process machine state for a loaded Windows x64 executable. -/
def loadWindowsProcess (imageBase : Address) (entryRva : UInt32) (sections : List (UInt32 × ByteArray)) (imports : List Win32Function) (idataRva : UInt32) : X86_64MachineState := {
  rip    := imageBase + entryRva.toUInt64,
  gprs   := fun r => if r == .rsp then 0x7FFFFFFF0008 else 0,
  flags  := 0,
  memory := X86_64Mem.initRegion (loadMemory imageBase sections imports idataRva)
}

/- REF: docs/TARGETS/WINDOWS.md#3-pe32-binary-header-loader-invariants -/
/-- Structured definition of a Windows x64 PE32+ executable image. -/
structure WindowsExecutable where
  imageBase  : Address := 0x140000000
  entryRva   : UInt32  := 0x1000
  textBytes  : ByteArray
  rdataBytes : ByteArray
  imports    : List Win32Function := [GetStdHandleDef, ReadFileDef, WriteFileDef, ExitProcessDef, VirtualAllocDef, VirtualFreeDef]

namespace WindowsExecutable

/- REF: docs/TARGETS/WINDOWS.md#3-pe32-binary-header-loader-invariants -/
/-- Serializes the executable to PE32+ binary bytes on disk with dynamic multi-DLL imports. -/
def emit (exe : WindowsExecutable) : ByteArray :=
  let dllImports := groupImportsByDll exe.imports
  emitPE32ExecutableMultiDll exe.textBytes exe.rdataBytes dllImports

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Loads the executable directly into initial X86_64MachineState using computed dynamic layout. -/
def load (exe : WindowsExecutable) : X86_64MachineState :=
  let layout := computeSectionLayout exe.textBytes.size exe.rdataBytes.size 512
  loadWindowsProcess exe.imageBase exe.entryRva
    [ (layout.textRva, exe.textBytes),
      (layout.rdataRva, exe.rdataBytes) ]
    exe.imports
    layout.idataRva

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Loads the executable into initial X86_64MachineState with pre-seeded standard input stream. -/
def loadWithStdin (exe : WindowsExecutable) (stdin : ByteArray) : X86_64MachineState :=
  let s := exe.load
  { s with stdinBuffer := stdin }

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Loads the executable into initial X86_64MachineState with pre-seeded incoming HTTP requests queue. -/
def loadWithRequests (exe : WindowsExecutable) (incomingRequests : List String) : X86_64MachineState :=
  let s := exe.load
  { s with incomingRequests := incomingRequests }

/- REF: docs/TARGETS/WINDOWS.md#12-mandatory-32-byte-shadow-space-16-byte-stack-alignment -/
/-- Formal MS x64 Entry Precondition: Stack aligned to 8 mod 16, RIP at entry, .rdata loaded, IAT non-null. -/
def isValidEntryState (exe : WindowsExecutable) (s : X86_64MachineState) : Bool :=
  let layout := computeSectionLayout exe.textBytes.size exe.rdataBytes.size 512
  s.rip == exe.imageBase + exe.entryRva.toUInt64 &&
  s.rsp % 16 == 8 &&
  (List.range exe.rdataBytes.size).all (fun i => s.read8 (exe.imageBase + layout.rdataRva.toUInt64 + i.toUInt64) == (exe.rdataBytes.get! i).toUInt64) &&
  (List.range exe.imports.length).all (fun idx => s.read64 (exe.imageBase + layout.idataRva.toUInt64 + (idx * 8).toUInt64) != 0)

end WindowsExecutable

end Gasm.Targets.Windows
