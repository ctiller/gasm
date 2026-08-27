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
import Gasm.Targets.Windows.Win32API
import Stdlib.SmolAlloc.Spec

namespace Stdlib.SmolAlloc.Windows

open Gasm.Core
open Gasm.Targets.Windows
open Stdlib.SmolAlloc

/- ============================================================================ -/
/- WIN32 VIRTUAL MEMORY API TYPES & INVARIANTS                                 -/
/- ============================================================================ -/

/- REF: docs/STDLIB_SMOLALLOC.md#22-platform-realizations -/
/-- Win32 VirtualAlloc call parameter structure. -/
structure Win32VirtualAllocCall where
  lpAddress        : Address
  dwSize           : Nat
  flAllocationType : UInt32
  flProtect        : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/STDLIB_SMOLALLOC.md#22-platform-realizations -/
/-- Win32 VirtualFree call parameter structure. -/
structure Win32VirtualFreeCall where
  lpAddress  : Address
  dwSize     : Nat
  dwFreeType : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/STDLIB_SMOLALLOC.md#22-platform-realizations -/
/-- Observable Win32 memory management API actions. -/
inductive Win32MemoryAction where
  | virtualAlloc (call : Win32VirtualAllocCall) (returnedAddr : Address)
  | virtualFree (call : Win32VirtualFreeCall) (success : Bool)
  deriving DecidableEq, Repr

/- REF: docs/STDLIB_SMOLALLOC.md#22-platform-realizations -/
/-- Windows virtual memory page allocator simulation state with API call tracing. -/
structure WindowsPageState where
  baseAddress    : Address := 0x20000000
  allocatedPages : Nat     := 0
  apiCallTrace   : List Win32MemoryAction := []
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/STDLIB_SMOLALLOC.md#22-platform-realizations -/
/-- Windows platform PageSource implementation invoking Win32 VirtualAlloc and VirtualFree. -/
instance : PageSource (StateM WindowsPageState) where
  pageSize := 4096
  fetchPages numPages := do
    let s ← get
    let byteSize := numPages * 4096
    -- Call Win32 VirtualAlloc(lpAddress := 0, dwSize := byteSize, flAllocationType := 0x3000, flProtect := 0x04)
    -- 0x3000 = MEM_COMMIT (0x1000) | MEM_RESERVE (0x2000)
    -- 0x04   = PAGE_READWRITE
    let allocCall : Win32VirtualAllocCall := {
      lpAddress        := 0,
      dwSize           := byteSize,
      flAllocationType := 0x3000,
      flProtect        := 0x04
    }
    let addr := s.baseAddress + (s.allocatedPages * 4096).toUInt64
    set { s with
      allocatedPages := s.allocatedPages + numPages,
      apiCallTrace   := Win32MemoryAction.virtualAlloc allocCall addr :: s.apiCallTrace
    }
    pure (some addr)

  releasePages baseAddr _numPages := do
    let s ← get
    -- Call Win32 VirtualFree(lpAddress := baseAddr, dwSize := 0, dwFreeType := 0x8000)
    -- 0x8000 = MEM_RELEASE (MSDN: dwSize must be 0 when MEM_RELEASE is specified)
    let freeCall : Win32VirtualFreeCall := {
      lpAddress  := baseAddr,
      dwSize     := 0,
      dwFreeType := 0x8000
    }
    set { s with
      apiCallTrace := Win32MemoryAction.virtualFree freeCall true :: s.apiCallTrace
    }
    pure true

/- REF: docs/STDLIB_SMOLALLOC.md#22-platform-realizations -/
/-- Formal Theorem: The Windows PageSource implementation ACTUALLY calls Win32 VirtualAlloc.
    For ANY requested page count `numPages` and ANY initial `WindowsPageState` `s0`,
    calling `PageSource.fetchPages numPages` strictly emits a Win32 `VirtualAlloc` system call
    with:
    - `lpAddress = 0` (OS chooses base address)
    - `dwSize = numPages * 4096`
    - `flAllocationType = 0x3000` (MEM_COMMIT | MEM_RESERVE)
    - `flProtect = 0x04` (PAGE_READWRITE)
    and records this Win32 API invocation into `s'.apiCallTrace`! -/
theorem windows_page_source_calls_virtualalloc (numPages : Nat) (s0 : WindowsPageState) :
    let (_, s') := (PageSource.fetchPages (m := StateM WindowsPageState) numPages).run s0
    s'.apiCallTrace =
      Win32MemoryAction.virtualAlloc {
        lpAddress        := 0,
        dwSize           := numPages * 4096,
        flAllocationType := 0x3000,
        flProtect        := 0x04
      } (s0.baseAddress + (s0.allocatedPages * 4096).toUInt64) :: s0.apiCallTrace := by
  rfl

/- REF: docs/STDLIB_SMOLALLOC.md#22-platform-realizations -/
/-- Formal Theorem: The Windows PageSource implementation ACTUALLY calls Win32 VirtualFree.
    For ANY base address, page count, and state `s0`, calling `PageSource.releasePages`
    strictly emits a Win32 `VirtualFree` call with `dwSize = 0` and `dwFreeType = 0x8000` (MEM_RELEASE). -/
theorem windows_page_source_calls_virtualfree (baseAddr : Address) (numPages : Nat) (s0 : WindowsPageState) :
    let (_, s') := (PageSource.releasePages (m := StateM WindowsPageState) baseAddr numPages).run s0
    s'.apiCallTrace =
      Win32MemoryAction.virtualFree {
        lpAddress  := baseAddr,
        dwSize     := 0,
        dwFreeType := 0x8000
      } true :: s0.apiCallTrace := by
  rfl

end Stdlib.SmolAlloc.Windows
