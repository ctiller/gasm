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
import Gasm.Effects.Inject

namespace Gasm.Effects

/- REF: docs/SYSTEM_EFFECTS.md#22-monadfilesystem-file-io-descriptor-typestates -/
/-- File open modes. -/
inductive OpenMode where
  | Read
  | Write
  | ReadWrite
  | Append
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/SYSTEM_EFFECTS.md#22-monadfilesystem-file-io-descriptor-typestates -/
/-- File system error codes. -/
inductive FileError where
  | NotFound
  | PermissionDenied
  | DiskFull
  | InvalidHandle
  | IoError (code : Nat)
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/SYSTEM_EFFECTS.md#22-monadfilesystem-file-io-descriptor-typestates -/
/-- Abstract file handle. -/
structure FileHandle where
  id : Nat
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/SYSTEM_EFFECTS.md#22-monadfilesystem-file-io-descriptor-typestates -/
/-- Strongly-typed file system event. -/
inductive FileSystemEvent where
  | write (handle : FileHandle) (len : Nat)
  | close (handle : FileHandle)
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/SYSTEM_EFFECTS.md#11-core-effect-typeclass-hierarchy-gasmeffects -/
instance : IsEvent FileSystemEvent where
  domain := "FileSystem"
  format := fun
    | .write h len => s!"write(h={h.id}, len={len})"
    | .close h     => s!"close(h={h.id})"

/- REF: docs/SYSTEM_EFFECTS.md#22-monadfilesystem-file-io-descriptor-typestates -/
/-- Portable effect typeclass for file system operations. -/
class MonadFileSystem (m : Type → Type) [Monad m] where
  openFile  : String → OpenMode → m (Except FileError FileHandle)
  readFile  : FileHandle → (maxBytes : Nat) → m (Except FileError ByteArray)
  writeFile : FileHandle → ByteArray → m (Except FileError Nat)
  closeFile : FileHandle → m (Except FileError Unit)

end Gasm.Effects
