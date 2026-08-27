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
import Gasm.Effects.Console
import Gasm.Effects.Process

namespace Spikes.Spike1Hello

open Gasm.Effects

/- REF: docs/SPIKES.md#2-spike-1-windows-x64-hello-world-pe-binary -/
/-- High-level behavioral specification for Spike 1 (Hello World). -/
def helloWorldSpec [Monad m] [MonadConsole m] [MonadProcess m] : m Unit := do
  MonadConsole.printStr "Hello, World!\n"
  MonadProcess.exitProcess 0

/- REF: docs/SPIKES.md#2-spike-1-windows-x64-hello-world-pe-binary -/
/-- Windows-specific variant with CRLF line terminator. -/
def helloWorldWindowsSpec [Monad m] [MonadConsole m] [MonadProcess m] : m Unit := do
  MonadConsole.printStr "Hello, World!\r\n"
  MonadProcess.exitProcess 0

end Spikes.Spike1Hello
