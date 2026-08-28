/-
Copyright 2026 Google LLC

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
import Gasm.Targets.AArch64.MemoryCell

open Lean
open Gasm.Targets.AArch64.AArch64Mem

#print axioms byte0_bit
#print axioms slice_getLsbD
#print axioms read8_write8_same
#print axioms read16_write16_same
#print axioms read32_write32_same
#print axioms read64_write64_same
