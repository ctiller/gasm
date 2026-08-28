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
import Gasm.Targets.AArch64.Roundtrip
import Gasm.Targets.AArch64.RoundtripGate

open Lean

def main : IO UInt32 := do
  let env ← importModules #[
    {module := `Gasm.Targets.AArch64.Roundtrip},
    {module := `Gasm.Targets.AArch64.RoundtripGate}
  ] {} (trustLevel := 0)
  let ctx : Core.Context := { fileName := "check_roundtrip_axioms", fileMap := default }
  let targetMods := [`Gasm.Targets.AArch64.Roundtrip, `Gasm.Targets.AArch64.RoundtripGate]

  IO.println "=== Checking Axiom Dependencies for Roundtrip.lean and RoundtripGate.lean ==="
  let mut count := 0
  let mut nonStandardCount := 0
  let standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

  for (name, _) in env.constants.toList do
    match env.getModuleIdxFor? name with
    | some idx =>
      let modName? := env.allImportedModuleNames[idx.toNat]?
      if targetMods.any (fun m => modName? == some m) then
        count := count + 1
        let coreState : Core.State := { env := env }
        let (axs, _) ← (Lean.collectAxioms (m := Core.CoreM) name).toIO ctx coreState
        let nonStandard := axs.filter (fun a => !standardAxioms.contains a)
        IO.println s!"Decl: {name} (mod: {modName?})"
        IO.println s!"  Axioms: {axs.toList}"
        if !nonStandard.isEmpty then
          nonStandardCount := nonStandardCount + 1
          IO.println s!"  [!] NON-STANDARD: {nonStandard.toList}"
    | none => pure ()

  IO.println s!"Total declarations checked in target modules: {count}"
  IO.println s!"Total non-standard axiom dependencies: {nonStandardCount}"
  if nonStandardCount == 0 && count > 0 then
    IO.println "[PASS] All declarations in Roundtrip.lean and RoundtripGate.lean are 100% axiom pure!"
    return 0
  else
    IO.println "[FAIL] Non-standard axioms detected or no declarations found!"
    return 1
