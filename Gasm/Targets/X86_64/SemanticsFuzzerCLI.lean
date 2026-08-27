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
import Gasm.Targets.X86_64.SemanticsFuzzer

open Gasm.Targets.X86_64.SemanticsFuzzer

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CLI Driver for x86-64 Hardware Semantic Fuzzer. -/
def main (args : List String) : IO UInt32 := do
  let mut iterations : Nat := 150
  let mut seed : UInt64 := 88172645463325252
  let mut instrFilter : Option String := none

  let mut i := 0
  let argsArr := args.toArray
  while i < argsArr.size do
    let arg := argsArr[i]!
    if arg.startsWith "--iterations=" then
      if let some n := (arg.drop 13).toNat? then iterations := n
    else if arg.startsWith "--seed=" then
      if let some s := (arg.drop 7).toNat? then seed := s.toUInt64
    else if arg.startsWith "--instruction=" then
      instrFilter := some (arg.drop 14).toString
    else if arg == "-n" && i + 1 < argsArr.size then
      if let some n := argsArr[i+1]!.toNat? then iterations := n; i := i + 1
    else if arg == "-i" && i + 1 < argsArr.size then
      instrFilter := some argsArr[i+1]!; i := i + 1
    i := i + 1

  let (_passed, _skipped, failed, _) ← runX86SemanticsFuzzerSuite iterations seed instrFilter
  if failed == 0 then
    return 0
  else
    return 1
