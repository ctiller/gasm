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

import Spikes.Common.WasmHostRunner

import Spikes.Spike1Hello.Spec
import Spikes.Spike1Hello.Windows.Program
import Spikes.Spike1Hello.Windows.Equivalence
import Spikes.Spike1Hello.Linux.Program
import Spikes.Spike1Hello.Linux.Equivalence
import Spikes.Spike1Hello.Wasm.Program
import Spikes.Spike1Hello.Wasm.Equivalence
import Spikes.Spike1Hello.BareMetal.Program
import Spikes.Spike1Hello.BareMetal.Equivalence
import Spikes.Spike1Hello.AArch64BareMetal.Program
import Spikes.Spike1Hello.AArch64BareMetal.Equivalence
import Spikes.Spike1Hello.AArch64Linux.Program
import Spikes.Spike1Hello.AArch64Linux.Equivalence

import Spikes.Spike2Fibonacci.Spec
import Spikes.Spike2Fibonacci.NativeLoop
import Spikes.Spike2Fibonacci.Windows.Program
import Spikes.Spike2Fibonacci.Windows.Equivalence
import Spikes.Spike2Fibonacci.Windows.IATLemmas
import Spikes.Spike2Fibonacci.Linux.Program
import Spikes.Spike2Fibonacci.Linux.Equivalence
import Spikes.Spike2Fibonacci.Wasm.Program
import Spikes.Spike2Fibonacci.Wasm.Equivalence

import Spikes.Spike3SortLines.Spec
import Spikes.Spike3SortLines.Windows.Program
import Spikes.Spike3SortLines.Windows.Equivalence
import Spikes.Spike3SortLines.TraceStepLemmas
import Spikes.Spike3SortLines.Windows.InterceptLemmas
import Spikes.Spike3SortLines.Windows.InstructionStepLemmas
import Spikes.Spike3SortLines.Windows.IATLemmas
import Spikes.Spike3SortLines.Linux.Program
import Spikes.Spike3SortLines.Linux.Equivalence
import Spikes.Spike3SortLines.NativeRuntime
import Spikes.Spike3SortLines.NativeOutcome
import Spikes.Spike3SortLines.Wasm.Program
import Spikes.Spike3SortLines.Wasm.Equivalence

import Spikes.Spike4HttpServer.Spec
import Spikes.Spike4HttpServer.MethodDispatch
import Spikes.Spike4HttpServer.Windows.Program
import Spikes.Spike4HttpServer.Linux.Program
import Spikes.Spike4HttpServer.Wasm.Program
import Spikes.Spike4HttpServer.Equivalence

import Spikes.Spike5Gzip.Spec
import Spikes.Spike5Gzip.Windows.Program
import Spikes.Spike5Gzip.Linux.Program
import Spikes.Spike5Gzip.Wasm.Program
import Spikes.Spike5Gzip.UniversalInput
import Spikes.Spike5Gzip.StreamingCapability
import Spikes.Spike5Gzip.Runtime
import Spikes.Spike5Gzip.NativeProofs
import Spikes.Spike5Gzip.Equivalence

