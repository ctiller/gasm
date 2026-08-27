# Copyright 2026 Craig Tiller
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Fast local iteration build: type-checks the 3 library targets only
# (Gasm, Stdlib, Spikes) without linking any of the 25 spike/fuzzer/test
# executables in lakefile.toml's defaultTargets.
#
# This is an OPT-IN convenience for local/agent iteration speed. It does
# NOT change lakefile.toml's defaultTargets, so plain `lake build` (the CI
# gate) is completely unaffected and still builds/links everything.
#
# Use this when you only need fast type-checking feedback on library code
# (e.g. Gasm/Core, Gasm/Targets/X86_64/Instructions, Stdlib/...) and don't
# need every spike exe relinked. Run a full `lake build` before committing
# to make sure the exes/tests still build.

lake build Gasm Stdlib Spikes
