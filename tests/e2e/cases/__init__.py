# Copyright 2026 Google LLC
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

"""Test case definitions for gasm x86-64 GPR E2E test suite."""

from tests.e2e.cases.tier1_feature_coverage import get_tier1_tests
from tests.e2e.cases.tier2_boundary_corner import get_tier2_tests
from tests.e2e.cases.tier3_cross_feature import get_tier3_tests
from tests.e2e.cases.tier4_real_world import get_tier4_tests

__all__ = [
    "get_tier1_tests",
    "get_tier2_tests",
    "get_tier3_tests",
    "get_tier4_tests",
]
