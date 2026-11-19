/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import RHIndependentElevenCompositionV1

/-!
Read-only final type and transitive axiom probes for the restricted
independent-eleven theorem. This file proves no additional mathematics
and makes no RH claim. Its output is evidence only when actually run
against the source-bound freshly compiled F module.
-/

set_option pp.universes true
set_option pp.fullNames true

#check @AEGIS.RHIndependentElevenCompositionV1.actual_independent_eleven_coercive
#print axioms AEGIS.RHIndependentElevenCompositionV1.actual_independent_eleven_coercive

#check @AEGIS.RHIndependentElevenCompositionV1.all_independent_eleven_mixed_bounds
#print axioms AEGIS.RHIndependentElevenCompositionV1.all_independent_eleven_mixed_bounds

#check @AEGIS.RHIndependentElevenCompositionV1.norm_le_sqrt_energy_of_scaled_mean
#print axioms AEGIS.RHIndependentElevenCompositionV1.norm_le_sqrt_energy_of_scaled_mean
