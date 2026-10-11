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

import RHFeshbachWeilClosureV2

/-!
# Direct exact Mathlib RH target probe

Unlike the archived WholeChain exact? attempt, this explicitly applies the
existing proof assembly to the actual Mathlib RiemannHypothesis proposition.
The file never assumes RH, uses no sorry, exact?, or new axioms.
An unfinished goal reports only the state of this one integration route.
-/

set_option autoImplicit false

namespace AEGIS.RHOfficialTargetProbeV1

/-- Exactly the official Mathlib goal; this fails Lean if an obligation remains. -/
theorem riemannHypothesis : _root_.RiemannHypothesis := by
  apply AEGIS.RHFeshbachWeilClosureV2.riemannHypothesis_of_window_schur_families

end AEGIS.RHOfficialTargetProbeV1

#print axioms AEGIS.RHOfficialTargetProbeV1.riemannHypothesis
