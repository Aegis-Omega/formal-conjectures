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

import CvSWindowL32V1
import WeilWindowExhaustionV1
import V13Scratch

/-!
# The window `2r ≤ 3/2` in the window-exhaustion chain

`WeilWindowExhaustionV1` splits the final sign residual into one sign obligation per log
window `[−L, L]`, and `V13Scratch` proves that the residual is equivalent to RH.
`CvSWindowL32V1.window_L32` closes every window with `L ≤ 3/4`, with no hypotheses:

* `window_le_three_quarters`: every log window with `L ≤ 3/4` has the arithmetic sign;
* `final_sign_iff_windows_above_three_quarters`: the final sign residual is equivalent to
  the sign on the windows `L > 3/4`;
* `rh_iff_windows_above_three_quarters`: RH is equivalent to the sign on the windows
  `L > 3/4`.

The previous frontier was `11/16` (`RHWindowL118ExhaustionV1.rh_iff_windows_above_eleven_sixteenths`).
No hypothesis remains besides the windows `L > 3/4`, which are not proved. Not RH.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHWindowL32ExhaustionV1

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilWindowExhaustionV1
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHFinalClosureV1
open AEGIS.CvSWindowL32V1
open AEGIS.V13Scratch

/-- Every log window `[−L, L]` with `L ≤ 3/4` has the arithmetic sign. -/
theorem window_le_three_quarters {L : ℝ} (hL : L ≤ 3 / 4) :
    WindowArithmeticNonpositiveV1 L := by
  intro g hm hwindow
  have hw : HalfWidthAt g L 0 := by
    simpa [HalfWidthAt, LogSupportIn, LogWindowContainsV1] using hwindow
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mpr
    (window_L32 g hm L 0 hw (by linarith))

/-- The final sign residual is equivalent to the sign on the windows `L > 3/4`. -/
theorem final_sign_iff_windows_above_three_quarters :
    FinalSignResidualV1 ↔ ∀ L : ℝ, 3 / 4 < L → WindowArithmeticNonpositiveV1 L := by
  have e : FinalSignResidualV1 ↔ UniversalArithmeticNonpositiveV1 := Iff.rfl
  rw [e, universal_arithmetic_nonpositive_iff_all_windows_v1]
  constructor
  · intro h L hL
    exact h L (by linarith)
  · intro h L _
    rcases le_or_gt L (3 / 4) with hle | hlt
    · exact window_le_three_quarters hle
    · exact h L hlt

/-- RH is equivalent to the sign on the windows `L > 3/4`. -/
theorem rh_iff_windows_above_three_quarters :
    RiemannHypothesis ↔ ∀ L : ℝ, 3 / 4 < L → WindowArithmeticNonpositiveV1 L :=
  final_sign_iff_rh_v13.symm.trans final_sign_iff_windows_above_three_quarters

end AEGIS.RHWindowL32ExhaustionV1

#print axioms AEGIS.RHWindowL32ExhaustionV1.window_le_three_quarters
#print axioms AEGIS.RHWindowL32ExhaustionV1.final_sign_iff_windows_above_three_quarters
#print axioms AEGIS.RHWindowL32ExhaustionV1.rh_iff_windows_above_three_quarters
