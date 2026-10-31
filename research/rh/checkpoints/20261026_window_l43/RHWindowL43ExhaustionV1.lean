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

import CvSWindowL43V1
import WeilWindowExhaustionV1
import V13Scratch

/-!
# The window `2r ≤ 4/3` in the window-exhaustion chain

`WeilWindowExhaustionV1` splits the final sign residual into one sign obligation per log
window `[−L, L]`, and `V13Scratch` proves that the residual is equivalent to RH.
`CvSWindowL43V1.window_L43` closes every window with `L ≤ 2/3`, with no hypotheses:

* `window_le_two_thirds`: every log window with `L ≤ 2/3` has the arithmetic sign;
* `final_sign_iff_windows_above_two_thirds`: the final sign residual is equivalent to the
  sign on the windows `L > 2/3`;
* `rh_iff_windows_above_two_thirds`: RH is equivalent to the sign on the windows `L > 2/3`.

The previous frontier was `3/5` (`RHWindowL65ExhaustionV1.rh_iff_windows_above_three_fifths`).
No hypothesis remains besides the windows `L > 2/3`, which are not proved. Not RH.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHWindowL43ExhaustionV1

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilWindowExhaustionV1
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHFinalClosureV1
open AEGIS.CvSWindowL43V1
open AEGIS.V13Scratch

/-- Every log window `[−L, L]` with `L ≤ 2/3` has the arithmetic sign. -/
theorem window_le_two_thirds {L : ℝ} (hL : L ≤ 2 / 3) :
    WindowArithmeticNonpositiveV1 L := by
  intro g hm hwindow
  have hw : HalfWidthAt g L 0 := by
    simpa [HalfWidthAt, LogSupportIn, LogWindowContainsV1] using hwindow
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mpr
    (window_L43 g hm L 0 hw (by linarith))

/-- The final sign residual is equivalent to the sign on the windows `L > 2/3`. -/
theorem final_sign_iff_windows_above_two_thirds :
    FinalSignResidualV1 ↔ ∀ L : ℝ, 2 / 3 < L → WindowArithmeticNonpositiveV1 L := by
  have e : FinalSignResidualV1 ↔ UniversalArithmeticNonpositiveV1 := Iff.rfl
  rw [e, universal_arithmetic_nonpositive_iff_all_windows_v1]
  constructor
  · intro h L hL
    exact h L (by linarith)
  · intro h L _
    rcases le_or_gt L (2 / 3) with hle | hlt
    · exact window_le_two_thirds hle
    · exact h L hlt

/-- RH is equivalent to the sign on the windows `L > 2/3`. -/
theorem rh_iff_windows_above_two_thirds :
    RiemannHypothesis ↔ ∀ L : ℝ, 2 / 3 < L → WindowArithmeticNonpositiveV1 L :=
  final_sign_iff_rh_v13.symm.trans final_sign_iff_windows_above_two_thirds

end AEGIS.RHWindowL43ExhaustionV1

#print axioms AEGIS.RHWindowL43ExhaustionV1.window_le_two_thirds
#print axioms AEGIS.RHWindowL43ExhaustionV1.final_sign_iff_windows_above_two_thirds
#print axioms AEGIS.RHWindowL43ExhaustionV1.rh_iff_windows_above_two_thirds
