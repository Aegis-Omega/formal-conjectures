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

import CvSWindowL65V1
import WeilWindowExhaustionV1
import V13Scratch

/-!
# The window `2r ≤ 6/5` in the window-exhaustion chain

`WeilWindowExhaustionV1` splits the final sign residual into one sign obligation per log
window `[−L, L]`, and `V13Scratch` proves that the residual is equivalent to RH.
`CvSWindowL65V1.window_L65` closes every window with `L ≤ 3/5`, with no hypotheses:

* `window_le_three_fifths`: every log window with `L ≤ 3/5` has the arithmetic sign;
* `final_sign_iff_windows_above_three_fifths`: the final sign residual is equivalent to the
  sign on the windows `L > 3/5`;
* `rh_iff_windows_above_three_fifths`: RH is equivalent to the sign on the windows `L > 3/5`.

The earlier frontier was `21/40` (`RHWindowConnectedL105V1.rh_of_windows_from_21_40`), stated
relative to the finite-range certificate `hfin` and a tail check. Here no hypothesis remains
besides the windows `L > 3/5`, which are not proved. Not RH.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHWindowL65ExhaustionV1

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilWindowExhaustionV1
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHFinalClosureV1
open AEGIS.CvSWindowL65V1
open AEGIS.V13Scratch

/-- Every log window `[−L, L]` with `L ≤ 3/5` has the arithmetic sign. -/
theorem window_le_three_fifths {L : ℝ} (hL : L ≤ 3 / 5) :
    WindowArithmeticNonpositiveV1 L := by
  intro g hm hwindow
  have hw : HalfWidthAt g L 0 := by
    simpa [HalfWidthAt, LogSupportIn, LogWindowContainsV1] using hwindow
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mpr
    (window_L65 g hm L 0 hw (by linarith))

/-- The final sign residual is equivalent to the sign on the windows `L > 3/5`. -/
theorem final_sign_iff_windows_above_three_fifths :
    FinalSignResidualV1 ↔ ∀ L : ℝ, 3 / 5 < L → WindowArithmeticNonpositiveV1 L := by
  have e : FinalSignResidualV1 ↔ UniversalArithmeticNonpositiveV1 := Iff.rfl
  rw [e, universal_arithmetic_nonpositive_iff_all_windows_v1]
  constructor
  · intro h L hL
    exact h L (by linarith)
  · intro h L _
    rcases le_or_gt L (3 / 5) with hle | hlt
    · exact window_le_three_fifths hle
    · exact h L hlt

/-- RH is equivalent to the sign on the windows `L > 3/5`. -/
theorem rh_iff_windows_above_three_fifths :
    RiemannHypothesis ↔ ∀ L : ℝ, 3 / 5 < L → WindowArithmeticNonpositiveV1 L :=
  final_sign_iff_rh_v13.symm.trans final_sign_iff_windows_above_three_fifths

end AEGIS.RHWindowL65ExhaustionV1

#print axioms AEGIS.RHWindowL65ExhaustionV1.window_le_three_fifths
#print axioms AEGIS.RHWindowL65ExhaustionV1.final_sign_iff_windows_above_three_fifths
#print axioms AEGIS.RHWindowL65ExhaustionV1.rh_iff_windows_above_three_fifths
