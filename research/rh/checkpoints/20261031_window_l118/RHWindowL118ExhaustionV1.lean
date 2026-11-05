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

import CvSWindowL118V1
import WeilWindowExhaustionV1
import V13Scratch

/-!
# The window `2r ≤ 11/8` in the window-exhaustion chain

`WeilWindowExhaustionV1` splits the final sign residual into one sign obligation per log
window `[−L, L]`, and `V13Scratch` proves that the residual is equivalent to RH.
`CvSWindowL118V1.window_L118` closes every window with `L ≤ 11/16`, with no hypotheses:

* `window_le_eleven_sixteenths`: every log window with `L ≤ 11/16` has the arithmetic sign;
* `final_sign_iff_windows_above_eleven_sixteenths`: the final sign residual is equivalent to
  the sign on the windows `L > 11/16`;
* `rh_iff_windows_above_eleven_sixteenths`: RH is equivalent to the sign on the windows
  `L > 11/16`.

The previous frontier was `2/3` (`RHWindowL43ExhaustionV1.rh_iff_windows_above_two_thirds`).
No hypothesis remains besides the windows `L > 11/16`, which are not proved. Not RH.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHWindowL118ExhaustionV1

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilWindowExhaustionV1
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHFinalClosureV1
open AEGIS.CvSWindowL118V1
open AEGIS.V13Scratch

/-- Every log window `[−L, L]` with `L ≤ 11/16` has the arithmetic sign. -/
theorem window_le_eleven_sixteenths {L : ℝ} (hL : L ≤ 11 / 16) :
    WindowArithmeticNonpositiveV1 L := by
  intro g hm hwindow
  have hw : HalfWidthAt g L 0 := by
    simpa [HalfWidthAt, LogSupportIn, LogWindowContainsV1] using hwindow
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mpr
    (window_L118 g hm L 0 hw (by linarith))

/-- The final sign residual is equivalent to the sign on the windows `L > 11/16`. -/
theorem final_sign_iff_windows_above_eleven_sixteenths :
    FinalSignResidualV1 ↔ ∀ L : ℝ, 11 / 16 < L → WindowArithmeticNonpositiveV1 L := by
  have e : FinalSignResidualV1 ↔ UniversalArithmeticNonpositiveV1 := Iff.rfl
  rw [e, universal_arithmetic_nonpositive_iff_all_windows_v1]
  constructor
  · intro h L hL
    exact h L (by linarith)
  · intro h L _
    rcases le_or_gt L (11 / 16) with hle | hlt
    · exact window_le_eleven_sixteenths hle
    · exact h L hlt

/-- RH is equivalent to the sign on the windows `L > 11/16`. -/
theorem rh_iff_windows_above_eleven_sixteenths :
    RiemannHypothesis ↔ ∀ L : ℝ, 11 / 16 < L → WindowArithmeticNonpositiveV1 L :=
  final_sign_iff_rh_v13.symm.trans final_sign_iff_windows_above_eleven_sixteenths

end AEGIS.RHWindowL118ExhaustionV1

#print axioms AEGIS.RHWindowL118ExhaustionV1.window_le_eleven_sixteenths
#print axioms AEGIS.RHWindowL118ExhaustionV1.final_sign_iff_windows_above_eleven_sixteenths
#print axioms AEGIS.RHWindowL118ExhaustionV1.rh_iff_windows_above_eleven_sixteenths
