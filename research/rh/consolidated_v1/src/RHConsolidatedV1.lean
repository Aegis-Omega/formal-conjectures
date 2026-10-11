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

import RHWindowL105FinalV1
import WeilRHImpliesFinalSignV13
import RHNineZerosV1

/-!
# The Riemann Hypothesis, reduced to one statement

Everything below is assembled from kernel-checked modules listed in `manifest.json`; this file adds
only the glue.

* `rh_iff_all_windows`: `RiemannHypothesis` is equivalent to the Weil window condition
  `WindowArithmeticNonpositiveV1 L` for every `L > 0`
  (`rh_iff_final_sign_v13`, `final_sign_residual_iff_weil_negativity_v1`,
  `weil_compact_smooth_negativity_iff_all_windows_v1`).
* `windows_below_21_40`: the window condition holds for every `0 ≤ L < 21/40`
  (the `L = 21/20` Krein certificate, 133 kernel-checked batch modules).
* `rh_iff_windows_from_21_40`: therefore `RiemannHypothesis` is equivalent to the window
  condition for `L ≥ 21/40` alone. That statement is the one open step; nothing here proves it.
* `nine_zeros`: nine zeros of `ζ` on the critical line with `14 ≤ t ≤ 48.9`.

`consolidated` states the four facts together. It is not a proof of `RiemannHypothesis`.
AUTHORITY_EFFECT = NONE.
-/

open Complex

namespace AEGIS.RHConsolidatedV1

open AEGIS.WeilWindowExhaustionV1

/-- `RiemannHypothesis` holds exactly when every Weil window is arithmetically nonpositive. -/
theorem rh_iff_all_windows :
    RiemannHypothesis ↔ ∀ L : ℝ, 0 < L → WindowArithmeticNonpositiveV1 L :=
  AEGIS.WeilRHImpliesFinalSignV13.rh_iff_final_sign_v13.trans
    (AEGIS.RHFinalClosureV1.final_sign_residual_iff_weil_negativity_v1.trans
      weil_compact_smooth_negativity_iff_all_windows_v1)

/-- The proved range: every window with `0 ≤ L < 21/40`. -/
theorem windows_below_21_40 :
    ∀ L : ℝ, 0 ≤ L → L < 21 / 40 → WindowArithmeticNonpositiveV1 L :=
  fun _ h0 h1 => AEGIS.RHWindowL105FinalV1.window_lt_21_40 h0 h1

/-- What remains: `RiemannHypothesis` is equivalent to the windows from `21/40` on. -/
theorem rh_iff_windows_from_21_40 :
    RiemannHypothesis ↔ ∀ L : ℝ, 21 / 40 ≤ L → WindowArithmeticNonpositiveV1 L :=
  ⟨fun h L hL => rh_iff_all_windows.1 h L (by linarith),
    AEGIS.RHWindowL105FinalV1.rh_of_windows_from_21_40⟩

/-- **The consolidated statement.** The windows below `21/40` hold, `RiemannHypothesis` is
equivalent to the windows from `21/40` on, and nine zeros of `ζ` lie on the critical line. -/
theorem consolidated :
    (∀ L : ℝ, 0 ≤ L → L < 21 / 40 → WindowArithmeticNonpositiveV1 L) ∧
    (RiemannHypothesis ↔ ∀ L : ℝ, 21 / 40 ≤ L → WindowArithmeticNonpositiveV1 L) ∧
    (∃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ : ℝ,
      14 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₄ ∧ t₄ < t₅ ∧ t₅ < t₆ ∧ t₆ < t₇ ∧ t₇ < t₈ ∧ t₈ < t₉ ∧
      t₉ ≤ 489 / 10 ∧
      riemannZeta (1 / 2 + t₁ * I) = 0 ∧ riemannZeta (1 / 2 + t₂ * I) = 0 ∧
      riemannZeta (1 / 2 + t₃ * I) = 0 ∧ riemannZeta (1 / 2 + t₄ * I) = 0 ∧
      riemannZeta (1 / 2 + t₅ * I) = 0 ∧ riemannZeta (1 / 2 + t₆ * I) = 0 ∧
      riemannZeta (1 / 2 + t₇ * I) = 0 ∧ riemannZeta (1 / 2 + t₈ * I) = 0 ∧
      riemannZeta (1 / 2 + t₉ * I) = 0) :=
  ⟨windows_below_21_40, rh_iff_windows_from_21_40, AEGIS.RHNineZerosV1.nine_zeros⟩

end AEGIS.RHConsolidatedV1

#print axioms AEGIS.RHConsolidatedV1.rh_iff_all_windows
#print axioms AEGIS.RHConsolidatedV1.windows_below_21_40
#print axioms AEGIS.RHConsolidatedV1.rh_iff_windows_from_21_40
#print axioms AEGIS.RHConsolidatedV1.consolidated
