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

import CvSHplusBoundsV1

/-!
# The four-term Krein symbol: the prime power 4 in the slack (`M = 4`)

`ppw 3 = log 2` (`Λ(4) = log 2`, `2 e^{−(log 4)/2} = 1`), so `w4Hi = l2Hi` bounds the weight of
`n = 4`, and `scertM_four_ge`: `ScertM 4 t ≥ h₊(t) − w₂⁺ − w₃⁺ − w₄⁺`. This is
`CvSHplusBoundsV1.scertM_three_ge` with one more term. Not RH.
-/

open Finset

namespace AEGIS.CvSTraceM4SlackV1

open AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchSourceV1 AEGIS.CvSTauL12V1 AEGIS.CvSTauPrimeL12V1
open AEGIS.CvSDiagL12V1 AEGIS.CvSHplusBoundsV1
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

theorem ppw_three : ppw 3 = Real.log 2 := by
  simp only [ppw]
  rw [show (3 + 1 : ℕ) = 2 ^ 2 from rfl,
    ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have h4 : Real.log (((2 ^ 2 : ℕ) : ℝ)) = 2 * Real.log 2 := by
    push_cast
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h4]
  have he : Real.exp (-(2 * Real.log 2) / 2) = 1 / 2 := by
    rw [show -(2 * Real.log 2) / 2 = -Real.log 2 by ring, Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [he]
  push_cast
  ring

/-- Upper bound for the weight of `n = 4`. -/
def w4Hi : ℚ := l2Hi

theorem w4_bounds : ppw 3 ≤ (w4Hi : ℝ) := by
  rw [ppw_three]
  exact log2_bounds.2

/-- `ScertM 4 t ≥ h₊(t) − w₂⁺ − w₃⁺ − w₄⁺`. -/
theorem scertM_four_ge (t : ℝ) : hplus t - w2Hi - w3Hi - w4Hi ≤ ScertM 4 t := by
  unfold ScertM
  rw [AEGIS.CvSRingBridgeV1.psi_sub_log_eq_hplus]
  simp only [sum_range_succ, sum_range_zero, AEGIS.CvSHplusBoundsV1.ppw_zero, zero_mul, zero_add]
  have h1 := w2_bounds.2
  have h2 := w3_bounds.2
  have h3 := w4_bounds
  have c1 := Real.cos_le_one (t * Real.log ((1 + 1 : ℕ) : ℝ))
  have c2 := Real.cos_le_one (t * Real.log ((2 + 1 : ℕ) : ℝ))
  have c3 := Real.cos_le_one (t * Real.log ((3 + 1 : ℕ) : ℝ))
  have q1 := mul_nonneg (ppw_nonneg 1) (sub_nonneg.mpr c1)
  have q2 := mul_nonneg (ppw_nonneg 2) (sub_nonneg.mpr c2)
  have q3 := mul_nonneg (ppw_nonneg 3) (sub_nonneg.mpr c3)
  nlinarith

end AEGIS.CvSTraceM4SlackV1

#print axioms AEGIS.CvSTraceM4SlackV1.ppw_three
#print axioms AEGIS.CvSTraceM4SlackV1.scertM_four_ge
