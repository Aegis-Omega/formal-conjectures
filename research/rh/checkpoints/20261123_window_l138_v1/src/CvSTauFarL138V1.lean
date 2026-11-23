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

import CvSTauFarL12V1
import CvSTauFast2L138V1

/-!
# A bound for `τ_n` far from the low block at L = 13/8

`CvSTauFarL12V1.source_integral_abs_le_inv` gives `|∫ h₊ S_n| ≤ L/|n| + π²/2` for every window, and at
`L = 13/8` the prime powers `2, 3, 4, 5` contribute to the prime part (`CvSTauFast2L138V1.primeSum_eq`,
`ppw 3 = log 2`, `ppw 4 = 2 log 5/√5`). For `|n| ≥ 2001` and every `M ≥ 5` this gives `|τ_n| ≤ 19` (the
value is about `18.7`). As `CvSTauFarL85V1` at `L = 8/5`, with the weight of `5`. Not RH.
-/

open Finset
open AEGIS.CvSRowTailV1 AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchSourceV1 AEGIS.CvSArchLorentzV1
open AEGIS.RHKreinZetaBridgeV3
open AEGIS.CvSTauFast2L138V1 (primeSum_eq)
open AEGIS.CvSTraceM4SlackV1 (ppw_three)
open AEGIS.CvSTauFarL12V1 (source_integral_abs_le_inv)
open AEGIS.CvSTauPrimeL12V1 (w2Lo w2Hi w3Lo w3Hi l2Lo l2Hi l3Lo l3Hi s2Lo s2Hi s3Lo s3Hi w2_bounds
  w3_bounds)
open AEGIS.CvSPrimeFiveV1 (w5Lo w5Hi l5Lo l5Hi s5Lo s5Hi w5_bounds)

namespace AEGIS.CvSTauFarL138V1

/-- **`|τ_n| ≤ 19` for `|n| ≥ 2001` at L = 13/8**, for every prime cutoff `M ≥ 5`. -/
theorem tau_abs_le_far {M : ℕ} (hM : 5 ≤ M) {n : ℤ} (hn : 2001 ≤ |n|) :
    |tau M (13 / 8) n| ≤ 19 := by
  have hn0 : n ≠ 0 := by intro h; rw [h] at hn; simp at hn
  have hnR : (2001 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hn
  have hsrc := source_integral_abs_le_inv (L := 13 / 8) (by norm_num) hn0
  rw [tau, primeSum_eq hM n]
  have w2 := w2_bounds
  have w3 := w3_bounds
  have w5 := w5_bounds
  have hw2 : (w2Hi : ℝ) ≤ 981 / 1000 := by norm_num [w2Hi, l2Hi, s2Hi]
  have hw3 : (w3Hi : ℝ) ≤ 1269 / 1000 := by norm_num [w3Hi, l3Hi, s3Hi]
  have hw5 : (w5Hi : ℝ) ≤ 14396 / 10000 := by norm_num [w5Hi, l5Hi, s5Hi]
  have z2 : (0 : ℝ) ≤ ppw 1 := by have : (0 : ℝ) ≤ w2Lo := by norm_num [w2Lo, l2Lo, s2Lo]
                                  linarith [w2.1]
  have z3 : (0 : ℝ) ≤ ppw 2 := by have : (0 : ℝ) ≤ w3Lo := by norm_num [w3Lo, l3Lo, s3Lo]
                                  linarith [w3.1]
  have z5 : (0 : ℝ) ≤ ppw 4 := by have : (0 : ℝ) ≤ w5Lo := by norm_num [w5Lo, l5Lo, s5Lo]
                                  linarith [w5.1]
  have h4 : ppw 3 ≤ 6932 / 10000 := by
    rw [ppw_three]; have := Real.log_two_lt_d9; linarith
  have z4 : (0 : ℝ) ≤ ppw 3 := by rw [ppw_three]; exact (Real.log_pos (by norm_num)).le
  have hp : |ppw 1 * Real.sin (Real.pi * (16 * n * Real.log 2 / 13)) +
      ppw 2 * Real.sin (Real.pi * (16 * n * Real.log 3 / 13)) +
      ppw 3 * Real.sin (Real.pi * (32 * n * Real.log 2 / 13)) +
      ppw 4 * Real.sin (Real.pi * (16 * n * Real.log 5 / 13))| ≤ 43829 / 10000 := by
    have q1 : |ppw 1 * Real.sin (Real.pi * (16 * n * Real.log 2 / 13))| ≤ ppw 1 := by
      rw [abs_mul, abs_of_nonneg z2]; exact mul_le_of_le_one_right z2 (Real.abs_sin_le_one _)
    have q2 : |ppw 2 * Real.sin (Real.pi * (16 * n * Real.log 3 / 13))| ≤ ppw 2 := by
      rw [abs_mul, abs_of_nonneg z3]; exact mul_le_of_le_one_right z3 (Real.abs_sin_le_one _)
    have q3 : |ppw 3 * Real.sin (Real.pi * (32 * n * Real.log 2 / 13))| ≤ ppw 3 := by
      rw [abs_mul, abs_of_nonneg z4]; exact mul_le_of_le_one_right z4 (Real.abs_sin_le_one _)
    have q4 : |ppw 4 * Real.sin (Real.pi * (16 * n * Real.log 5 / 13))| ≤ ppw 4 := by
      rw [abs_mul, abs_of_nonneg z5]; exact mul_le_of_le_one_right z5 (Real.abs_sin_le_one _)
    have a3 := abs_add_three (ppw 1 * Real.sin (Real.pi * (16 * n * Real.log 2 / 13)))
      (ppw 2 * Real.sin (Real.pi * (16 * n * Real.log 3 / 13)))
      (ppw 3 * Real.sin (Real.pi * (32 * n * Real.log 2 / 13)))
    have a4 := abs_add_le (ppw 1 * Real.sin (Real.pi * (16 * n * Real.log 2 / 13)) +
      ppw 2 * Real.sin (Real.pi * (16 * n * Real.log 3 / 13)) +
      ppw 3 * Real.sin (Real.pi * (32 * n * Real.log 2 / 13)))
      (ppw 4 * Real.sin (Real.pi * (16 * n * Real.log 5 / 13)))
    linarith [w2.2, w3.2, w5.2]
  have hL : (13 / 8 : ℝ) / |(n : ℝ)| ≤ 13 / 16008 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hpi2 : Real.pi ^ 2 < 3.15 ^ 2 := by nlinarith
  calc |(∫ r, hplus r * sourceS (13 / 8) r n) + Real.pi *
        (ppw 1 * Real.sin (Real.pi * (16 * n * Real.log 2 / 13)) +
          ppw 2 * Real.sin (Real.pi * (16 * n * Real.log 3 / 13)) +
          ppw 3 * Real.sin (Real.pi * (32 * n * Real.log 2 / 13)) +
          ppw 4 * Real.sin (Real.pi * (16 * n * Real.log 5 / 13)))|
      ≤ |∫ r, hplus r * sourceS (13 / 8) r n| + Real.pi *
        |ppw 1 * Real.sin (Real.pi * (16 * n * Real.log 2 / 13)) +
          ppw 2 * Real.sin (Real.pi * (16 * n * Real.log 3 / 13)) +
          ppw 3 * Real.sin (Real.pi * (32 * n * Real.log 2 / 13)) +
          ppw 4 * Real.sin (Real.pi * (16 * n * Real.log 5 / 13))| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_of_pos hpi0]
    _ ≤ (13 / 16008 + Real.pi ^ 2 / 2) + Real.pi * (43829 / 10000) := by
        gcongr
        linarith
    _ ≤ 19 := by nlinarith

end AEGIS.CvSTauFarL138V1

#print axioms AEGIS.CvSTauFarL138V1.tau_abs_le_far
