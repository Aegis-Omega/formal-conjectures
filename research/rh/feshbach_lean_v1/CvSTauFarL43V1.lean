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
import CvSTauPrimeL43V1

/-!
# A sharp bound for `τ_n` far from the low block at L = 4/3

`CvSTauFarL12V1.source_integral_abs_le_inv` gives `|∫ h₊ S_n| ≤ L/|n| + π²/2` for every window,
and at `L = 4/3` only `p = 2, 3` contribute to the prime part (`CvSTauPrimeL43V1.primeSum_eq`).
For `|n| ≥ 71` and every `M ≥ 3` this gives `|τ_n| ≤ 13`. Not RH.
-/

open Finset
open AEGIS.CvSRowTailV1 AEGIS.CvSDigammaSeriesV1 AEGIS.CvSArchSourceV1 AEGIS.CvSArchLorentzV1
open AEGIS.CvSTauPrimeL43V1 AEGIS.RHKreinZetaBridgeV3
open AEGIS.CvSTauFarL12V1 (source_integral_abs_le_inv)
open AEGIS.CvSTauPrimeL12V1 (w2Lo w2Hi w3Lo w3Hi l2Lo l2Hi l3Lo l3Hi s2Lo s2Hi s3Lo s3Hi w2_bounds
  w3_bounds)

namespace AEGIS.CvSTauFarL43V1

/-- **`|τ_n| ≤ 13` for `|n| ≥ 71` at L = 4/3**, for every prime cutoff `M ≥ 3`. -/
theorem tau_abs_le_far {M : ℕ} (hM : 3 ≤ M) {n : ℤ} (hn : 71 ≤ |n|) :
    |tau M (4 / 3) n| ≤ 13 := by
  have hn0 : n ≠ 0 := by intro h; rw [h] at hn; simp at hn
  have hnR : (71 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hn
  have hsrc := source_integral_abs_le_inv (L := 4 / 3) (by norm_num) hn0
  rw [tau, primeSum_eq hM n]
  have w2 := w2_bounds
  have w3 := w3_bounds
  have z2 : (0 : ℝ) ≤ w2Lo := by norm_num [w2Lo, l2Lo, s2Lo]
  have z3 : (0 : ℝ) ≤ w3Lo := by norm_num [w3Lo, l3Lo, s3Lo]
  have hw2 : (w2Hi : ℝ) ≤ 981 / 1000 := by norm_num [w2Hi, l2Hi, s2Hi]
  have hw3 : (w3Hi : ℝ) ≤ 1269 / 1000 := by norm_num [w3Hi, l3Hi, s3Hi]
  have hp : |ppw 1 * Real.sin (Real.pi * (3 * n * Real.log 2 / 2)) +
      ppw 2 * Real.sin (Real.pi * (3 * n * Real.log 3 / 2))| ≤ 2250 / 1000 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ ppw 1 by linarith [w2.1]),
      abs_of_nonneg (show (0 : ℝ) ≤ ppw 2 by linarith [w3.1])]
    have s1 := Real.abs_sin_le_one (Real.pi * (3 * n * Real.log 2 / 2))
    have s2 := Real.abs_sin_le_one (Real.pi * (3 * n * Real.log 3 / 2))
    have p1 : ppw 1 * |Real.sin (Real.pi * (3 * n * Real.log 2 / 2))| ≤ ppw 1 :=
      mul_le_of_le_one_right (by linarith [w2.1]) s1
    have p2 : ppw 2 * |Real.sin (Real.pi * (3 * n * Real.log 3 / 2))| ≤ ppw 2 :=
      mul_le_of_le_one_right (by linarith [w3.1]) s2
    linarith [w2.2, w3.2]
  have hL : (4 / 3 : ℝ) / |(n : ℝ)| ≤ 4 / 213 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hpi2 : Real.pi ^ 2 < 3.15 ^ 2 := by nlinarith
  calc |(∫ r, hplus r * sourceS (4 / 3) r n) + Real.pi *
        (ppw 1 * Real.sin (Real.pi * (3 * n * Real.log 2 / 2)) +
          ppw 2 * Real.sin (Real.pi * (3 * n * Real.log 3 / 2)))|
      ≤ |∫ r, hplus r * sourceS (4 / 3) r n| + Real.pi *
        |ppw 1 * Real.sin (Real.pi * (3 * n * Real.log 2 / 2)) +
          ppw 2 * Real.sin (Real.pi * (3 * n * Real.log 3 / 2))| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_of_pos hpi0]
    _ ≤ (4 / 213 + Real.pi ^ 2 / 2) + Real.pi * (2250 / 1000) := by
        gcongr
        linarith
    _ ≤ 13 := by nlinarith

end AEGIS.CvSTauFarL43V1

#print axioms AEGIS.CvSTauFarL43V1.tau_abs_le_far
