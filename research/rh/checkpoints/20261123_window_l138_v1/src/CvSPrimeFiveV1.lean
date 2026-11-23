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
import CvSTauPrimeL12V1
import CvSHplusBoundsV1

/-!
# The prime `5`: `log 5`, `5^{−1/2}` and the weight `ppw 4`

`log 5 = 2 log 2 − log(4/5)` with the series of `−log(1 − 1/5)` (30 terms, error `(1/5)^31·5/4`)
and `CvSTauPrimeL12V1.log2_bounds` (`log5_bounds`); `5^{−1/2}` by squares (`s5_bounds`);
`ppw 4 = Λ(5)·2·5^{−1/2} = 2 log 5/√5` (`ppw_four`, `w5_bounds`). These are the inputs of the fifth
prime term once a window passes `log 5`. Not RH.
-/

open Finset

namespace AEGIS.CvSPrimeFiveV1

open AEGIS.CvSTauPrimeL12V1 AEGIS.RHKreinZetaBridgeV3

def l5Lo : ℚ := 29688889273197213358 / 18446744073709551616
def l5Hi : ℚ := 29688889273197213361 / 18446744073709551616

theorem log4_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

theorem log5_bounds : (l5Lo : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ l5Hi := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1 / 5 : ℚ) : ℝ)) (by norm_num) 30
  rw [← logSum_cast, show (1 : ℝ) - ((1 / 5 : ℚ) : ℝ) = 4 / 5 by norm_num,
    Real.log_div (by norm_num) (by norm_num), log4_eq,
    show |((1 / 5 : ℚ) : ℝ)| ^ (30 + 1) / (1 - |((1 / 5 : ℚ) : ℝ)|) =
      (((1 / 5) ^ 31 * (5 / 4) : ℚ) : ℝ) by norm_num] at h
  have h1 : l5Lo ≤ 2 * l2Lo + logSum (1 / 5) 30 - (1 / 5) ^ 31 * (5 / 4) := by decide +kernel
  have h2 : 2 * l2Hi + logSum (1 / 5) 30 + (1 / 5) ^ 31 * (5 / 4) ≤ l5Hi := by decide +kernel
  have h1' : (l5Lo : ℝ) ≤ 2 * l2Lo + (logSum (1 / 5) 30 : ℝ) -
      (((1 / 5) ^ 31 * (5 / 4) : ℚ) : ℝ) := by
    exact_mod_cast h1
  have h2' : 2 * (l2Hi : ℝ) + (logSum (1 / 5) 30 : ℝ) + (((1 / 5) ^ 31 * (5 / 4) : ℚ) : ℝ) ≤
      l5Hi := by
    exact_mod_cast h2
  have := abs_le.mp h
  have := log2_bounds
  constructor <;> linarith

def s5Lo : ℚ := 8249634742471189717 / 18446744073709551616
def s5Hi : ℚ := 8249634742471189718 / 18446744073709551616

theorem s5_bounds : (s5Lo : ℝ) ≤ Real.exp (-Real.log 5 / 2) ∧
    Real.exp (-Real.log 5 / 2) ≤ s5Hi := by
  have h1 : s5Lo ^ 2 ≤ 5⁻¹ := by decide +kernel
  have h2 : 5⁻¹ ≤ s5Hi ^ 2 := by decide +kernel
  have h1' : ((s5Lo ^ 2 : ℚ) : ℝ) ≤ ((5⁻¹ : ℚ) : ℝ) := Rat.cast_le.mpr h1
  have h2' : ((5⁻¹ : ℚ) : ℝ) ≤ ((s5Hi ^ 2 : ℚ) : ℝ) := Rat.cast_le.mpr h2
  push_cast at h1' h2'
  exact exp_half_bounds (by norm_num) (by simp [s5Lo]; norm_num) (by simp [s5Hi]; norm_num)
    h1' h2'

theorem ppw_four : ppw 4 = Real.log 5 * (2 * Real.exp (-Real.log 5 / 2)) := by
  simp only [ppw]
  rw [show (4 + 1 : ℕ) = 5 from rfl,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 5)]
  push_cast
  ring_nf

def w5Lo : ℚ := l5Lo * (2 * s5Lo)
def w5Hi : ℚ := l5Hi * (2 * s5Hi)

theorem w5_bounds : (w5Lo : ℝ) ≤ ppw 4 ∧ ppw 4 ≤ w5Hi := by
  rw [ppw_four]
  have a := log5_bounds
  have b := s5_bounds
  have h0 : (0 : ℝ) ≤ l5Lo := by norm_num [l5Lo]
  have h1 : (0 : ℝ) ≤ s5Lo := by norm_num [s5Lo]
  simp only [w5Lo, w5Hi]
  push_cast
  constructor
  · exact mul_le_mul a.1 (by linarith) (by linarith) (by linarith)
  · exact mul_le_mul a.2 (by linarith) (by linarith [Real.exp_pos (-Real.log 5 / 2)])
      (by linarith)

end AEGIS.CvSPrimeFiveV1

#print axioms AEGIS.CvSPrimeFiveV1.log5_bounds
#print axioms AEGIS.CvSPrimeFiveV1.s5_bounds
#print axioms AEGIS.CvSPrimeFiveV1.ppw_four
#print axioms AEGIS.CvSPrimeFiveV1.w5_bounds
