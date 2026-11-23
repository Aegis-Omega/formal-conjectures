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
import CvSPrimeFiveV1

/-!
# Prime-power nodes at the window `L = 13/8`

At `L = 13/8` four prime powers lie inside the window: `log 2`, `log 3`, `log 4 = 2 log 2` and
`log 5` (`node_one` … `node_four`, the last from `CvSPrimeFiveV1.log5_bounds`, `log 5 < 1.6095 < 13/8`);
every `j + 1 ≥ 6` sits at the window end (`node_big`, from `e^13 < 6^8`). As `CvSNodeL85V1` at
`L = 8/5`, with one more prime. Not RH.
-/

namespace AEGIS.CvSNodeL138V1

open AEGIS.CvSRowTailV1
open AEGIS.CvSTauPrimeL12V1 (l2Lo l2Hi l3Lo l3Hi log2_bounds log3_bounds)
open AEGIS.CvSPrimeFiveV1 (l5Lo l5Hi log5_bounds)

theorem node_zero : node (13 / 8) 0 = 0 := by
  simp only [node]
  norm_num

theorem node_one : node (13 / 8) 1 = Real.log 2 := by
  simp only [node]
  rw [show ((1 + 1 : ℕ) : ℝ) = 2 by norm_num, abs_of_pos (Real.log_pos (by norm_num))]
  exact min_eq_left (by linarith [Real.log_two_lt_d9])

theorem node_two : node (13 / 8) 2 = Real.log 3 := by
  simp only [node]
  rw [show ((2 + 1 : ℕ) : ℝ) = 3 by norm_num, abs_of_pos (Real.log_pos (by norm_num))]
  have h : (l3Hi : ℝ) ≤ 13 / 8 := by norm_num [l3Hi]
  exact min_eq_left (by linarith [log3_bounds.2])

/-- The prime power `4 = 2²` is inside the window, `log 4 = 2 log 2 < 13/8`. -/
theorem node_three : node (13 / 8) 3 = 2 * Real.log 2 := by
  simp only [node]
  have h42 : Real.log ((3 + 1 : ℕ) : ℝ) = 2 * Real.log 2 := by
    rw [show ((3 + 1 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hpos : (0 : ℝ) < 2 * Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  rw [h42, abs_of_pos hpos]
  exact min_eq_left (by linarith [Real.log_two_lt_d9])

/-- The prime `5` is inside the window, `log 5 < 13/8`. -/
theorem node_four : node (13 / 8) 4 = Real.log 5 := by
  simp only [node]
  rw [show ((4 + 1 : ℕ) : ℝ) = 5 by norm_num, abs_of_pos (Real.log_pos (by norm_num))]
  have h : (l5Hi : ℝ) ≤ 13 / 8 := by norm_num [l5Hi]
  exact min_eq_left (by linarith [log5_bounds.2])

/-- Prime powers `j + 1 ≥ 6` have `log(j+1) > 13/8`, so their node is the window end
(`exp (13/8) ^ 8 = e^13 < 6^8`). -/
theorem node_big {j : ℕ} (hj : 5 ≤ j) : node (13 / 8) j = 13 / 8 := by
  simp only [node]
  apply min_eq_right
  have h6 : (6 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 6 ≤ j + 1)
  have hl : Real.log 6 ≤ Real.log ((j + 1 : ℕ) : ℝ) := Real.log_le_log (by norm_num) h6
  have h138 : (13 / 8 : ℝ) < Real.log 6 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h := Real.exp_one_lt_d9
    have e : Real.exp (13 / 8) ^ 8 = Real.exp 1 ^ 13 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have h1 : Real.exp 1 ^ 13 < 6 ^ 8 := by
      have := pow_lt_pow_left₀ h (Real.exp_pos 1).le (by norm_num : (13 : ℕ) ≠ 0)
      linarith [show (2.7182818286 : ℝ) ^ 13 < 6 ^ 8 by norm_num]
    by_contra hc
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) (not_lt.mp hc) 8
    linarith
  rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
  linarith

end AEGIS.CvSNodeL138V1

#print axioms AEGIS.CvSNodeL138V1.node_four
#print axioms AEGIS.CvSNodeL138V1.node_big
