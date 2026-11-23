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

/-!
# Prime-power nodes at the window `L = 3/2`

At `L = 3/2` three prime powers lie inside the window: `log 2`, `log 3` and `log 4 = 2 log 2`
(`node_one`, `node_two`, `node_three`); every `j + 1 ≥ 5` sits at the window end (`node_big`,
from `log 5 ≥ log (9/2) = 2 log 3 − log 2 > 3/2`). This is the `L = 3/2` analogue of the node
lemmas of `CvSTauPrimeL118V1`, with one more interior node. Not RH.
-/

namespace AEGIS.CvSNodeL32V1

open AEGIS.CvSRowTailV1
open AEGIS.CvSTauPrimeL12V1 (l2Lo l2Hi l3Lo l3Hi log2_bounds log3_bounds)

theorem node_zero : node (3 / 2) 0 = 0 := by
  simp only [node]
  norm_num

theorem node_one : node (3 / 2) 1 = Real.log 2 := by
  simp only [node]
  rw [show ((1 + 1 : ℕ) : ℝ) = 2 by norm_num, abs_of_pos (Real.log_pos (by norm_num))]
  exact min_eq_left (by linarith [Real.log_two_lt_d9])

theorem node_two : node (3 / 2) 2 = Real.log 3 := by
  simp only [node]
  rw [show ((2 + 1 : ℕ) : ℝ) = 3 by norm_num, abs_of_pos (Real.log_pos (by norm_num))]
  have h : (l3Hi : ℝ) ≤ 3 / 2 := by norm_num [l3Hi]
  exact min_eq_left (by linarith [log3_bounds.2])

/-- New at `L = 3/2`: the prime power `4 = 2²` is inside the window, `log 4 = 2 log 2 < 3/2`. -/
theorem node_three : node (3 / 2) 3 = 2 * Real.log 2 := by
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

/-- Prime powers `j + 1 ≥ 5` have `log(j+1) > 3/2`, so their node is the window end. -/
theorem node_big {j : ℕ} (hj : 4 ≤ j) : node (3 / 2) j = 3 / 2 := by
  simp only [node]
  apply min_eq_right
  have h5 : (5 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 5 ≤ j + 1)
  have h92 : (9 / 2 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by linarith
  have hl : Real.log (9 / 2) ≤ Real.log ((j + 1 : ℕ) : ℝ) := Real.log_le_log (by norm_num) h92
  have e92 : Real.log (9 / 2 : ℝ) = 2 * Real.log 3 - Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlo : (3 / 2 : ℝ) ≤ 2 * l3Lo - l2Hi := by norm_num [l3Lo, l2Hi]
  have a := log2_bounds.2
  have b := log3_bounds.1
  rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
  linarith

end AEGIS.CvSNodeL32V1

#print axioms AEGIS.CvSNodeL32V1.node_three
#print axioms AEGIS.CvSNodeL32V1.node_big
