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

import CvSProjectedEntryL12V1

/-!
Exact, source-bound row budget for the original projected CvS error radii.
Unlike `bigCheck`, this closed computation has no packed Gram products,
no `hI`/ `neI` calculation, and no 9730-entry interval test.
-/

open Finset
open AEGIS.CvSProjectedEntryL12V1
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace AEGIS.CvSResidualRowBudgetV1

/-- Pure integer check over 139 rows of the SOURCE `radI`, not a second matrix. -/
def radiusRowsCheck : Bool :=
  (List.range 139).all fun i =>
    decide (230000 * ((List.range 139).map (radI i)).sum < SR)

/-- The row check is deliberately separate from the packed `bigCheck`. -/
theorem radiusRowsCheck_true : radiusRowsCheck = true := by
  decide +kernel

theorem radius_row_int (i : ℕ) (hi : i < 139) :
    (230000 : ℤ) * ((List.range 139).map (radI i)).sum < SR := by
  have h := radiusRowsCheck_true
  simp only [radiusRowsCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h i hi

/-- Ready-made Schur/ residual row premise, with epsilon = 1/230000. -/
theorem radius_row_real (i : Fin 139) :
    (∑ j : Fin 139, (radI i.val j.val : ℝ) / (SR : ℝ)) <
      (1 / 230000 : ℝ) := by
  have h := radius_row_int i.val i.isLt
  rw [lsum_range] at h
  rw [← Fin.sum_univ_eq_sum_range (radI i.val) 139] at h
  have hr :
      (230000 : ℝ) * (∑ j : Fin 139, (radI i.val j.val : ℝ)) <
        (SR : ℝ) := by exact_mod_cast h
  have hs : (0 : ℝ) < (SR : ℝ) := by norm_num [SR]
  have he :
      (∑ j : Fin 139, (radI i.val j.val : ℝ)) / (SR : ℝ) <
        (1 / 230000 : ℝ) := by
    apply (div_lt_div_iff₀ hs (by norm_num : (0 : ℝ) < 230000)).2
    simpa only [one_mul, mul_comm] using hr
  simpa only [Finset.sum_div] using he

end AEGIS.CvSResidualRowBudgetV1

#print axioms AEGIS.CvSResidualRowBudgetV1.radiusRowsCheck_true
#print axioms AEGIS.CvSResidualRowBudgetV1.radius_row_real
