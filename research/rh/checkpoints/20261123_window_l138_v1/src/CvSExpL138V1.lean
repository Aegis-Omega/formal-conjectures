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

import Mathlib

/-!
# Rational enclosure of `e^{−13/16}` (window `L = 13/8`)

`e1316_bounds` from `Real.exp_bound` with 24 terms, as `CvSExpL85V1.e45_bounds` at `L = 8/5`.
Not RH.
-/

namespace AEGIS.CvSExpL138V1

def e1316Lo : ℚ := 2145830322166225933802239 / 4835703278458516698824704
def e1316Hi : ℚ := 4291660644332451867604479 / 9671406556917033397649408

theorem e1316_bounds : (e1316Lo : ℝ) ≤ Real.exp (-13 / 16) ∧ Real.exp (-13 / 16) ≤ e1316Hi := by
  have h := Real.exp_bound (x := -13 / 16) (by norm_num [abs_div]) (n := 24) (by norm_num)
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  constructor <;> simp only [e1316Lo, e1316Hi] <;> push_cast <;> linarith [h.1, h.2]

end AEGIS.CvSExpL138V1

#print axioms AEGIS.CvSExpL138V1.e1316_bounds
