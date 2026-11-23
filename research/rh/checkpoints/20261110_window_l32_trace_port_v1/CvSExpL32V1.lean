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
# Rational enclosure of `e^{−3/4}` (window `L = 3/2`)

`e34_bounds` from `Real.exp_bound` with 24 terms, as `CvSTauL118V1.e1116_bounds` at `L = 11/8`.
Not RH.
-/

namespace AEGIS.CvSExpL32V1

def e34Lo : ℚ := 146190367214327850032107338 / 309485009821345068724781056
def e34Hi : ℚ := 73095183607163925016053672 / 154742504910672534362390528

theorem e34_bounds : (e34Lo : ℝ) ≤ Real.exp (-3 / 4) ∧ Real.exp (-3 / 4) ≤ e34Hi := by
  have h := Real.exp_bound (x := -3 / 4) (by norm_num [abs_div]) (n := 24) (by norm_num)
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  constructor <;> simp only [e34Lo, e34Hi] <;> push_cast <;> linarith [h.1, h.2]

end AEGIS.CvSExpL32V1

#print axioms AEGIS.CvSExpL32V1.e34_bounds
