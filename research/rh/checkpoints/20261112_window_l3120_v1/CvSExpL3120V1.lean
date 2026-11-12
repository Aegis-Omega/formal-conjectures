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
# Rational enclosure of `e^{−31/40}` (window `L = 31/20`)

`e3140_bounds` from `Real.exp_bound` with 24 terms, as `CvSExpL32V1.e34_bounds` at `L = 3/2`.
Not RH.
-/

namespace AEGIS.CvSExpL3120V1

def e3140Lo : ℚ := 142580914187195743784704817 / 309485009821345068724781056
def e3140Hi : ℚ := 4455653568349866993272026 / 9671406556917033397649408

theorem e3140_bounds : (e3140Lo : ℝ) ≤ Real.exp (-31 / 40) ∧ Real.exp (-31 / 40) ≤ e3140Hi := by
  have h := Real.exp_bound (x := -31 / 40) (by norm_num [abs_div]) (n := 24) (by norm_num)
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  constructor <;> simp only [e3140Lo, e3140Hi] <;> push_cast <;> linarith [h.1, h.2]

end AEGIS.CvSExpL3120V1

#print axioms AEGIS.CvSExpL3120V1.e3140_bounds
