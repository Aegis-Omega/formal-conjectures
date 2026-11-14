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
# Rational enclosure of `e^{−49/64}` (window `L = 49/32`)

`e4964_bounds` from `Real.exp_bound` with 24 terms, as `CvSExpL32V1.e34_bounds` at `L = 3/2`.
Not RH.
-/

namespace AEGIS.CvSExpL4932V1

def e4964Lo : ℚ := 143923895647018040563762077 / 309485009821345068724781056
def e4964Hi : ℚ := 4497621738969313767617565 / 9671406556917033397649408

theorem e4964_bounds : (e4964Lo : ℝ) ≤ Real.exp (-49 / 64) ∧ Real.exp (-49 / 64) ≤ e4964Hi := by
  have h := Real.exp_bound (x := -49 / 64) (by norm_num [abs_div]) (n := 24) (by norm_num)
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  constructor <;> simp only [e4964Lo, e4964Hi] <;> push_cast <;> linarith [h.1, h.2]

end AEGIS.CvSExpL4932V1

#print axioms AEGIS.CvSExpL4932V1.e4964_bounds
