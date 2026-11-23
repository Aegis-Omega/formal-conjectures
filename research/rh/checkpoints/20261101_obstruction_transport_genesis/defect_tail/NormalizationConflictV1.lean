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
import Mathlib.Tactic

/-! Scalar incompatibility of two necessary conditions for a proposed
pointwise symbol comparison. The analytic derivation of these conditions
for the actual Weil symbol is ordinary analysis in DEFECT_TAIL.md.
This file does not claim to formalize that analytic connection. -/

set_option autoImplicit false

namespace AEGIS.NormalizationConflictV1

theorem incompatible_low_and_high_frequency_bounds (s C : ℝ)
    (hs : 1 < s) (hzero : s ≤ C) (htail : C * s ^ 3 ≤ 1) : False := by
  have hspos : 0 < s := lt_trans zero_lt_one hs
  have hp : 0 < (s - 1) * (s ^ 3 + s ^ 2 + s + 1) := by positivity
  have hfour : 1 < s ^ 4 := by nlinarith [hp]
  have hbound : s ^ 4 ≤ C * s ^ 3 := by
    calc
      s ^ 4 = s * s ^ 3 := by ring
      _ ≤ C * s ^ 3 := mul_le_mul_of_nonneg_right hzero (by positivity)
  linarith

end AEGIS.NormalizationConflictV1

#print axioms AEGIS.NormalizationConflictV1.incompatible_low_and_high_frequency_bounds
