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

/-!
AEGIS signed, fixed-width Weil cross-entry arithmetic V1.

The sign of a source-specific off-diagonal entry is not positivity of the
full Gram matrix. This module discharges ONLY the real algebra of the
prime/Archimedean composition and the three explicit rational margins.

Analytic obligations external to this module:
1. genuine von Mangoldt row enumeration and correlation identity;
2. smooth moment-zero packet and mollifier L2 approximation;
3. existing AEGIS V31 bound on the actual Archimedean integral.
This module neither assumes nor proves RH.
-/

namespace AEGIS.RHSignedWeilMarginsV1

/-- Algebraic bridge: a strict signed prime estimate plus a bounded
complex Archimedean integral yields a strict real mixed-Weil margin. -/
theorem signed_real_of_prime_arch_bound
    (E P a b c : ℝ) (A : ℂ)
    (hE : 0 ≤ E)
    (hPrime : P < -(a * E))
    (hArch : ‖A‖ ≤ b * E)
    (hBudget : b + c ≤ a) :
    P + A.re < -(c * E) := by
  have hRe : |A.re| ≤ ‖A‖ := Complex.abs_re_le_norm A
  have hA : A.re ≤ b * E :=
    (le_abs_self _).trans (hRe.trans hArch)
  have hScale : (b + c) * E ≤ a * E :=
    mul_le_mul_of_nonneg_right hBudget hE
  nlinarith

/-- Source-bound 4-term k=7 rational margin, including V31 Arch 1/100. -/
theorem k7_margin_exact :
    ((124036 / 1000000 - (11 / 10) *
      (2 * (1 / 200) + (1 / 200) ^ 2)) /
      (1 + 1 / 200) ^ 2 - 1 / 100 : ℚ) = 45737 / 448900 := by
  norm_num

theorem k7_margin_gt_tenth :
    (1 / 10 : ℚ) < 45737 / 448900 := by
  norm_num

/-- Source-bound 11-term k=10 rational margin, including V31 Arch 1/100. -/
theorem k10_margin_exact :
    ((59 / 250 - (11 / 5) *
      (2 * (1 / 200) + (1 / 200) ^ 2)) /
      (1 + 1 / 200) ^ 2 - 1 / 100 : ℚ) = 271793 / 1346700 := by
  norm_num

theorem k10_margin_gt_fifth :
    (1 / 5 : ℚ) < 271793 / 1346700 := by
  norm_num

/-- Source-bound 18-term k=11 rational margin, including V31 Arch 1/100. -/
theorem k11_margin_exact :
    ((1 / 10 - 3 *
      (2 * (1 / 200) + (1 / 200) ^ 2)) /
      (1 + 1 / 200) ^ 2 - 1 / 100 : ℚ) = 239299 / 4040100 := by
  norm_num

theorem k11_margin_gt_twentieth :
    (1 / 20 : ℚ) < 239299 / 4040100 := by
  norm_num

end AEGIS.RHSignedWeilMarginsV1

#print axioms AEGIS.RHSignedWeilMarginsV1.signed_real_of_prime_arch_bound
#print axioms AEGIS.RHSignedWeilMarginsV1.k7_margin_exact
#print axioms AEGIS.RHSignedWeilMarginsV1.k7_margin_gt_tenth
#print axioms AEGIS.RHSignedWeilMarginsV1.k10_margin_exact
#print axioms AEGIS.RHSignedWeilMarginsV1.k10_margin_gt_fifth
#print axioms AEGIS.RHSignedWeilMarginsV1.k11_margin_exact
#print axioms AEGIS.RHSignedWeilMarginsV1.k11_margin_gt_twentieth
