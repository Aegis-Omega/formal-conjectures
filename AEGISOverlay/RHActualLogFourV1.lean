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

import AEGISOverlay.RHActualMixedDefectV1

/-!
Source-bound exact von Mangoldt cutoff for the genuine mixed Weil form.
No surrogate gram, no universal sign hypothesis and no loss of the inverse sample.
This is additional proof source; it does not establish RH.
-/

open Set Finset Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHActualLogFourV1

open AEGIS.RHActualMixedDefectV1
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilDisjointEnergyV2

/-- For separated fine packets with correlation horizon below log 4,
both genuine von Mangoldt samples vanish for every m >= 4. -/
theorem actual_fine_prime_sum_truncated_below_log_four
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hsep : (1 / 128 : ℝ) < b - a)
    (hclock : b - a + (1 / 128 : ℝ) < Real.log 4) :
    WeilPrimeSumV1 (mixed p q) =
      ∑ n ∈ Finset.range 3, WeilPrimeTermV1 (mixed p q) n := by
  have htail : ∀ n : ℕ, 3 ≤ n →
      WeilPrimeTermV1 (mixed p q) n = 0 := by
    intro n hn
    have hm : 0 < n + 1 := by omega
    have hfour : 4 ≤ n + 1 := by omega
    have hfourR : (4 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast hfour
    have hlog : Real.log (4 : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) hfourR
    have haway : (1 / 128 : ℝ) <
        |Real.log ((n + 1 : ℕ) : ℝ) - (b - a)| := by
      rw [abs_of_pos (by linarith)]
      linarith
    obtain ⟨hpos, hinv⟩ :=
      distinct_fine_prime_samples_vanish_of_integer_log_gap
        p q a b hp hq hsep (n + 1) hm haway
    simp only [WeilPrimeTermV1, hpos, hinv, mul_zero, add_zero]
  unfold WeilPrimeSumV1
  apply tsum_eq_sum
  intro n hn
  exact htail n (Nat.le_of_not_gt (by simpa using hn))

/-- Reuse the already proved actual full-Weil Arch+prime norm estimate
with exact arithmetic summation restricted to m = 1, 2, 3.
The m=1 term has zero von Mangoldt weight. -/
theorem actual_fine_B_bounded_by_two_prime_samples
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hsep : (1 / 128 : ℝ) < b - a)
    (hgap : Real.log 2 ≤ b - a)
    (hclock : b - a + (1 / 128 : ℝ) < Real.log 4) :
    ‖B p q‖ ≤
      ‖∑ n ∈ Finset.range 3, WeilPrimeTermV1 (mixed p q) n‖ +
        (1 / 200 : ℝ) * (energy p.1 + energy q.1) := by
  have hsum :=
    actual_fine_prime_sum_truncated_below_log_four
      p q a b hp hq hsep hclock
  have hbound :=
    distinct_fine_far_actual_B_norm_le_prime_plus_arch
      p q a b hp hq hm hgap
  rw [hsum] at hbound
  exact hbound

end AEGIS.RHActualLogFourV1

#print axioms AEGIS.RHActualLogFourV1.actual_fine_prime_sum_truncated_below_log_four
#print axioms AEGIS.RHActualLogFourV1.actual_fine_B_bounded_by_two_prime_samples
