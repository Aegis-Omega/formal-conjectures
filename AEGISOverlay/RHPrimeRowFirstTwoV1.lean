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
AEGIS Omega: a strictly bounded prime-pair producer for the first two
integer-log-free fine correlation windows. This neither certifies an
arbitrary prime row nor produces an arbitrary-packet decomposition.
-/

open Set Finset Complex MeasureTheory
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHGramExpansionV13
open AEGIS.RHRationalNinePacketPrimeWindowV1

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHPrimeRowFirstTwoV1

/-- For the two explicit integer-log-free windows, EVERY actual von Mangoldt
summand is zero (including prime powers), and the genuine mixed Weil B entry
has an outward Q16.16 norm cost 676. The Arch term is charged, not erased.
The center-gap and fine-support hypotheses are visible: this is not a
universal row or RH theorem. -/
theorem actual_prime_pair_q16_first_two_log_windows
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hmin : (35 / 128 : ℝ) ≤ b - a)
    (hgap : b - a < Real.log 2 - (1 / 128 : ℝ) ∨
      (Real.log 2 + (1 / 128 : ℝ) < b - a ∧
        b - a < Real.log 3 - (1 / 128 : ℝ))) :
    WeilPrimeSumV1 (mixed p q) = 0 ∧
      ‖B p q‖ ≤ (676 / 65536 : ℝ) * (energy p.1 + energy q.1) := by
  rcases hgap with hbelow | hbetween
  · constructor
    · exact AEGIS.RHActualMixedDefectV1.distinct_fine_prime_zero_below_log_two
        p q a b hp hq (by linarith) hbelow
    · exact AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_q16_middle_gap
        p q a b hp hq hm hmin hbelow
  · obtain ⟨hlow, hhigh⟩ := hbetween
    constructor
    · exact AEGIS.RHActualMixedDefectV1.distinct_fine_prime_zero_between_log_two_three
        p q a b hp hq hlow hhigh
    · have harch :=
        AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_between_log_two_three
          p q a b hp hq hm hlow hhigh
      have hkernel :=
        AEGIS.RHActualMixedDefectV1.moment_zero_fine_middle_arch_q16
          ((b - a) - 1 / 128) (by linarith)
      exact harch.trans (mul_le_mul_of_nonneg_right hkernel
        (add_nonneg (energy_nonnegative p.1) (energy_nonnegative q.1)))

end AEGIS.RHPrimeRowFirstTwoV1

#print axioms AEGIS.RHPrimeRowFirstTwoV1.actual_prime_pair_q16_first_two_log_windows
