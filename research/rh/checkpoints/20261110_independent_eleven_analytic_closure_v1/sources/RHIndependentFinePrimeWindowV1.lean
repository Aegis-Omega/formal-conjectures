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

import RHIndependentFinePrimeSupportV1

/-!
Full actual prime-sum consumers for independent fine packets.
The only arithmetic premise is a scalar von Mangoldt window certificate.
For finite candidate sets, the Nat indices are those of WeilPrimeTermV1:
index n represents the positive integer n+1. No sign or mixed-form bound
is assumed, and all complex signed prime terms are retained.
-/

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHIndependentFinePrimeWindowV1

open AEGIS.WeilMixedClosureV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHIndependentFinePrimeSupportV1

theorem prime_sum_zero_of_fine_window_vonMangoldt
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : LogSupportIn p (a - 1 / 256) (a + 1 / 256))
    (hq : LogSupportIn q (b - 1 / 256) (b + 1 / 256))
    (hsep : (1 / 128 : ℝ) < b - a)
    (hvm : ∀ m : ℕ, 0 < m →
      |Real.log (m : ℝ) - (b - a)| ≤ 1 / 128 →
        ArithmeticFunction.vonMangoldt m = 0) :
    WeilPrimeSumV1 (mixed p q) = 0 := by
  unfold WeilPrimeSumV1
  have hterms : ∀ n : ℕ, WeilPrimeTermV1 (mixed p q) n = 0 := by
    intro n
    exact prime_term_zero_of_fine_window_vonMangoldt p q a b hp hq hsep n
      (hvm (n + 1) (by omega))
  simp only [hterms, tsum_zero]

theorem prime_sum_eq_sum_of_fine_window_vonMangoldt
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : LogSupportIn p (a - 1 / 256) (a + 1 / 256))
    (hq : LogSupportIn q (b - 1 / 256) (b + 1 / 256))
    (hsep : (1 / 128 : ℝ) < b - a) (S : Finset ℕ)
    (hvm : ∀ n : ℕ, n ∉ S →
      |Real.log ((n + 1 : ℕ) : ℝ) - (b - a)| ≤ 1 / 128 →
        ArithmeticFunction.vonMangoldt (n + 1) = 0) :
    WeilPrimeSumV1 (mixed p q) =
      ∑ n ∈ S, WeilPrimeTermV1 (mixed p q) n := by
  unfold WeilPrimeSumV1
  apply tsum_eq_sum
  intro n hn
  exact prime_term_zero_of_fine_window_vonMangoldt p q a b hp hq hsep n
    (hvm n hn)

end AEGIS.RHIndependentFinePrimeWindowV1

#print axioms AEGIS.RHIndependentFinePrimeWindowV1.prime_sum_zero_of_fine_window_vonMangoldt
#print axioms AEGIS.RHIndependentFinePrimeWindowV1.prime_sum_eq_sum_of_fine_window_vonMangoldt
