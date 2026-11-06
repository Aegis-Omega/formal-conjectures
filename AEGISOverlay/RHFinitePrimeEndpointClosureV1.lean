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
import AEGISOverlay.RHFinitePrimeSieveBridgeV1
import Mathlib.Tactic

/-!
AEGIS Ω: exact endpoint closure for the existing finite prime sieve.

This module does NOT define a new Weil form, introduce an axiom, or prove RH.
It closes the previously exposed real-log endpoint inputs for the three
finite resonance windows using Mathlib's verified exponential upper bound
  exp(1/128) <= 128/127
and six finite rational inequalities, plus the finite IsPrimePow ledgers
already present in RHFinitePrimeSieveBridgeV1.

Status: Lean source candidate, NOT kernel replayed locally.
-/

open Set Finset Complex MeasureTheory
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFinitePrimeEndpointClosureV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHRationalNinePacketPrimeWindowV1
open AEGIS.RHFinitePrimeSieveBridgeV1

private theorem exp_one_128_le :
    Real.exp (1 / 128 : ℝ) ≤ 128 / 127 := by
  have h := Real.exp_bound_div_one_sub_of_interval
    (show (0 : ℝ) ≤ 1 / 128 by norm_num)
    (show (1 / 128 : ℝ) < 1 by norm_num)
  convert h using 1; norm_num

/-- A generic *exact rational* endpoint test: two rational comparisons
suffice to enclose both real logarithmic endpoints. -/
theorem log_interval_of_rational_power_bounds
    (k lo hi : ℕ) (hlo_pos : 0 < lo) (hhi_pos : 0 < hi)
    (hlow : (lo : ℝ) * (128 / 127 : ℝ) < ((33 : ℝ) / 16) ^ k)
    (hhigh : ((33 : ℝ) / 16) ^ k * (128 / 127 : ℝ) < (hi : ℝ)) :
    Real.log (lo : ℝ) <
        (k : ℝ) * Real.log ((33 : ℝ) / 16) - 1 / 128 ∧
      (k : ℝ) * Real.log ((33 : ℝ) / 16) + 1 / 128 <
        Real.log (hi : ℝ) := by
  have hloR : (0 : ℝ) < (lo : ℝ) := by exact_mod_cast hlo_pos
  have hhiR : (0 : ℝ) < (hi : ℝ) := by exact_mod_cast hhi_pos
  have hr : (0 : ℝ) < (33 : ℝ) / 16 := by norm_num
  have hpowexp :
      Real.exp ((k : ℝ) * Real.log ((33 : ℝ) / 16)) =
        ((33 : ℝ) / 16) ^ k := by
    simpa only [Real.exp_log hr] using
      (Real.exp_nat_mul (Real.log ((33 : ℝ) / 16)) k)
  have hleft_exp :
      Real.exp (Real.log (lo : ℝ) + 1 / 128) <
        Real.exp ((k : ℝ) * Real.log ((33 : ℝ) / 16)) := by
    rw [Real.exp_add, Real.exp_log hloR, hpowexp]
    exact (mul_le_mul_of_nonneg_left exp_one_128_le
      (le_of_lt hloR)).trans_lt hlow
  have hright_exp :
      Real.exp ((k : ℝ) * Real.log ((33 : ℝ) / 16) + 1 / 128) <
        Real.exp (Real.log (hi : ℝ)) := by
    rw [Real.exp_add, hpowexp, Real.exp_log hhiR]
    exact (mul_le_mul_of_nonneg_left exp_one_128_le
      (pow_nonneg (le_of_lt hr) k)).trans_lt hhigh
  constructor
  · have h := (Real.exp_lt_exp).mp hleft_exp
    linarith
  · exact (Real.exp_lt_exp).mp hright_exp

/-- k=9: all m outside [671,680] are separated from the mixed log support. -/
theorem gap9_log_endpoints :
    Real.log (670 : ℝ) <
        (9 : ℝ) * Real.log ((33 : ℝ) / 16) - 1 / 128 ∧
      (9 : ℝ) * Real.log ((33 : ℝ) / 16) + 1 / 128 <
        Real.log (681 : ℝ) := by
  exact log_interval_of_rational_power_bounds 9 670 681
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- k=10: all m outside [1383,1403] are separated. -/
theorem gap10_log_endpoints :
    Real.log (1382 : ℝ) <
        (10 : ℝ) * Real.log ((33 : ℝ) / 16) - 1 / 128 ∧
      (10 : ℝ) * Real.log ((33 : ℝ) / 16) + 1 / 128 <
        Real.log (1404 : ℝ) := by
  exact log_interval_of_rational_power_bounds 10 1382 1404
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- k=11: all m outside [2851,2895] are separated. -/
theorem gap11_log_endpoints :
    Real.log (2850 : ℝ) <
        (11 : ℝ) * Real.log ((33 : ℝ) / 16) - 1 / 128 ∧
      (11 : ℝ) * Real.log ((33 : ℝ) / 16) + 1 / 128 <
        Real.log (2896 : ℝ) := by
  exact log_interval_of_rational_power_bounds 11 2850 2896
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Reuse the original finite sieve, now discharging its finite ledger
and both real-log endpoint inputs via source-bound proofs. -/
theorem finite_actual_prime_of_rational_window
    (k lo hi : ℕ) (s : Finset ℕ) (hlo_pos : 1 ≤ lo)
    (hend : Real.log (lo : ℝ) <
        (k : ℝ) * Real.log ((33 : ℝ) / 16) - 1 / 128 ∧
      (k : ℝ) * Real.log ((33 : ℝ) / 16) + 1 / 128 <
        Real.log ((hi + 2 : ℕ) : ℝ))
    (hledger : (Finset.Icc lo hi).filter
        (fun n : ℕ => IsPrimePow (n + 1)) = s)
    (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q
      (a + (k : ℝ) * Real.log ((33 : ℝ) / 16))) :
    WeilPrimeSumV1 (mixed p q) =
      ∑ n ∈ s, WeilPrimeTermV1 (mixed p q) n := by
  obtain ⟨hlow, hhigh⟩ := hend
  have hloglo : (0 : ℝ) ≤ Real.log (lo : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hlo_pos)
  have hsep : (1 / 128 : ℝ) <
      (a + (k : ℝ) * Real.log ((33 : ℝ) / 16)) - a := by
    linarith
  apply genuine_weil_prime_tsum_eq_finite_of_interval_and_sieve
    p q a (a + (k : ℝ) * Real.log ((33 : ℝ) / 16))
    hp hq hsep lo hi s
  · convert hlow using 1; ring
  · convert hhigh using 1; ring
  · intro n hn hnnot
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    intro hnprime
    have hin : n ∈ (Finset.Icc lo hi).filter
        (fun n : ℕ => IsPrimePow (n + 1)) :=
      Finset.mem_filter.mpr ⟨hn, hnprime⟩
    rw [hledger] at hin
    exact hnnot hin

/-- Closed finite identity for k=9; no caller-supplied sieve or endpoints. -/
theorem gap9_actual_weil_prime_two_terms
    (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q
      (a + (9 : ℝ) * Real.log ((33 : ℝ) / 16))) :
    WeilPrimeSumV1 (mixed p q) =
      ∑ n ∈ gap9Indices, WeilPrimeTermV1 (mixed p q) n := by
  exact finite_actual_prime_of_rational_window 9 670 679 gap9Indices
    (by norm_num) gap9_log_endpoints gap9_exact_primepower_indices
    p q a hp hq

/-- Closed finite identity for k=10; no caller-supplied sieve or endpoints. -/
theorem gap10_actual_weil_prime_one_term
    (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q
      (a + (10 : ℝ) * Real.log ((33 : ℝ) / 16))) :
    WeilPrimeSumV1 (mixed p q) =
      ∑ n ∈ gap10Indices, WeilPrimeTermV1 (mixed p q) n := by
  exact finite_actual_prime_of_rational_window 10 1382 1402 gap10Indices
    (by norm_num) gap10_log_endpoints gap10_exact_primepower_indices
    p q a hp hq

/-- Closed finite identity for k=11; no caller-supplied sieve or endpoints. -/
theorem gap11_actual_weil_prime_five_terms
    (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q
      (a + (11 : ℝ) * Real.log ((33 : ℝ) / 16))) :
    WeilPrimeSumV1 (mixed p q) =
      ∑ n ∈ gap11Indices, WeilPrimeTermV1 (mixed p q) n := by
  exact finite_actual_prime_of_rational_window 11 2850 2894 gap11Indices
    (by norm_num) gap11_log_endpoints gap11_exact_primepower_indices
    p q a hp hq

end AEGIS.RHFinitePrimeEndpointClosureV1

#print axioms AEGIS.RHFinitePrimeEndpointClosureV1.gap9_actual_weil_prime_two_terms
#print axioms AEGIS.RHFinitePrimeEndpointClosureV1.gap10_actual_weil_prime_one_term
#print axioms AEGIS.RHFinitePrimeEndpointClosureV1.gap11_actual_weil_prime_five_terms