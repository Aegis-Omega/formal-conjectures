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
import AEGISOverlay.WeilPrimeReindexV1
import Mathlib.Tactic

/-!
AEGIS Ω · Source-exact finite-prime sieve handoff.

This module is a *Lean proof candidate*, not a kernel replay. It binds an
explicit finite sieve to the repository's actual WeilPrimeSumV1, never to a
substitute prime sum. It reuses the already proved support-vanishing theorem.

The remaining input `hsieve` is quantitative: for each index outside `s`,
either the log sample is separated from the support OR von Mangoldt is zero.
To eliminate this input for gaps 9,10,11, prove the source-bound rational
interval exclusions and the 68 finite non-prime-power cases. Nothing in
this file assumes Weil sign, RH, or a new axiom.
-/

open Set Finset Complex MeasureTheory
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFinitePrimeSieveBridgeV1
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHRationalNinePacketPrimeWindowV1
open AEGIS.RHActualMixedDefectV1

/-- Canonical *index* sets: the source `WeilPrimeTermV1` indexes m=n+1. -/
def gap9Indices : Finset ℕ := {672, 676}
def gap10Indices : Finset ℕ := {1398}
def gap11Indices : Finset ℕ := {2850, 2856, 2860, 2878, 2886}

/-- A directly reusable finite-sieve statement for the actual von Mangoldt
`tsum`. `hsieve` may use either a support separation or a zero Λ-value.
The result is an equality, not an assumed sign inequality. -/
theorem genuine_weil_prime_tsum_eq_finite_of_sieve
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hsep : (1 / 128 : ℝ) < b - a)
    (s : Finset ℕ)
    (hsieve : ∀ n : ℕ, n ∉ s →
       (1 / 128 : ℝ) < |Real.log (((n + 1 : ℕ) : ℝ)) - (b - a)| ∨
       ArithmeticFunction.vonMangoldt (n + 1) = 0) :
    WeilPrimeSumV1 (mixed p q) =
      ∑ n ∈ s, WeilPrimeTermV1 (mixed p q) n := by
  unfold WeilPrimeSumV1
  apply tsum_eq_sum
  intro n hn
  rcases hsieve n hn with hgap | hΛ
  · have hm : 0 < n + 1 := by omega
    obtain ⟨hpos, hinv⟩ :=
      distinct_fine_prime_samples_vanish_of_integer_log_gap
        p q a b hp hq hsep (n + 1) hm hgap
    simp [WeilPrimeTermV1, hpos, hinv]
  · simp [WeilPrimeTermV1, hΛ]

/-- Reduce the infinite real-log exclusion to just two endpoint
inequalities.  Here `n` is the *source* index, so m=n+1. -/
theorem log_distance_outside_index_interval
    (d : ℝ) (lo hi n : ℕ)
    (hlo : Real.log (lo : ℝ) < d - (1 / 128 : ℝ))
    (hhi : d + (1 / 128 : ℝ) < Real.log ((hi + 2 : ℕ) : ℝ))
    (hout : n ∉ Finset.Icc lo hi) :
    (1 / 128 : ℝ) <
      |Real.log (((n + 1 : ℕ) : ℝ)) - d| := by
  have hmpos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos n
  by_cases hbelow : n < lo
  · have hnlo : n + 1 ≤ lo := by omega
    have hr : (((n + 1 : ℕ) : ℝ)) ≤ (lo : ℝ) := by exact_mod_cast hnlo
    have hlog := Real.log_le_log hmpos hr
    have hneg : Real.log (((n + 1 : ℕ) : ℝ)) - d < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  · have hnot : ¬ (lo ≤ n ∧ n ≤ hi) := by
      simpa only [Finset.mem_Icc] using hout
    have hnhi : hi + 2 ≤ n + 1 := by omega
    have hr : (((hi + 2 : ℕ) : ℝ)) ≤ (((n + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hnhi
    have hhpos : (0 : ℝ) < (((hi + 2 : ℕ) : ℝ)) := by positivity
    have hlog := Real.log_le_log hhpos hr
    have hpos : 0 < Real.log (((n + 1 : ℕ) : ℝ)) - d := by linarith
    rw [abs_of_pos hpos]
    linarith

/-- All *infinite* index work follows from two real-log endpoint checks;
only finitely many von Mangoldt zero facts remain on the chosen interval. -/
theorem genuine_weil_prime_tsum_eq_finite_of_interval_and_sieve
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hsep : (1 / 128 : ℝ) < b - a)
    (lo hi : ℕ) (s : Finset ℕ)
    (hlo : Real.log (lo : ℝ) < (b - a) - (1 / 128 : ℝ))
    (hhi : (b - a) + (1 / 128 : ℝ) <
      Real.log ((hi + 2 : ℕ) : ℝ))
    (hfinite : ∀ n ∈ Finset.Icc lo hi, n ∉ s →
      ArithmeticFunction.vonMangoldt (n + 1) = 0) :
    WeilPrimeSumV1 (mixed p q) =
      ∑ n ∈ s, WeilPrimeTermV1 (mixed p q) n := by
  apply genuine_weil_prime_tsum_eq_finite_of_sieve
    p q a b hp hq hsep s
  intro n hn
  by_cases hin : n ∈ Finset.Icc lo hi
  · exact Or.inr (hfinite n hin hn)
  · exact Or.inl
      (log_distance_outside_index_interval (b - a) lo hi n hlo hhi hin)

/-- Explicit five-prime gap-11 handoff. The *only* remaining assumption is
its finite sieve certificate, not Weil positivity or a sign budget. -/
theorem gap11_weil_prime_eq_five_terms
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hsep : (1 / 128 : ℝ) < b - a)
    (hsieve : ∀ n : ℕ, n ∉ gap11Indices →
       (1 / 128 : ℝ) < |Real.log (((n + 1 : ℕ) : ℝ)) - (b - a)| ∨
       ArithmeticFunction.vonMangoldt (n + 1) = 0) :
    WeilPrimeSumV1 (mixed p q) =
      ∑ n ∈ gap11Indices, WeilPrimeTermV1 (mixed p q) n := by
  exact genuine_weil_prime_tsum_eq_finite_of_sieve
    p q a b hp hq hsep gap11Indices hsieve

/-! Finite decidable prime-power ledgers, subject to kernel replay. -/
set_option maxRecDepth 65536 in
set_option maxHeartbeats 20000000 in
theorem gap9_exact_primepower_indices :
    (Finset.Icc 670 679).filter (fun n : ℕ => IsPrimePow (n + 1)) = gap9Indices := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 20000000 in
theorem gap10_exact_primepower_indices :
    (Finset.Icc 1382 1402).filter (fun n : ℕ => IsPrimePow (n + 1)) = gap10Indices := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 20000000 in
theorem gap11_exact_primepower_indices :
    (Finset.Icc 2850 2894).filter (fun n : ℕ => IsPrimePow (n + 1)) = gap11Indices := by decide

/-- Convert the finite ledger into genuine von Mangoldt zeros. -/
theorem gap11_nonactive_vonMangoldt_zero
    (n : ℕ) (hn : n ∈ Finset.Icc 2850 2894) (hnot : n ∉ gap11Indices) :
    ArithmeticFunction.vonMangoldt (n + 1) = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
  intro hp
  have hx : n ∈ (Finset.Icc 2850 2894).filter (fun n : ℕ => IsPrimePow (n + 1)) :=
    Finset.mem_filter.mpr ⟨hn, hp⟩
  rw [gap11_exact_primepower_indices] at hx
  exact hnot hx

/-- Actual gap-11 five-term identity with only real-log endpoint premises. -/
theorem gap11_actual_weil_prime_five_term_of_endpoints
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a) (hq : WidthOneOneTwentyEightAt q b)
    (hsep : (1 / 128 : ℝ) < b - a)
    (hlo : Real.log (2850 : ℝ) < (b - a) - (1 / 128 : ℝ))
    (hhi : (b - a) + (1 / 128 : ℝ) < Real.log (2896 : ℝ)) :
    WeilPrimeSumV1 (mixed p q) =
      ∑ n ∈ gap11Indices, WeilPrimeTermV1 (mixed p q) n := by
  exact genuine_weil_prime_tsum_eq_finite_of_interval_and_sieve
    p q a b hp hq hsep 2850 2894 gap11Indices hlo hhi
      (fun n hn hnot => gap11_nonactive_vonMangoldt_zero n hn hnot)

end AEGIS.RHFinitePrimeSieveBridgeV1

#print axioms AEGIS.RHFinitePrimeSieveBridgeV1.genuine_weil_prime_tsum_eq_finite_of_sieve
#print axioms AEGIS.RHFinitePrimeSieveBridgeV1.gap11_weil_prime_eq_five_terms
