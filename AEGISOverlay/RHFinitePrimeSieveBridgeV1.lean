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
open AEGIS.WeilMixedClosureV2
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

/-! Split certified prime-power ledgers, avoiding large opaque `decide` reductions. -/
private theorem npp_671 : ¬IsPrimePow 671 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 671).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_672 : ¬IsPrimePow 672 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 672).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem pp_673 : IsPrimePow 673 := by
  exact (show Nat.Prime 673 by norm_num).prime.isPrimePow

private theorem npp_674 : ¬IsPrimePow 674 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 674).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_675 : ¬IsPrimePow 675 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 675).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_676 : ¬IsPrimePow 676 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 676).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem pp_677 : IsPrimePow 677 := by
  exact (show Nat.Prime 677 by norm_num).prime.isPrimePow

private theorem npp_678 : ¬IsPrimePow 678 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 678).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_679 : ¬IsPrimePow 679 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 679).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_680 : ¬IsPrimePow 680 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 680).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

set_option maxRecDepth 65536 in
set_option maxHeartbeats 20000000 in
theorem gap9_exact_primepower_indices :
    (Finset.Icc 670 679).filter (fun n : ℕ => IsPrimePow (n + 1)) = gap9Indices := by
  classical
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  by_cases hin : 670 ≤ n ∧ n ≤ 679
  · have hlo : 670 ≤ n := hin.1
    have hhi : n ≤ 679 := hin.2
    interval_cases n <;>
      simp [npp_671, npp_672, pp_673, npp_674, npp_675, npp_676, pp_677, npp_678, npp_679, npp_680, gap9Indices]
  · have hnot : n ∉ gap9Indices := by
      simp only [gap9Indices, Finset.mem_insert, Finset.mem_singleton]
      omega
    simp [hin, hnot]

private theorem npp_1383 : ¬IsPrimePow 1383 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1383).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1384 : ¬IsPrimePow 1384 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1384).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1385 : ¬IsPrimePow 1385 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1385).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1386 : ¬IsPrimePow 1386 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1386).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1387 : ¬IsPrimePow 1387 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1387).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1388 : ¬IsPrimePow 1388 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1388).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1389 : ¬IsPrimePow 1389 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1389).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1390 : ¬IsPrimePow 1390 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1390).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1391 : ¬IsPrimePow 1391 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1391).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1392 : ¬IsPrimePow 1392 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1392).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1393 : ¬IsPrimePow 1393 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1393).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1394 : ¬IsPrimePow 1394 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1394).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1395 : ¬IsPrimePow 1395 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1395).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1396 : ¬IsPrimePow 1396 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1396).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1397 : ¬IsPrimePow 1397 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1397).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1398 : ¬IsPrimePow 1398 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1398).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem pp_1399 : IsPrimePow 1399 := by
  exact (show Nat.Prime 1399 by norm_num).prime.isPrimePow

private theorem npp_1400 : ¬IsPrimePow 1400 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1400).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1401 : ¬IsPrimePow 1401 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1401).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1402 : ¬IsPrimePow 1402 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1402).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_1403 : ¬IsPrimePow 1403 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 1403).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

set_option maxRecDepth 65536 in
set_option maxHeartbeats 20000000 in
theorem gap10_exact_primepower_indices :
    (Finset.Icc 1382 1402).filter (fun n : ℕ => IsPrimePow (n + 1)) = gap10Indices := by
  classical
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  by_cases hin : 1382 ≤ n ∧ n ≤ 1402
  · have hlo : 1382 ≤ n := hin.1
    have hhi : n ≤ 1402 := hin.2
    interval_cases n <;>
      simp [npp_1383, npp_1384, npp_1385, npp_1386, npp_1387, npp_1388, npp_1389, npp_1390, npp_1391, npp_1392, npp_1393, npp_1394, npp_1395, npp_1396, npp_1397, npp_1398, pp_1399, npp_1400, npp_1401, npp_1402, npp_1403, gap10Indices]
  · have hnot : n ∉ gap10Indices := by
      simp only [gap10Indices, Finset.mem_insert, Finset.mem_singleton]
      omega
    simp [hin, hnot]

private theorem pp_2851 : IsPrimePow 2851 := by
  exact (show Nat.Prime 2851 by norm_num).prime.isPrimePow

private theorem npp_2852 : ¬IsPrimePow 2852 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2852).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2853 : ¬IsPrimePow 2853 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2853).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2854 : ¬IsPrimePow 2854 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2854).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2855 : ¬IsPrimePow 2855 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2855).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2856 : ¬IsPrimePow 2856 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2856).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem pp_2857 : IsPrimePow 2857 := by
  exact (show Nat.Prime 2857 by norm_num).prime.isPrimePow

private theorem npp_2858 : ¬IsPrimePow 2858 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2858).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2859 : ¬IsPrimePow 2859 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2859).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2860 : ¬IsPrimePow 2860 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2860).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem pp_2861 : IsPrimePow 2861 := by
  exact (show Nat.Prime 2861 by norm_num).prime.isPrimePow

private theorem npp_2862 : ¬IsPrimePow 2862 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2862).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2863 : ¬IsPrimePow 2863 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2863).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2864 : ¬IsPrimePow 2864 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2864).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2865 : ¬IsPrimePow 2865 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2865).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2866 : ¬IsPrimePow 2866 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2866).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2867 : ¬IsPrimePow 2867 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2867).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2868 : ¬IsPrimePow 2868 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2868).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2869 : ¬IsPrimePow 2869 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2869).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2870 : ¬IsPrimePow 2870 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2870).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2871 : ¬IsPrimePow 2871 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2871).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2872 : ¬IsPrimePow 2872 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2872).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2873 : ¬IsPrimePow 2873 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2873).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2874 : ¬IsPrimePow 2874 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2874).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2875 : ¬IsPrimePow 2875 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2875).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2876 : ¬IsPrimePow 2876 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2876).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2877 : ¬IsPrimePow 2877 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2877).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2878 : ¬IsPrimePow 2878 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2878).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem pp_2879 : IsPrimePow 2879 := by
  exact (show Nat.Prime 2879 by norm_num).prime.isPrimePow

private theorem npp_2880 : ¬IsPrimePow 2880 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2880).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2881 : ¬IsPrimePow 2881 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2881).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2882 : ¬IsPrimePow 2882 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2882).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2883 : ¬IsPrimePow 2883 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2883).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2884 : ¬IsPrimePow 2884 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2884).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2885 : ¬IsPrimePow 2885 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2885).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2886 : ¬IsPrimePow 2886 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2886).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem pp_2887 : IsPrimePow 2887 := by
  exact (show Nat.Prime 2887 by norm_num).prime.isPrimePow

private theorem npp_2888 : ¬IsPrimePow 2888 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2888).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2889 : ¬IsPrimePow 2889 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2889).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2890 : ¬IsPrimePow 2890 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2890).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2891 : ¬IsPrimePow 2891 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2891).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2892 : ¬IsPrimePow 2892 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2892).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2893 : ¬IsPrimePow 2893 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2893).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2894 : ¬IsPrimePow 2894 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2894).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

private theorem npp_2895 : ¬IsPrimePow 2895 := by
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac 2895).mp hpp
  norm_num at hk
  interval_cases k <;> norm_num at heq

set_option maxRecDepth 65536 in
set_option maxHeartbeats 20000000 in
theorem gap11_exact_primepower_indices :
    (Finset.Icc 2850 2894).filter (fun n : ℕ => IsPrimePow (n + 1)) = gap11Indices := by
  classical
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  by_cases hin : 2850 ≤ n ∧ n ≤ 2894
  · have hlo : 2850 ≤ n := hin.1
    have hhi : n ≤ 2894 := hin.2
    interval_cases n <;>
      simp [pp_2851, npp_2852, npp_2853, npp_2854, npp_2855, npp_2856, pp_2857, npp_2858, npp_2859, npp_2860, pp_2861, npp_2862, npp_2863, npp_2864, npp_2865, npp_2866, npp_2867, npp_2868, npp_2869, npp_2870, npp_2871, npp_2872, npp_2873, npp_2874, npp_2875, npp_2876, npp_2877, npp_2878, pp_2879, npp_2880, npp_2881, npp_2882, npp_2883, npp_2884, npp_2885, npp_2886, pp_2887, npp_2888, npp_2889, npp_2890, npp_2891, npp_2892, npp_2893, npp_2894, npp_2895, gap11Indices]
  · have hnot : n ∉ gap11Indices := by
      simp only [gap11Indices, Finset.mem_insert, Finset.mem_singleton]
      omega
    simp [hin, hnot]

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
