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
import Mathlib

/-!
AEGIS Ω — rational improvement of the separated moment-zero Arch tail.
This file adds mathematical source candidates, NOT an unconditional RH claim.
All genuine von Mangoldt terms remain outside the Arch bound.
-/

open Finset
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHArchRow29V1

open AEGIS.RHGramExpansionV13
open AEGIS.RHActualMixedDefectV1
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHRationalNinePacketPrimeWindowV1

private theorem exp_five_ge_145 : (145 : ℝ) ≤ Real.exp 5 := by
  have h : (∑ i ∈ Finset.range 11, (5 : ℝ) ^ i / (i.factorial : ℝ)) ≤
      Real.exp 5 :=
    Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5) 11
  have hs : (145 : ℝ) ≤
      ∑ i ∈ Finset.range 11, (5 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  exact hs.trans h

private theorem exp_four_ge_54 : (54 : ℝ) ≤ Real.exp 4 := by
  have h : (∑ i ∈ Finset.range 11, (4 : ℝ) ^ i / (i.factorial : ℝ)) ≤
      Real.exp 4 :=
    Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 11
  have hs : (54 : ℝ) ≤
      ∑ i ∈ Finset.range 11, (4 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  exact hs.trans h

/-- The exact exponential kernel at gap ≥ 2k is bounded by
(1/32)*(54/53)*(1/145)^k, without floating-point arithmetic. -/
theorem arch_kernel_geometric_145 (δ : ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hδ : 2 * (k : ℝ) ≤ δ) :
    (1 / 32 : ℝ) *
        (Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ))) ≤
      ((1 / 32 : ℝ) * (54 / 53)) * ((1 / 145 : ℝ) ^ k) := by
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hd2 : (2 : ℝ) ≤ δ := by nlinarith
  have hpair5 : Real.exp 5 * Real.exp (-5) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hpair4 : Real.exp 4 * Real.exp (-4) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have h5 : Real.exp (-5) ≤ (1 / 145 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right exp_five_ge_145
      (Real.exp_nonneg (-5))
    rw [hpair5] at hm
    nlinarith
  have h4 : Real.exp (-4) ≤ (1 / 54 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right exp_four_ge_54
      (Real.exp_nonneg (-4))
    rw [hpair4] at hm
    nlinarith
  have hdenUpper : Real.exp (-2 * δ) ≤ (1 / 54 : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith : -2 * δ ≤ -4)).trans h4
  have hden : (53 / 54 : ℝ) ≤ 1 - Real.exp (-2 * δ) := by linarith
  have hdpos : 0 < 1 - Real.exp (-2 * δ) := by linarith
  have hpow : Real.exp (-(5 * (k : ℝ))) = (Real.exp (-5)) ^ k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hnum : Real.exp (-5 * δ / 2) ≤ (1 / 145 : ℝ) ^ k := by
    calc
      _ ≤ Real.exp (-(5 * (k : ℝ))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = (Real.exp (-5)) ^ k := hpow
      _ ≤ (1 / 145 : ℝ) ^ k :=
        pow_le_pow_left₀ (Real.exp_nonneg _) h5 k
  have hratio :
      Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ)) ≤
        ((1 / 145 : ℝ) ^ k) / (53 / 54) := by
    apply (div_le_div_iff₀ hdpos
      (by norm_num : (0 : ℝ) < 53 / 54)).mpr
    calc
      Real.exp (-5 * δ / 2) * (53 / 54) ≤
          ((1 / 145 : ℝ) ^ k) * (53 / 54) :=
        mul_le_mul_of_nonneg_right hnum (by norm_num)
      _ ≤ ((1 / 145 : ℝ) ^ k) *
          (1 - Real.exp (-2 * δ)) :=
        mul_le_mul_of_nonneg_left hden
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 145) k)
  calc
    _ ≤ (1 / 32 : ℝ) * (((1 / 145 : ℝ) ^ k) / (53 / 54)) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = ((1 / 32 : ℝ) * (54 / 53)) * ((1 / 145 : ℝ) ^ k) := by ring

/-- Dimension-free bound on the WHOLE row: 3/6784 < 29/65536. -/
theorem geometric_arch_row_29 {n : ℕ} (i : Fin (n + 1)) :
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      ((1 / 32 : ℝ) * (54 / 53)) *
        ((1 / 145 : ℝ) ^ Nat.dist i j)) ≤
      (29 / 65536 : ℝ) := by
  have hgeom :
      (∑ k ∈ Finset.Icc 1 n, ((1 / 145 : ℝ) ^ k)) ≤
        (1 / 144 : ℝ) := by
    have hIcc : (Finset.Icc 1 n : Finset ℕ) = Finset.Ico 1 (n + 1) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    calc
      _ = ∑ k ∈ Finset.Ico 1 (n + 1), ((1 / 145 : ℝ) ^ k) := by rw [hIcc]
      _ ≤ ((1 / 145 : ℝ) ^ 1) / (1 - (1 / 145 : ℝ)) :=
        geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
      _ = (1 / 144 : ℝ) := by norm_num
  have hcost :
      (∑ k ∈ Finset.Icc 1 n,
        ((1 / 32 : ℝ) * (54 / 53)) * ((1 / 145 : ℝ) ^ k)) ≤
        ((1 / 32 : ℝ) * (54 / 53)) * (1 / 144) := by
    simpa only [Finset.mul_sum] using
      mul_le_mul_of_nonneg_left hgeom
        (by norm_num : (0 : ℝ) ≤ (1 / 32) * (54 / 53))
  have hrow := AEGIS.RHGramExpansionV13.rowSum_le
    (n := n) (c := fun k => ((1 / 32 : ℝ) * (54 / 53)) *
      ((1 / 145 : ℝ) ^ k))
    (by intro k; positivity) i
  have hb :
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        ((1 / 32 : ℝ) * (54 / 53)) *
          ((1 / 145 : ℝ) ^ Nat.dist i j)) ≤
      2 * (((1 / 32 : ℝ) * (54 / 53)) * (1 / 144)) :=
    hrow.trans (mul_le_mul_of_nonneg_left hcost
      (by norm_num : (0 : ℝ) ≤ 2))
  exact hb.trans (by norm_num)

/-- Actual Weil-Arch contribution, separate from the prime sum. -/
theorem actual_arch_le_geometric_145
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (k : ℕ) (hk : 1 ≤ k)
    (hsep : (65 / 32 : ℝ) * (k : ℝ) ≤ b - a) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤
      (((1 / 32 : ℝ) * (54 / 53)) *
        ((1 / 145 : ℝ) ^ k)) *
      (energy p.1 + energy q.1) := by
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlog : Real.log 2 ≤ b - a := by
    linarith [AEGIS.WeilThreeBlockAnalyticConstantsV21.log_two_upper]
  have hδ : 2 * (k : ℝ) ≤ (b - a) - 1 / 32 := by nlinarith
  have ha := AEGIS.RHActualMixedDefectV1.distinct_fine_far_arch_moment_decay
    p q a b hp hq hm hlog
  have hc := arch_kernel_geometric_145 ((b - a) - 1 / 32) k hk hδ
  have he : 0 ≤ energy p.1 + energy q.1 :=
    add_nonneg (energy_nonnegative p.1) (energy_nonnegative q.1)
  exact ha.trans (mul_le_mul_of_nonneg_right hc he)


/-- The sharper 1/145 Arch envelope controls the original arithmetic
Weil pairing. It retains the entire genuine von Mangoldt prime term;
only the explicit moment-zero Arch integral is majorized. -/
theorem actual_B_norm_le_prime_plus_arch145
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (k : ℕ) (hk : 1 ≤ k)
    (hsep : (65 / 32 : ℝ) * (k : ℝ) ≤ b - a) :
    ‖B p q‖ ≤ ‖WeilPrimeSumV1 (mixed p q)‖ +
      (((1 / 32 : ℝ) * (54 / 53)) * ((1 / 145 : ℝ) ^ k)) *
        (energy p.1 + energy q.1) := by
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hgap : Real.log 2 ≤ b - a := by
    linarith [AEGIS.WeilThreeBlockAnalyticConstantsV21.log_two_upper]
  have hzero :=
    distinct_fine_far_mixed_one_zero p q a b hp hq hgap
  have harch := actual_arch_le_geometric_145
    p q a b hp hq hm k hk hsep
  have heq :
      B p q = WeilPrimeSumV1 (mixed p q) +
        WeilArchimedeanIntegralV1 (mixed p q) := by
    unfold B WeilExplicitRightSideV1
    rw [hzero]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add le_rfl harch)

end AEGIS.RHArchRow29V1

#print axioms AEGIS.RHArchRow29V1.arch_kernel_geometric_145
#print axioms AEGIS.RHArchRow29V1.geometric_arch_row_29
#print axioms AEGIS.RHArchRow29V1.actual_arch_le_geometric_145
#print axioms AEGIS.RHArchRow29V1.actual_B_norm_le_prime_plus_arch145
