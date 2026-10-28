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
import CvSRelRowTailL43V1
import CvSAtomInversionV1

/-!
# Coefficient inversion onto the 139 atoms at `L = 4/3`

* `inv_coeff`: every `x` on `F = [−70, 70]` with `Σ_F x = 0` and `Σ_F k x_k = 0` is
  `x_m = Σ_i λ_i wt(m, i)` with `λ_i = alpha 70 x (i + 1)` (the second-difference inversion of
  `CvSAtomInversionV1` at the level of coefficients);
* `atomRow_eq`: the atom rows are `wt(m, i) f_m`;
* `odd_sum`: odd sums over `F` vanish.
Not RH.
-/

open Finset
open AEGIS.CvSRelRowDataL43V1 AEGIS.CvSRelRowBoxL43V1 AEGIS.CvSRelRowFormL43V1
  AEGIS.CvSAtomInversionV1 AEGIS.CvSMomentBasisV1 AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSCrossCertV1

noncomputable section

namespace AEGIS.CvSRelRowInvL43V1

/-- The atom coefficients reproducing `x`. -/
def lamOf (x : ℤ → ℂ) (i : Fin 139) : ℂ := alpha 70 x (i.val + 1)

theorem alpha_zero (x : ℤ → ℂ) : alpha 70 x 0 = 0 := by simp [alpha, dsum_zero]

theorem moments (x : ℤ → ℂ) (h0 : ∑ k ∈ F, x k = 0) (h1 : ∑ k ∈ F, (k : ℂ) * x k = 0) :
    ∑ j ∈ range (2 * 70 + 1), x ((j : ℤ) - 70) = 0 ∧
      ∑ j ∈ range (2 * 70 + 1), (j : ℂ) * x ((j : ℤ) - 70) = 0 := by
  have c0 : ∑ j ∈ range (2 * 70 + 1), x ((j : ℤ) - 70) = 0 := by
    have := sum_Icc_eq_range 70 x
    push_cast at this
    rw [← this]; exact h0
  refine ⟨c0, ?_⟩
  have e : ∑ j ∈ range (2 * 70 + 1), (j : ℂ) * x ((j : ℤ) - 70) =
      ∑ k ∈ F, ((k : ℂ) + 70) * x k := by
    have := sum_Icc_eq_range 70 (fun k => ((k : ℂ) + 70) * x k)
    push_cast at this
    rw [this]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  simp only [add_mul, sum_add_distrib, h1, zero_add]
  rw [← mul_sum, h0, mul_zero]

theorem alpha_140 (x : ℤ → ℂ) (h0 : ∑ k ∈ F, x k = 0) (h1 : ∑ k ∈ F, (k : ℂ) * x k = 0) :
    alpha 70 x 140 = 0 := by
  obtain ⟨c0, c1⟩ := moments x h0 h1
  simp only [alpha]
  rw [dsum_end]
  push_cast at c0 c1 ⊢
  rw [c0, c1]
  ring

theorem alpha_141 (x : ℤ → ℂ) (h0 : ∑ k ∈ F, x k = 0) (h1 : ∑ k ∈ F, (k : ℂ) * x k = 0) :
    alpha 70 x 141 = 0 := by
  obtain ⟨c0, c1⟩ := moments x h0 h1
  simp only [alpha]
  rw [show (141 : ℕ) = 140 + 1 from rfl, dsum_succ, dsum_end]
  push_cast at c0 c1 ⊢
  rw [c0, c1]
  ring

/-- The weight of atom `i` at `m`. -/
theorem wt_eq (m : ℤ) (i : Fin 139) :
    wt m i = -(1 / 4) * (if m = ctr i - 1 then 1 else 0) + (1 / 2) * (if m = ctr i then 1 else 0) -
      (1 / 4) * (if m = ctr i + 1 then 1 else 0) := by
  unfold wt sinSqWeight
  have hS : (m ∈ sinSqSupport (ctr i)) ↔ (m = ctr i - 1 ∨ m = ctr i ∨ m = ctr i + 1) := by
    simp only [sinSqSupport, mem_insert, mem_singleton]
  by_cases h1 : m = ctr i - 1
  · rw [if_pos (hS.mpr (Or.inl h1)), if_neg (show ¬ m = ctr i by omega),
      if_pos (show m = ctr i - 1 ∨ m = ctr i + 1 from Or.inl h1), if_pos h1,
      if_neg (show ¬ m = ctr i by omega), if_neg (show ¬ m = ctr i + 1 by omega)]
    norm_num
  by_cases h2 : m = ctr i
  · rw [if_pos (hS.mpr (Or.inr (Or.inl h2))), if_pos h2, if_neg h1, if_pos h2,
      if_neg (show ¬ m = ctr i + 1 by omega)]
    norm_num
  by_cases h3 : m = ctr i + 1
  · rw [if_pos (hS.mpr (Or.inr (Or.inr h3))), if_neg h2,
      if_pos (show m = ctr i - 1 ∨ m = ctr i + 1 from Or.inr h3), if_neg h1, if_neg h2, if_pos h3]
    norm_num
  · rw [if_neg (show m ∉ sinSqSupport (ctr i) by rw [hS]; omega), if_neg h1, if_neg h2, if_neg h3]
    norm_num

theorem inv_coeff (x : ℤ → ℂ) (h0 : ∑ k ∈ F, x k = 0) (h1 : ∑ k ∈ F, (k : ℂ) * x k = 0)
    {m : ℤ} (hm : m ∈ F) : ∑ i : Fin 139, lamOf x i * wt m i = x m := by
  have hmF := mem_Icc.mp hm
  set p0 := (m + 70).toNat with hp0
  have hp0' : ((p0 : ℕ) : ℤ) = m + 70 := by omega
  set E : ℕ → ℂ := fun p => if (p : ℤ) = m + 70 then 1 else 0 with hE
  have hs := shift_sum (alpha 70 x) E 139 (alpha_zero x) (alpha_140 x h0 h1) (alpha_141 x h0 h1)
  have lhs : ∑ i : Fin 139, lamOf x i * wt m i =
      ∑ i ∈ range 139, alpha 70 x (i + 1) * (-(1 / 4) * E i + (1 / 2) * E (i + 1) - (1 / 4) * E (i + 2)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => alpha 70 x (i + 1) *
      (-(1 / 4) * E i + (1 / 2) * E (i + 1) - (1 / 4) * E (i + 2))) 139]
    refine sum_congr rfl fun i _ => ?_
    rw [wt_eq m i]
    have c1 : (m = ctr i - 1) ↔ (((i : ℕ) : ℤ) = m + 70) := by simp only [ctr]; omega
    have c2 : (m = ctr i) ↔ ((((i : ℕ) + 1 : ℕ) : ℤ) = m + 70) := by simp only [ctr]; push_cast; omega
    have c3 : (m = ctr i + 1) ↔ ((((i : ℕ) + 2 : ℕ) : ℤ) = m + 70) := by simp only [ctr]; push_cast; omega
    simp only [lamOf, hE, c1, c2, c3]
  rw [lhs, hs]
  rw [Finset.sum_eq_single p0]
  · simp only [hE, if_pos hp0', mul_one]
    rcases Nat.eq_zero_or_pos p0 with h | h
    · rw [h]
      simp only [alpha, dsum]
      have hm' : m = -70 := by omega
      simp [hm']
    · obtain ⟨p', hp'⟩ : ∃ p', p0 = p' + 1 := ⟨p0 - 1, by omega⟩
      rw [hp']
      have := dsum_second (fun j : ℕ => x ((j : ℤ) - ((70 : ℕ) : ℤ))) p'
      simp only [alpha, show p' + 1 - 1 = p' by omega, show p' + 1 + 1 = p' + 2 by ring]
      have hx : x ((((p' + 1 : ℕ)) : ℤ) - ((70 : ℕ) : ℤ)) = x m := by
        congr 1; push_cast; omega
      rw [← hx]
      linear_combination this
  · intro p _ hp
    have : ¬ ((p : ℤ) = m + 70) := fun h => hp (by omega)
    simp only [hE, if_neg this, mul_zero]
  · intro h
    exfalso; apply h; rw [mem_range]; omega

/-- The atom rows on `F` are `wt(m, i) f_m`. -/
theorem atomRow_eq (i : Fin 139) (m : ℤ) :
    atomRow (4 / 3) (fun i => sinSqSupport (ctr i)) (fun i => sinSqWeight (ctr i)) i m =
      wt m i * ((fr m : ℝ) : ℂ) := by
  simp only [atomRow, lowCoeff]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, one_mul, wt, ← fC_eq]
    split_ifs <;> ring
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Odd sums over `F` vanish. -/
theorem odd_sum {M : Type*} [AddCommGroup M] [Module ℚ M] (h : ℤ → M) (hodd : ∀ m, h (-m) = -h m) :
    ∑ m ∈ F, h m = 0 := by
  have e : ∑ m ∈ F, h m = ∑ m ∈ F, h (-m) := by
    refine sum_nbij' (fun m => -m) (fun m => -m) ?_ ?_ ?_ ?_ ?_
    · intro m hm; simp only [mem_Icc] at hm ⊢; omega
    · intro m hm; simp only [mem_Icc] at hm ⊢; omega
    · intro m _; simp
    · intro m _; simp
    · intro m _; simp
  have e2 : ∑ m ∈ F, h (-m) = -∑ m ∈ F, h m := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun m _ => hodd m
  rw [e2] at e
  have : (2 : ℚ) • ∑ m ∈ F, h m = 0 := by
    rw [two_smul]
    nth_rewrite 1 [e]
    exact neg_add_cancel _
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp this).resolve_left h2

end AEGIS.CvSRelRowInvL43V1

end

#print axioms AEGIS.CvSRelRowInvL43V1.inv_coeff
#print axioms AEGIS.CvSRelRowInvL43V1.atomRow_eq
#print axioms AEGIS.CvSRelRowInvL43V1.odd_sum
