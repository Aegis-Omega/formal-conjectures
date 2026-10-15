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

/-! Weighted Schur test for the complete complex Gram form. -/
open Finset
open scoped BigOperators
set_option autoImplicit false
open Complex
open scoped ComplexConjugate
noncomputable section
namespace AEGIS.WeightedSchur

theorem weighted_young (a b u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    a * b ≤ ((v / u) * a ^ 2 + (u / v) * b ^ 2) / 2 := by
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  apply (le_of_mul_le_mul_left (a := u * v) ?_ (mul_pos hu hv))
  field_simp
  nlinarith [sq_nonneg (v * a - u * b)]

theorem weighted_schur {ι : Type*} [Fintype ι]
    (c : ι → ι → ℝ) (w a : ι → ℝ) (S : ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hsym : ∀ i j, c i j = c j i)
    (hw : ∀ i, 0 < w i)
    (hrow : ∀ i, ∑ j, c i j * (w j / w i) ≤ S) :
    (∑ i, ∑ j, c i j * (a i * a j)) ≤ S * ∑ i, a i ^ 2 := by
  have hpair : (∑ i, ∑ j, c i j * (a i * a j)) ≤
      ∑ i, ∑ j, c i j * (((w j / w i) * a i ^ 2 +
        (w i / w j) * a j ^ 2) / 2) := by
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (weighted_young _ _ _ _ (hw i) (hw j)) (hc i j)
  have hswap : (∑ i, ∑ j, c i j * (w i / w j) * a j ^ 2) =
      ∑ i, ∑ j, c i j * (w j / w i) * a i ^ 2 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [hsym j i]
  have hid : (∑ i, ∑ j, c i j * (((w j / w i) * a i ^ 2 +
      (w i / w j) * a j ^ 2) / 2)) =
      ∑ i, (∑ j, c i j * (w j / w i)) * a i ^ 2 := by
    have heach : ∀ i j, c i j * (((w j / w i) * a i ^ 2 +
        (w i / w j) * a j ^ 2) / 2) =
        (c i j * (w j / w i) * a i ^ 2 + c i j * (w i / w j) * a j ^ 2) / 2 := by
      intro i j
      ring
    simp_rw [heach]
    simp only [← sum_div, sum_add_distrib]
    rw [hswap]
    simp only [sum_mul]
    ring
  rw [hid] at hpair
  calc
    _ ≤ ∑ i, (∑ j, c i j * (w j / w i)) * a i ^ 2 := hpair
    _ ≤ ∑ i, S * a i ^ 2 := by
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
    _ = _ := (mul_sum _ _ _).symm


theorem weighted_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ι → ι → ℂ) (z : ι → ℂ) (c : ι → ι → ℝ) (w : ι → ℝ)
    (D E S : ℝ) (hE : 0 ≤ E)
    (hc : ∀ i j, 0 ≤ c i j) (hzero : ∀ i, c i i = 0)
    (hsym : ∀ i j, c i j = c j i) (hw : ∀ i, 0 < w i)
    (hdiag : ∀ i, D * E ≤ -(H i i).re)
    (hcross : ∀ i j, i ≠ j → ‖H i j‖ ≤ c i j * E)
    (hrow : ∀ i, ∑ j, c i j * (w j / w i) ≤ S) :
    (∑ i, ∑ j, z i * star (z j) * H i j).re ≤
      -(D - S) * E * ∑ i, ‖z i‖ ^ 2 := by
  have hpoint (i j : ι) :
      (z i * star (z j) * H i j).re ≤
      (if j = i then -(D * E) * ‖z i‖ ^ 2 else 0) +
        E * (c i j * (‖z i‖ * ‖z j‖)) := by
    by_cases hij : j = i
    · subst j
      simp only [ite_true, hzero, zero_mul, mul_zero, add_zero]
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.re_ofReal_mul]
      have hd : (H i i).re ≤ -(D * E) := by linarith [hdiag i]
      nlinarith [mul_le_mul_of_nonneg_left hd (sq_nonneg ‖z i‖)]
    · simp only [if_neg hij, zero_add]
      calc
        _ ≤ ‖z i * star (z j) * H i j‖ := Complex.re_le_norm _
        _ = ‖z i‖ * ‖z j‖ * ‖H i j‖ := by simp only [norm_mul, norm_star]
        _ ≤ ‖z i‖ * ‖z j‖ * (c i j * E) :=
          mul_le_mul_of_nonneg_left (hcross i j (Ne.symm hij))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = _ := by ring
  have hall : (∑ i, ∑ j, (z i * star (z j) * H i j).re) ≤
      ∑ i, ∑ j, ((if j = i then -(D * E) * ‖z i‖ ^ 2 else 0) +
        E * (c i j * (‖z i‖ * ‖z j‖))) := by
    exact sum_le_sum fun i _ => sum_le_sum fun j _ => hpoint i j
  have hs := weighted_schur c w (fun i => ‖z i‖) S hc hsym hw hrow
  simp only [sum_add_distrib, sum_ite_eq', mem_univ, if_true, ← mul_sum] at hall
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  calc
    _ ≤ -(D * E) * ∑ i, ‖z i‖ ^ 2 + E *
        (∑ i, ∑ j, c i j * (‖z i‖ * ‖z j‖)) := hall
    _ ≤ -(D * E) * ∑ i, ‖z i‖ ^ 2 + E * (S * ∑ i, ‖z i‖ ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hs hE)
    _ = _ := by ring


/-- Full complex weighted-Schur Gram with *unequal* individual energies.
The previous eleven-translate consumer has one common energy. This
version retains every atom's own energy and arbitrary complex
coefficients, so it can be applied to non-translate finite families.

The cross estimate with square-root energies is an EXPLICIT input:
the theorem does not assume or manufacture Weil prime estimates. -/
theorem weighted_gram_variable_energy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ι → ι → ℂ) (z : ι → ℂ) (E : ι → ℝ)
    (c : ι → ι → ℝ) (w : ι → ℝ) (D S : ℝ)
    (hE : ∀ i, 0 ≤ E i)
    (hc : ∀ i j, 0 ≤ c i j)
    (hzero : ∀ i, c i i = 0)
    (hsym : ∀ i j, c i j = c j i)
    (hw : ∀ i, 0 < w i)
    (hdiag : ∀ i, D * E i ≤ -(H i i).re)
    (hcross : ∀ i j, i ≠ j →
      ‖H i j‖ ≤ c i j * (Real.sqrt (E i) * Real.sqrt (E j)))
    (hrow : ∀ i, ∑ j, c i j * (w j / w i) ≤ S) :
    (∑ i, ∑ j, z i * star (z j) * H i j).re ≤
      -(D - S) * ∑ i, E i * ‖z i‖ ^ 2 := by
  let a : ι → ℝ := fun i => Real.sqrt (E i) * ‖z i‖
  have hpoint (i j : ι) :
      (z i * star (z j) * H i j).re ≤
      (if j = i then -(D * E i) * ‖z i‖ ^ 2 else 0) +
        c i j * (a i * a j) := by
    by_cases hij : j = i
    · subst j
      simp only [ite_true, hzero, zero_mul, zero_add, add_zero]
      rw [Complex.star_def, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, Complex.re_ofReal_mul]
      have hd : (H i i).re ≤ -(D * E i) := by linarith [hdiag i]
      nlinarith [mul_le_mul_of_nonneg_left hd (sq_nonneg ‖z i‖)]
    · simp only [if_neg hij, zero_add]
      calc
        (z i * star (z j) * H i j).re ≤
            ‖z i * star (z j) * H i j‖ := Complex.re_le_norm _
        _ = ‖z i‖ * ‖z j‖ * ‖H i j‖ := by
          simp only [norm_mul, norm_star]
        _ ≤ ‖z i‖ * ‖z j‖ *
            (c i j * (Real.sqrt (E i) * Real.sqrt (E j))) :=
          mul_le_mul_of_nonneg_left (hcross i j (Ne.symm hij))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = c i j * (a i * a j) := by
          dsimp [a]
          ring
  have hall :
      (∑ i, ∑ j, (z i * star (z j) * H i j).re) ≤
      ∑ i, ∑ j,
        ((if j = i then -(D * E i) * ‖z i‖ ^ 2 else 0) +
          c i j * (a i * a j)) := by
    exact sum_le_sum fun i _ => sum_le_sum fun j _ => hpoint i j
  have hs := weighted_schur c w a S hc hsym hw hrow
  have hsquares :
      (∑ i, a i ^ 2) = ∑ i, E i * ‖z i‖ ^ 2 := by
    apply sum_congr rfl
    intro i _
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt (hE i)]
  rw [hsquares] at hs
  simp only [sum_add_distrib, sum_ite_eq', mem_univ, if_true] at hall
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  calc
    _ ≤ (∑ i, -(D * E i) * ‖z i‖ ^ 2) +
        (∑ i, ∑ j, c i j * (a i * a j)) := hall
    _ ≤ (∑ i, -(D * E i) * ‖z i‖ ^ 2) +
        S * (∑ i, E i * ‖z i‖ ^ 2) :=
          add_le_add_left hs _
    _ = -(D - S) * (∑ i, E i * ‖z i‖ ^ 2) := by
      have hdiagSum :
          (∑ i, -(D * E i) * ‖z i‖ ^ 2) =
            -D * (∑ i, E i * ‖z i‖ ^ 2) := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro i _
        ring
      rw [hdiagSum]
      ring


#print axioms AEGIS.WeightedSchur.weighted_schur
#print axioms AEGIS.WeightedSchur.weighted_gram
#print axioms AEGIS.WeightedSchur.weighted_gram_variable_energy
end AEGIS.WeightedSchur
