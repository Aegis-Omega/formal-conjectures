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

import Mathlib

/-!
# Rank-two pivots of the moment-zero basis (the 9/5 Arb blocks)

The Feshbach blocks of `feshbach_arb_v2` use the moment-zero part of `span{e_m : |m| ≤ N}` on a window of
length `L`, with the constraints `Σ_m u_m μ_s(m) = 0` for `s = ±1/2`. Here `μ_s(m) = (e^{sL} − 1)/(s + iωm)`
and `ω = 2π/L`. The basis vector of a non-pivot mode `m` is `e_m + U₀(m) e₀ + U₁(m) e₁`.

* `pivot_cleared`, `pivot_moment_zero`: with the real rational pivots
  `U₀(m) = ((m − 1)/4)/(1/4 + ω²m²)` and `U₁(m) = −m(1/4 + ω²)/(1/4 + ω²m²)`, both moments of every basis
  vector vanish (the factor `e^{sL} − 1` is common to the three terms).
* `one_le_det`: `det(1 + U Uᵀ) ≥ 1` for every real `2 × ι` matrix, by Cauchy–Schwarz.
* `woodbury`: `(1 + Uᵀ U)⁻¹ = 1 − Uᵀ (1 + U Uᵀ)⁻¹ U`, so the Gram block `G11 = 1 + UᵀU` of the basis is
  inverted through a 2 × 2 matrix.

Not RH.
-/

open Matrix

namespace AEGIS.CvSPivotRankTwoV1

/-- `U₀(m) = ((m − 1)/4)/(1/4 + ω²m²)`. -/
noncomputable def U0 (ω m : ℝ) : ℝ := (m - 1) / 4 / (1 / 4 + ω ^ 2 * m ^ 2)

/-- `U₁(m) = −m(1/4 + ω²)/(1/4 + ω²m²)`. -/
noncomputable def U1 (ω m : ℝ) : ℝ := -m * (1 / 4 + ω ^ 2) / (1 / 4 + ω ^ 2 * m ^ 2)

/-- The moment identity with the denominators cleared. -/
theorem pivot_cleared (ω m s : ℂ) (hs : s = 1 / 2 ∨ s = -1 / 2) :
    (1 / 4 + ω ^ 2 * m ^ 2) * s * (s + ω * Complex.I) +
      (m - 1) / 4 * (s + ω * m * Complex.I) * (s + ω * Complex.I) -
      m * (1 / 4 + ω ^ 2) * (s + ω * m * Complex.I) * s = 0 := by
  rcases hs with rfl | rfl <;> linear_combination (m * ω ^ 2 * (m - 1) / 4) * Complex.I_sq

/-- **Both moments of the basis vector vanish.** -/
theorem pivot_moment_zero (ω m s : ℝ) (hs : s = 1 / 2 ∨ s = -1 / 2) :
    1 / ((s : ℂ) + ω * m * Complex.I) + (U0 ω m : ℂ) / s +
      (U1 ω m : ℂ) / ((s : ℂ) + ω * Complex.I) = 0 := by
  have hs0 : (s : ℂ) ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hre : ∀ t : ℝ, (s : ℂ) + t * Complex.I ≠ 0 := fun t h => by
    have := congrArg Complex.re h
    simp at this
    rcases hs with rfl | rfl <;> norm_num at this
  have h1 : (s : ℂ) + ω * m * Complex.I ≠ 0 := by simpa [mul_assoc] using hre (ω * m)
  have h2 := hre ω
  have hD : (1 / 4 + (ω : ℂ) ^ 2 * (m : ℂ) ^ 2) ≠ 0 := by
    have h : (0 : ℝ) < 1 / 4 + ω ^ 2 * m ^ 2 := by positivity
    have h' : ((1 / 4 + ω ^ 2 * m ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h.ne'
    push_cast at h'
    exact h'
  have hs' : (s : ℂ) = 1 / 2 ∨ (s : ℂ) = -1 / 2 := by
    rcases hs with rfl | rfl <;> [left; right] <;> push_cast <;> ring
  have e0 : (U0 ω m : ℂ) / s = ((m : ℂ) - 1) / 4 / ((1 / 4 + (ω : ℂ) ^ 2 * (m : ℂ) ^ 2) * s) := by
    simp only [U0]; push_cast; rw [div_div]
  have e1 : (U1 ω m : ℂ) / ((s : ℂ) + ω * Complex.I) =
      (-(m : ℂ) * (1 / 4 + (ω : ℂ) ^ 2)) / ((1 / 4 + (ω : ℂ) ^ 2 * (m : ℂ) ^ 2) * ((s : ℂ) + ω * Complex.I)) := by
    simp only [U1]; push_cast; rw [div_div]
  rw [e0, e1, div_add_div _ _ h1 (mul_ne_zero hD hs0),
    div_add_div _ _ (mul_ne_zero h1 (mul_ne_zero hD hs0)) (mul_ne_zero hD h2), div_eq_zero_iff]
  left
  linear_combination (1 / 4 + (ω : ℂ) ^ 2 * (m : ℂ) ^ 2) * pivot_cleared ω m s hs'

variable {ι : Type*} [Fintype ι]

/-- **`det(1 + U Uᵀ) ≥ 1`** for a real `2 × ι` matrix. -/
theorem one_le_det (U : Matrix (Fin 2) ι ℝ) : 1 ≤ (1 + U * Uᵀ).det := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
    zero_add]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => U 0 i) (fun i => U 1 i)
  have e0 : ∑ i, U 0 i * U 0 i = ∑ i, U 0 i ^ 2 := by simp [sq]
  have e1 : ∑ i, U 1 i * U 1 i = ∑ i, U 1 i ^ 2 := by simp [sq]
  have e2 : ∑ i, U 1 i * U 0 i = ∑ i, U 0 i * U 1 i := by simp [mul_comm]
  have h0 : 0 ≤ ∑ i, U 0 i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : 0 ≤ ∑ i, U 1 i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [e0, e1, e2]
  nlinarith [cs, h0, h1, mul_nonneg h0 h1]

/-- **Woodbury for the rank-two Gram block.** -/
theorem woodbury [DecidableEq ι] (U : Matrix (Fin 2) ι ℝ) :
    (1 + Uᵀ * U)⁻¹ = 1 - Uᵀ * (1 + U * Uᵀ)⁻¹ * U := by
  have hS : IsUnit (1 + U * Uᵀ).det := isUnit_iff_ne_zero.mpr (by linarith [one_le_det U])
  refine Matrix.inv_eq_right_inv ?_
  have push : (1 + Uᵀ * U) * Uᵀ = Uᵀ * (1 + U * Uᵀ) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  calc (1 + Uᵀ * U) * (1 - Uᵀ * (1 + U * Uᵀ)⁻¹ * U)
      = (1 + Uᵀ * U) - (1 + Uᵀ * U) * Uᵀ * (1 + U * Uᵀ)⁻¹ * U := by
        rw [Matrix.mul_sub, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (1 + Uᵀ * U) - Uᵀ * ((1 + U * Uᵀ) * (1 + U * Uᵀ)⁻¹) * U := by
        rw [push]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.mul_nonsing_inv _ hS, Matrix.mul_one]; abel

end AEGIS.CvSPivotRankTwoV1

#print axioms AEGIS.CvSPivotRankTwoV1.pivot_moment_zero
#print axioms AEGIS.CvSPivotRankTwoV1.one_le_det
#print axioms AEGIS.CvSPivotRankTwoV1.woodbury
