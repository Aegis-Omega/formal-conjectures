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

import CvSPivotRankTwoV1

/-!
# Block identities behind the HOLON V6 and V7 Feshbach block candidates

The blocks of `feshbach_arb_v2/feshbach_blocks_arb.py` live on the moment-zero part `V` of `span{e_m : |m| ≤ N}`.
After the rows are reordered as free modes `F` and the two pivots `P = {0, 1}`, the basis is
`Z = fromRows 1 U`, with the pivot rows `U` of `AEGIS.CvSPivotRankTwoV1`.

* `congruence` (V6): `Zᴴ X Z = X_FF + X_FP U + Uᴴ X_PF + Uᴴ X_PP U` for every square `X`.
* `gram_eq`, `gram_det_pos`: `Zᵀ Z = 1 + Uᵀ U`, with positive determinant.
* `perp_a`, `perp_b`: the pole vectors `a_j = 1/(j² + β²)` and `b_j = j/(j² + β²)` (`β = 1/(2ω) = L/(4π)`) are
  orthogonal to every basis vector `e_m + U₀(m) e₀ + U₁(m) e₁`.
* `projector_split`: if `Mᵀ Z = 0` and both Gram blocks are invertible, then
  `Z (ZᵀZ)⁻¹ Zᵀ + M (MᵀM)⁻¹ Mᵀ = 1`.
* `cb_eq` (V7): for symmetric `Q` and any `X`,
  `Zᵀ(QᵀQ + X)Z − (ZᵀQZ)(ZᵀZ)⁻¹(ZᵀQZ) = Zᵀ X Z + (MᵀQZ)ᵀ (MᵀM)⁻¹ (MᵀQZ)`.
  With `Q` the in-band rows, `X` the rows `N < |n| ≤ NP` plus the tail bound, this is the V7 form of `C_B`:
  no `k × k` inverse, no `A11 A11` and no difference of two large blocks.

Not RH.
-/

open Matrix

namespace AEGIS.CvSPivotCongruenceV1

open AEGIS.CvSPivotRankTwoV1 (U0 U1)

variable {F P R : Type*} [Fintype F] [Fintype P] [DecidableEq F] [DecidableEq P]

omit [DecidableEq P] in
/-- **The rank-two congruence (V6).** -/
theorem congruence [CommRing R] [StarRing R] (X : Matrix (F ⊕ P) (F ⊕ P) R) (U : Matrix P F R) :
    (fromRows (1 : Matrix F F R) U)ᴴ * X * fromRows 1 U =
      X.toBlocks₁₁ + X.toBlocks₁₂ * U + Uᴴ * X.toBlocks₂₁ + Uᴴ * X.toBlocks₂₂ * U := by
  rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_one]
  conv_lhs => rw [← fromBlocks_toBlocks X]
  rw [fromCols_mul_fromBlocks]
  erw [fromCols_mul_fromRows]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.add_mul, Matrix.mul_assoc]
  abel

omit [DecidableEq P] in
/-- The Gram block of the basis. -/
theorem gram_eq (U : Matrix P F ℝ) :
    (fromRows (1 : Matrix F F ℝ) U)ᵀ * fromRows 1 U = 1 + Uᵀ * U := by
  rw [transpose_fromRows, transpose_one]
  erw [fromCols_mul_fromRows]
  rw [Matrix.one_mul]

omit [DecidableEq P] in
theorem gram_det_pos (U : Matrix P F ℝ) : 0 < (1 + Uᵀ * U).det := by
  have h : (1 + Uᴴ * U).PosDef := PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self U)
  rw [conjTranspose_eq_transpose_of_trivial] at h
  exact h.det_pos

/-- The first pole vector is orthogonal to the basis vector of `m`. -/
theorem perp_a (ω m : ℝ) (hω : ω ≠ 0) :
    1 / (m ^ 2 + (1 / (2 * ω)) ^ 2) + U0 ω m * (1 / (0 ^ 2 + (1 / (2 * ω)) ^ 2)) +
      U1 ω m * (1 / (1 ^ 2 + (1 / (2 * ω)) ^ 2)) = 0 := by
  have h1 : (0 : ℝ) < 1 / 4 + ω ^ 2 * m ^ 2 := by positivity
  have h2 : (0 : ℝ) < 1 / 4 + ω ^ 2 := by positivity
  have hw : (0 : ℝ) < ω ^ 2 := by positivity
  unfold U0 U1
  field_simp
  ring

/-- The second pole vector is orthogonal to the basis vector of `m`. -/
theorem perp_b (ω m : ℝ) (hω : ω ≠ 0) :
    m / (m ^ 2 + (1 / (2 * ω)) ^ 2) + U0 ω m * (0 / (0 ^ 2 + (1 / (2 * ω)) ^ 2)) +
      U1 ω m * (1 / (1 ^ 2 + (1 / (2 * ω)) ^ 2)) = 0 := by
  have h1 : (0 : ℝ) < 1 / 4 + ω ^ 2 * m ^ 2 := by positivity
  have h2 : (0 : ℝ) < 1 / 4 + ω ^ 2 := by positivity
  have hw : (0 : ℝ) < ω ^ 2 := by positivity
  unfold U0 U1
  field_simp
  ring

/-- **Complementary projectors**: `Z (ZᵀZ)⁻¹ Zᵀ + M (MᵀM)⁻¹ Mᵀ = 1` when `Mᵀ Z = 0`. -/
theorem projector_split (Z : Matrix (F ⊕ P) F ℝ) (M : Matrix (F ⊕ P) P ℝ) (hMZ : Mᵀ * Z = 0)
    (hG : IsUnit (Zᵀ * Z).det) (hH : IsUnit (Mᵀ * M).det) :
    Z * (Zᵀ * Z)⁻¹ * Zᵀ + M * (Mᵀ * M)⁻¹ * Mᵀ = 1 := by
  have hZM : Zᵀ * M = 0 := by
    rw [← transpose_transpose (Zᵀ * M), transpose_mul, transpose_transpose, hMZ, transpose_zero]
  set B := fromCols Z M
  set C := fromBlocks (Zᵀ * Z)⁻¹ 0 0 (Mᵀ * M)⁻¹
  have hBB : Bᵀ * B = fromBlocks (Zᵀ * Z) 0 0 (Mᵀ * M) := by
    rw [transpose_fromCols, fromRows_mul_fromCols, hZM, hMZ]
  have hCB : C * Bᵀ * B = 1 := by
    rw [Matrix.mul_assoc, hBB, fromBlocks_multiply, nonsing_inv_mul _ hG, nonsing_inv_mul _ hH]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, fromBlocks_one]
  have hBC : B * (C * Bᵀ) = 1 := mul_eq_one_comm.mp hCB
  rw [← hBC, transpose_fromCols, ← Matrix.mul_assoc, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, add_zero, zero_add]

/-- **The V7 form of `C_B`.** -/
theorem cb_eq (Z : Matrix (F ⊕ P) F ℝ) (M : Matrix (F ⊕ P) P ℝ) (hMZ : Mᵀ * Z = 0)
    (hG : IsUnit (Zᵀ * Z).det) (hH : IsUnit (Mᵀ * M).det) (Q X : Matrix (F ⊕ P) (F ⊕ P) ℝ)
    (hQ : Qᵀ = Q) :
    Zᵀ * (Qᵀ * Q + X) * Z - (Zᵀ * Q * Z) * (Zᵀ * Z)⁻¹ * (Zᵀ * Q * Z) =
      Zᵀ * X * Z + (Mᵀ * Q * Z)ᵀ * (Mᵀ * M)⁻¹ * (Mᵀ * Q * Z) := by
  have hP : Z * (Zᵀ * Z)⁻¹ * Zᵀ = 1 - M * (Mᵀ * M)⁻¹ * Mᵀ :=
    eq_sub_of_add_eq (projector_split Z M hMZ hG hH)
  have hP' : ∀ Y : Matrix (F ⊕ P) F ℝ,
      Z * ((Zᵀ * Z)⁻¹ * (Zᵀ * Y)) = Y - M * ((Mᵀ * M)⁻¹ * (Mᵀ * Y)) := fun Y => by
    have := congrArg (· * Y) hP
    simpa only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul] using this
  rw [transpose_mul, transpose_mul, transpose_transpose, hQ]
  simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
  rw [hP' (Q * Z)]
  simp only [Matrix.mul_sub]
  abel

end AEGIS.CvSPivotCongruenceV1

#print axioms AEGIS.CvSPivotCongruenceV1.congruence
#print axioms AEGIS.CvSPivotCongruenceV1.gram_det_pos
#print axioms AEGIS.CvSPivotCongruenceV1.perp_a
#print axioms AEGIS.CvSPivotCongruenceV1.perp_b
#print axioms AEGIS.CvSPivotCongruenceV1.cb_eq
