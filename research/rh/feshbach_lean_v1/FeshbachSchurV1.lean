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
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Feshbach–Schur lower bound for a symmetric form

The interval certificates `feshbach_arb_v1` (L = 1.05) and `feshbach_arb_v2` (L = 1.2 … 1.8)
prove `Q(G) ≥ μ ‖G‖²` from four inputs: a low subspace `V`, a lower bound `c` for `Q` on `Vᗮ`,
a bound `C_B` for the cross terms, and positivity of the Schur form
`Q − μ ‖·‖² − C_B / (c − μ)` on `V`. Their receipts list this implication as not
machine-checked. It is proved here for any symmetric real bilinear form on a real inner product
space. The Arb blocks are complex Hermitian; passing to the real part on the underlying real
space is the remaining reduction and is not formalized here.
-/

namespace AEGIS.FeshbachSchurV1

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The scalar step: `2 |b| ≤ k + a t` whenever `b² ≤ k a t` with `a > 0`, `k, t ≥ 0`. -/
theorem neg_two_mul_le_of_sq_le {a k t b : ℝ} (ha : 0 < a) (hk : 0 ≤ k) (ht : 0 ≤ t)
    (hb : b ^ 2 ≤ k * a * t) : -(2 * b) ≤ k + a * t := by
  have hsq : (2 * b) ^ 2 ≤ (k + a * t) ^ 2 := by nlinarith [sq_nonneg (k - a * t)]
  have hnn : 0 ≤ k + a * t := by positivity
  nlinarith [abs_le_of_sq_le_sq' hsq hnn]

/-- **Feshbach–Schur.** If `Q ≥ c` on `Vᗮ`, the cross terms satisfy `Q(v, w)² ≤ C(v) ‖w‖²`,
and `Q(v, v) ≥ μ ‖v‖² + C(v) / (c − μ)` on `V` with `μ < c`, then `Q ≥ μ` on the whole space. -/
theorem feshbach_lower_bound (Q : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, Q x y = Q y x)
    (V : Submodule ℝ E) [V.HasOrthogonalProjection] (C : E → ℝ) {μ c : ℝ} (hμc : μ < c)
    (hcomp : ∀ w ∈ Vᗮ, c * ‖w‖ ^ 2 ≤ Q w w)
    (hcross : ∀ v ∈ V, ∀ w ∈ Vᗮ, Q v w ^ 2 ≤ C v * ‖w‖ ^ 2)
    (hC : ∀ v ∈ V, 0 ≤ C v)
    (hschur : ∀ v ∈ V, μ * ‖v‖ ^ 2 + C v / (c - μ) ≤ Q v v) (x : E) :
    μ * ‖x‖ ^ 2 ≤ Q x x := by
  obtain ⟨v, hv, w, hw, rfl⟩ := V.exists_add_mem_mem_orthogonal x
  have ha : 0 < c - μ := sub_pos.mpr hμc
  have hnorm : ‖v + w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
    rw [norm_add_sq_real, V.inner_right_of_mem_orthogonal hv hw]; ring
  have hQ : Q (v + w) (v + w) = Q v v + 2 * Q v w + Q w w := by
    simp only [map_add, LinearMap.add_apply, hsymm w v]; ring
  have hk : 0 ≤ C v / (c - μ) := div_nonneg (hC v hv) ha.le
  have hb : Q v w ^ 2 ≤ C v / (c - μ) * (c - μ) * ‖w‖ ^ 2 := by
    rw [div_mul_cancel₀ _ ha.ne']; exact hcross v hv w hw
  have key := neg_two_mul_le_of_sq_le ha hk (sq_nonneg ‖w‖) hb
  have h1 := hcomp w hw
  have h3 := hschur v hv
  rw [hnorm, hQ]
  nlinarith

/-- Coordinate form of the Schur hypothesis. For `v = ∑ yᵢ bᵢ`, positivity of the matrix
`S = A − μ G − C_B / (c − μ)` (Gram matrix `G`, form matrix `A`), as checked by interval
Cholesky in `schur_arb.py`, gives `μ ‖v‖² + yᵀ C_B y / (c − μ) ≤ Q(v, v)`. -/
theorem schur_of_matrix {k : ℕ} (Q : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (b : Fin k → E)
    (A G CB : Fin k → Fin k → ℝ) {μ c : ℝ}
    (hA : ∀ i j, Q (b i) (b j) = A i j) (hG : ∀ i j, ⟪b i, b j⟫ = G i j)
    (hS : ∀ y : Fin k → ℝ,
      0 ≤ ∑ i, ∑ j, y i * y j * (A i j - μ * G i j - CB i j / (c - μ))) (y : Fin k → ℝ) :
    μ * ‖∑ i, y i • b i‖ ^ 2 + (∑ i, ∑ j, y i * y j * CB i j) / (c - μ) ≤
      Q (∑ i, y i • b i) (∑ i, y i • b i) := by
  have hQ : Q (∑ i, y i • b i) (∑ i, y i • b i) = ∑ i, ∑ j, y i * y j * A i j := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hA]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hN : ‖∑ i, y i • b i‖ ^ 2 = ∑ i, ∑ j, y i * y j * G i j := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right, hG]
    ring
  have hsplit : ∑ i, ∑ j, y i * y j * (A i j - μ * G i j - CB i j / (c - μ)) =
      (∑ i, ∑ j, y i * y j * A i j) - μ * (∑ i, ∑ j, y i * y j * G i j) -
        (∑ i, ∑ j, y i * y j * CB i j) / (c - μ) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
  have := hS y
  rw [hsplit] at this
  rw [hQ, hN]
  linarith

end AEGIS.FeshbachSchurV1

#print axioms AEGIS.FeshbachSchurV1.neg_two_mul_le_of_sq_le
#print axioms AEGIS.FeshbachSchurV1.feshbach_lower_bound
#print axioms AEGIS.FeshbachSchurV1.schur_of_matrix
