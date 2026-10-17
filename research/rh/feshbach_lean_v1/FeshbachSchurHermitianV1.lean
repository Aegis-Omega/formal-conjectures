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
import FeshbachSchurV1
import Mathlib.Analysis.Complex.Basic

/-!
# Feshbach–Schur for the complex Hermitian Arb blocks

`feshbach_arb_v1/v2` work in complex `L²[0, L]` with the Hermitian form `Q` of the restricted Weil
functional and complex Hermitian matrices `A11, G11, C_B`. `schur_arb.py` writes
`S = A11 − μ G11 − C_B / (c − μ) = R + iJ`, takes `jn = k · max |J_ij|` and checks `R − jn I` by
interval Cholesky. This file proves, for any Hermitian sesquilinear form on a complex inner
product space:

* `feshbach_lower_bound_hermitian`: the Feshbach–Schur bound `Re Q(x, x) ≥ μ ‖x‖²`;
* `schur_of_matrix_hermitian`: `Re (y* S y) ≥ 0` for all `y` gives the Schur hypothesis on the span;
* `hermitian_quadratic_nonneg_of_real_part`: `R − k m I` positive semidefinite on real vectors and
  `|J_ij| ≤ m` give `Re (y* S y) ≥ 0` for all complex `y` (the reduction used by `schur_arb.py`).
-/

namespace AEGIS.FeshbachSchurV1

open scoped ComplexConjugate InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

/-- **Feshbach–Schur, Hermitian form.** -/
theorem feshbach_lower_bound_hermitian (Q : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ)
    (hherm : ∀ x y, Q y x = conj (Q x y))
    (V : Submodule ℂ E) [V.HasOrthogonalProjection] (C : E → ℝ) {μ c : ℝ} (hμc : μ < c)
    (hcomp : ∀ w ∈ Vᗮ, c * ‖w‖ ^ 2 ≤ (Q w w).re)
    (hcross : ∀ v ∈ V, ∀ w ∈ Vᗮ, ‖Q v w‖ ^ 2 ≤ C v * ‖w‖ ^ 2)
    (hC : ∀ v ∈ V, 0 ≤ C v)
    (hschur : ∀ v ∈ V, μ * ‖v‖ ^ 2 + C v / (c - μ) ≤ (Q v v).re) (x : E) :
    μ * ‖x‖ ^ 2 ≤ (Q x x).re := by
  obtain ⟨v, hv, w, hw, rfl⟩ := V.exists_add_mem_mem_orthogonal x
  have ha : 0 < c - μ := sub_pos.mpr hμc
  have hnorm : ‖v + w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero v w
      (V.inner_right_of_mem_orthogonal hv hw)
    nlinarith [this]
  have hQ : (Q (v + w) (v + w)).re = (Q v v).re + 2 * (Q v w).re + (Q w w).re := by
    simp only [map_add, LinearMap.add_apply, Complex.add_re, hherm w v, Complex.conj_re]
    ring
  have hre : (Q v w).re ^ 2 ≤ ‖Q v w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, sq]; exact Complex.re_sq_le_normSq _
  have hk : 0 ≤ C v / (c - μ) := div_nonneg (hC v hv) ha.le
  have hb : (Q v w).re ^ 2 ≤ C v / (c - μ) * (c - μ) * ‖w‖ ^ 2 := by
    rw [div_mul_cancel₀ _ ha.ne']; exact hre.trans (hcross v hv w hw)
  have key := neg_two_mul_le_of_sq_le ha hk (sq_nonneg ‖w‖) hb
  have h1 := hcomp w hw
  have h3 := hschur v hv
  rw [hnorm, hQ]
  nlinarith

/-- Coordinate form of the Hermitian Schur hypothesis: `Re (y* S y) ≥ 0` for
`S = A − μ G − C_B / (c − μ)` gives `μ ‖v‖² + Re (y* C_B y) / (c − μ) ≤ Re Q(v, v)`
for `v = ∑ yᵢ bᵢ`. -/
theorem schur_of_matrix_hermitian {k : ℕ} (Q : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (b : Fin k → E)
    (A G CB : Fin k → Fin k → ℂ) {μ c : ℝ}
    (hA : ∀ i j, Q (b i) (b j) = A i j) (hG : ∀ i j, ⟪b i, b j⟫ = G i j)
    (hS : ∀ y : Fin k → ℂ,
      0 ≤ (∑ i, ∑ j, conj (y i) * y j * (A i j - μ * G i j - CB i j / (c - μ))).re)
    (y : Fin k → ℂ) :
    μ * ‖∑ i, y i • b i‖ ^ 2 + (∑ i, ∑ j, conj (y i) * y j * CB i j).re / (c - μ) ≤
      (Q (∑ i, y i • b i) (∑ i, y i • b i)).re := by
  have hQ : Q (∑ i, y i • b i) (∑ i, y i • b i) = ∑ i, ∑ j, conj (y i) * y j * A i j := by
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, hA]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RingHom.id_apply]
    ring
  have hN : ((‖∑ i, y i • b i‖ ^ 2 : ℝ) : ℂ) = ∑ i, ∑ j, conj (y i) * y j * G i j := by
    rw [show ((‖∑ i, y i • b i‖ ^ 2 : ℝ) : ℂ) = ⟪∑ i, y i • b i, ∑ i, y i • b i⟫ by
      exact_mod_cast (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _).symm, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right, hG]
    ring
  have hsplit : ∑ i, ∑ j, conj (y i) * y j * (A i j - μ * G i j - CB i j / (c - μ)) =
      (∑ i, ∑ j, conj (y i) * y j * A i j) - (μ : ℂ) * (∑ i, ∑ j, conj (y i) * y j * G i j) -
        (∑ i, ∑ j, conj (y i) * y j * CB i j) / ((c - μ : ℝ) : ℂ) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring
  have := hS y
  rw [hsplit, ← hN, ← hQ] at this
  simp only [Complex.sub_re, Complex.div_ofReal_re, Complex.re_ofReal_mul,
    Complex.ofReal_re] at this
  linarith

/-- The scalar step of the `R + iJ` reduction: `(a b − c d) J ≤ m (a² + b² + c² + d²) / 2`
whenever `|J| ≤ m`. -/
theorem cross_term_le {a b c d J m : ℝ} (hJ : |J| ≤ m) :
    (a * b - c * d) * J ≤ m * ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 2) := by
  have hP : |a * b - c * d| ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 2 := by
    rw [abs_le]; constructor <;>
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (c - d), sq_nonneg (c + d)]
  calc (a * b - c * d) * J ≤ |(a * b - c * d) * J| := le_abs_self _
    _ = |a * b - c * d| * |J| := abs_mul _ _
    _ ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 2 * m :=
        mul_le_mul hP hJ (abs_nonneg _) (by positivity)
    _ = m * ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 2) := by ring

/-- **The `R + iJ` reduction of `schur_arb.py`.** If `|Im S_ij| ≤ m` and `Re S − k m I` is
positive semidefinite on real vectors, then `Re (y* S y) ≥ 0` for every complex `y`. -/
theorem hermitian_quadratic_nonneg_of_real_part {k : ℕ} (S : Fin k → Fin k → ℂ) {m : ℝ}
    (hm : ∀ i j, |(S i j).im| ≤ m)
    (hR : ∀ x : Fin k → ℝ,
      0 ≤ ∑ i, ∑ j, x i * x j * ((S i j).re - if i = j then k * m else 0))
    (y : Fin k → ℂ) :
    0 ≤ (∑ i, ∑ j, conj (y i) * y j * S i j).re := by
  set x : Fin k → ℝ := fun i => (y i).re
  set z : Fin k → ℝ := fun i => (y i).im
  have hexp : (∑ i, ∑ j, conj (y i) * y j * S i j).re =
      (∑ i, ∑ j, x i * x j * (S i j).re) + (∑ i, ∑ j, z i * z j * (S i j).re) -
        ∑ i, ∑ j, (x i * z j - z i * x j) * (S i j).im := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [x, z]
    ring
  have hdiag : ∀ u : Fin k → ℝ,
      ∑ i, ∑ j, u i * u j * ((S i j).re - if i = j then k * m else 0) =
        (∑ i, ∑ j, u i * u j * (S i j).re) - k * m * ∑ i, u i ^ 2 := by
    intro u
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hx := hR x
  have hz := hR z
  rw [hdiag] at hx hz
  have hJ : ∑ i, ∑ j, (x i * z j - z i * x j) * (S i j).im ≤
      k * m * (∑ i, x i ^ 2) + k * m * ∑ i, z i ^ 2 := by
    calc ∑ i, ∑ j, (x i * z j - z i * x j) * (S i j).im
        ≤ ∑ i, ∑ j, m * ((x i ^ 2 + z j ^ 2 + z i ^ 2 + x j ^ 2) / 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => cross_term_le (hm i j)
      _ = m * ∑ i, ∑ j, (x i ^ 2 + z j ^ 2 + z i ^ 2 + x j ^ 2) / 2 := by
          simp only [Finset.mul_sum]
      _ = k * m * (∑ i, x i ^ 2) + k * m * ∑ i, z i ^ 2 := by
          simp only [add_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, ← Finset.mul_sum]
          ring
  rw [hexp]
  linarith

end AEGIS.FeshbachSchurV1

#print axioms AEGIS.FeshbachSchurV1.feshbach_lower_bound_hermitian
#print axioms AEGIS.FeshbachSchurV1.schur_of_matrix_hermitian
#print axioms AEGIS.FeshbachSchurV1.cross_term_le
#print axioms AEGIS.FeshbachSchurV1.hermitian_quadratic_nonneg_of_real_part
