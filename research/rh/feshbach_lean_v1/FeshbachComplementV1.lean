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
import FeshbachSchurHermitianV1
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The complement bound `c_∞ ≥ m − τ` of the Feshbach certificates

`complement_trace_arb.py` bounds the form on the complement of the low block: from the Krein step
`Q(w) ≥ m ‖w‖² − ⟨w, T w⟩` with `T = ∫ s(t) |e_t⟩⟨e_t|` (`s ≥ 0`), it takes
`c_∞ ≥ m − tr(P T P)`, `tr(P T P) = tr T − tr(Π T)`. Here the same bound is proved without operator
traces: for `w ⊥ V`, Bessel gives `|⟨e, w⟩|² ≤ (‖e‖² − ‖P_V e‖²) ‖w‖²`, and integrating against `s`
gives `⟨w, T w⟩ ≤ τ ‖w‖²` with `τ = ∫ s(t) (‖e_t‖² − ‖P_V e_t‖²) dt`, the quantity
`tr T − tr(Π T)` that the Arb script encloses. The result feeds `feshbach_lower_bound_hermitian`.
-/

namespace AEGIS.FeshbachSchurV1

open MeasureTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

/-- Bessel step: a vector orthogonal to `V` only sees the `Vᗮ` part of `e`. -/
theorem norm_inner_sq_le_of_mem_orthogonal (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    (e w : E) (hw : w ∈ Vᗮ) :
    ‖⟪e, w⟫‖ ^ 2 ≤ (‖e‖ ^ 2 - ‖V.starProjection e‖ ^ 2) * ‖w‖ ^ 2 := by
  set p := V.starProjection e
  have hp : p ∈ V := V.starProjection_apply_mem e
  have hz : e - p ∈ Vᗮ := V.sub_starProjection_mem_orthogonal e
  have hinner : ⟪e, w⟫ = ⟪e - p, w⟫ := by
    rw [inner_sub_left, V.inner_right_of_mem_orthogonal hp hw, sub_zero]
  have hpy : ‖e‖ ^ 2 = ‖p‖ ^ 2 + ‖e - p‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p (e - p)
      (V.inner_right_of_mem_orthogonal hp hz)
    have he : p + (e - p) = e := by abel
    rw [he] at h
    nlinarith [h]
  have hcs : ‖⟪e - p, w⟫‖ ≤ ‖e - p‖ * ‖w‖ := norm_inner_le_norm _ _
  have hd : ‖e‖ ^ 2 - ‖p‖ ^ 2 = ‖e - p‖ ^ 2 := by linarith
  rw [hinner, hd]
  calc ‖⟪e - p, w⟫‖ ^ 2 ≤ (‖e - p‖ * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcs 2
    _ = ‖e - p‖ ^ 2 * ‖w‖ ^ 2 := by ring

/-- Integrated Bessel step: `∫ s |⟨e_t, w⟩|² ≤ τ ‖w‖²` for `w ⊥ V`. -/
theorem slack_le_trace_mul_norm_sq {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (V : Submodule ℂ E) [V.HasOrthogonalProjection] (e : α → E) (s : α → ℝ)
    (hs : ∀ t, 0 ≤ s t) (w : E) (hw : w ∈ Vᗮ)
    (hi1 : Integrable (fun t => s t * ‖⟪e t, w⟫‖ ^ 2) ν)
    (hi2 : Integrable (fun t => s t * (‖e t‖ ^ 2 - ‖V.starProjection (e t)‖ ^ 2)) ν) :
    ∫ t, s t * ‖⟪e t, w⟫‖ ^ 2 ∂ν ≤
      (∫ t, s t * (‖e t‖ ^ 2 - ‖V.starProjection (e t)‖ ^ 2) ∂ν) * ‖w‖ ^ 2 := by
  rw [← integral_mul_const]
  refine integral_mono hi1 (hi2.mul_const _) fun t => ?_
  have h := norm_inner_sq_le_of_mem_orthogonal V (e t) w hw
  calc s t * ‖⟪e t, w⟫‖ ^ 2
      ≤ s t * ((‖e t‖ ^ 2 - ‖V.starProjection (e t)‖ ^ 2) * ‖w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h (hs t)
    _ = s t * (‖e t‖ ^ 2 - ‖V.starProjection (e t)‖ ^ 2) * ‖w‖ ^ 2 := by ring

/-- **Complement bound.** The Krein step with slack on `Vᗮ` gives `Re Q ≥ (m − τ) ‖·‖²` there. -/
theorem complement_lower_bound_of_slack {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (Q : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    (e : α → E) (s : α → ℝ) (hs : ∀ t, 0 ≤ s t) {m : ℝ}
    (hslack : ∀ w ∈ Vᗮ, m * ‖w‖ ^ 2 - ∫ t, s t * ‖⟪e t, w⟫‖ ^ 2 ∂ν ≤ (Q w w).re)
    (hi1 : ∀ w ∈ Vᗮ, Integrable (fun t => s t * ‖⟪e t, w⟫‖ ^ 2) ν)
    (hi2 : Integrable (fun t => s t * (‖e t‖ ^ 2 - ‖V.starProjection (e t)‖ ^ 2)) ν) :
    ∀ w ∈ Vᗮ, (m - ∫ t, s t * (‖e t‖ ^ 2 - ‖V.starProjection (e t)‖ ^ 2) ∂ν) * ‖w‖ ^ 2 ≤
      (Q w w).re := by
  intro w hw
  have h := hslack w hw
  have hb := slack_le_trace_mul_norm_sq ν V e s hs w hw (hi1 w hw) hi2
  rw [sub_mul]
  linarith

/-- **Feshbach from the Krein step.** With `c = m − τ`, the Krein inequality with slack on `Vᗮ`,
the cross-term bound and the Schur hypothesis on `V` give `Re Q ≥ μ ‖·‖²` everywhere. -/
theorem feshbach_of_krein_slack {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (Q : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (hherm : ∀ x y, Q y x = (starRingEnd ℂ) (Q x y))
    (V : Submodule ℂ E) [V.HasOrthogonalProjection] (C : E → ℝ)
    (e : α → E) (s : α → ℝ) (hs : ∀ t, 0 ≤ s t) {μ m : ℝ}
    (hslack : ∀ w ∈ Vᗮ, m * ‖w‖ ^ 2 - ∫ t, s t * ‖⟪e t, w⟫‖ ^ 2 ∂ν ≤ (Q w w).re)
    (hi1 : ∀ w ∈ Vᗮ, Integrable (fun t => s t * ‖⟪e t, w⟫‖ ^ 2) ν)
    (hi2 : Integrable (fun t => s t * (‖e t‖ ^ 2 - ‖V.starProjection (e t)‖ ^ 2)) ν)
    (hμc : μ < m - ∫ t, s t * (‖e t‖ ^ 2 - ‖V.starProjection (e t)‖ ^ 2) ∂ν)
    (hcross : ∀ v ∈ V, ∀ w ∈ Vᗮ, ‖Q v w‖ ^ 2 ≤ C v * ‖w‖ ^ 2)
    (hC : ∀ v ∈ V, 0 ≤ C v)
    (hschur : ∀ v ∈ V, μ * ‖v‖ ^ 2 +
      C v / ((m - ∫ t, s t * (‖e t‖ ^ 2 - ‖V.starProjection (e t)‖ ^ 2) ∂ν) - μ) ≤
        (Q v v).re)
    (x : E) : μ * ‖x‖ ^ 2 ≤ (Q x x).re :=
  feshbach_lower_bound_hermitian Q hherm V C hμc
    (complement_lower_bound_of_slack ν Q V e s hs hslack hi1 hi2) hcross hC hschur x

end AEGIS.FeshbachSchurV1

#print axioms AEGIS.FeshbachSchurV1.norm_inner_sq_le_of_mem_orthogonal
#print axioms AEGIS.FeshbachSchurV1.slack_le_trace_mul_norm_sq
#print axioms AEGIS.FeshbachSchurV1.complement_lower_bound_of_slack
#print axioms AEGIS.FeshbachSchurV1.feshbach_of_krein_slack
