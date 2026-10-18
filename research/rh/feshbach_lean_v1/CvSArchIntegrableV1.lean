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
import CvSArchDiagV1

/-!
# Integrability of the archimedean integrand (CvS step 5.5b)

`CvSArchDiagV1.arch_series_generic` evaluates `∫ (∑' k, a_k(r) − C) T(r) dr`. To split the
critical-line form of a trigonometric polynomial into its matrix entries the integrand itself must be
integrable. This file proves it, for every continuous `T` with `|T| ≤ M₀` and `|r² T| ≤ M₂`, from a
general fact: a pointwise-summable series of integrable functions whose `L¹` norms are summable has
an integrable sum.
-/

open MeasureTheory Set Real Filter

noncomputable section

namespace AEGIS.CvSArchIntegrableV1

open AEGIS.CvSArchLorentzV1 AEGIS.CvSArchSourceV1 AEGIS.CvSArchDiagV1

/-- A pointwise-summable series of integrable functions with summable `L¹` norms is integrable. -/
theorem integrable_tsum_of_summable_integral_norm {F : ℕ → ℝ → ℝ} (hF : ∀ k, Integrable (F k))
    (hs : Summable fun k => ∫ a, ‖F k a‖) (hpt : ∀ a, Summable fun k => F k a) :
    Integrable fun a => ∑' k, F k a := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun N a => ∑ k ∈ Finset.range N, F k a)
    (fun N => Finset.aestronglyMeasurable_fun_sum _ fun k _ => (hF k).aestronglyMeasurable)
    (Eventually.of_forall fun a => (hpt a).hasSum.tendsto_sum_nat), ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ a, ‖∑' k, F k a‖ₑ ≤ ∫⁻ a, ∑' k, ‖F k a‖ₑ :=
        lintegral_mono fun a => enorm_tsum_le_tsum_enorm
    _ = ∑' k, ∫⁻ a, ‖F k a‖ₑ := lintegral_tsum fun k => (hF k).aestronglyMeasurable.enorm
    _ = ∑' k, ENNReal.ofReal (∫ a, ‖F k a‖) := by
        congr 1; funext k; rw [ofReal_integral_norm_eq_lintegral_enorm (hF k)]
    _ = ENNReal.ofReal (∑' k, ∫ a, ‖F k a‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg fun a => norm_nonneg _) hs).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- **The archimedean integrand is integrable.** For continuous `T` with `|T| ≤ M₀`,
`|r² T| ≤ M₂` and every constant `C`, `r ↦ (∑' k, a_k(r) − C) T(r)` is integrable. -/
theorem arch_mul_integrable {T : ℝ → ℝ} (hT : Continuous T) {M0 M2 : ℝ}
    (h0 : ∀ r, |T r| ≤ M0) (h2 : ∀ r, |r ^ 2 * T r| ≤ M2) (C : ℝ) :
    Integrable fun r => ((∑' k, archTerm k r) - C) * T r := by
  have hTi := integrable_of_bounds hT h0 h2
  set b : ℕ → ℝ := fun k => if k = 0 then C else 0 with hb
  set F : ℕ → ℝ → ℝ := fun k r => (archTerm k r - b k) * T r with hF
  have hFint : ∀ k, Integrable (F k) := fun k =>
    ((archTerm_mul_integrable hTi k).sub (hTi.const_mul (b k))).congr
      (Eventually.of_forall fun r => by simp only [hF, Pi.sub_apply]; ring)
  have hbsum : Summable fun k => |b k| * ∫ r, |T r| := by
    refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
    have : k ≠ 0 := by simpa using hk
    simp [hb, this]
  have hFsum : Summable fun k => ∫ r, ‖F k r‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun r => norm_nonneg _)
      (fun k => ?_) ((archTerm_mul_summable hTi h2).add hbsum)
    have hpt : ∀ r, ‖F k r‖ ≤ ‖archTerm k r * T r‖ + |b k| * |T r| := by
      intro r
      simp only [hF, Real.norm_eq_abs, sub_mul]
      refine (abs_sub _ _).trans (le_of_eq ?_)
      rw [abs_mul (b k)]
    have hG : Integrable fun r => ‖archTerm k r * T r‖ + |b k| * |T r| :=
      (archTerm_mul_integrable hTi k).norm.add (hTi.abs.const_mul _)
    refine (integral_mono (hFint k).norm hG hpt).trans_eq ?_
    rw [integral_add (archTerm_mul_integrable hTi k).norm (hTi.abs.const_mul _),
      integral_const_mul]
  have hptsum : ∀ r, Summable fun k => F k r := fun r =>
    ((archTerm_summable r).sub (hasSum_ite_eq 0 C).summable).mul_right (T r)
  have hpt : ∀ r, ∑' k, F k r = ((∑' k, archTerm k r) - C) * T r := by
    intro r
    simp only [hF]
    rw [tsum_mul_right, ((archTerm_summable r).tsum_sub (hasSum_ite_eq 0 C).summable),
      tsum_ite_eq]
  exact (integrable_tsum_of_summable_integral_norm hFint hFsum hptsum).congr
    (Eventually.of_forall hpt)

theorem arch_mul_sourceS_integrable {L : ℝ} (hL : 0 < L) (n : ℤ) (C : ℝ) :
    Integrable fun r => ((∑' k, archTerm k r) - C) * sourceS L r n :=
  arch_mul_integrable (sourceS_continuous L n) (sourceS_abs_le hL n) (sq_mul_sourceS_abs_le hL n) C

theorem arch_mul_diagD_integrable {L : ℝ} (hL : 0 < L) (n : ℤ) (C : ℝ) :
    Integrable fun r => ((∑' k, archTerm k r) - C) * diagD L r n :=
  arch_mul_integrable (diagD_continuous L n) (diagD_abs_le hL n) (sq_mul_diagD_abs_le hL n) C

end AEGIS.CvSArchIntegrableV1

#print axioms AEGIS.CvSArchIntegrableV1.integrable_tsum_of_summable_integral_norm
#print axioms AEGIS.CvSArchIntegrableV1.arch_mul_integrable
#print axioms AEGIS.CvSArchIntegrableV1.arch_mul_sourceS_integrable
#print axioms AEGIS.CvSArchIntegrableV1.arch_mul_diagD_integrable
