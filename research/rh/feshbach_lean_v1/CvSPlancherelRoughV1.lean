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
import CvSRoughV1
import CvSMassV1
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Plancherel for bounded integrable profiles (CvS step 5.4c)

The trace and cross bounds of a Feshbach certificate are Cauchy–Schwarz estimates in `L²[lo, hi]`,
while the Krein bound (`CvSKreinRoughV1`) is stated for the energy `∫ |𝓕w(t/2π)|² dt`. Mathlib's
Plancherel theorem is for the `L²` extension of `𝓕`; this file proves it for the integral Fourier
transform of a bounded integrable `w` (such as `G − P_V G`):

* `fourier_pairing`: `∫ 𝓕φ · conj 𝓕w = ∫ φ · conj w` for continuous integrable `φ` with integrable
  `𝓕φ` (self-adjointness of `𝓕` and Fourier inversion);
* `mollify_ae_tendsto`: `w ⋆ ρ_ε → w` almost everywhere (Lebesgue differentiation, Mathlib);
* `plancherel_rough`: `∫ |𝓕w|² = ∫ |w|²`, by pairing `w ⋆ ρ_ε` with `w` and letting `ε → 0` on both
  sides (dominated convergence);
* `energy_eq_two_pi_L2`: `∫ |𝓕w(t/2π)|² dt = 2π ∫ |w|²`.
-/

open MeasureTheory FourierTransform Complex Set Filter Topology
open scoped ComplexConjugate Convolution

noncomputable section

namespace AEGIS.CvSPlancherelRoughV1

open AEGIS.RHMollifyV1 AEGIS.CvSRoughV1 AEGIS.CvSMassV1

theorem norm_fourier_le_L1 (w : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 w ξ‖ ≤ ∫ x, ‖w x‖ := by
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

theorem fourier_continuous {w : ℝ → ℂ} (hw : Integrable w) : Continuous (𝓕 w) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hw

/-- `∫ 𝓕f · g = ∫ f · 𝓕g`. -/
theorem fourier_self_adjoint {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner hf hg)

/-- **Parseval pairing.** -/
theorem fourier_pairing {φ w : ℝ → ℂ} (hφc : Continuous φ) (hφ : Integrable φ)
    (hFφ : Integrable (𝓕 φ)) (hw : Integrable w) :
    ∫ ξ, 𝓕 φ ξ * conj (𝓕 w ξ) = ∫ x, φ x * conj (w x) := by
  have h1 : ∀ ξ, 𝓕 φ ξ * conj (𝓕 w ξ) = 𝓕 (conjRefl w) ξ * 𝓕 φ ξ := fun ξ => by
    rw [fourier_conjRefl, mul_comm]
  simp_rw [h1]
  rw [fourier_self_adjoint (conjRefl_integrable hw) hFφ]
  have h2 : ∀ x, 𝓕 (𝓕 φ) x = φ (-x) := fun x => by
    have := congrFun (hφc.fourierInv_fourier_eq hφ hFφ) (-x)
    rw [Real.fourierInv_eq_fourier_neg, neg_neg] at this
    exact this
  simp_rw [h2]
  have h3 := integral_neg_eq_self (fun x => φ x * conj (w x)) volume
  rw [← h3]
  congr 1
  funext x
  simp only [conjRefl]
  ring

theorem mollify_eq_bump_conv (w : ℝ → ℂ) (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    mollify w ε hε x =
      ((bump ε hε).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) x := by
  simp only [mollify, convolution_def, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.lsmul_apply]
  have h := integral_sub_left_eq_self (fun t => w t * moll ε hε (x - t)) volume x
  rw [← h]
  congr 1
  funext t
  simp only [sub_sub_cancel, moll, mollR, Complex.real_smul]
  ring

theorem mollify_ae_tendsto {w : ℝ → ℂ} (hw : Integrable w) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ x, Tendsto (fun k => mollify w (eseq δ k) (eseq_pos hδ k) x) atTop (𝓝 (w x)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := volume) (φ := fun k => bump (eseq δ k) (eseq_pos hδ k)) (l := atTop) (K := 2)
    (eseq_tendsto δ)
    (Eventually.of_forall fun k => by show eseq δ k ≤ 2 * (eseq δ k / 2); linarith)
    hw.locallyIntegrable
  filter_upwards [h] with x hx
  simpa only [mollify_eq_bump_conv] using hx

theorem mollify_norm_le {w : ℝ → ℂ} {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) (ε : ℝ) (hε : 0 < ε)
    (x : ℝ) : ‖mollify w ε hε x‖ ≤ C := by
  rw [mollify_eq_bump_conv, convolution_def]
  refine (norm_integral_le_of_norm_le (g := fun t => (bump ε hε).normed volume t * C)
    ((mollR_integrable ε hε).mul_const C) (Eventually.of_forall fun t => ?_)).trans (le_of_eq ?_)
  · rw [ContinuousLinearMap.lsmul_apply, norm_smul,
      Real.norm_of_nonneg ((bump ε hε).nonneg_normed t)]
    exact mul_le_mul_of_nonneg_left (hC _) ((bump ε hε).nonneg_normed t)
  · rw [integral_mul_const, (bump ε hε).integral_normed, one_mul]

/-- **Plancherel for bounded integrable functions.** -/
theorem plancherel_rough {w : ℝ → ℂ} (hw : Integrable w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C)
    (hE : Integrable fun ξ => Complex.normSq (𝓕 w ξ)) :
    ∫ ξ, Complex.normSq (𝓕 w ξ) = ∫ x, Complex.normSq (w x) := by
  set e := eseq 1
  have he : ∀ k, 0 < e k := eseq_pos one_pos
  set W : ℕ → ℝ → ℂ := fun k => mollify w (e k) (he k) with hW
  have hFc := fourier_continuous hw
  have hWc : ∀ k, Continuous (W k) := fun k => (mollify_contDiff hw (e k) (he k)).continuous
  have hWi : ∀ k, Integrable (W k) := fun k =>
    hw.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (moll_integrable (e k) (he k))
  have hFW : ∀ k ξ, 𝓕 (W k) ξ = 𝓕 w ξ * 𝓕 (moll (e k) (he k)) ξ := fun k ξ =>
    Real.fourier_mul_convolution_eq hw (moll_integrable (e k) (he k)) ξ
  have hFρi : ∀ k, Integrable (𝓕 (moll (e k) (he k))) := fun k => by
    have h := (𝓕 ((moll_hasCompactSupport (e k) (he k)).toSchwartzMap
      (moll_contDiff (e k) (he k)))).integrable (μ := volume)
    rw [SchwartzMap.fourier_coe] at h
    exact h
  have hFWi : ∀ k, Integrable (𝓕 (W k)) := fun k => by
    refine ((hFρi k).bdd_mul (c := ∫ x, ‖w x‖) hFc.aestronglyMeasurable
      (Eventually.of_forall fun ξ => norm_fourier_le_L1 w ξ)).congr
      (Eventually.of_forall fun ξ => ?_)
    simp only [hFW]
  have hpair : ∀ k, ∫ ξ, 𝓕 (W k) ξ * conj (𝓕 w ξ) = ∫ x, W k x * conj (w x) := fun k =>
    fourier_pairing (hWc k) (hWi k) (hFWi k) hw
  -- the Fourier side
  have hL : Tendsto (fun k => ∫ ξ, 𝓕 (W k) ξ * conj (𝓕 w ξ)) atTop
      (𝓝 (∫ ξ, ((Complex.normSq (𝓕 w ξ) : ℝ) : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence (fun ξ => Complex.normSq (𝓕 w ξ))
      (fun k => (hFWi k).aestronglyMeasurable.mul
        (Complex.continuous_conj.comp hFc).aestronglyMeasurable) hE
      (fun k => Eventually.of_forall fun ξ => ?_) (Eventually.of_forall fun ξ => ?_)
    · rw [hFW, mul_right_comm, Complex.mul_conj, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Complex.normSq_nonneg _)]
      exact mul_le_of_le_one_right (Complex.normSq_nonneg _) (fourier_moll_norm_le _ _ ξ)
    · have h := (fourier_moll_tendsto one_pos ξ).const_mul (((Complex.normSq (𝓕 w ξ) : ℝ) : ℂ))
      rw [mul_one] at h
      refine h.congr fun k => ?_
      rw [hFW, mul_right_comm, Complex.mul_conj]
  -- the space side
  have hR : Tendsto (fun k => ∫ x, W k x * conj (w x)) atTop (𝓝 (∫ x, w x * conj (w x))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => C * ‖w x‖)
      (fun k => (hWc k).aestronglyMeasurable.mul
        (Complex.continuous_conj.comp_aestronglyMeasurable hw.aestronglyMeasurable))
      (hw.norm.const_mul C) (fun k => Eventually.of_forall fun x => ?_) ?_
    · rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_right (mollify_norm_le hC (e k) (he k) x) (norm_nonneg _)
    · filter_upwards [mollify_ae_tendsto hw one_pos] with x hx
      exact hx.mul_const _
  have hlim := tendsto_nhds_unique (hL.congr hpair) hR
  have e1 : (∫ x, w x * conj (w x)) = ((∫ x, Complex.normSq (w x) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; funext x; rw [Complex.mul_conj]
  rw [e1, integral_complex_ofReal] at hlim
  exact_mod_cast hlim

/-- **The energy is `2π` times the `L²` norm.** -/
theorem energy_eq_two_pi_L2 {w : ℝ → ℂ} (hw : Integrable w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C)
    (hE : Integrable (energy w)) :
    ∫ t, energy w t = 2 * Real.pi * ∫ x, Complex.normSq (w x) := by
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have hsub : (∫ t, energy w t) = (2 * Real.pi) * ∫ ξ, Complex.normSq (𝓕 w ξ) := by
    have e : (fun t => energy w t) =
        fun t => (fun ξ => Complex.normSq (𝓕 w ξ)) (t / (2 * Real.pi)) := rfl
    rw [e, Measure.integral_comp_div (fun ξ => Complex.normSq (𝓕 w ξ)) (2 * Real.pi),
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), smul_eq_mul]
  have hE' : Integrable fun ξ => Complex.normSq (𝓕 w ξ) := by
    refine (hE.comp_mul_left' h2pi).congr (Eventually.of_forall fun ξ => ?_)
    simp only [energy]
    congr 2
    field_simp
  rw [hsub, plancherel_rough hw hC hE']

end AEGIS.CvSPlancherelRoughV1

#print axioms AEGIS.CvSPlancherelRoughV1.fourier_self_adjoint
#print axioms AEGIS.CvSPlancherelRoughV1.fourier_pairing
#print axioms AEGIS.CvSPlancherelRoughV1.mollify_ae_tendsto
#print axioms AEGIS.CvSPlancherelRoughV1.mollify_norm_le
#print axioms AEGIS.CvSPlancherelRoughV1.plancherel_rough
#print axioms AEGIS.CvSPlancherelRoughV1.energy_eq_two_pi_L2
