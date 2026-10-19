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
import RHMollifyV1

/-!
# From smooth to rough moment-zero profiles by mollification (CvS step 5.4a)

The Krein certificates bound `∫ S |𝓕G(t/2π)|² dt` from below for smooth `G`. The Feshbach
complement `w = G − P_V G` of a trigonometric low block is not smooth (the atoms `e_n` jump at the
ends of `[0, L]`). This file transfers any such lower bound from smooth to integrable profiles:

* `G ⋆ ρ_ε` (`RHMollifyV1.moll`) is smooth, supported in `[lo − ε, hi + ε]`, and keeps both moments
  `∫ e^{∓u/2} G = 0` (the weight `e^{cu}` is multiplicative, so the moment of a convolution is the
  product of the moments);
* `|𝓕(G ⋆ ρ_ε)|² = |𝓕G|² |𝓕ρ_ε|²` with `|𝓕ρ_ε| ≤ 1` and `𝓕ρ_ε → 1` as `ε → 0`;
* `rough_of_smooth`: by dominated convergence, a bound `m ∫ |𝓕G|² ≤ ∫ S |𝓕G|²` valid for smooth
  moment-zero profiles of support length `< L` holds for integrable ones of support length `< L`.
-/

open MeasureTheory FourierTransform Complex Set Filter Topology
open scoped ContDiff Convolution SchwartzMap

noncomputable section

namespace AEGIS.CvSRoughV1

open AEGIS.RHMollifyV1

/-- The critical-line energy density `|𝓕G(t/2π)|²` of a log profile. -/
def energy (G : ℝ → ℂ) (t : ℝ) : ℝ := Complex.normSq (𝓕 G (t / (2 * Real.pi)))

/-- The two moment conditions `∫ e^{∓u/2} G = 0`. -/
def MomentZero (G : ℝ → ℂ) : Prop :=
  (∫ u, (Real.exp (-u / 2) : ℂ) * G u = 0) ∧ ∫ u, (Real.exp (u / 2) : ℂ) * G u = 0

/-- `G ⋆ ρ_ε`. -/
def mollify (G : ℝ → ℂ) (ε : ℝ) (hε : 0 < ε) : ℝ → ℂ :=
  G ⋆[ContinuousLinearMap.mul ℂ ℂ] moll ε hε

theorem moll_integrable (ε : ℝ) (hε : 0 < ε) : Integrable (moll ε hε) :=
  (moll_contDiff ε hε).continuous.integrable_of_hasCompactSupport (moll_hasCompactSupport ε hε)

theorem moll_ne_zero {ε : ℝ} {hε : 0 < ε} {x : ℝ} (h : moll ε hε x ≠ 0) : |x| < ε := by
  by_contra hx
  exact h (by simp [moll, mollR_zero_outside ε hε x (not_lt.mp hx)])

theorem mollify_contDiff {G : ℝ → ℂ} (hG : Integrable G) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (mollify G ε hε) := by
  have h := (moll_hasCompactSupport ε hε).contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℂ) (μ := volume) (n := ⊤) hG.locallyIntegrable (moll_contDiff ε hε)
  have e : (G ⋆[ContinuousLinearMap.mul ℝ ℂ] moll ε hε) = mollify G ε hε := by
    funext x
    simp only [mollify, convolution_def, ContinuousLinearMap.mul_apply']
  rw [← e]
  exact h

theorem mollify_tsupport {G : ℝ → ℂ} {lo hi : ℝ} (hsupp : Function.support G ⊆ Icc lo hi)
    (ε : ℝ) (hε : 0 < ε) : tsupport (mollify G ε hε) ⊆ Icc (lo - ε) (hi + ε) := by
  refine closure_minimal (fun z hz => ?_) isClosed_Icc
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp
    (support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) (μ := volume) hz)
  have h1 := hsupp ha
  have h2 := abs_lt.mp (moll_ne_zero hb)
  exact ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩

theorem weighted_integrable {G : ℝ → ℂ} (hG : Integrable G) {lo hi : ℝ}
    (hsupp : Function.support G ⊆ Icc lo hi) (c : ℝ) :
    Integrable fun u => (Real.exp (c * u) : ℂ) * G u := by
  set C := Real.exp (|c| * max |lo| |hi|)
  refine (hG.norm.const_mul C).mono'
    ((by fun_prop : Continuous fun u : ℝ => (Real.exp (c * u) : ℂ)).aestronglyMeasurable.mul
      hG.aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  by_cases hu : G u = 0
  · rw [hu, norm_zero, mul_zero, mul_zero]
  · have hmem := hsupp hu
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have h1 : |u| ≤ max |lo| |hi| := abs_le.mpr
      ⟨by linarith [neg_abs_le lo, le_max_left |lo| |hi|, hmem.1],
        by linarith [le_abs_self hi, le_max_right |lo| |hi|, hmem.2]⟩
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg c)

theorem moll_weighted_integrable (ε : ℝ) (hε : 0 < ε) (c : ℝ) :
    Integrable fun u => (Real.exp (c * u) : ℂ) * moll ε hε u := by
  refine Continuous.integrable_of_hasCompactSupport (by
    have := (moll_contDiff ε hε).continuous
    fun_prop) ?_
  exact (moll_hasCompactSupport ε hε).mul_left

theorem weighted_mollify (G : ℝ → ℂ) (ε : ℝ) (hε : 0 < ε) (c u : ℝ) :
    (Real.exp (c * u) : ℂ) * mollify G ε hε u =
      ((fun y => (Real.exp (c * y) : ℂ) * G y) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun y => (Real.exp (c * y) : ℂ) * moll ε hε y)) u := by
  simp only [mollify, convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_const_mul]
  congr 1
  funext t
  have : Real.exp (c * u) = Real.exp (c * t) * Real.exp (c * (u - t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]
  push_cast
  ring

/-- The weighted moment of `G ⋆ ρ_ε` is the product of the weighted moments. -/
theorem mollify_weighted_integral {G : ℝ → ℂ} (hG : Integrable G) {lo hi : ℝ}
    (hsupp : Function.support G ⊆ Icc lo hi) (ε : ℝ) (hε : 0 < ε) (c : ℝ) :
    ∫ u, (Real.exp (c * u) : ℂ) * mollify G ε hε u =
      (∫ u, (Real.exp (c * u) : ℂ) * G u) * ∫ u, (Real.exp (c * u) : ℂ) * moll ε hε u := by
  simp_rw [weighted_mollify G ε hε c]
  rw [integral_convolution (ContinuousLinearMap.mul ℂ ℂ) (weighted_integrable hG hsupp c)
    (moll_weighted_integrable ε hε c)]
  rfl

theorem mollify_momentZero {G : ℝ → ℂ} (hG : Integrable G) {lo hi : ℝ}
    (hsupp : Function.support G ⊆ Icc lo hi) (hmom : MomentZero G) (ε : ℝ) (hε : 0 < ε) :
    MomentZero (mollify G ε hε) := by
  have e1 : ∀ F : ℝ → ℂ, (∫ u, (Real.exp (-u / 2) : ℂ) * F u) =
      ∫ u, (Real.exp ((-1 / 2) * u) : ℂ) * F u := fun F => by
    congr 1; funext u; rw [show -u / 2 = (-1 / 2) * u by ring]
  have e2 : ∀ F : ℝ → ℂ, (∫ u, (Real.exp (u / 2) : ℂ) * F u) =
      ∫ u, (Real.exp ((1 / 2) * u) : ℂ) * F u := fun F => by
    congr 1; funext u; rw [show u / 2 = (1 / 2) * u by ring]
  refine ⟨?_, ?_⟩
  · rw [e1, mollify_weighted_integral hG hsupp ε hε, ← e1, hmom.1, zero_mul]
  · rw [e2, mollify_weighted_integral hG hsupp ε hε, ← e2, hmom.2, zero_mul]

/-- The mollifier's Fourier factor `|𝓕ρ_ε(t/2π)|²`. -/
def mfac (ε : ℝ) (hε : 0 < ε) (t : ℝ) : ℝ := Complex.normSq (𝓕 (moll ε hε) (t / (2 * Real.pi)))

theorem mollify_energy {G : ℝ → ℂ} (hG : Integrable G) (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    energy (mollify G ε hε) t = energy G t * mfac ε hε t := by
  simp only [energy, mfac, mollify]
  rw [Real.fourier_mul_convolution_eq hG (moll_integrable ε hε), map_mul]

theorem mfac_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (mfac ε hε) := by
  set ψ : 𝓢(ℝ, ℂ) := (moll_hasCompactSupport ε hε).toSchwartzMap (moll_contDiff ε hε)
  have hc : Continuous (𝓕 (moll ε hε)) := by
    have h := (𝓕 ψ).continuous
    rw [SchwartzMap.fourier_coe] at h
    exact h
  unfold mfac
  fun_prop

theorem mfac_nonneg (ε : ℝ) (hε : 0 < ε) (t : ℝ) : 0 ≤ mfac ε hε t := Complex.normSq_nonneg _

theorem mfac_le_one (ε : ℝ) (hε : 0 < ε) (t : ℝ) : mfac ε hε t ≤ 1 := by
  have hn : ‖𝓕 (moll ε hε) (t / (2 * Real.pi))‖ ≤ 1 := by
    rw [Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp_rw [Circle.norm_smul]
    simp only [moll, Complex.norm_real, Real.norm_of_nonneg (mollR_nonneg ε hε _)]
    exact mollR_integral ε hε
  unfold mfac
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (𝓕 (moll ε hε) (t / (2 * Real.pi)))]

/-- The mollifier scales `δ/(k+2) → 0`. -/
def eseq (δ : ℝ) (k : ℕ) : ℝ := δ / (k + 2)

theorem eseq_pos {δ : ℝ} (hδ : 0 < δ) (k : ℕ) : 0 < eseq δ k := by
  unfold eseq; positivity

theorem eseq_le {δ : ℝ} (hδ : 0 < δ) (k : ℕ) : eseq δ k ≤ δ / 2 := by
  unfold eseq
  exact div_le_div_of_nonneg_left hδ.le (by norm_num) (by linarith [k.cast_nonneg (α := ℝ)])

theorem eseq_tendsto (δ : ℝ) : Tendsto (eseq δ) atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => ((k : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have h2 := h.inv_tendsto_atTop.const_mul δ
  rw [mul_zero] at h2
  refine h2.congr fun k => ?_
  simp [eseq, div_eq_mul_inv]

theorem mfac_tendsto {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    Tendsto (fun k => mfac (eseq δ k) (eseq_pos hδ k) t) atTop (𝓝 1) := by
  set ξ := t / (2 * Real.pi)
  have hF : Tendsto (fun k => 𝓕 (moll (eseq δ k) (eseq_pos hδ k)) ξ) atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun k => (2 * Real.pi * eseq δ k * ξ) ^ 2 / 2) atTop (𝓝 0) := by
      have : Tendsto (fun k => (2 * Real.pi * eseq δ k * ξ) ^ 2 / 2) atTop
          (𝓝 ((2 * Real.pi * 0 * ξ) ^ 2 / 2)) :=
        ((((eseq_tendsto δ).const_mul (2 * Real.pi)).mul_const ξ).pow 2).div_const 2
      simpa using this
    exact squeeze_zero (fun k => norm_nonneg _)
      (fun k => fourier_moll_sub_one (eseq δ k) (eseq_pos hδ k) ξ) hb
  have h := (Complex.continuous_normSq.tendsto 1).comp hF
  rw [map_one] at h
  exact h

/-- **Smooth bounds extend to rough profiles.** If `m ∫ |𝓕F|² ≤ ∫ S |𝓕F|²` holds for every smooth
moment-zero `F` supported in an interval of length `< L`, it holds for every integrable moment-zero
`G` vanishing outside an interval of length `< L` with `|𝓕G|²` and `S |𝓕G|²` integrable. -/
theorem rough_of_smooth (S : ℝ → ℝ) (m L : ℝ)
    (hsmooth : ∀ F : ℝ → ℂ, ContDiff ℝ ∞ F → ∀ lo hi : ℝ, lo ≤ hi → tsupport F ⊆ Icc lo hi →
      hi - lo < L → MomentZero F → Integrable (fun t => S t * energy F t) →
      m * ∫ t, energy F t ≤ ∫ t, S t * energy F t)
    {G : ℝ → ℂ} (hG : Integrable G) {lo hi : ℝ} (hlh : lo ≤ hi)
    (hsupp : Function.support G ⊆ Icc lo hi) (hlen : hi - lo < L) (hmom : MomentZero G)
    (hE : Integrable (energy G)) (hSE : Integrable fun t => S t * energy G t) :
    m * ∫ t, energy G t ≤ ∫ t, S t * energy G t := by
  set δ := (L - (hi - lo)) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set e := eseq δ
  have he : ∀ k, 0 < e k := eseq_pos hδ
  set P : ℕ → ℝ → ℝ := fun k => mfac (e k) (he k) with hP
  have hPc : ∀ k, Continuous (P k) := fun k => mfac_continuous _ _
  have hP0 : ∀ k t, 0 ≤ P k t := fun k t => mfac_nonneg _ _ t
  have hP1 : ∀ k t, P k t ≤ 1 := fun k t => mfac_le_one _ _ t
  have hPt : ∀ t, Tendsto (fun k => P k t) atTop (𝓝 1) := fun t => mfac_tendsto hδ t
  have hPn : ∀ k t, ‖P k t‖ ≤ 1 := fun k t => by
    rw [Real.norm_of_nonneg (hP0 k t)]; exact hP1 k t
  -- the bound for each mollified profile
  have hk : ∀ k, m * ∫ t, energy G t * P k t ≤ ∫ t, S t * energy G t * P k t := by
    intro k
    have hEk : ∀ t, energy (mollify G (e k) (he k)) t = energy G t * P k t := fun t =>
      mollify_energy hG (e k) (he k) t
    have hSk : Integrable fun t => S t * energy (mollify G (e k) (he k)) t := by
      refine (hSE.mul_bdd (c := 1) (hPc k).aestronglyMeasurable
        (Eventually.of_forall (hPn k))).congr (Eventually.of_forall fun t => ?_)
      simp only [hEk]; ring
    have hb := hsmooth _ (mollify_contDiff hG (e k) (he k)) (lo - e k) (hi + e k)
      (by linarith [he k]) (mollify_tsupport hsupp (e k) (he k))
      (by linarith [eseq_le hδ k, he k]) (mollify_momentZero hG hsupp hmom (e k) (he k)) hSk
    simp only [hEk] at hb
    refine hb.trans (le_of_eq ?_)
    congr 1; funext t; ring
  -- dominated convergence on both sides
  have h1 : Tendsto (fun k => ∫ t, energy G t * P k t) atTop (𝓝 (∫ t, energy G t)) := by
    refine tendsto_integral_of_dominated_convergence (fun t => energy G t)
      (fun k => hE.aestronglyMeasurable.mul (hPc k).aestronglyMeasurable) hE
      (fun k => Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
    · rw [norm_mul, Real.norm_of_nonneg (show 0 ≤ energy G t from Complex.normSq_nonneg _)]
      exact mul_le_of_le_one_right (Complex.normSq_nonneg _) (hPn k t)
    · simpa using (hPt t).const_mul (energy G t)
  have h2 : Tendsto (fun k => ∫ t, S t * energy G t * P k t) atTop
      (𝓝 (∫ t, S t * energy G t)) := by
    refine tendsto_integral_of_dominated_convergence (fun t => ‖S t * energy G t‖)
      (fun k => hSE.aestronglyMeasurable.mul (hPc k).aestronglyMeasurable) hSE.norm
      (fun k => Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hPn k t)
    · simpa using (hPt t).const_mul (S t * energy G t)
  exact le_of_tendsto_of_tendsto' (h1.const_mul m) h2 hk

end AEGIS.CvSRoughV1

#print axioms AEGIS.CvSRoughV1.mollify_contDiff
#print axioms AEGIS.CvSRoughV1.mollify_tsupport
#print axioms AEGIS.CvSRoughV1.mollify_momentZero
#print axioms AEGIS.CvSRoughV1.mollify_energy
#print axioms AEGIS.CvSRoughV1.mfac_le_one
#print axioms AEGIS.CvSRoughV1.mfac_tendsto
#print axioms AEGIS.CvSRoughV1.rough_of_smooth
