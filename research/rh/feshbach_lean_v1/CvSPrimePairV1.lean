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
# Prime-power pairing of a block profile (CvS step 5.5c)

For a continuous profile `f` on `[0, L]` with `f(L) = 0` whose cosine transform `T = cosT f L`
satisfies `|T| ≤ M₀` and `|r² T| ≤ M₂`, Fourier inversion of the even extension gives

`∫ cos(t a) T(t) dt = π f(a)` for `0 ≤ a ≤ L`, and `= 0` for `a > L`.

So a prime power `q` with `log q < L` contributes `π B_nm(log q)` to the block, and every prime power
with `log q > L` contributes nothing: the prime entries of `feshbach_blocks_arb.py`.
-/

open MeasureTheory Complex Set Real
open scoped FourierTransform

noncomputable section

namespace AEGIS.CvSPrimePairV1

open AEGIS.CvSArchLorentzV1 AEGIS.CvSArchSourceV1 AEGIS.CvSArchDiagV1

/-- The even extension `f(min(|y|, L))`; it vanishes for `|y| ≥ L` when `f(L) = 0`. -/
def evenExt (f : ℝ → ℝ) (L : ℝ) (y : ℝ) : ℂ := ((f (min |y| L) : ℝ) : ℂ)

theorem evenExt_continuous {f : ℝ → ℝ} (hf : Continuous f) (L : ℝ) :
    Continuous (evenExt f L) := by
  unfold evenExt; fun_prop

theorem evenExt_eq_indicator {f : ℝ → ℝ} {L : ℝ} (hfL : f L = 0) :
    evenExt f L = indicator (Icc (-L) L) (fun y => ((f |y| : ℝ) : ℂ)) := by
  funext y
  by_cases hy : y ∈ Icc (-L) L
  · rw [indicator_of_mem hy, evenExt, min_eq_left (abs_le.mpr ⟨hy.1, hy.2⟩)]
  · rw [indicator_of_notMem hy, evenExt]
    have : L ≤ |y| := by
      by_contra h
      push Not at h
      exact hy ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
    rw [min_eq_right this, hfL, Complex.ofReal_zero]

theorem evenExt_integrable {f : ℝ → ℝ} (hf : Continuous f) {L : ℝ} (hfL : f L = 0) :
    Integrable (evenExt f L) := by
  rw [evenExt_eq_indicator hfL]
  refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
  exact (by fun_prop : Continuous fun y : ℝ => ((f |y| : ℝ) : ℂ)).integrableOn_Icc

/-- `𝓕 f_e(ξ) = 2 cosT f L (2πξ)`. -/
theorem fourier_evenExt {f : ℝ → ℝ} (hf : Continuous f) {L : ℝ} (hL : 0 ≤ L) (hfL : f L = 0)
    (ξ : ℝ) :
    𝓕 (evenExt f L) ξ = ((2 * cosT f L (2 * Real.pi * ξ) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, evenExt_eq_indicator hfL]
  have hind : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * ξ) * I) •
      indicator (Icc (-L) L) (fun y => ((f |y| : ℝ) : ℂ)) v) =
      indicator (Icc (-L) L) (fun v => Complex.exp (↑(-2 * Real.pi * v * ξ) * I) •
        ((f |v| : ℝ) : ℂ)) := by
    funext v
    by_cases hv : v ∈ Icc (-L) L <;> simp [hv]
  have hc : Continuous fun y : ℝ => Complex.exp (↑(-2 * Real.pi * y * ξ) * I) •
      ((f |y| : ℝ) : ℂ) := by fun_prop
  rw [hind, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -L ≤ L),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hneg : (∫ y in (-L)..0, Complex.exp (↑(-2 * Real.pi * y * ξ) * I) • ((f |y| : ℝ) : ℂ)) =
      ∫ y in (0 : ℝ)..L, Complex.exp (↑(2 * Real.pi * y * ξ) * I) • ((f y : ℝ) : ℂ) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := L)
      (f := fun y => Complex.exp (↑(-2 * Real.pi * y * ξ) * I) • ((f |y| : ℝ) : ℂ))
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hL] at hy
    simp only [abs_neg, abs_of_nonneg hy.1]
    congr 3
    ring_nf
  have hpos : (∫ y in (0 : ℝ)..L, Complex.exp (↑(-2 * Real.pi * y * ξ) * I) • ((f |y| : ℝ) : ℂ)) =
      ∫ y in (0 : ℝ)..L, Complex.exp (↑(-2 * Real.pi * y * ξ) * I) • ((f y : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hL] at hy
    simp only [abs_of_nonneg hy.1]
  have hc1 : Continuous fun y : ℝ => Complex.exp (↑(2 * Real.pi * y * ξ) * I) •
      ((f y : ℝ) : ℂ) := by fun_prop
  have hc2 : Continuous fun y : ℝ => Complex.exp (↑(-2 * Real.pi * y * ξ) * I) •
      ((f y : ℝ) : ℂ) := by fun_prop
  rw [hneg, hpos, ← intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _), cosT,
    show ((2 * ∫ y in (0 : ℝ)..L, f y * Real.cos (2 * Real.pi * ξ * y) : ℝ) : ℂ) =
      ∫ y in (0 : ℝ)..L, ((2 * (f y * Real.cos (2 * Real.pi * ξ * y)) : ℝ) : ℂ) by
      rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]]
  refine intervalIntegral.integral_congr fun y _ => ?_
  simp only [smul_eq_mul]
  rw [← add_mul, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [show -2 * (π : ℂ) * y * ξ = -(2 * π * ξ * y) by ring,
    show 2 * (π : ℂ) * y * ξ = 2 * π * ξ * y by ring, Complex.cos_neg, Complex.sin_neg]
  ring_nf

theorem cosT_bound {f : ℝ → ℝ} {L M0 M2 : ℝ} (h0 : ∀ r, |cosT f L r| ≤ M0)
    (h2 : ∀ r, |r ^ 2 * cosT f L r| ≤ M2) (r : ℝ) :
    |cosT f L r| ≤ (M0 + M2) * (1 + r ^ 2)⁻¹ := by
  have a := h0 r
  have b := h2 r
  rw [abs_mul, abs_of_nonneg (sq_nonneg r)] at b
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc |cosT f L r| * (1 + r ^ 2) = |cosT f L r| + r ^ 2 * |cosT f L r| := by ring
    _ ≤ M0 + M2 := by linarith

theorem fourier_evenExt_integrable {f : ℝ → ℝ} (hf : Continuous f) {L : ℝ} (hL : 0 ≤ L)
    (hfL : f L = 0) {M0 M2 : ℝ} (h0 : ∀ r, |cosT f L r| ≤ M0)
    (h2 : ∀ r, |r ^ 2 * cosT f L r| ≤ M2) : Integrable (𝓕 (evenExt f L)) := by
  have hT := integrable_of_bounds (cosT_continuous hf L) h0 h2
  have hT2 : Integrable fun ξ : ℝ => cosT f L (2 * Real.pi * ξ) :=
    hT.comp_mul_left' (by positivity)
  refine ((hT2.const_mul 2).ofReal (𝕜 := ℂ)).congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [fourier_evenExt hf hL hfL]
  rfl

/-- **Prime-power pairing.** -/
theorem cos_pairing {f : ℝ → ℝ} (hf : Continuous f) {L : ℝ} (hL : 0 ≤ L) (hfL : f L = 0)
    {M0 M2 : ℝ} (h0 : ∀ r, |cosT f L r| ≤ M0) (h2 : ∀ r, |r ^ 2 * cosT f L r| ≤ M2) (a : ℝ) :
    ∫ t : ℝ, Real.cos (t * a) * cosT f L t = Real.pi * f (min |a| L) := by
  have hinv := (evenExt_continuous hf L).fourierInv_fourier_eq (evenExt_integrable hf hfL)
    (fourier_evenExt_integrable hf hL hfL h0 h2)
  have ha := congrFun hinv a
  rw [Real.fourierInv_eq'] at ha
  simp_rw [fourier_evenExt hf hL hfL] at ha
  have hT := integrable_of_bounds (cosT_continuous hf L) h0 h2
  -- real parts
  have hre := congrArg Complex.re ha
  rw [evenExt, Complex.ofReal_re] at hre
  have hint : Integrable fun ξ : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ ξ a) * I) •
      ((2 * cosT f L (2 * Real.pi * ξ) : ℝ) : ℂ) := by
    have h := ((hT.comp_mul_left' (by positivity : (2 * Real.pi) ≠ 0)).const_mul 2).ofReal (𝕜 := ℂ)
    refine (h.bdd_mul (c := 1) (by fun_prop : Continuous fun ξ : ℝ =>
      Complex.exp (↑(2 * Real.pi * inner ℝ ξ a) * I)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)).congr (Filter.Eventually.of_forall fun ξ => ?_)
    · rw [Complex.norm_exp_ofReal_mul_I]
    · simp only [smul_eq_mul]
      rfl
  have hre' := integral_re hint
  simp only [RCLike.re_to_complex] at hre'
  rw [← hre'] at hre
  have hcos : ∀ ξ : ℝ, (Complex.exp (↑(2 * Real.pi * inner ℝ ξ a) * I) •
      ((2 * cosT f L (2 * Real.pi * ξ) : ℝ) : ℂ)).re =
      2 * (Real.cos (2 * Real.pi * ξ * a) * cosT f L (2 * Real.pi * ξ)) := by
    intro ξ
    simp only [smul_eq_mul, Complex.re_mul_ofReal,
      Complex.exp_ofReal_mul_I_re, RCLike.inner_apply, conj_trivial]
    ring_nf
  simp_rw [hcos] at hre
  rw [integral_const_mul] at hre
  have hsub := Measure.integral_comp_mul_left
    (fun t : ℝ => Real.cos (t * a) * cosT f L t) (2 * Real.pi)
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [abs_of_pos (inv_pos.mpr hpi), smul_eq_mul] at hsub
  have hsub' : (∫ ξ : ℝ, Real.cos (2 * Real.pi * ξ * a) * cosT f L (2 * Real.pi * ξ)) =
      (2 * Real.pi)⁻¹ * ∫ t : ℝ, Real.cos (t * a) * cosT f L t := hsub
  rw [hsub'] at hre
  field_simp at hre
  linarith

end AEGIS.CvSPrimePairV1

#print axioms AEGIS.CvSPrimePairV1.evenExt_continuous
#print axioms AEGIS.CvSPrimePairV1.evenExt_eq_indicator
#print axioms AEGIS.CvSPrimePairV1.evenExt_integrable
#print axioms AEGIS.CvSPrimePairV1.fourier_evenExt
#print axioms AEGIS.CvSPrimePairV1.cosT_bound
#print axioms AEGIS.CvSPrimePairV1.fourier_evenExt_integrable
#print axioms AEGIS.CvSPrimePairV1.cos_pairing
