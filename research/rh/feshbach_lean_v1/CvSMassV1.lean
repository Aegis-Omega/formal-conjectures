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
import CvSPrimeBlockV1
import Mathlib.Analysis.Fourier.Convolution

/-!
# Spectral mass of a trigonometric polynomial (CvS step 5.5a)

For an integrable `G`, `|𝓕G(ξ)|² = 𝓕A(ξ)` with the autocorrelation `A(y) = ∫ G(x + y) conj G(x) dx`
(Mathlib's convolution theorem applied to `G ⋆ G̃`). For `G = ∑ v_n e_n` on `[0, L]` this gives

`|𝓕G(t/2π)|² + |𝓕G(−t/2π)|² = 2 ∑_{n,m} v_n conj(v_m) ∫₀ᴸ B_nm(y) cos(ty) dy`,

with the prime-block profiles `B_nm` of `CvSPrimeBlockV1.trigPoly_prime_block`. So the critical-line
form of `G` against any even symbol is the Hermitian form of the matrix `∫ S(t) ∫₀ᴸ B_nm cos(ty) dy dt`.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate FourierTransform Convolution

noncomputable section

namespace AEGIS.CvSMassV1

open AEGIS.CvSPrimeBlockV1

/-- `G̃(x) = conj G(−x)`. -/
def conjRefl (G : ℝ → ℂ) (x : ℝ) : ℂ := conj (G (-x))

/-- The autocorrelation `A(y) = ∫ G(x + y) conj G(x) dx`. -/
def autocorr (G : ℝ → ℂ) (y : ℝ) : ℂ := ∫ x, G (x + y) * conj (G x)

/-- The prime-block profile `B_nm(y)` (real). -/
def blockFn (L : ℝ) (n m : ℤ) (y : ℝ) : ℝ :=
  if n = m then 2 * (L - y) * Real.cos (2 * Real.pi * n * y / L)
  else L * (Real.sin (2 * Real.pi * m * y / L) - Real.sin (2 * Real.pi * n * y / L)) /
    (Real.pi * (n - m))

theorem conjRefl_integrable {G : ℝ → ℂ} (hG : Integrable G) : Integrable (conjRefl G) := by
  have h := (Complex.conjCLE.toContinuousLinearMap).integrable_comp hG.comp_neg
  change Integrable (fun x => conj (G (-x)))
  simpa using h

theorem fourier_conjRefl (G : ℝ → ℂ) (ξ : ℝ) : 𝓕 (conjRefl G) ξ = conj (𝓕 G ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj]
  rw [← integral_neg_eq_self]
  congr 1
  funext v
  simp only [conjRefl, neg_neg, smul_eq_mul, map_mul, ← Complex.exp_conj]
  congr 2
  simp only [Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem conv_conjRefl (G : ℝ → ℂ) (y : ℝ) :
    (G ⋆[ContinuousLinearMap.mul ℂ ℂ] conjRefl G) y = autocorr G y := by
  rw [convolution_def, autocorr, ← integral_add_right_eq_self
    (fun t => (ContinuousLinearMap.mul ℂ ℂ) (G t) (conjRefl G (y - t))) y]
  congr 1
  funext x
  simp only [ContinuousLinearMap.mul_apply', conjRefl, neg_sub, add_sub_cancel_right]

/-- **`|𝓕G|² = 𝓕A`.** -/
theorem normSq_fourier {G : ℝ → ℂ} (hG : Integrable G) (ξ : ℝ) :
    ((Complex.normSq (𝓕 G ξ) : ℝ) : ℂ) = 𝓕 (autocorr G) ξ := by
  have h := Real.fourier_mul_convolution_eq hG (conjRefl_integrable hG) ξ
  rw [show (G ⋆[ContinuousLinearMap.mul ℂ ℂ] conjRefl G) = autocorr G from
    funext (conv_conjRefl G), fourier_conjRefl, Complex.mul_conj] at h
  exact h.symm

theorem autocorr_integrable {G : ℝ → ℂ} (hG : Integrable G) : Integrable (autocorr G) := by
  have h := hG.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (conjRefl_integrable hG)
  rwa [show (G ⋆[ContinuousLinearMap.mul ℂ ℂ] conjRefl G) = autocorr G from
    funext (conv_conjRefl G)] at h

/-- **Two-sided mass as a cosine transform of the autocorrelation.** -/
theorem mass_eq_cos {G : ℝ → ℂ} (hG : Integrable G) (t : ℝ) :
    ((Complex.normSq (𝓕 G (t / (2 * Real.pi))) + Complex.normSq (𝓕 G (-t / (2 * Real.pi))) : ℝ) : ℂ) =
      ∫ y, 2 * (Real.cos (t * y) : ℂ) * autocorr G y := by
  have hA := autocorr_integrable hG
  push_cast
  rw [normSq_fourier hG, normSq_fourier hG, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_add]
  · congr 1
    funext y
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    rw [smul_eq_mul, smul_eq_mul, ← add_mul]
    congr 1
    have e1 : (↑(-2 * Real.pi * y * (t / (2 * Real.pi))) : ℂ) * I = (↑(-(t * y)) : ℂ) * I := by
      congr 2; field_simp
    have e2 : (↑(-2 * Real.pi * y * (-t / (2 * Real.pi))) : ℂ) * I = (↑(t * y) : ℂ) * I := by
      congr 2; field_simp
    rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg,
      Complex.sin_neg]
    push_cast
    ring
  · exact (hA.bdd_mul (c := 1) (by fun_prop : Continuous fun y : ℝ =>
      Complex.exp (↑(-2 * Real.pi * y * (t / (2 * Real.pi))) * I)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Complex.norm_exp_ofReal_mul_I]))
  · exact (hA.bdd_mul (c := 1) (by fun_prop : Continuous fun y : ℝ =>
      Complex.exp (↑(-2 * Real.pi * y * (-t / (2 * Real.pi))) * I)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Complex.norm_exp_ofReal_mul_I]))

theorem blockFn_continuous (L : ℝ) (n m : ℤ) : Continuous (blockFn L n m) := by
  unfold blockFn
  split_ifs <;> fun_prop

theorem trigAtom_eq_zero {L x : ℝ} (n : ℤ) (hx : x ∉ Icc 0 L) : trigAtom L n x = 0 := by
  simp [trigAtom, indicator_of_notMem hx]

theorem trigPoly_eq_zero {L x : ℝ} (S : Finset ℤ) (v : ℤ → ℂ) (hx : x ∉ Icc 0 L) :
    trigPoly L S v x = 0 := by
  simp [trigPoly, trigAtom_eq_zero _ hx]

theorem trigPoly_integrable (L : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) :
    Integrable (trigPoly L S v) := by
  unfold trigPoly
  refine integrable_finsetSum _ fun n _ => (Integrable.const_mul ?_ _)
  unfold trigAtom
  refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
  exact (by fun_prop : Continuous fun x : ℝ =>
    Complex.exp (2 * Real.pi * I * n * x / L)).integrableOn_Icc

theorem autocorr_trigPoly_eq_zero {L y : ℝ} (S : Finset ℤ) (v : ℤ → ℂ) (hy : L < |y|) :
    autocorr (trigPoly L S v) y = 0 := by
  unfold autocorr
  rw [← integral_zero ℝ ℂ]
  congr 1
  funext x
  by_cases hx : x ∈ Icc 0 L
  · have : x + y ∉ Icc 0 L := by
      intro h
      rcases le_or_gt 0 y with h0 | h0
      · rw [abs_of_nonneg h0] at hy; linarith [hx.1, h.2]
      · rw [abs_of_neg h0] at hy; linarith [hx.2, h.1]
    rw [trigPoly_eq_zero S v this, zero_mul]
  · rw [trigPoly_eq_zero S v hx, map_zero, mul_zero]

/-- The whole-line cosine transform of the autocorrelation folds onto `[0, L]`. -/
theorem cos_autocorr_fold {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (v : ℤ → ℂ) (t : ℝ) :
    ∫ y, 2 * (Real.cos (t * y) : ℂ) * autocorr (trigPoly L S v) y =
      ∫ y in (0 : ℝ)..L, 2 * (Real.cos (t * y) : ℂ) *
        (autocorr (trigPoly L S v) y + autocorr (trigPoly L S v) (-y)) := by
  set A := autocorr (trigPoly L S v)
  set f : ℝ → ℂ := fun y => 2 * (Real.cos (t * y) : ℂ) * A y
  have hA := autocorr_integrable (trigPoly_integrable L S v)
  have hf : Integrable f := hA.bdd_mul (c := 2)
    (by fun_prop : Continuous fun y : ℝ => 2 * (Real.cos (t * y) : ℂ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simpa using Real.abs_cos_le_one (t * y))
  have hsplit := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hf
  have hI : (∫ y in Iic (0 : ℝ), f y) = ∫ y in Ioi (0 : ℝ), f (-y) := by
    have := integral_comp_neg_Iic 0 (fun y => f (-y))
    simp at this ⊢
  rw [compl_Ioi, hI, ← integral_add (hf.integrableOn) (hf.comp_neg.integrableOn)] at hsplit
  rw [← hsplit]
  -- restrict `Ioi 0` to `Ioc 0 L`
  have hzero : ∀ y ∈ Ioi L, f y + f (-y) = 0 := by
    intro y hy
    have h1 : L < |y| := by rw [abs_of_pos (hL.trans hy)]; exact hy
    have h2 : L < |-y| := by rwa [abs_neg]
    simp only [f, A, autocorr_trigPoly_eq_zero S v h1, autocorr_trigPoly_eq_zero S v h2,
      mul_zero, add_zero]
  have hIoi : Ioi (0 : ℝ) = Ioc 0 L ∪ Ioi L := (Ioc_union_Ioi_eq_Ioi hL.le).symm
  have hg : Integrable fun a => f a + f (-a) := hf.add hf.comp_neg
  rw [hIoi, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    hg.integrableOn hg.integrableOn,
    setIntegral_congr_fun measurableSet_Ioi hzero, integral_zero, add_zero,
    intervalIntegral.integral_of_le hL.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
  simp only [f, Real.cos_neg, mul_neg]
  ring

/-- **Spectral mass of a trigonometric polynomial.** -/
theorem mass_trigPoly {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (v : ℤ → ℂ) (t : ℝ) :
    ((Complex.normSq (𝓕 (trigPoly L S v) (t / (2 * Real.pi))) +
        Complex.normSq (𝓕 (trigPoly L S v) (-t / (2 * Real.pi))) : ℝ) : ℂ) =
      ∑ n ∈ S, ∑ m ∈ S, v n * conj (v m) *
        ((2 * ∫ y in (0 : ℝ)..L, blockFn L n m y * Real.cos (t * y) : ℝ) : ℂ) := by
  rw [mass_eq_cos (trigPoly_integrable L S v), cos_autocorr_fold hL]
  have hblock : ∀ y ∈ uIcc (0 : ℝ) L, 2 * (Real.cos (t * y) : ℂ) *
      (autocorr (trigPoly L S v) y + autocorr (trigPoly L S v) (-y)) =
      ∑ n ∈ S, ∑ m ∈ S, v n * conj (v m) * ((2 * (blockFn L n m y * Real.cos (t * y)) : ℝ) : ℂ) := by
    intro y hy
    rw [uIcc_of_le hL.le] at hy
    have hneg : autocorr (trigPoly L S v) (-y) =
        ∫ x, trigPoly L S v (x - y) * conj (trigPoly L S v x) := by
      simp only [autocorr, ← sub_eq_add_neg]
    rw [hneg, autocorr, trigPoly_prime_block hL hy.1 hy.2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [blockFn]
    push_cast
    ring
  have hc : ∀ n m : ℤ, Continuous fun y : ℝ =>
      (((2 * (blockFn L n m y * Real.cos (t * y))) : ℝ) : ℂ) := fun n m => by
    have := blockFn_continuous L n m
    fun_prop
  rw [intervalIntegral.integral_congr hblock, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
        intervalIntegral.integral_const_mul]
    · intro m _
      exact ((hc n m).intervalIntegrable _ _).const_mul _
  · intro n _
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_finsetSum _ fun m _ => continuous_const.mul (hc n m)

end AEGIS.CvSMassV1

#print axioms AEGIS.CvSMassV1.conjRefl_integrable
#print axioms AEGIS.CvSMassV1.fourier_conjRefl
#print axioms AEGIS.CvSMassV1.conv_conjRefl
#print axioms AEGIS.CvSMassV1.normSq_fourier
#print axioms AEGIS.CvSMassV1.autocorr_integrable
#print axioms AEGIS.CvSMassV1.mass_eq_cos
#print axioms AEGIS.CvSMassV1.trigPoly_integrable
#print axioms AEGIS.CvSMassV1.autocorr_trigPoly_eq_zero
#print axioms AEGIS.CvSMassV1.cos_autocorr_fold
#print axioms AEGIS.CvSMassV1.mass_trigPoly
