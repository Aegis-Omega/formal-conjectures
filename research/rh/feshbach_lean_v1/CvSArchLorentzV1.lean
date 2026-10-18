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
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Lorentzian Fourier pair (CvS step 5.2a)

The archimedean entries of `feshbach_blocks_arb.py` come from the digamma series of
`h₊(r) = Re ψ(1/4 + ir/2) − log π`, whose terms are Lorentzians `2c/(c² + r²)`, `c = 2k + 1/2`.
This file proves the Fourier pair behind them,
`∫ cos(r y) · 2c/(c² + r²) dr = 2π e^{−c|y|}` for `c > 0`.
-/

open MeasureTheory Complex Set Real

noncomputable section

namespace AEGIS.CvSArchLorentzV1

/-- `e^{−c|t|}` as a complex function. -/
def expAbs (c : ℝ) (t : ℝ) : ℂ := ((Real.exp (-c * |t|) : ℝ) : ℂ)

theorem expAbs_continuous (c : ℝ) : Continuous (expAbs c) := by
  unfold expAbs; fun_prop

/-- The Fourier integrand of `expAbs c` on each half-line is a single exponential. -/
theorem expAbs_integrand_Ioi (c ξ : ℝ) {t : ℝ} (ht : 0 < t) :
    Complex.exp (↑(-2 * π * t * ξ) * I) • expAbs c t =
      Complex.exp ((-(c : ℂ) - 2 * π * ξ * I) * t) := by
  rw [expAbs, abs_of_pos ht, smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem expAbs_integrand_Iic (c ξ : ℝ) {t : ℝ} (ht : t ≤ 0) :
    Complex.exp (↑(-2 * π * t * ξ) * I) • expAbs c t =
      Complex.exp (((c : ℂ) - 2 * π * ξ * I) * t) := by
  rw [expAbs, abs_of_nonpos ht, smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem expAbs_fourier_integrand_integrable {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (↑(-2 * π * t * ξ) * I) • expAbs c t) := by
  have ha1 : ((-(c : ℂ) - 2 * π * ξ * I)).re < 0 := by simp [hc]
  have ha2 : 0 < (((c : ℂ) - 2 * π * ξ * I)).re := by simp [hc]
  have h1 : IntegrableOn (fun t : ℝ => Complex.exp (↑(-2 * π * t * ξ) * I) • expAbs c t)
      (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi ha1 0).congr_fun
      (fun t ht => (expAbs_integrand_Ioi c ξ ht).symm) measurableSet_Ioi
  have h2 : IntegrableOn (fun t : ℝ => Complex.exp (↑(-2 * π * t * ξ) * I) • expAbs c t)
      (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic ha2 0).congr_fun
      (fun t ht => (expAbs_integrand_Iic c ξ ht).symm) measurableSet_Iic
  have := h2.union h1
  rwa [Iic_union_Ioi, integrableOn_univ] at this

theorem expAbs_integrable {c : ℝ} (hc : 0 < c) : Integrable (expAbs c) := by
  simpa using expAbs_fourier_integrand_integrable hc 0

/-- **Fourier transform of `e^{−c|t|}`.** -/
theorem expAbs_fourier {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    FourierTransform.fourier (expAbs c) ξ = ((2 * c / (c ^ 2 + (2 * π * ξ) ^ 2) : ℝ) : ℂ) := by
  have ha1 : ((-(c : ℂ) - 2 * π * ξ * I)).re < 0 := by simp [hc]
  have ha2 : 0 < (((c : ℂ) - 2 * π * ξ * I)).re := by simp [hc]
  rw [Real.fourier_real_eq_integral_exp_smul,
    ← integral_add_compl measurableSet_Ioi (expAbs_fourier_integrand_integrable hc ξ),
    compl_Ioi, setIntegral_congr_fun measurableSet_Ioi (fun t ht => expAbs_integrand_Ioi c ξ ht),
    setIntegral_congr_fun measurableSet_Iic (fun t ht => expAbs_integrand_Iic c ξ ht),
    integral_exp_mul_complex_Ioi ha1, integral_exp_mul_complex_Iic ha2]
  have hne1 : (-(c : ℂ) - 2 * π * ξ * I) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hne2 : ((c : ℂ) - 2 * π * ξ * I) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hden : ((c : ℂ) ^ 2 + (2 * π * ξ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < c ^ 2 + (2 * π * ξ) ^ 2 := by positivity
    exact_mod_cast this.ne'
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  have hden' : (c : ℂ) ^ 2 + (π : ℂ) ^ 2 * (ξ : ℂ) ^ 2 * 4 ≠ 0 := by
    rw [show (c : ℂ) ^ 2 + (π : ℂ) ^ 2 * (ξ : ℂ) ^ 2 * 4 = (c : ℂ) ^ 2 + (2 * π * ξ) ^ 2 by ring]
    exact hden
  field_simp
  ring

/-- The Lorentzian `2c/(c² + (a x)²)` is integrable for `c > 0`, `a ≠ 0`. -/
theorem lorentz_integrable {c a : ℝ} (hc : 0 < c) (ha : a ≠ 0) :
    Integrable (fun x : ℝ => 2 * c / (c ^ 2 + (a * x) ^ 2)) := by
  have h := (integrable_inv_one_add_sq.comp_mul_left' (div_ne_zero ha hc.ne')).const_mul (2 / c)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  have hc2 : c ^ 2 + (a * x) ^ 2 ≠ 0 := by positivity
  simp only
  field_simp

theorem expAbs_fourier_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (FourierTransform.fourier (expAbs c)) := by
  have h := (lorentz_integrable hc (by positivity : (2 * π) ≠ 0)).ofReal (𝕜 := ℂ)
  exact h.congr (Filter.Eventually.of_forall fun ξ => (expAbs_fourier hc ξ).symm)

/-- **Lorentzian Fourier pair**, exponential form. -/
theorem lorentz_exp_integral {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ∫ r : ℝ, Complex.exp (↑(r * y) * I) * ((2 * c / (c ^ 2 + r ^ 2) : ℝ) : ℂ) =
      2 * π * expAbs c y := by
  have hinv := (expAbs_continuous c).fourierInv_fourier_eq (expAbs_integrable hc)
    (expAbs_fourier_integrable hc)
  have hy := congrFun hinv y
  rw [Real.fourierInv_eq'] at hy
  simp_rw [expAbs_fourier hc] at hy
  set g : ℝ → ℂ := fun r => Complex.exp (↑(r * y) * I) * ((2 * c / (c ^ 2 + r ^ 2) : ℝ) : ℂ)
  have hcomp : (fun ξ : ℝ => Complex.exp (↑(2 * π * (inner ℝ ξ y)) * I) •
      ((2 * c / (c ^ 2 + (2 * π * ξ) ^ 2) : ℝ) : ℂ)) = fun ξ => g (2 * π * ξ) := by
    funext ξ
    simp only [g, smul_eq_mul, RCLike.inner_apply, conj_trivial]
    congr 3
    ring_nf
  rw [hcomp, Measure.integral_comp_mul_left g (2 * π)] at hy
  have hpi : (0 : ℝ) < 2 * π := by positivity
  rw [abs_of_pos (inv_pos.mpr hpi), Complex.real_smul] at hy
  have hpi' : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
  calc (∫ r : ℝ, g r) = ((2 * π : ℝ) : ℂ) * (((2 * π)⁻¹ : ℝ) * ∫ r : ℝ, g r) := by
        push_cast; field_simp
    _ = 2 * π * expAbs c y := by rw [hy]; push_cast; ring

/-- **Lorentzian Fourier pair**, cosine form: `∫ cos(r y) · 2c/(c² + r²) dr = 2π e^{−c|y|}`. -/
theorem lorentz_cos_integral {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ∫ r : ℝ, Real.cos (r * y) * (2 * c / (c ^ 2 + r ^ 2)) = 2 * π * Real.exp (-c * |y|) := by
  have hg : Integrable (fun r : ℝ =>
      Complex.exp (↑(r * y) * I) * ((2 * c / (c ^ 2 + r ^ 2) : ℝ) : ℂ)) := by
    have h := ((lorentz_integrable hc one_ne_zero).ofReal (𝕜 := ℂ))
    have h' : Integrable (fun r : ℝ => ((2 * c / (c ^ 2 + r ^ 2) : ℝ) : ℂ)) :=
      h.congr (Filter.Eventually.of_forall fun r => by simp)
    refine h'.bdd_mul (c := 1)
      (by fun_prop : Continuous fun r : ℝ => Complex.exp (↑(r * y) * I)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have h := congrArg Complex.re (lorentz_exp_integral hc y)
  have hre := integral_re hg
  simp only [RCLike.re_to_complex] at hre
  rw [← hre] at h
  convert h using 1
  · congr 1
    funext r
    rw [Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
  · simp only [expAbs]
    rw [show (2 * (π : ℂ) * ((Real.exp (-c * |y|) : ℝ) : ℂ)) =
      (((2 * π * Real.exp (-c * |y|)) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

/-- Groskin's archimedean source kernel at an integer node,
`S(r, n, L) = ∫₀ᴸ sin(2πn(1 − y/L)) cos(r y) dy`. -/
def sourceS (L r : ℝ) (n : ℤ) : ℝ :=
  ∫ y in (0 : ℝ)..L, Real.sin (2 * π * n * (1 - y / L)) * Real.cos (r * y)

theorem sin_int_mul_two_pi' (n : ℤ) : Real.sin (n * (2 * π)) = 0 := by
  rw [show (n : ℝ) * (2 * π) = ((2 * n : ℤ) : ℝ) * π by push_cast; ring]
  exact Real.sin_int_mul_pi _

/-- At integer `n`, `sin(2πn(1 − y/L)) = −sin(ωy)` with `ω = 2πn/L`. -/
theorem sin_node (L y : ℝ) (n : ℤ) :
    Real.sin (2 * π * n * (1 - y / L)) = -Real.sin (2 * π * n / L * y) := by
  have h : 2 * π * n * (1 - y / L) = (n * (2 * π)) - 2 * π * n / L * y := by ring
  rw [h, Real.sin_sub, sin_int_mul_two_pi', Real.cos_int_mul_two_pi]
  ring

theorem sin_exp_hasDerivAt {c ω : ℝ} (hden : c ^ 2 + ω ^ 2 ≠ 0) (y : ℝ) :
    HasDerivAt (fun y => Real.exp (-c * y) * (c * Real.sin (ω * y) + ω * Real.cos (ω * y)) /
      (c ^ 2 + ω ^ 2)) (-Real.sin (ω * y) * Real.exp (-c * y)) y := by
  have h1 : HasDerivAt (fun y => Real.exp (-c * y)) (Real.exp (-c * y) * (-c)) y := by
    simpa using ((hasDerivAt_id y).const_mul (-c)).exp
  have h2 : HasDerivAt (fun y => c * Real.sin (ω * y) + ω * Real.cos (ω * y))
      (c * (Real.cos (ω * y) * ω) + ω * (-Real.sin (ω * y) * ω)) y := by
    have hs : HasDerivAt (fun y => Real.sin (ω * y)) (Real.cos (ω * y) * ω) y := by
      simpa using ((hasDerivAt_id y).const_mul ω).sin
    have hc : HasDerivAt (fun y => Real.cos (ω * y)) (-Real.sin (ω * y) * ω) y := by
      simpa using ((hasDerivAt_id y).const_mul ω).cos
    exact (hs.const_mul c).add (hc.const_mul ω)
  refine ((h1.mul h2).div_const (c ^ 2 + ω ^ 2)).congr_deriv ?_
  rw [div_eq_iff hden]
  ring

/-- `∫₀ᴸ sin(2πn(1 − y/L)) e^{−cy} dy = −ω(1 − e^{−cL})/(c² + ω²)`, `ω = 2πn/L`. -/
theorem sin_exp_integral {L : ℝ} (hL : 0 < L) (n : ℤ) {c : ℝ} (hc : 0 < c) :
    ∫ y in (0 : ℝ)..L, Real.sin (2 * π * n * (1 - y / L)) * Real.exp (-c * y) =
      -(2 * π * n / L) * (1 - Real.exp (-c * L)) / (c ^ 2 + (2 * π * n / L) ^ 2) := by
  set ω := 2 * π * n / L with hω
  have hden : c ^ 2 + ω ^ 2 ≠ 0 := by positivity
  simp_rw [sin_node L _ n, ← hω]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => sin_exp_hasDerivAt hden y)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have hωL : ω * L = n * (2 * π) := by rw [hω]; field_simp
  rw [hωL, sin_int_mul_two_pi', Real.cos_int_mul_two_pi]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, Real.exp_zero]
  field_simp
  ring

/-- **One digamma term of the archimedean source.** For `c > 0`,
`∫ 2c/(c² + r²) · S(r, n, L) dr = 2π ∫₀ᴸ sin(2πn(1 − y/L)) e^{−cy} dy`. -/
theorem lorentz_source {c L : ℝ} (hc : 0 < c) (hL : 0 < L) (n : ℤ) :
    ∫ r : ℝ, 2 * c / (c ^ 2 + r ^ 2) * sourceS L r n =
      2 * π * ∫ y in (0 : ℝ)..L, Real.sin (2 * π * n * (1 - y / L)) * Real.exp (-c * y) := by
  set F : ℝ → ℝ → ℝ := fun y r =>
    Real.sin (2 * π * n * (1 - y / L)) * (Real.cos (r * y) * (2 * c / (c ^ 2 + r ^ 2)))
  have hcont : Continuous (Function.uncurry F) := by
    have hd : ∀ r : ℝ, c ^ 2 + r ^ 2 ≠ 0 := fun r => by positivity
    simp only [F]
    exact (by fun_prop : Continuous fun p : ℝ × ℝ => Real.sin (2 * π * n * (1 - p.1 / L))).mul
      ((by fun_prop : Continuous fun p : ℝ × ℝ => Real.cos (p.2 * p.1)).mul
        (continuous_const.div (by fun_prop) fun p => hd p.2))
  have hint : Integrable (Function.uncurry F) ((volume.restrict (uIoc 0 L)).prod volume) := by
    rw [uIoc_of_le hL.le]
    have hg : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * (2 * c / (c ^ 2 + (1 * p.2) ^ 2)))
        ((volume.restrict (Ioc 0 L)).prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod (lorentz_integrable hc one_ne_zero)
    refine hg.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    simp only [F, Function.uncurry, one_mul, norm_mul, Real.norm_eq_abs]
    have hw : 0 ≤ 2 * c / (c ^ 2 + p.2 ^ 2) := by positivity
    rw [abs_of_nonneg hw]
    calc |Real.sin (2 * π * n * (1 - p.1 / L))| * (|Real.cos (p.2 * p.1)| *
          (2 * c / (c ^ 2 + p.2 ^ 2)))
        ≤ 1 * (1 * (2 * c / (c ^ 2 + p.2 ^ 2))) := by
          gcongr
          · exact Real.abs_sin_le_one _
          · exact Real.abs_cos_le_one _
      _ = 2 * c / (c ^ 2 + p.2 ^ 2) := by ring
  have hswap := intervalIntegral_integral_swap hint
  have hlhs : (∫ r : ℝ, 2 * c / (c ^ 2 + r ^ 2) * sourceS L r n) =
      ∫ r : ℝ, ∫ y in (0 : ℝ)..L, F y r := by
    congr 1; funext r
    simp only [sourceS, F, ← intervalIntegral.integral_const_mul]
    congr 1; funext y; ring
  rw [hlhs, ← hswap, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le hL.le] at hy
  simp only [F]
  rw [integral_const_mul, lorentz_cos_integral hc, abs_of_nonneg hy.1]
  ring

/-- **Value of one digamma term.** `∫ 2c/(c² + r²) · S(r, n, L) dr = −2πω(1 − e^{−cL})/(c² + ω²)`. -/
theorem lorentz_source_value {c L : ℝ} (hc : 0 < c) (hL : 0 < L) (n : ℤ) :
    ∫ r : ℝ, 2 * c / (c ^ 2 + r ^ 2) * sourceS L r n =
      -(2 * π) * (2 * π * n / L) * (1 - Real.exp (-c * L)) /
        (c ^ 2 + (2 * π * n / L) ^ 2) := by
  rw [lorentz_source hc hL n, sin_exp_integral hL n hc]
  ring

end AEGIS.CvSArchLorentzV1

#print axioms AEGIS.CvSArchLorentzV1.expAbs_integrable
#print axioms AEGIS.CvSArchLorentzV1.expAbs_fourier
#print axioms AEGIS.CvSArchLorentzV1.lorentz_integrable
#print axioms AEGIS.CvSArchLorentzV1.expAbs_fourier_integrable
#print axioms AEGIS.CvSArchLorentzV1.lorentz_exp_integral
#print axioms AEGIS.CvSArchLorentzV1.lorentz_cos_integral
#print axioms AEGIS.CvSArchLorentzV1.sin_int_mul_two_pi'
#print axioms AEGIS.CvSArchLorentzV1.sin_node
#print axioms AEGIS.CvSArchLorentzV1.sin_exp_hasDerivAt
#print axioms AEGIS.CvSArchLorentzV1.sin_exp_integral
#print axioms AEGIS.CvSArchLorentzV1.lorentz_source
#print axioms AEGIS.CvSArchLorentzV1.lorentz_source_value
