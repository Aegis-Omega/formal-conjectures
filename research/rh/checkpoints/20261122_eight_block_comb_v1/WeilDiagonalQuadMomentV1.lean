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

import WeilDiagonalMomentGainV1
import WeilDiagonalQuadGainV1

/-!
AEGIS Ω — the width-1/32 diagonal with the quadratic gain and both moments (Claude Lab, 2026-11-22).

`WeilDiagonalQuadGainV1.quad_gain` gives, for `h = logLift g` on a window of width `w = 1/32`,

  `(log 2 + 4/3) E − 3 ‖M‖²/(2w) + 4 Q/w³ ≤ ∫_{(0,w]} (E − Re C(s))/s ds`.

For a packet with `WeilMomentConditionsV1`, both moments `∫ e^{±(t−a)/2} logLift g` vanish, so

* `M = ∫ (1 − cosh((t−a)/2)) logLift g`, hence `‖M‖ ≤ N/16384` with `N = ∫ ‖logLift g‖`;
* `M₁ = ∫ (t−a) logLift g = ∫ ((t−a) − 2 sinh((t−a)/2)) logLift g`, hence `‖M₁‖ ≤ N/8192`;
* `Q ≥ −N²/16777216` (`qMom_lower`), and `N² ≤ E/32` (Cauchy–Schwarz).

Both correction terms are then at most `E/4096`, and

  `diagonal_quad_moment_v1 : E · (tail − κ − small + e^{−1/32} (log 2 + 4/3 − 1/2048)) ≤ −Re B(g, g)`,

whose constant exceeds `59/20` (`width_diagonal_59_over_20`; numerically about `2.99`).

Diagonal estimate only, for the width-1/32 moment-zero packet class. Not RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators ENNReal
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilDiagonalQuadMomentV1

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilWidthArchBudgetV26
open AEGIS.WeilWidthArchIntegralV27
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilWidthDiagonalArchFrontierV24
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDiagonalLogGainV1
open AEGIS.WeilDiagonalLogGainS1V1 (integrable_of_zero_off)

/-- A bounded real weight on the support. -/
theorem norm_integral_weight_le (h : ℝ → ℂ) (lo hi : ℝ) (hz : ∀ t, t ∉ Icc lo hi → h t = 0)
    (hI : Integrable h) (ψ : ℝ → ℝ) (K : ℝ) (hK : ∀ t ∈ Icc lo hi, |ψ t| ≤ K) :
    ‖∫ t, (ψ t : ℂ) * h t‖ ≤ K * ∫ t, ‖h t‖ := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hI.norm.const_mul K) (Filter.Eventually.of_forall (fun t => ?_))
  by_cases ht : t ∈ Icc lo hi
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hK t ht) (norm_nonneg _)
  · simp [hz t ht]

/-- Both moments vanish, so any combination of `e^{±(t−c)/2}` may be subtracted from a weight. -/
theorem integral_kill (h : ℝ → ℂ) (hc : Continuous h) (lo hi c : ℝ) (hz : ∀ t, t ∉ Icc lo hi → h t = 0)
    (hp : (∫ t, (Real.exp ((t - c) / 2) : ℂ) * h t) = 0)
    (hn : (∫ t, (Real.exp (-((t - c) / 2)) : ℂ) * h t) = 0)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (α β : ℝ) :
    (∫ t, (ψ t : ℂ) * h t) =
      ∫ t, ((ψ t - α * Real.exp ((t - c) / 2) - β * Real.exp (-((t - c) / 2)) : ℝ) : ℂ) * h t := by
  have i0 : Integrable (fun t => (ψ t : ℂ) * h t) :=
    integrable_of_zero_off _ ((Complex.continuous_ofReal.comp hψ).mul hc) lo hi
      (fun t ht => by simp [hz t ht])
  have c1 : Continuous (fun t : ℝ => (Real.exp ((t - c) / 2) : ℂ)) := by fun_prop
  have c2 : Continuous (fun t : ℝ => (Real.exp (-((t - c) / 2)) : ℂ)) := by fun_prop
  have i1 : Integrable (fun t => (Real.exp ((t - c) / 2) : ℂ) * h t) :=
    integrable_of_zero_off _ (c1.mul hc) lo hi (fun t ht => by simp [hz t ht])
  have i2 : Integrable (fun t => (Real.exp (-((t - c) / 2)) : ℂ) * h t) :=
    integrable_of_zero_off _ (c2.mul hc) lo hi (fun t ht => by simp [hz t ht])
  have e : (fun t => ((ψ t - α * Real.exp ((t - c) / 2) - β * Real.exp (-((t - c) / 2)) : ℝ) : ℂ) * h t) =
      fun t => ((ψ t : ℂ) * h t - (α : ℂ) * ((Real.exp ((t - c) / 2) : ℂ) * h t)) -
        (β : ℂ) * ((Real.exp (-((t - c) / 2)) : ℂ) * h t) := by
    funext t
    push_cast
    ring
  have Ia : Integrable (fun t => (ψ t : ℂ) * h t - (α : ℂ) * ((Real.exp ((t - c) / 2) : ℂ) * h t)) :=
    i0.sub (i1.const_mul _)
  have e1 : (∫ t, ((ψ t : ℂ) * h t - (α : ℂ) * ((Real.exp ((t - c) / 2) : ℂ) * h t) -
      (β : ℂ) * ((Real.exp (-((t - c) / 2)) : ℂ) * h t))) =
      (∫ t, ((ψ t : ℂ) * h t - (α : ℂ) * ((Real.exp ((t - c) / 2) : ℂ) * h t))) -
        ∫ t, (β : ℂ) * ((Real.exp (-((t - c) / 2)) : ℂ) * h t) :=
    integral_sub Ia (i2.const_mul _)
  have e2 : (∫ t, ((ψ t : ℂ) * h t - (α : ℂ) * ((Real.exp ((t - c) / 2) : ℂ) * h t))) =
      (∫ t, (ψ t : ℂ) * h t) - ∫ t, (α : ℂ) * ((Real.exp ((t - c) / 2) : ℂ) * h t) :=
    integral_sub i0 (i1.const_mul _)
  have e3 : (∫ t, (α : ℂ) * ((Real.exp ((t - c) / 2) : ℂ) * h t)) =
      (α : ℂ) * ∫ t, (Real.exp ((t - c) / 2) : ℂ) * h t := integral_const_mul _ _
  have e4 : (∫ t, (β : ℂ) * ((Real.exp (-((t - c) / 2)) : ℂ) * h t)) =
      (β : ℂ) * ∫ t, (Real.exp (-((t - c) / 2)) : ℂ) * h t := integral_const_mul _ _
  rw [e, e1, e2, e3, e4, hp, hn]
  ring

theorem moment_plus_centre (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (c : ℝ) :
    (∫ t, (Real.exp ((t - c) / 2) : ℂ) * logLift g.1 t) = 0 := by
  have h0 : (∫ t, (Real.exp (t / 2) : ℂ) * logLift g.1 t) = 0 :=
    (logMomentPlus_eq_repository g).trans hm.2
  have e : (fun t => (Real.exp ((t - c) / 2) : ℂ) * logLift g.1 t) =
      fun t => (Real.exp (-c / 2) : ℂ) * ((Real.exp (t / 2) : ℂ) * logLift g.1 t) := by
    funext t
    have he : Real.exp ((t - c) / 2) = Real.exp (-c / 2) * Real.exp (t / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    push_cast
    ring
  rw [e, integral_const_mul, h0, mul_zero]

theorem moment_minus_centre (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (c : ℝ) :
    (∫ t, (Real.exp (-((t - c) / 2)) : ℂ) * logLift g.1 t) = 0 := by
  have h0 : (∫ t, (Real.exp (-t / 2) : ℂ) * logLift g.1 t) = 0 :=
    (logMomentMinus_eq_repository g).trans hm.1
  have e : (fun t => (Real.exp (-((t - c) / 2)) : ℂ) * logLift g.1 t) =
      fun t => (Real.exp (c / 2) : ℂ) * ((Real.exp (-t / 2) : ℂ) * logLift g.1 t) := by
    funext t
    have he : Real.exp (-((t - c) / 2)) = Real.exp (c / 2) * Real.exp (-t / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    push_cast
    ring
  rw [e, integral_const_mul, h0, mul_zero]

theorem exp_pair (y : ℝ) (hy : |y| ≤ 1 / 64) :
    |Real.exp (y / 2) - 1 - y / 2| ≤ 1 / 16384 ∧ |Real.exp (-(y / 2)) - 1 + y / 2| ≤ 1 / 16384 := by
  have hy2 : |y / 2| ≤ 1 := by
    rw [abs_div, abs_two]
    linarith
  have hy3 : |-(y / 2)| ≤ 1 := by rwa [abs_neg]
  have h1 := Real.abs_exp_sub_one_sub_id_le hy2
  have h2 := Real.abs_exp_sub_one_sub_id_le hy3
  have hsq : (y / 2) ^ 2 ≤ 1 / 16384 := by
    have : y ^ 2 ≤ (1 / 64) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hy 2
    nlinarith
  have e2 : Real.exp (-(y / 2)) - 1 + y / 2 = Real.exp (-(y / 2)) - 1 - -(y / 2) := by ring
  have e3 : (-(y / 2)) ^ 2 = (y / 2) ^ 2 := by ring
  rw [e2]
  rw [e3] at h2
  exact ⟨h1.trans hsq, h2.trans hsq⟩

theorem cosh_weight (y : ℝ) (hy : |y| ≤ 1 / 64) :
    |1 - 1 / 2 * Real.exp (y / 2) - 1 / 2 * Real.exp (-(y / 2))| ≤ 1 / 16384 := by
  obtain ⟨h1, h2⟩ := exp_pair y hy
  obtain ⟨l1, u1⟩ := abs_le.mp h1
  obtain ⟨l2, u2⟩ := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith

theorem sinh_weight (y : ℝ) (hy : |y| ≤ 1 / 64) :
    |y - 1 * Real.exp (y / 2) - (-1) * Real.exp (-(y / 2))| ≤ 1 / 8192 := by
  obtain ⟨h1, h2⟩ := exp_pair y hy
  obtain ⟨l1, u1⟩ := abs_le.mp h1
  obtain ⟨l2, u2⟩ := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith

section packet

variable (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a) (hm : WeilMomentConditionsV1 g)
include hw hm

omit hw hm in
theorem window_abs' {t : ℝ} (ht : t ∈ Icc (a - 1 / 64) (a + 1 / 64)) : |t - a| ≤ 1 / 64 := by
  rw [abs_le]
  constructor <;> linarith [ht.1, ht.2]

theorem mean_le : ‖∫ t, logLift g.1 t‖ ≤ (1 / 16384) * ∫ t, ‖logLift g.1 t‖ := by
  have hc := logLift_continuous g
  have hz := logLift_zero_off g (a - 1 / 64) (a + 1 / 64) hw
  have hI : Integrable (logLift g.1) := integrable_of_zero_off _ hc _ _ hz
  have e1 : (∫ t, logLift g.1 t) = ∫ t, (((fun _ : ℝ => (1 : ℝ)) t : ℝ) : ℂ) * logLift g.1 t := by
    simp
  rw [e1, integral_kill (logLift g.1) hc _ _ a hz (moment_plus_centre g hm a) (moment_minus_centre g hm a)
    (fun _ => 1) continuous_const (1 / 2) (1 / 2)]
  exact norm_integral_weight_le (logLift g.1) _ _ hz hI _ _
    (fun t ht => cosh_weight (t - a) (window_abs' a ht))

theorem first_moment_le :
    ‖∫ t, ((t - a : ℝ) : ℂ) * logLift g.1 t‖ ≤ (1 / 8192) * ∫ t, ‖logLift g.1 t‖ := by
  have hc := logLift_continuous g
  have hz := logLift_zero_off g (a - 1 / 64) (a + 1 / 64) hw
  have hI : Integrable (logLift g.1) := integrable_of_zero_off _ hc _ _ hz
  rw [integral_kill (logLift g.1) hc _ _ a hz (moment_plus_centre g hm a) (moment_minus_centre g hm a)
    (fun t => t - a) (continuous_id.sub continuous_const) 1 (-1)]
  exact norm_integral_weight_le (logLift g.1) _ _ hz hI _ _
    (fun t ht => sinh_weight (t - a) (window_abs' a ht))

omit hm in
theorem l1_sq_le : (∫ t, ‖logLift g.1 t‖) ^ 2 ≤ (1 / 32) * energy g.1 := by
  have hc := logLift_continuous g
  have hz := logLift_zero_off g (a - 1 / 64) (a + 1 / 64) hw
  have hI1 : Integrable (logLift g.1) := integrable_of_zero_off _ hc _ _ hz
  have hsq2 : Integrable (fun t => ‖logLift g.1 t‖ ^ 2) :=
    integrable_of_zero_off _ (hc.norm.pow 2) (a - 1 / 64) (a + 1 / 64) (fun t ht => by simp [hz t ht])
  have hCS := AEGIS.WeilLogCorrelationL1V1.sq_integral_le_mul (fun t => ‖logLift g.1 t‖)
    (a - 1 / 64) (1 / 32) (by norm_num)
    (fun x hx => by
      rw [hz x (fun hm' => hx ⟨hm'.1, by linarith [hm'.2]⟩)]
      simp)
    hI1.norm hsq2
  rwa [logLift_energy_eq_packet_energy] at hCS

omit hm in
theorem second_weight_le (f : ℝ → ℝ) (hfle : ∀ t, |f t| ≤ ‖logLift g.1 t‖) :
    |∫ t, (t - a) ^ 2 * f t| ≤ (1 / 4096) * ∫ t, ‖logLift g.1 t‖ := by
  have hc := logLift_continuous g
  have hz := logLift_zero_off g (a - 1 / 64) (a + 1 / 64) hw
  have hI1 : Integrable (logLift g.1) := integrable_of_zero_off _ hc _ _ hz
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hI1.norm.const_mul _) (Filter.Eventually.of_forall (fun t => ?_))
  by_cases ht : t ∈ Icc (a - 1 / 64) (a + 1 / 64)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have h1 : (t - a) ^ 2 ≤ 1 / 4096 := by
      have := pow_le_pow_left₀ (abs_nonneg _) (window_abs' a ht) 2
      rw [sq_abs] at this
      linarith
    exact mul_le_mul h1 (hfle t) (abs_nonneg _) (by norm_num)
  · have h0 : f t = 0 := by
      have := hfle t
      rw [hz t ht, norm_zero] at this
      exact abs_nonpos_iff.mp this
    simp [h0]

theorem qMom_lower :
    -((∫ t, ‖logLift g.1 t‖) ^ 2 / 16777216) ≤ AEGIS.WeilDiagonalQuadGainV1.qMom (logLift g.1) a := by
  have hc := logLift_continuous g
  have hz := logLift_zero_off g (a - 1 / 64) (a + 1 / 64) hw
  have hI : Integrable (logLift g.1) := integrable_of_zero_off _ hc _ _ hz
  set N := ∫ t, ‖logLift g.1 t‖ with hN
  have hN0 : 0 ≤ N := integral_nonneg (fun t => norm_nonneg _)
  have hM := mean_le g a hw hm
  have hM1 := first_moment_le g a hw hm
  rw [← hN] at hM hM1
  have hI1 : Integrable (fun t => ((t - a : ℝ) : ℂ) * logLift g.1 t) :=
    integrable_of_zero_off _ ((Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).mul hc)
      (a - 1 / 64) (a + 1 / 64) (fun t ht => by simp [hz t ht])
  have eBr : (∫ x, (logLift g.1 x).re) = (∫ x, logLift g.1 x).re := by
    have := integral_re hI
    simpa using this
  have eBi : (∫ x, (logLift g.1 x).im) = (∫ x, logLift g.1 x).im := by
    have := integral_im hI
    simpa using this
  have eCr : (∫ x, (x - a) * (logLift g.1 x).re) = (∫ x, ((x - a : ℝ) : ℂ) * logLift g.1 x).re := by
    have := integral_re hI1
    simpa [Complex.re_ofReal_mul] using this
  have eCi : (∫ x, (x - a) * (logLift g.1 x).im) = (∫ x, ((x - a : ℝ) : ℂ) * logLift g.1 x).im := by
    have := integral_im hI1
    simpa [Complex.im_ofReal_mul] using this
  have hAr := second_weight_le g a hw (fun t => (logLift g.1 t).re)
    (fun t => Complex.abs_re_le_norm _)
  have hAi := second_weight_le g a hw (fun t => (logLift g.1 t).im)
    (fun t => Complex.abs_im_le_norm _)
  rw [← hN] at hAr hAi
  have hBr : |(∫ x, (logLift g.1 x).re)| ≤ N / 16384 := by
    rw [eBr]
    linarith [Complex.abs_re_le_norm (∫ x, logLift g.1 x)]
  have hBi : |(∫ x, (logLift g.1 x).im)| ≤ N / 16384 := by
    rw [eBi]
    linarith [Complex.abs_im_le_norm (∫ x, logLift g.1 x)]
  have hCr : |(∫ x, (x - a) * (logLift g.1 x).re)| ≤ N / 8192 := by
    rw [eCr]
    linarith [Complex.abs_re_le_norm (∫ x, ((x - a : ℝ) : ℂ) * logLift g.1 x)]
  have hCi : |(∫ x, (x - a) * (logLift g.1 x).im)| ≤ N / 8192 := by
    rw [eCi]
    linarith [Complex.abs_im_le_norm (∫ x, ((x - a : ℝ) : ℂ) * logLift g.1 x)]
  have prod_lb : ∀ A B : ℝ, |A| ≤ N / 4096 → |B| ≤ N / 16384 → -(N ^ 2 / 67108864) ≤ A * B := by
    intro A B hA hB
    have h1 : |A * B| ≤ N / 4096 * (N / 16384) := by
      rw [abs_mul]
      exact mul_le_mul hA hB (abs_nonneg _) (by positivity)
    have h2 := neg_abs_le (A * B)
    nlinarith
  have sq_ub : ∀ C : ℝ, |C| ≤ N / 8192 → C ^ 2 ≤ N ^ 2 / 67108864 := by
    intro C hC
    have := pow_le_pow_left₀ (abs_nonneg _) hC 2
    rw [sq_abs] at this
    nlinarith
  have hAr' : |(∫ t, (t - a) ^ 2 * (logLift g.1 t).re)| ≤ N / 4096 := by linarith
  have hAi' : |(∫ t, (t - a) ^ 2 * (logLift g.1 t).im)| ≤ N / 4096 := by linarith
  have p1 := prod_lb _ _ hAr' hBr
  have p2 := prod_lb _ _ hAi' hBi
  have s1 := sq_ub _ hCr
  have s2 := sq_ub _ hCi
  unfold AEGIS.WeilDiagonalQuadGainV1.qMom
  linarith

/-- **Inner window with the quadratic gain.** -/
theorem inner_integral_quad_moment :
    (∫ u in Ioc (0 : ℝ) (1 / 32), widthArchLogIntegrandV26 g u) ≤
      energy g.1 * (diagonalSmallV21 - Real.exp (-(1 / 32)) * (Real.log 2 + 4 / 3 - 1 / 2048)) := by
  have hcpos : 0 < Real.exp (-(1 / 32) : ℝ) := Real.exp_pos _
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hf := inner_integrableOn g
  have hKi : IntegrableOn (fun _ : ℝ => energy g.1 * (Real.exp (1 / 64) / 2)) (Ioc (0 : ℝ) (1 / 32)) :=
    continuous_const.integrableOn_Ioc
  have hdi : IntegrableOn (fun u => (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u) /
      Real.exp (-(1 / 32))) (Ioc (0 : ℝ) (1 / 32)) :=
    (hKi.sub hf).div_const _
  have hpt : ∀ u ∈ Ioc (0 : ℝ) (1 / 32),
      (energy g.1 - (logCorrelationV25 g u).re) / u ≤
        (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u) / Real.exp (-(1 / 32)) := by
    intro u hu
    rw [le_div_iff₀ hcpos]
    have := inner_pointwise g hu.1 hu.2
    linarith
  have hφ0 : ∀ u ∈ Ioc (0 : ℝ) (1 / 32), 0 ≤ (energy g.1 - (logCorrelationV25 g u).re) / u :=
    fun u hu => div_nonneg (by linarith [logCorrelation_re_le g u]) hu.1.le
  have hcont := logLift_continuous g
  have hz0 := logLift_zero_off g (a - 1 / 64) (a + 1 / 64) hw
  have hz := AEGIS.WeilDiagonalLogGainS1V1.zero_off_Ioo_of_continuous (logLift g.1) hcont _ _ hz0
  have hR := AEGIS.WeilDiagonalMeanGainV1.integrable_reCorr (logLift g.1) hcont _ _ hz0
  have hφm : AEStronglyMeasurable (fun u => (energy g.1 - (logCorrelationV25 g u).re) / u)
      (volume.restrict (Ioc (0 : ℝ) (1 / 32))) := by
    have e : (fun u => (energy g.1 - (logCorrelationV25 g u).re) / u) =
        fun u => (energy g.1 - AEGIS.WeilDiagonalMeanGainV1.reCorr (logLift g.1) u) * u⁻¹ := by
      funext u
      rw [div_eq_mul_inv]
      rfl
    rw [e]
    exact ((aestronglyMeasurable_const.sub hR.aestronglyMeasurable).mul
      measurable_inv.aestronglyMeasurable).restrict
  have hφint : IntegrableOn (fun u => (energy g.1 - (logCorrelationV25 g u).re) / u) (Ioc (0 : ℝ) (1 / 32)) := by
    refine Integrable.mono' hdi hφm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 u hu)]
    exact hpt u hu
  have hwidth : a + 1 / 64 - (a - 1 / 64) = (1 / 32 : ℝ) := by ring
  have hint : IntegrableOn (fun s => ((∫ x, ‖logLift g.1 x‖ ^ 2) -
      (∫ x, logLift g.1 (x + s) * conj (logLift g.1 x)).re) / s)
      (Ioc (0 : ℝ) (a + 1 / 64 - (a - 1 / 64))) := by
    rw [hwidth, logLift_energy_eq_packet_energy]
    exact hφint
  have hG := AEGIS.WeilDiagonalQuadGainV1.quad_gain (logLift g.1) hcont _ _ (by linarith) hz hint
  rw [hwidth, logLift_energy_eq_packet_energy] at hG
  have hq1 := AEGIS.WeilDiagonalQuadGainV1.integral_sq_reCorr (logLift g.1) hcont _ _ hz0 (a - 1 / 64)
  have hq2 := AEGIS.WeilDiagonalQuadGainV1.integral_sq_reCorr (logLift g.1) hcont _ _ hz0 a
  have hqeq : AEGIS.WeilDiagonalQuadGainV1.qMom (logLift g.1) (a - 1 / 64) =
      AEGIS.WeilDiagonalQuadGainV1.qMom (logLift g.1) a := by linarith
  rw [hqeq] at hG
  have hN2 := l1_sq_le g a hw
  have hq := qMom_lower g a hw hm
  have hM := mean_le g a hw hm
  have hN0 : 0 ≤ ∫ t, ‖logLift g.1 t‖ := integral_nonneg (fun t => norm_nonneg _)
  have hMsq : ‖∫ t, logLift g.1 t‖ ^ 2 ≤ ((1 / 16384) * ∫ t, ‖logLift g.1 t‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hM 2
  have hc1 : 3 * ‖∫ x, logLift g.1 x‖ ^ 2 / (2 * (1 / 32 : ℝ)) ≤ energy g.1 / 4096 := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have hc2 : -(energy g.1 / 4096) ≤ 4 * AEGIS.WeilDiagonalQuadGainV1.qMom (logLift g.1) a / (1 / 32 : ℝ) ^ 3 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hgain : (Real.log 2 + 4 / 3 - 1 / 2048) * energy g.1 ≤
      ∫ s in Ioc (0 : ℝ) (1 / 32), (energy g.1 - (logCorrelationV25 g s).re) / s := by
    have : (Real.log 2 + 4 / 3 - 1 / 2048) * energy g.1 =
        (Real.log 2 + 4 / 3) * energy g.1 - energy g.1 / 4096 - energy g.1 / 4096 := by ring
    rw [this]
    refine le_trans ?_ hG
    linarith
  have hle : (∫ s in Ioc (0 : ℝ) (1 / 32), (energy g.1 - (logCorrelationV25 g s).re) / s) ≤
      ∫ u in Ioc (0 : ℝ) (1 / 32),
        (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u) / Real.exp (-(1 / 32)) :=
    setIntegral_mono_on hφint hdi measurableSet_Ioc hpt
  have e0 : (∫ u in Ioc (0 : ℝ) (1 / 32),
      (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u) / Real.exp (-(1 / 32))) =
      (∫ u in Ioc (0 : ℝ) (1 / 32),
        (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u)) / Real.exp (-(1 / 32)) :=
    integral_div _ _
  have e1 : (∫ u in Ioc (0 : ℝ) (1 / 32),
      (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u)) =
      (∫ _u in Ioc (0 : ℝ) (1 / 32), energy g.1 * (Real.exp (1 / 64) / 2)) -
        ∫ u in Ioc (0 : ℝ) (1 / 32), widthArchLogIntegrandV26 g u :=
    integral_sub hKi hf
  have e2 : (∫ _u in Ioc (0 : ℝ) (1 / 32), energy g.1 * (Real.exp (1 / 64) / 2)) =
      (1 / 32) * (energy g.1 * (Real.exp (1 / 64) / 2)) := by
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 32)]
    ring
  have hfin := hgain.trans hle
  rw [e0, e1, e2, le_div_iff₀ hcpos] at hfin
  unfold diagonalSmallV21
  nlinarith [hfin]

theorem width_archimedean_budget_quad_moment :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
      energy g.1 * ((diagonalSmallV21 - Real.exp (-(1 / 32)) * (Real.log 2 + 4 / 3 - 1 / 2048)) -
        diagonalTailV24) := by
  rw [archimedean_real_eq_log_integral_v27, width_arch_log_split_v27,
    width_arch_tail_integral_eq_v27 g a hw]
  have h := inner_integral_quad_moment g a hw hm
  nlinarith [h]

/-- **Diagonal with the quadratic gain and both moments.** -/
theorem diagonal_quad_moment_v1 :
    energy g.1 * (diagonalTailV24 - diagonalKappaV21 - diagonalSmallV21 +
      Real.exp (-(1 / 32)) * (Real.log 2 + 4 / 3 - 1 / 2048)) ≤ -(B g g).re := by
  have h := actual_diagonal_from_arch_budget g diagonalTailV24
    (diagonalSmallV21 - Real.exp (-(1 / 32)) * (Real.log 2 + 4 / 3 - 1 / 2048))
    (width_diagonal_prime_sum_zero_v24 g a hw) (width_archimedean_budget_quad_moment g a hw hm)
  calc energy g.1 * (diagonalTailV24 - diagonalKappaV21 - diagonalSmallV21 +
        Real.exp (-(1 / 32)) * (Real.log 2 + 4 / 3 - 1 / 2048))
      = energy g.1 * (diagonalTailV24 - diagonalKappaV21 -
          (diagonalSmallV21 - Real.exp (-(1 / 32)) * (Real.log 2 + 4 / 3 - 1 / 2048))) := by ring
    _ ≤ -(B g g).re := h

end packet

theorem quad_moment_constant_gt :
    (59 / 20 : ℝ) < diagonalTailV24 - diagonalKappaV21 - diagonalSmallV21 +
      Real.exp (-(1 / 32)) * (Real.log 2 + 4 / 3 - 1 / 2048) := by
  have hfloor := AEGIS.WeilThreeBlockAnalyticConstantsV21.diagonal_constant_floor
  have htail := diagonal_tail_gt_six_log_two_v24
  have hl := AEGIS.WeilThreeBlockAnalyticConstantsV21.log_two_lower
  have hc : (31 / 32 : ℝ) ≤ Real.exp (-(1 / 32)) := by
    have := Real.add_one_le_exp (-(1 / 32) : ℝ)
    linarith
  have hprod : (31 / 32 : ℝ) * (693 / 1000 + 4 / 3 - 1 / 2048) ≤
      Real.exp (-(1 / 32)) * (Real.log 2 + 4 / 3 - 1 / 2048) :=
    mul_le_mul hc (by linarith) (by norm_num) (Real.exp_pos _).le
  unfold diagonalKappaV21 diagonalSmallV21
  linarith

/-- **Width-1/32 moment-zero diagonal, `59/20`.** -/
theorem width_diagonal_59_over_20 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) :
    (59 / 20 : ℝ) * energy g.1 ≤ -(B g g).re := by
  have h := diagonal_quad_moment_v1 g a hw hm
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hmul := mul_le_mul_of_nonneg_left quad_moment_constant_gt.le hE
  linarith

end AEGIS.WeilDiagonalQuadMomentV1

#print axioms AEGIS.WeilDiagonalQuadMomentV1.qMom_lower
#print axioms AEGIS.WeilDiagonalQuadMomentV1.diagonal_quad_moment_v1
#print axioms AEGIS.WeilDiagonalQuadMomentV1.width_diagonal_59_over_20
