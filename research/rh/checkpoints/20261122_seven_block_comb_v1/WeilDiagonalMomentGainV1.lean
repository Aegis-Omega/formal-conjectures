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

import WeilDiagonalLogGainV1
import WeilDiagonalMeanGainV1

/-!
AEGIS Ω — the width-1/32 diagonal with the mean gain and both moments (Claude Lab, 2026-11-22).

`WeilDiagonalLogGainV1` gives `17/10` without moments, from the S1 gain `log 2 · E`. Here the inner window uses
`WeilDiagonalMeanGainV1.mean_gain_lintegral`, a gain of `(log 2 + 1/2) · E − ‖M‖²/(2w)` with `M = ∫ logLift g`.
For a packet with `WeilMomentConditionsV1`, `∫ e^{t/2} logLift g = 0` forces `M = ∫ (1 − e^{(t−a)/2}) logLift g`,
so `‖M‖ ≤ (1/64) ∫ ‖logLift g‖` and `‖M‖² ≤ E/(32 · 4096)` (`mean_sq_le`). The result is

  `diagonal_moment_gain_v1 : E · (tail − κ − small + e^{−1/32} (log 2 + 1/2 − 1/8192)) ≤ −Re B(g, g)`,

whose constant exceeds `109/50` (`width_diagonal_109_over_50`; numerically `2.1913`).

Diagonal estimate only, for the width-1/32 moment-zero packet class. Not RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators ENNReal
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilDiagonalMomentGainV1

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

/-- **The mean of a moment-zero width-1/32 packet is tiny.** -/
theorem mean_sq_le (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) :
    ‖∫ t, logLift g.1 t‖ ^ 2 ≤ (1 / 32) * energy g.1 / 4096 := by
  have hc := logLift_continuous g
  have hz := logLift_zero_off g (a - 1 / 64) (a + 1 / 64) hw
  have hplus : (∫ t, (Real.exp (t / 2) : ℂ) * logLift g.1 t) = 0 :=
    (logMomentPlus_eq_repository g).trans hm.2
  have hI1 : Integrable (logLift g.1) :=
    AEGIS.WeilDiagonalLogGainS1V1.integrable_of_zero_off _ hc _ _ hz
  have hcont2 : Continuous (fun t : ℝ => (Real.exp (t / 2) : ℂ) * logLift g.1 t) := by
    have : Continuous (fun t : ℝ => (Real.exp (t / 2) : ℂ)) := by fun_prop
    exact this.mul hc
  have hI2 : Integrable (fun t : ℝ => (Real.exp (t / 2) : ℂ) * logLift g.1 t) :=
    AEGIS.WeilDiagonalLogGainS1V1.integrable_of_zero_off _ hcont2 (a - 1 / 64) (a + 1 / 64)
      (fun t ht => by simp [hz t ht])
  have hMeq : (∫ t, logLift g.1 t) =
      ∫ t, (1 - (Real.exp ((t - a) / 2) : ℂ)) * logLift g.1 t := by
    calc (∫ t, logLift g.1 t)
        = (∫ t, logLift g.1 t) -
            (Real.exp (-a / 2) : ℂ) * ∫ t, (Real.exp (t / 2) : ℂ) * logLift g.1 t := by
          rw [hplus, mul_zero, sub_zero]
      _ = ∫ t, (logLift g.1 t - (Real.exp (-a / 2) : ℂ) * ((Real.exp (t / 2) : ℂ) * logLift g.1 t)) := by
          rw [integral_sub hI1 (hI2.const_mul _), integral_const_mul]
      _ = ∫ t, (1 - (Real.exp ((t - a) / 2) : ℂ)) * logLift g.1 t := by
          congr 1
          funext t
          have he : (Real.exp ((t - a) / 2) : ℂ) = (Real.exp (-a / 2) : ℂ) * (Real.exp (t / 2) : ℂ) := by
            rw [← Complex.ofReal_mul, ← Real.exp_add]
            congr 2
            ring
          rw [he]
          ring
  have hbound : ∀ t, ‖(1 - (Real.exp ((t - a) / 2) : ℂ)) * logLift g.1 t‖ ≤ (1 / 64) * ‖logLift g.1 t‖ := by
    intro t
    by_cases ht : t ∈ Icc (a - 1 / 64) (a + 1 / 64)
    · rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hx : |(t - a) / 2| ≤ 1 / 128 := by
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
      have h1 := Real.abs_exp_sub_one_le (le_trans hx (by norm_num))
      have hn : ‖(1 : ℂ) - (Real.exp ((t - a) / 2) : ℂ)‖ = |Real.exp ((t - a) / 2) - 1| := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      rw [hn]
      linarith
    · simp [hz t ht]
  have hInorm : Integrable (fun t => ‖logLift g.1 t‖) := hI1.norm
  have hM : ‖∫ t, logLift g.1 t‖ ≤ (1 / 64) * ∫ t, ‖logLift g.1 t‖ := by
    rw [hMeq, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hInorm.const_mul _) (Filter.Eventually.of_forall hbound)
  have hsq2 : Integrable (fun t => ‖logLift g.1 t‖ ^ 2) :=
    AEGIS.WeilDiagonalLogGainS1V1.integrable_of_zero_off _ (hc.norm.pow 2) (a - 1 / 64) (a + 1 / 64)
      (fun t ht => by simp [hz t ht])
  have hCS := AEGIS.WeilLogCorrelationL1V1.sq_integral_le_mul (fun t => ‖logLift g.1 t‖)
    (a - 1 / 64) (1 / 32) (by norm_num)
    (fun x hx => by
      rw [hz x (fun hm' => hx ⟨hm'.1, by linarith [hm'.2]⟩)]
      simp)
    hInorm hsq2
  rw [logLift_energy_eq_packet_energy] at hCS
  have h0 : 0 ≤ ∫ t, ‖logLift g.1 t‖ := integral_nonneg (fun t => norm_nonneg _)
  calc ‖∫ t, logLift g.1 t‖ ^ 2 ≤ ((1 / 64) * ∫ t, ‖logLift g.1 t‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hM 2
    _ = (1 / 4096) * (∫ t, ‖logLift g.1 t‖) ^ 2 := by ring
    _ ≤ (1 / 4096) * ((1 / 32) * energy g.1) := mul_le_mul_of_nonneg_left hCS (by norm_num)
    _ = (1 / 32) * energy g.1 / 4096 := by ring

/-- **Inner window with the mean gain.** -/
theorem inner_integral_moment_gain (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) :
    (∫ u in Ioc (0 : ℝ) (1 / 32), widthArchLogIntegrandV26 g u) ≤
      energy g.1 * (diagonalSmallV21 - Real.exp (-(1 / 32)) * (Real.log 2 + 1 / 2 - 1 / 8192)) := by
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
  have hd0 : ∀ u ∈ Ioc (0 : ℝ) (1 / 32),
      0 ≤ (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u) / Real.exp (-(1 / 32)) :=
    fun u hu => (hφ0 u hu).trans (hpt u hu)
  have hcont := logLift_continuous g
  have hz := AEGIS.WeilDiagonalLogGainS1V1.zero_off_Ioo_of_continuous (logLift g.1) hcont _ _
    (logLift_zero_off g (a - 1 / 64) (a + 1 / 64) hw)
  have hG := AEGIS.WeilDiagonalMeanGainV1.mean_gain_lintegral (logLift g.1) hcont _ _ (by linarith) hz
  have hwidth : a + 1 / 64 - (a - 1 / 64) = (1 / 32 : ℝ) := by ring
  rw [hwidth, logLift_energy_eq_packet_energy] at hG
  have hmean := mean_sq_le g a hw hm
  have hG' : ENNReal.ofReal ((Real.log 2 + 1 / 2 - 1 / 8192) * energy g.1) ≤
      ∫⁻ s in Ioc (0 : ℝ) (1 / 32), ENNReal.ofReal
        ((energy g.1 - (∫ x, logLift g.1 (x + s) * conj (logLift g.1 x)).re) / s) := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hG
    have : ‖∫ x, logLift g.1 x‖ ^ 2 / (2 * (1 / 32 : ℝ)) ≤ energy g.1 / 8192 := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith [hmean]
    nlinarith [this]
  have hlin : ENNReal.ofReal ((Real.log 2 + 1 / 2 - 1 / 8192) * energy g.1) ≤
      ENNReal.ofReal (∫ u in Ioc (0 : ℝ) (1 / 32),
        (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u) / Real.exp (-(1 / 32))) := by
    refine hG'.trans ?_
    rw [ofReal_integral_eq_lintegral_ofReal hdi
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu; exact hd0 u hu)]
    exact setLIntegral_mono' measurableSet_Ioc (fun u hu => ENNReal.ofReal_le_ofReal (hpt u hu))
  have hint0 : 0 ≤ ∫ u in Ioc (0 : ℝ) (1 / 32),
      (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u) / Real.exp (-(1 / 32)) :=
    setIntegral_nonneg measurableSet_Ioc hd0
  have hle := (ENNReal.ofReal_le_ofReal_iff hint0).mp hlin
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
  rw [e0, e1, e2, le_div_iff₀ hcpos] at hle
  unfold diagonalSmallV21
  nlinarith [hle]

theorem width_archimedean_budget_moment_gain (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) (hm : WeilMomentConditionsV1 g) :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
      energy g.1 * ((diagonalSmallV21 - Real.exp (-(1 / 32)) * (Real.log 2 + 1 / 2 - 1 / 8192)) -
        diagonalTailV24) := by
  rw [archimedean_real_eq_log_integral_v27, width_arch_log_split_v27,
    width_arch_tail_integral_eq_v27 g a hw]
  have h := inner_integral_moment_gain g a hw hm
  nlinarith [h]

/-- **Diagonal with the mean gain and both moments.** -/
theorem diagonal_moment_gain_v1 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) :
    energy g.1 * (diagonalTailV24 - diagonalKappaV21 - diagonalSmallV21 +
      Real.exp (-(1 / 32)) * (Real.log 2 + 1 / 2 - 1 / 8192)) ≤ -(B g g).re := by
  have h := actual_diagonal_from_arch_budget g diagonalTailV24
    (diagonalSmallV21 - Real.exp (-(1 / 32)) * (Real.log 2 + 1 / 2 - 1 / 8192))
    (width_diagonal_prime_sum_zero_v24 g a hw) (width_archimedean_budget_moment_gain g a hw hm)
  calc energy g.1 * (diagonalTailV24 - diagonalKappaV21 - diagonalSmallV21 +
        Real.exp (-(1 / 32)) * (Real.log 2 + 1 / 2 - 1 / 8192))
      = energy g.1 * (diagonalTailV24 - diagonalKappaV21 -
          (diagonalSmallV21 - Real.exp (-(1 / 32)) * (Real.log 2 + 1 / 2 - 1 / 8192))) := by ring
    _ ≤ -(B g g).re := h

theorem moment_gain_constant_gt :
    (109 / 50 : ℝ) < diagonalTailV24 - diagonalKappaV21 - diagonalSmallV21 +
      Real.exp (-(1 / 32)) * (Real.log 2 + 1 / 2 - 1 / 8192) := by
  have hfloor := AEGIS.WeilThreeBlockAnalyticConstantsV21.diagonal_constant_floor
  have htail := diagonal_tail_gt_six_log_two_v24
  have hl := AEGIS.WeilThreeBlockAnalyticConstantsV21.log_two_lower
  have hc : (31 / 32 : ℝ) ≤ Real.exp (-(1 / 32)) := by
    have := Real.add_one_le_exp (-(1 / 32) : ℝ)
    linarith
  have hprod : (31 / 32 : ℝ) * (693 / 1000 + 1 / 2 - 1 / 8192) ≤
      Real.exp (-(1 / 32)) * (Real.log 2 + 1 / 2 - 1 / 8192) :=
    mul_le_mul hc (by linarith) (by norm_num) (Real.exp_pos _).le
  unfold diagonalKappaV21 diagonalSmallV21
  linarith

/-- **Width-1/32 moment-zero diagonal, `109/50`.** -/
theorem width_diagonal_109_over_50 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) :
    (109 / 50 : ℝ) * energy g.1 ≤ -(B g g).re := by
  have h := diagonal_moment_gain_v1 g a hw hm
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hmul := mul_le_mul_of_nonneg_left moment_gain_constant_gt.le hE
  linarith

end AEGIS.WeilDiagonalMomentGainV1

#print axioms AEGIS.WeilDiagonalMomentGainV1.mean_sq_le
#print axioms AEGIS.WeilDiagonalMomentGainV1.diagonal_moment_gain_v1
#print axioms AEGIS.WeilDiagonalMomentGainV1.width_diagonal_109_over_50
