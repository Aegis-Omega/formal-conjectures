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

import WeilWidthArchIntegralV27
import WeilDiagonalLogGainS1V1

/-!
AEGIS Ω — the diagonal log gain, transported into the width-1/32 Weil diagonal (Claude Lab, 2026-11-21).

`WeilWidthArchIntegralV27.width_diagonal_103_over_100_v27` bounds the inner Archimedean window `(0, 1/32]` by the
constant majorant `E · e^{1/64}/2` (V26), which discards the sign of `E − Re C(u)`. Here the inner integrand
`(e^{u/2} Re C(u) − E)/sinh u` is split as

  `(e^{u/2} − 1) Re C(u)/sinh u − (E − Re C(u))/sinh u`.

The first part keeps the V26 majorant. The second part is bounded through `1/sinh u ≥ e^{−1/32}/u` and the
sub-lemma S1 (`WeilDiagonalLogGainS1V1.log_gain_lintegral`, applied to the log-lift on its support interval),
which gives `∫_{(0,1/32]} (E − Re C(u))/u du ≥ log 2 · E`. The result is

  `diagonal_log_gain_v1 : E · (tail − κ − small + e^{−1/32} log 2) ≤ −Re B(g, g)`,

with the same `tail`, `κ` and `small` as V21/V24/V27, and the rational form `width_diagonal_17_over_10`.
This is step 2 of `research/rh/atomic_map_v1` §4.5 (AEGIS-OMEGA PR #835). No moment hypothesis is used.

Diagonal estimate only, for the width-1/32 packet class. No off-diagonal estimate, no global Weil sign, not RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators ENNReal
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilDiagonalLogGainV1

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilWidthArchBudgetV26
open AEGIS.WeilWidthArchIntegralV27
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilWidthDiagonalArchFrontierV24
open AEGIS.WeilMixedAlgebraV2

theorem logLift_continuous (g : WeilCompactSmoothGV1) : Continuous (logLift g.1) := by
  unfold logLift
  have hscalar : Continuous (fun t : ℝ => (Real.exp (t / 2) : ℂ)) := by fun_prop
  exact hscalar.mul (g.2.1.continuous.comp Real.continuous_exp)

theorem logLift_zero_off (g : WeilCompactSmoothGV1) (lo hi : ℝ) (hw : LogSupportIn g lo hi) :
    ∀ x, x ∉ Icc lo hi → logLift g.1 x = 0 :=
  fun _ hx => image_eq_zero_of_notMem_tsupport (fun hm => hx (hw hm))

theorem exp_mul_autocorrelation_re (g : WeilCompactSmoothGV1) (u : ℝ) :
    Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re =
      Real.exp (u / 2) * (logCorrelationV25 g u).re := by
  rw [logCorrelation_eq_autocorrelation_v25, Complex.re_ofReal_mul, ← mul_assoc, ← Real.exp_add,
    show u / 2 + u / 2 = u by ring]

/-- The V26 integrand in terms of the log-correlation. -/
theorem integrand_eq (g : WeilCompactSmoothGV1) (u : ℝ) :
    widthArchLogIntegrandV26 g u =
      (Real.exp (u / 2) * (logCorrelationV25 g u).re - energy g.1) / Real.sinh u := by
  unfold widthArchLogIntegrandV26
  rw [exp_mul_autocorrelation_re]

theorem logCorrelation_re_le (g : WeilCompactSmoothGV1) (u : ℝ) :
    (logCorrelationV25 g u).re ≤ energy g.1 :=
  (Complex.re_le_norm _).trans (norm_logCorrelation_le_energy_v25 g u)

theorem sinh_le_mul_exp (u : ℝ) : Real.sinh u ≤ u * Real.exp u := by
  have h1 := Real.add_one_le_exp (-(2 * u))
  have he : Real.exp (-u) = Real.exp u * Real.exp (-(2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.sinh_eq, he]
  have hpos := Real.exp_pos u
  nlinarith [mul_le_mul_of_nonneg_left h1 hpos.le]

theorem exp_half_sub_one_le {u : ℝ} (hu0 : 0 < u) (huw : u ≤ 1 / 32) :
    Real.exp (u / 2) - 1 ≤ Real.sinh u / 2 * Real.exp (1 / 64) := by
  have h1 : Real.exp (u / 2) - 1 ≤ u / 2 * Real.exp (u / 2) := by
    have h := Real.add_one_le_exp (-(u / 2))
    have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (u / 2)).le
    have hexp : Real.exp (u / 2) * Real.exp (-(u / 2)) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [hexp] at hm
    nlinarith
  have hsinh_ge : u ≤ Real.sinh u := Real.self_le_sinh_iff.mpr hu0.le
  have hexpmono : Real.exp (u / 2) ≤ Real.exp (1 / 64) := Real.exp_le_exp.mpr (by linarith)
  calc Real.exp (u / 2) - 1 ≤ u / 2 * Real.exp (u / 2) := h1
    _ ≤ Real.sinh u / 2 * Real.exp (1 / 64) :=
        mul_le_mul (by linarith) hexpmono (Real.exp_pos _).le (by linarith)

/-- Pointwise split of the inner integrand: the `E − Re C` part is kept with weight `e^{−1/32}/u`. -/
theorem inner_pointwise (g : WeilCompactSmoothGV1) {u : ℝ} (hu0 : 0 < u) (huw : u ≤ 1 / 32) :
    Real.exp (-(1 / 32)) * ((energy g.1 - (logCorrelationV25 g u).re) / u) ≤
      energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u := by
  rw [integrand_eq]
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hRE := logCorrelation_re_le g u
  have hsh : 0 < Real.sinh u := AEGIS.WeilArchimedeanCothTailV1.sinh_pos_of_pos hu0
  have he2 : 1 ≤ Real.exp (u / 2) := Real.one_le_exp (by linarith)
  have hk := exp_half_sub_one_le hu0 huw
  have hexpw : Real.exp u ≤ Real.exp (1 / 32) := Real.exp_le_exp.mpr huw
  have hc : Real.exp (-(1 / 32)) * Real.exp (1 / 32) = 1 := by
    rw [← Real.exp_add]
    simp
  have hcpos : 0 < Real.exp (-(1 / 32) : ℝ) := Real.exp_pos _
  have hcs : Real.exp (-(1 / 32)) * Real.sinh u ≤ u := by
    have h1 : Real.sinh u ≤ u * Real.exp (1 / 32) :=
      (sinh_le_mul_exp u).trans (mul_le_mul_of_nonneg_left hexpw hu0.le)
    calc Real.exp (-(1 / 32)) * Real.sinh u ≤ Real.exp (-(1 / 32)) * (u * Real.exp (1 / 32)) :=
          mul_le_mul_of_nonneg_left h1 hcpos.le
      _ = u := by rw [mul_comm u, ← mul_assoc, hc, one_mul]
  have hq0 : 0 ≤ (energy g.1 - (logCorrelationV25 g u).re) / u := div_nonneg (by linarith) hu0.le
  have hqu : (energy g.1 - (logCorrelationV25 g u).re) / u * u = energy g.1 - (logCorrelationV25 g u).re :=
    div_mul_cancel₀ _ hu0.ne'
  have hX : (Real.exp (u / 2) * (logCorrelationV25 g u).re - energy g.1) / Real.sinh u * Real.sinh u =
      Real.exp (u / 2) * (logCorrelationV25 g u).re - energy g.1 :=
    div_mul_cancel₀ _ hsh.ne'
  have f1 : 0 ≤ (Real.exp (u / 2) - 1) * (energy g.1 - (logCorrelationV25 g u).re) :=
    mul_nonneg (by linarith) (by linarith)
  have f2 : 0 ≤ (Real.sinh u / 2 * Real.exp (1 / 64) - (Real.exp (u / 2) - 1)) * energy g.1 :=
    mul_nonneg (by linarith) hE
  have f3 : 0 ≤ (u - Real.exp (-(1 / 32)) * Real.sinh u) *
      ((energy g.1 - (logCorrelationV25 g u).re) / u) :=
    mul_nonneg (by linarith) hq0
  have key : (Real.exp (-(1 / 32)) * ((energy g.1 - (logCorrelationV25 g u).re) / u) +
      (Real.exp (u / 2) * (logCorrelationV25 g u).re - energy g.1) / Real.sinh u) * Real.sinh u ≤
      energy g.1 * (Real.exp (1 / 64) / 2) * Real.sinh u := by
    nlinarith [hX, hqu, f1, f2, f3]
  have := le_of_mul_le_mul_right key hsh
  linarith

theorem inner_integrableOn (g : WeilCompactSmoothGV1) :
    IntegrableOn (widthArchLogIntegrandV26 g) (Ioc (0 : ℝ) (1 / 32)) :=
  (width_arch_log_integrableOn_v27 g).mono_set (fun _ hu => hu.1)

/-- **Inner window with the log gain.** Replaces `width_arch_inner_integral_le_v27`. -/
theorem inner_integral_log_gain (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a) :
    (∫ u in Ioc (0 : ℝ) (1 / 32), widthArchLogIntegrandV26 g u) ≤
      energy g.1 * (diagonalSmallV21 - Real.exp (-(1 / 32)) * Real.log 2) := by
  have hcpos : 0 < Real.exp (-(1 / 32) : ℝ) := Real.exp_pos _
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
  have hS1 := AEGIS.WeilDiagonalLogGainS1V1.log_gain_lintegral (logLift g.1) hcont _ _ hz
  have hwidth : a + 1 / 64 - (a - 1 / 64) = (1 / 32 : ℝ) := by ring
  rw [hwidth, logLift_energy_eq_packet_energy] at hS1
  have hlin : ENNReal.ofReal (Real.log 2 * energy g.1) ≤
      ENNReal.ofReal (∫ u in Ioc (0 : ℝ) (1 / 32),
        (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u) / Real.exp (-(1 / 32))) := by
    refine hS1.trans ?_
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

/-- The Archimedean budget with the log gain. Replaces `width_archimedean_budget_v27`. -/
theorem width_archimedean_budget_log_gain (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
      energy g.1 * ((diagonalSmallV21 - Real.exp (-(1 / 32)) * Real.log 2) - diagonalTailV24) := by
  rw [archimedean_real_eq_log_integral_v27, width_arch_log_split_v27,
    width_arch_tail_integral_eq_v27 g a hw]
  have h := inner_integral_log_gain g a hw
  nlinarith [h]

/-- **Diagonal log gain** (PR #835 §4.5, step 2), no moment hypothesis. -/
theorem diagonal_log_gain_v1 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a) :
    energy g.1 * (diagonalTailV24 - diagonalKappaV21 - diagonalSmallV21 +
      Real.exp (-(1 / 32)) * Real.log 2) ≤ -(B g g).re := by
  have h := actual_diagonal_from_arch_budget g diagonalTailV24
    (diagonalSmallV21 - Real.exp (-(1 / 32)) * Real.log 2)
    (width_diagonal_prime_sum_zero_v24 g a hw) (width_archimedean_budget_log_gain g a hw)
  calc energy g.1 * (diagonalTailV24 - diagonalKappaV21 - diagonalSmallV21 +
        Real.exp (-(1 / 32)) * Real.log 2)
      = energy g.1 * (diagonalTailV24 - diagonalKappaV21 -
          (diagonalSmallV21 - Real.exp (-(1 / 32)) * Real.log 2)) := by ring
    _ ≤ -(B g g).re := h

/-- The new diagonal constant exceeds `17/10` (the V27 constant is `103/100`). -/
theorem log_gain_constant_gt :
    (17 / 10 : ℝ) < diagonalTailV24 - diagonalKappaV21 - diagonalSmallV21 +
      Real.exp (-(1 / 32)) * Real.log 2 := by
  have hfloor := AEGIS.WeilThreeBlockAnalyticConstantsV21.diagonal_constant_floor
  have htail := diagonal_tail_gt_six_log_two_v24
  have hl := AEGIS.WeilThreeBlockAnalyticConstantsV21.log_two_lower
  have hc : (31 / 32 : ℝ) ≤ Real.exp (-(1 / 32)) := by
    have := Real.add_one_le_exp (-(1 / 32) : ℝ)
    linarith
  have hprod : (31 / 32 : ℝ) * (693 / 1000) ≤ Real.exp (-(1 / 32)) * Real.log 2 :=
    mul_le_mul hc hl.le (by norm_num) (Real.exp_pos _).le
  unfold diagonalKappaV21 diagonalSmallV21
  linarith

/-- **Width-1/32 diagonal, `17/10`.** Same hypotheses as `width_diagonal_103_over_100_v27`. -/
theorem width_diagonal_17_over_10 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a) :
    (17 / 10 : ℝ) * energy g.1 ≤ -(B g g).re := by
  have h := diagonal_log_gain_v1 g a hw
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hm := mul_le_mul_of_nonneg_left log_gain_constant_gt.le hE
  linarith

end AEGIS.WeilDiagonalLogGainV1

#print axioms AEGIS.WeilDiagonalLogGainV1.inner_pointwise
#print axioms AEGIS.WeilDiagonalLogGainV1.inner_integral_log_gain
#print axioms AEGIS.WeilDiagonalLogGainV1.diagonal_log_gain_v1
#print axioms AEGIS.WeilDiagonalLogGainV1.log_gain_constant_gt
#print axioms AEGIS.WeilDiagonalLogGainV1.width_diagonal_17_over_10
