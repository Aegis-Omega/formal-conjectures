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

import WeilDiagonalQuadMomentV1

/-!
AEGIS Ω — the diagonal of a moment-zero atom of log-width 1/128 (Claude Lab, 2026-11-22).

Hypotheses: `LogSupportIn g (a − 1/256) (a + 1/256)` (definitionally the `WidthOneOneTwentyEightAt g a` of
`RHRationalNinePacketPrimeWindowV1`, the atoms of the operator's fine Gram decomposition) and
`WeilMomentConditionsV1 g`. The Archimedean inner window `(0, 1/32]` is split at `1/128`:

* on `(1/128, 1/32]` the log correlation vanishes (`fine_corr_zero`), the integrand is `−E/sinh u`, and
  `sinh u ≤ u e^{u}` gives `∫ ≤ −e^{−1/32} log 4 · E` (`middle_integral_le`);
* on `(0, 1/128]` the quadratic gain `WeilDiagonalQuadGainV1.quad_gain` is applied on the window of width
  `1/128`, with the moment losses of `WeilDiagonalQuadMomentV1` (`inner_fine_integral_le`).

Result (`fine_diagonal_quad_v1`):
`E · (tail − κ − e^{1/64}/256 + e^{−1/32} (3 log 2 + 4/3 − 1/128)) ≤ −Re B(g, g)`, and
`fine_diagonal_43_over_10`: `(43/10) · E ≤ −Re B(g, g)` (rational lower bound `4.3416`). The previous fine diagonal
`RHFineDiagonalUpgradeV3.fine_diagonal_5671_over_3200_v3` is `1.7722`.

Diagonal estimate only. Not RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators ENNReal
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilFineDiagonalQuadV1

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

section atom

variable (g : WeilCompactSmoothGV1) (a : ℝ) (hf : LogSupportIn g (a - 1 / 256) (a + 1 / 256))

include hf

theorem fine_retained : WidthOneThirtyTwoAt g a := by
  intro t ht
  have h := hf ht
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem fine_corr_zero (u : ℝ) (hu : (1 / 128 : ℝ) < |u|) : logCorrelationV25 g u = 0 := by
  unfold logCorrelationV25
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  by_cases h0 : logLift g.1 v = 0
  · simp [h0]
  · by_cases h1 : logLift g.1 (v + u) = 0
    · simp [h1]
    · have hv := hf (subset_tsupport _ h0)
      have hvu := hf (subset_tsupport _ h1)
      have habs : |u| ≤ (1 / 128 : ℝ) := by
        rw [abs_le]
        constructor <;> linarith [hv.1, hv.2, hvu.1, hvu.2]
      exact False.elim ((not_le_of_gt hu) habs)

theorem fine_integrand (u : ℝ) (hu : (1 / 128 : ℝ) < u) :
    widthArchLogIntegrandV26 g u = -energy g.1 / Real.sinh u := by
  rw [integrand_eq, fine_corr_zero g a hf u (by rw [abs_of_pos (by linarith)]; exact hu)]
  simp

/-- `(1/128, 1/32]`: the correlation vanishes. -/
theorem middle_integral_le :
    (∫ u in Ioc (1 / 128 : ℝ) (1 / 32), widthArchLogIntegrandV26 g u) ≤
      -(energy g.1 * Real.exp (-(1 / 32)) * (2 * Real.log 2)) := by
  have hE := energy_nonnegative g.1
  have hfull := width_arch_log_integrableOn_v27 g
  have hI : IntegrableOn (widthArchLogIntegrandV26 g) (Ioc (1 / 128 : ℝ) (1 / 32)) :=
    hfull.mono_set (fun u hu => show (0 : ℝ) < u by linarith [hu.1])
  have hbI : IntegrableOn (fun u : ℝ => -(energy g.1 * Real.exp (-(1 / 32))) * u⁻¹)
      (Ioc (1 / 128 : ℝ) (1 / 32)) := by
    have hco : ContinuousOn (fun u : ℝ => -(energy g.1 * Real.exp (-(1 / 32))) * u⁻¹)
        (Icc (1 / 128 : ℝ) (1 / 32)) :=
      continuousOn_const.mul (continuousOn_inv₀.mono (fun u hu => by
        have : (0 : ℝ) < u := by linarith [hu.1]
        exact this.ne'))
    exact hco.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hpt : ∀ u ∈ Ioc (1 / 128 : ℝ) (1 / 32),
      widthArchLogIntegrandV26 g u ≤ -(energy g.1 * Real.exp (-(1 / 32))) * u⁻¹ := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    rw [fine_integrand g a hf u hu.1]
    have hsh : 0 < Real.sinh u := AEGIS.WeilArchimedeanCothTailV1.sinh_pos_of_pos hu0
    have hs1 := sinh_le_mul_exp u
    have hex : Real.exp u ≤ Real.exp (1 / 32) := Real.exp_le_exp.mpr hu.2
    have hc : Real.exp (-(1 / 32)) * Real.exp (1 / 32) = 1 := by
      rw [← Real.exp_add]
      simp
    have hs2 : Real.sinh u * Real.exp (-(1 / 32)) ≤ u := by
      have := mul_le_mul_of_nonneg_left hex hu0.le
      have hpos := Real.exp_pos (-(1 / 32) : ℝ)
      nlinarith
    rw [div_le_iff₀ hsh]
    have hinv : u⁻¹ * Real.sinh u * Real.exp (-(1 / 32)) ≤ 1 := by
      rw [mul_assoc]
      calc u⁻¹ * (Real.sinh u * Real.exp (-(1 / 32))) ≤ u⁻¹ * u :=
            mul_le_mul_of_nonneg_left hs2 (inv_nonneg.mpr hu0.le)
        _ = 1 := inv_mul_cancel₀ hu0.ne'
    nlinarith
  have hint : (∫ u in Ioc (1 / 128 : ℝ) (1 / 32), -(energy g.1 * Real.exp (-(1 / 32))) * u⁻¹) =
      -(energy g.1 * Real.exp (-(1 / 32))) * Real.log 4 := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le (by norm_num),
      integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  calc (∫ u in Ioc (1 / 128 : ℝ) (1 / 32), widthArchLogIntegrandV26 g u)
      ≤ ∫ u in Ioc (1 / 128 : ℝ) (1 / 32), -(energy g.1 * Real.exp (-(1 / 32))) * u⁻¹ :=
        setIntegral_mono_on hI hbI measurableSet_Ioc hpt
    _ = -(energy g.1 * Real.exp (-(1 / 32)) * (2 * Real.log 2)) := by
        rw [hint, h4]
        ring

theorem l1_sq_le_fine : (∫ t, ‖logLift g.1 t‖) ^ 2 ≤ (1 / 128) * energy g.1 := by
  have hc := logLift_continuous g
  have hz := logLift_zero_off g (a - 1 / 256) (a + 1 / 256) hf
  have hI1 : Integrable (logLift g.1) := integrable_of_zero_off _ hc _ _ hz
  have hsq2 : Integrable (fun t => ‖logLift g.1 t‖ ^ 2) :=
    integrable_of_zero_off _ (hc.norm.pow 2) (a - 1 / 256) (a + 1 / 256) (fun t ht => by simp [hz t ht])
  have hCS := AEGIS.WeilLogCorrelationL1V1.sq_integral_le_mul (fun t => ‖logLift g.1 t‖)
    (a - 1 / 256) (1 / 128) (by norm_num)
    (fun x hx => by
      rw [hz x (fun hm' => hx ⟨hm'.1, by linarith [hm'.2]⟩)]
      simp)
    hI1.norm hsq2
  rwa [logLift_energy_eq_packet_energy] at hCS

variable (hm : WeilMomentConditionsV1 g)
include hm

/-- `(0, 1/128]`: the quadratic gain on the window of width `1/128`. -/
theorem inner_fine_integral_le :
    (∫ u in Ioc (0 : ℝ) (1 / 128), widthArchLogIntegrandV26 g u) ≤
      (1 / 128) * (energy g.1 * (Real.exp (1 / 64) / 2)) -
        Real.exp (-(1 / 32)) * (Real.log 2 + 4 / 3 - 1 / 128) * energy g.1 := by
  have hw := fine_retained g a hf
  have hcpos : 0 < Real.exp (-(1 / 32) : ℝ) := Real.exp_pos _
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hf' : IntegrableOn (widthArchLogIntegrandV26 g) (Ioc (0 : ℝ) (1 / 128)) :=
    (width_arch_log_integrableOn_v27 g).mono_set (fun u hu => hu.1)
  have hKi : IntegrableOn (fun _ : ℝ => energy g.1 * (Real.exp (1 / 64) / 2)) (Ioc (0 : ℝ) (1 / 128)) :=
    continuous_const.integrableOn_Ioc
  have hdi : IntegrableOn (fun u => (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u) /
      Real.exp (-(1 / 32))) (Ioc (0 : ℝ) (1 / 128)) :=
    (hKi.sub hf').div_const _
  have hpt : ∀ u ∈ Ioc (0 : ℝ) (1 / 128),
      (energy g.1 - (logCorrelationV25 g u).re) / u ≤
        (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u) / Real.exp (-(1 / 32)) := by
    intro u hu
    rw [le_div_iff₀ hcpos]
    have := inner_pointwise g hu.1 (by linarith [hu.2])
    linarith
  have hφ0 : ∀ u ∈ Ioc (0 : ℝ) (1 / 128), 0 ≤ (energy g.1 - (logCorrelationV25 g u).re) / u :=
    fun u hu => div_nonneg (by linarith [logCorrelation_re_le g u]) hu.1.le
  have hcont := logLift_continuous g
  have hz0 := logLift_zero_off g (a - 1 / 256) (a + 1 / 256) hf
  have hz := AEGIS.WeilDiagonalLogGainS1V1.zero_off_Ioo_of_continuous (logLift g.1) hcont _ _ hz0
  have hR := AEGIS.WeilDiagonalMeanGainV1.integrable_reCorr (logLift g.1) hcont _ _ hz0
  have hφm : AEStronglyMeasurable (fun u => (energy g.1 - (logCorrelationV25 g u).re) / u)
      (volume.restrict (Ioc (0 : ℝ) (1 / 128))) := by
    have e : (fun u => (energy g.1 - (logCorrelationV25 g u).re) / u) =
        fun u => (energy g.1 - AEGIS.WeilDiagonalMeanGainV1.reCorr (logLift g.1) u) * u⁻¹ := by
      funext u
      rw [div_eq_mul_inv]
      rfl
    rw [e]
    exact ((aestronglyMeasurable_const.sub hR.aestronglyMeasurable).mul
      measurable_inv.aestronglyMeasurable).restrict
  have hφint : IntegrableOn (fun u => (energy g.1 - (logCorrelationV25 g u).re) / u)
      (Ioc (0 : ℝ) (1 / 128)) := by
    refine Integrable.mono' hdi hφm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 u hu)]
    exact hpt u hu
  have hwidth : a + 1 / 256 - (a - 1 / 256) = (1 / 128 : ℝ) := by ring
  have hint : IntegrableOn (fun s => ((∫ x, ‖logLift g.1 x‖ ^ 2) -
      (∫ x, logLift g.1 (x + s) * conj (logLift g.1 x)).re) / s)
      (Ioc (0 : ℝ) (a + 1 / 256 - (a - 1 / 256))) := by
    rw [hwidth, logLift_energy_eq_packet_energy]
    exact hφint
  have hG := AEGIS.WeilDiagonalQuadGainV1.quad_gain (logLift g.1) hcont _ _ (by linarith) hz hint
  rw [hwidth, logLift_energy_eq_packet_energy] at hG
  have hq1 := AEGIS.WeilDiagonalQuadGainV1.integral_sq_reCorr (logLift g.1) hcont _ _ hz0 (a - 1 / 256)
  have hq2 := AEGIS.WeilDiagonalQuadGainV1.integral_sq_reCorr (logLift g.1) hcont _ _ hz0 a
  have hqeq : AEGIS.WeilDiagonalQuadGainV1.qMom (logLift g.1) (a - 1 / 256) =
      AEGIS.WeilDiagonalQuadGainV1.qMom (logLift g.1) a := by linarith
  rw [hqeq] at hG
  have hN2 := l1_sq_le_fine g a hf
  have hq := AEGIS.WeilDiagonalQuadMomentV1.qMom_lower g a hw hm
  have hM := AEGIS.WeilDiagonalQuadMomentV1.mean_le g a hw hm
  have hN0 : 0 ≤ ∫ t, ‖logLift g.1 t‖ := integral_nonneg (fun t => norm_nonneg _)
  have hMsq : ‖∫ t, logLift g.1 t‖ ^ 2 ≤ ((1 / 16384) * ∫ t, ‖logLift g.1 t‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hM 2
  have hc1 : 3 * ‖∫ x, logLift g.1 x‖ ^ 2 / (2 * (1 / 128 : ℝ)) ≤ energy g.1 / 256 := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have hc2 : -(energy g.1 / 256) ≤
      4 * AEGIS.WeilDiagonalQuadGainV1.qMom (logLift g.1) a / (1 / 128 : ℝ) ^ 3 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hgain : (Real.log 2 + 4 / 3 - 1 / 128) * energy g.1 ≤
      ∫ s in Ioc (0 : ℝ) (1 / 128), (energy g.1 - (logCorrelationV25 g s).re) / s := by
    have : (Real.log 2 + 4 / 3 - 1 / 128) * energy g.1 =
        (Real.log 2 + 4 / 3) * energy g.1 - energy g.1 / 256 - energy g.1 / 256 := by ring
    rw [this]
    refine le_trans ?_ hG
    linarith
  have hle : (∫ s in Ioc (0 : ℝ) (1 / 128), (energy g.1 - (logCorrelationV25 g s).re) / s) ≤
      ∫ u in Ioc (0 : ℝ) (1 / 128),
        (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u) / Real.exp (-(1 / 32)) :=
    setIntegral_mono_on hφint hdi measurableSet_Ioc hpt
  have e0 : (∫ u in Ioc (0 : ℝ) (1 / 128),
      (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u) / Real.exp (-(1 / 32))) =
      (∫ u in Ioc (0 : ℝ) (1 / 128),
        (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u)) / Real.exp (-(1 / 32)) :=
    integral_div _ _
  have e1 : (∫ u in Ioc (0 : ℝ) (1 / 128),
      (energy g.1 * (Real.exp (1 / 64) / 2) - widthArchLogIntegrandV26 g u)) =
      (∫ _u in Ioc (0 : ℝ) (1 / 128), energy g.1 * (Real.exp (1 / 64) / 2)) -
        ∫ u in Ioc (0 : ℝ) (1 / 128), widthArchLogIntegrandV26 g u :=
    integral_sub hKi hf'
  have e2 : (∫ _u in Ioc (0 : ℝ) (1 / 128), energy g.1 * (Real.exp (1 / 64) / 2)) =
      (1 / 128) * (energy g.1 * (Real.exp (1 / 64) / 2)) := by
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 128)]
    ring
  have hfin := hgain.trans hle
  rw [e0, e1, e2, le_div_iff₀ hcpos] at hfin
  nlinarith [hfin]

theorem inner_window_fine :
    (∫ u in Ioc (0 : ℝ) (1 / 32), widthArchLogIntegrandV26 g u) ≤
      energy g.1 * (Real.exp (1 / 64) / 256 -
        Real.exp (-(1 / 32)) * (3 * Real.log 2 + 4 / 3 - 1 / 128)) := by
  have hfull := width_arch_log_integrableOn_v27 g
  have hA : IntegrableOn (widthArchLogIntegrandV26 g) (Ioc (0 : ℝ) (1 / 128)) :=
    hfull.mono_set (fun u hu => hu.1)
  have hB : IntegrableOn (widthArchLogIntegrandV26 g) (Ioc (1 / 128 : ℝ) (1 / 32)) :=
    hfull.mono_set (fun u hu => show (0 : ℝ) < u by linarith [hu.1])
  have hdisj : Disjoint (Ioc (0 : ℝ) (1 / 128)) (Ioc (1 / 128 : ℝ) (1 / 32)) := by
    rw [Set.disjoint_left]
    intro u h1 h2
    linarith [h1.2, h2.1]
  have hU : Ioc (0 : ℝ) (1 / 128) ∪ Ioc (1 / 128 : ℝ) (1 / 32) = Ioc (0 : ℝ) (1 / 32) :=
    Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)
  rw [← hU, setIntegral_union hdisj measurableSet_Ioc hA hB]
  have h1 := inner_fine_integral_le g a hf hm
  have h2 := middle_integral_le g a hf
  nlinarith [h1, h2]

theorem fine_archimedean_budget :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
      energy g.1 * ((Real.exp (1 / 64) / 256 -
        Real.exp (-(1 / 32)) * (3 * Real.log 2 + 4 / 3 - 1 / 128)) - diagonalTailV24) := by
  rw [archimedean_real_eq_log_integral_v27, width_arch_log_split_v27,
    width_arch_tail_integral_eq_v27 g a (fine_retained g a hf)]
  have h := inner_window_fine g a hf hm
  nlinarith [h]

/-- **Diagonal of a moment-zero atom of log-width 1/128.** -/
theorem fine_diagonal_quad_v1 :
    energy g.1 * (diagonalTailV24 - diagonalKappaV21 - Real.exp (1 / 64) / 256 +
      Real.exp (-(1 / 32)) * (3 * Real.log 2 + 4 / 3 - 1 / 128)) ≤ -(B g g).re := by
  have h := actual_diagonal_from_arch_budget g diagonalTailV24
    (Real.exp (1 / 64) / 256 - Real.exp (-(1 / 32)) * (3 * Real.log 2 + 4 / 3 - 1 / 128))
    (width_diagonal_prime_sum_zero_v24 g a (fine_retained g a hf)) (fine_archimedean_budget g a hf hm)
  calc energy g.1 * (diagonalTailV24 - diagonalKappaV21 - Real.exp (1 / 64) / 256 +
        Real.exp (-(1 / 32)) * (3 * Real.log 2 + 4 / 3 - 1 / 128))
      = energy g.1 * (diagonalTailV24 - diagonalKappaV21 -
          (Real.exp (1 / 64) / 256 - Real.exp (-(1 / 32)) * (3 * Real.log 2 + 4 / 3 - 1 / 128))) := by ring
    _ ≤ -(B g g).re := h

end atom

theorem fine_constant_gt :
    (43 / 10 : ℝ) < diagonalTailV24 - diagonalKappaV21 - Real.exp (1 / 64) / 256 +
      Real.exp (-(1 / 32)) * (3 * Real.log 2 + 4 / 3 - 1 / 128) := by
  have hfloor := AEGIS.WeilThreeBlockAnalyticConstantsV21.diagonal_constant_floor
  have htail := diagonal_tail_gt_six_log_two_v24
  have hl := AEGIS.WeilThreeBlockAnalyticConstantsV21.log_two_lower
  have hc := AEGIS.WeilArchimedeanCothTailV1.exp_neg_one_div_32_gt
  have he : (1 : ℝ) ≤ Real.exp (1 / 64) := Real.one_le_exp (by norm_num)
  have hprod : (63 / 65 : ℝ) * (3 * (693 / 1000) + 4 / 3 - 1 / 128) ≤
      Real.exp (-(1 / 32)) * (3 * Real.log 2 + 4 / 3 - 1 / 128) :=
    mul_le_mul hc.le (by linarith) (by norm_num) (Real.exp_pos _).le
  unfold diagonalKappaV21
  linarith

/-- **Fine diagonal `43/10`.** -/
theorem fine_diagonal_43_over_10 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hf : LogSupportIn g (a - 1 / 256) (a + 1 / 256)) (hm : WeilMomentConditionsV1 g) :
    (43 / 10 : ℝ) * energy g.1 ≤ -(B g g).re := by
  have h := fine_diagonal_quad_v1 g a hf hm
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hmul := mul_le_mul_of_nonneg_left fine_constant_gt.le hE
  linarith

end AEGIS.WeilFineDiagonalQuadV1

#print axioms AEGIS.WeilFineDiagonalQuadV1.middle_integral_le
#print axioms AEGIS.WeilFineDiagonalQuadV1.fine_diagonal_quad_v1
#print axioms AEGIS.WeilFineDiagonalQuadV1.fine_diagonal_43_over_10
