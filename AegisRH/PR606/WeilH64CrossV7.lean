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
import WeilSeparatedArchBridgeV31
import WeilH64DiagonalV7

/-!
# OPTIMUS V7: Archimedean cross terms of separated packets

For packets `p` (log-support `[plo, phi]`) and `q` (log-support `[qlo, qhi]`) with `phi < qlo`, write
`lo = qlo − phi`, `hi = qhi − plo`. On the actual repository functional:

* `logCross_norm_le`: `‖C_pq(u)‖ ≤ (E_p + E_q)/2` (Cauchy–Schwarz in the form `2ab ≤ a² + b²`);
* `sep_arch_le`: `‖Arch(mixed p q)‖ ≤ E ((hi − lo) + ½ log(hi/lo))` (V7 §3, `w(u) ≤ 1 + 1/(2u)`);
* `sep_arch_le_two`: `‖Arch(mixed p q)‖ ≤ 2 E (hi − lo)` once `lo ≥ 1/2` (`w ≤ 2`);
* `mixed_one_zero`: the centre value `mixed p q 1` vanishes.

Not RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators

noncomputable section

namespace AEGIS.WeilH64CrossV7

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilSeparatedArchBridgeV31

/-- **Cauchy–Schwarz for the mixed log correlation.** -/
theorem logCross_norm_le (p q : WeilCompactSmoothGV1) (u : ℝ) :
    ‖logCrossV28 p q u‖ ≤ (energy p.1 + energy q.1) / 2 := by
  let f : ℝ → ℂ := fun v => logLift p.1 (v + u) * conj (logLift q.1 v)
  let M : ℝ → ℝ := fun v => (1 / 2 : ℝ) * (‖logLift p.1 (v + u)‖ ^ 2 + ‖logLift q.1 v‖ ^ 2)
  have hM : Integrable M :=
    ((shifted_logLift_sq_integrable_v25 p u).add (logLift_sq_integrable_v25 q)).const_mul (1 / 2 : ℝ)
  have hpoint : ∀ v : ℝ, ‖f v‖ ≤ M v := by
    intro v
    have hab : ‖logLift p.1 (v + u)‖ * ‖logLift q.1 v‖ ≤
        (1 / 2 : ℝ) * (‖logLift p.1 (v + u)‖ ^ 2 + ‖logLift q.1 v‖ ^ 2) := by
      nlinarith [sq_nonneg (‖logLift p.1 (v + u)‖ - ‖logLift q.1 v‖)]
    simpa [f, M, norm_mul, norm_conj] using hab
  have hfc : Continuous f :=
    ((logLift_continuous p).comp (continuous_id.add continuous_const)).mul
      (continuous_conj.comp (logLift_continuous q))
  have hf : Integrable f :=
    hM.mono' hfc.aestronglyMeasurable (Filter.Eventually.of_forall fun v => hpoint v)
  calc ‖logCrossV28 p q u‖ = ‖∫ v : ℝ, f v‖ := rfl
    _ ≤ ∫ v : ℝ, ‖f v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, M v := integral_mono hf.norm hM hpoint
    _ = (1 / 2 : ℝ) * ((∫ v : ℝ, ‖logLift p.1 (v + u)‖ ^ 2) + ∫ v : ℝ, ‖logLift q.1 v‖ ^ 2) := by
        unfold M
        rw [integral_const_mul, integral_add (shifted_logLift_sq_integrable_v25 p u)
          (logLift_sq_integrable_v25 q)]
    _ = (energy p.1 + energy q.1) / 2 := by
        rw [shifted_logLift_sq_integral_v25, logLift_energy_eq_packet_energy]; ring

/-- The Archimedean weight. -/
def wK (u : ℝ) : ℝ := Real.exp (-u / 2) / (1 - Real.exp (-2 * u))

theorem wK_den_pos {u : ℝ} (hu : 0 < u) : 0 < 1 - Real.exp (-2 * u) := by
  have : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

theorem wK_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ wK u :=
  div_nonneg (Real.exp_pos _).le (wK_den_pos hu).le

theorem wK_continuousOn : ContinuousOn wK (Ioi 0) := by
  intro u hu
  apply ContinuousAt.continuousWithinAt
  unfold wK
  exact ((by fun_prop : Continuous fun u : ℝ => Real.exp (-u / 2)).continuousAt).div
    ((by fun_prop : Continuous fun u : ℝ => 1 - Real.exp (-2 * u)).continuousAt)
    (wK_den_pos hu).ne'

/-- The centre value of a separated mixed correlation vanishes. -/
theorem mixed_one_zero (p q : WeilCompactSmoothGV1) {plo phi qlo qhi : ℝ}
    (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi) (hsep : phi < qlo) :
    mixed p q 1 = 0 := by
  have hc := logCross_zero_outside p q plo phi qlo qhi 0 hp hq (Or.inr (by linarith))
  rw [logCross_eq_mixed_v28] at hc
  simpa using hc

/-- The Archimedean integral of a separated pair, as a bounded integral over `[lo, hi]`. -/
theorem sep_arch_norm_le_integral (p q : WeilCompactSmoothGV1) {plo phi qlo qhi E : ℝ}
    (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi) (hsep : phi < qlo)
    (hE : ∀ u, ‖logCrossV28 p q u‖ ≤ E) {b : ℝ → ℝ}
    (hb : ContinuousOn b (Icc (qlo - phi) (qhi - plo)))
    (hwb : ∀ u ∈ Icc (qlo - phi) (qhi - plo), wK u ≤ b u) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤ E * ∫ u in Icc (qlo - phi) (qhi - plo), b u := by
  set lo := qlo - phi
  set hi := qhi - plo
  have hlo : 0 < lo := by simp only [lo]; linarith
  have hE0 : 0 ≤ E := (norm_nonneg _).trans (hE 0)
  rw [separated_arch_eq_log_kernel p q plo phi qlo qhi hp hq hsep]
  set F : ℝ → ℂ := fun u => ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) *
    logCrossV28 p q (-u) with hF
  have hsub : Icc lo hi ⊆ Ioi (0 : ℝ) := fun u hu => lt_of_lt_of_le hlo hu.1
  have hzero : ∀ u ∈ Ioi (0 : ℝ) \ Icc lo hi, F u = 0 := by
    intro u hu
    have hnot : u < lo ∨ hi < u := by
      by_contra h
      exact hu.2 ⟨le_of_not_gt fun h' => h (Or.inl h'), le_of_not_gt fun h' => h (Or.inr h')⟩
    have hc : logCrossV28 p q (-u) = 0 := by
      apply logCross_zero_outside p q plo phi qlo qhi (-u) hp hq
      rcases hnot with h | h
      · right; simp only [lo] at h; linarith
      · left; simp only [hi] at h; linarith
    simp [hF, hc]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub hzero]
  have hFc : ContinuousOn F (Icc lo hi) := by
    have hw : ContinuousOn (fun u : ℝ => ((wK u : ℝ) : ℂ)) (Icc lo hi) :=
      (Complex.continuous_ofReal.comp_continuousOn (wK_continuousOn.mono hsub))
    exact hw.mul ((logCross_continuous p q).comp continuous_neg).continuousOn
  have hFi : IntegrableOn (fun u => ‖F u‖) (Icc lo hi) :=
    (hFc.integrableOn_compact isCompact_Icc).norm
  have hbi : IntegrableOn (fun u => E * b u) (Icc lo hi) :=
    ((continuousOn_const.mul hb).integrableOn_compact isCompact_Icc)
  calc ‖∫ u in Icc lo hi, F u‖ ≤ ∫ u in Icc lo hi, ‖F u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in Icc lo hi, E * b u := by
        refine setIntegral_mono_on hFi hbi measurableSet_Icc fun u hu => ?_
        have hu0 : 0 < u := hsub hu
        have hn : ‖F u‖ = wK u * ‖logCrossV28 p q (-u)‖ := by
          simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          show |wK u| * ‖logCrossV28 p q (-u)‖ = wK u * ‖logCrossV28 p q (-u)‖
          rw [abs_of_nonneg (wK_nonneg hu0)]
        rw [hn]
        calc wK u * ‖logCrossV28 p q (-u)‖ ≤ wK u * E :=
              mul_le_mul_of_nonneg_left (hE _) (wK_nonneg hu0)
          _ ≤ b u * E := mul_le_mul_of_nonneg_right (hwb u hu) hE0
          _ = E * b u := mul_comm _ _
    _ = E * ∫ u in Icc lo hi, b u := integral_const_mul _ _

/-- **V7 same-cluster bound**: `‖Arch(mixed p q)‖ ≤ E ((hi − lo) + ½ log(hi/lo))`. -/
theorem sep_arch_le (p q : WeilCompactSmoothGV1) {plo phi qlo qhi E : ℝ}
    (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi) (hsep : phi < qlo)
    (hlohi : qlo - phi ≤ qhi - plo) (hE : ∀ u, ‖logCrossV28 p q u‖ ≤ E) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤
      E * (((qhi - plo) - (qlo - phi)) + 1 / 2 * Real.log ((qhi - plo) / (qlo - phi))) := by
  set lo := qlo - phi
  set hi := qhi - plo
  have hlo : 0 < lo := by simp only [lo]; linarith
  have hb : ContinuousOn (fun u : ℝ => 1 + 1 / 2 * u⁻¹) (Icc lo hi) :=
    continuousOn_const.add (continuousOn_const.mul (continuousOn_inv₀.mono fun u hu =>
      (ne_of_gt (lt_of_lt_of_le hlo hu.1))))
  have hwb : ∀ u ∈ Icc lo hi, wK u ≤ 1 + 1 / 2 * u⁻¹ := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hlo hu.1
    have := AEGIS.WeilH64ElementaryV7.w_le hu0
    have e : 1 / (2 * u) = 1 / 2 * u⁻¹ := by field_simp
    rw [← e]; exact this
  refine (sep_arch_norm_le_integral p q hp hq hsep hE hb hwb).trans (le_of_eq ?_)
  congr 1
  have hhi : 0 < hi := lt_of_lt_of_le hlo hlohi
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume lo hi := intervalIntegrable_const
  have h2 : IntervalIntegrable (fun x : ℝ => 1 / 2 * x⁻¹) volume lo hi := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.mul
    apply continuousOn_inv₀.mono
    intro u hu
    rw [Set.uIcc_of_le hlohi] at hu
    exact ne_of_gt (lt_of_lt_of_le hlo hu.1)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlohi,
    intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_inv_of_pos hlo hhi]
  simp

/-- **V7 cross-cluster bound**: `‖Arch(mixed p q)‖ ≤ 2 E (hi − lo)` once `lo ≥ 1/2`. -/
theorem sep_arch_le_two (p q : WeilCompactSmoothGV1) {plo phi qlo qhi E : ℝ}
    (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi) (hgap : 1 / 2 ≤ qlo - phi)
    (hlohi : qlo - phi ≤ qhi - plo) (hE : ∀ u, ‖logCrossV28 p q u‖ ≤ E) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤ E * (2 * ((qhi - plo) - (qlo - phi))) := by
  have hsep : phi < qlo := by linarith
  have hwb : ∀ u ∈ Icc (qlo - phi) (qhi - plo), wK u ≤ (fun _ => (2 : ℝ)) u := fun u hu =>
    AEGIS.WeilH64ElementaryV7.w_le_two (le_trans hgap hu.1)
  refine (sep_arch_norm_le_integral p q hp hq hsep hE continuousOn_const hwb).trans (le_of_eq ?_)
  rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le hlohi]
  ring

end AEGIS.WeilH64CrossV7

#print axioms AEGIS.WeilH64CrossV7.logCross_norm_le
#print axioms AEGIS.WeilH64CrossV7.sep_arch_le
#print axioms AEGIS.WeilH64CrossV7.sep_arch_le_two
#print axioms AEGIS.WeilH64CrossV7.mixed_one_zero
