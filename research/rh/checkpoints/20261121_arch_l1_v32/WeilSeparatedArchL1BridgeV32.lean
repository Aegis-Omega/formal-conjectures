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
import WeilLogCorrelationL1V1

/-!
AEGIS Ω — L¹ form of the separated Archimedean bridge (V3.2, Claude Lab 2026-11-16).

`WeilSeparatedArchBridgeV31.separated_arch_norm_bound` integrates the pointwise bound `‖C‖ ≤ E` over the
support-difference interval (width 1/16). `WeilLogCorrelationL1V1.l1_autocorr_le` gives `∫ ‖C‖ ≤ (1/32) E`
for a width-1/32 packet, so the same kernel estimates give:

* `three_arch_bounds_l1`: the three retained mixed Archimedean terms are `≤ E/200` (V31: `E/100`);
* `translated_arch_norm_bound_dyadic`: for any shift `D = d₂ - d₁ ≥ log 2`,
  `‖Arch‖ ≤ (30/649) · exp(-5D/2) · E`; `dyadic_arch_decay` states it at `D = k log 2` as
  `(30/649) · 2^(-5k/2) · E`. The constant is exact from `exp x < 1/(1-x)` at `x = 5/64` and
  `exp(1/16) < 16/15`: `(64/59) / (11/15) / 32 = 30/649`.

* `distinct_arch_norm_bound_gap_l1`: two different packets of log-width `w` at support gap `δ > 0`,
  `‖Arch(mixed p q)‖ ≤ R(δ) · (w/2) · (E(p) + E(q))`, half of the pointwise route's `R(δ) · w · (E(p) + E(q))`.

The V30 cross/three-block assembly takes the Archimedean bound at 1/100 and is not re-derived here.
Archimedean side only: no prime-side estimate, no global Weil sign, not RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section
namespace AEGIS.WeilSeparatedArchL1BridgeV32

open AEGIS.WeilMixedClosureV2
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28

/-- Remainder kernel after subtracting the moment-cancelled rank-one term `exp(-u/2)`. -/
def archRemainderV32 (u : ℝ) : ℝ := Real.exp (-5 * u / 2) / (1 - Real.exp (-2 * u))

theorem archRemainder_nonneg (u : ℝ) (hu : 0 < u) : 0 ≤ archRemainderV32 u := by
  unfold archRemainderV32
  apply div_nonneg (Real.exp_pos _).le
  have h : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

/-- Generic L¹ kernel estimate: if the moment-cancelled kernel `K(u) - c·exp(-u/2)` is bounded by `κ`
beyond the support gap, the mixed Archimedean integral is at most `κ · ∫ ‖logCross‖`. -/
theorem separated_arch_norm_le_of_kernel
    (p q : WeilCompactSmoothGV1) (plo phi qlo qhi c κ L : ℝ)
    (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi)
    (hsep : phi < qlo) (hm : WeilMomentConditionsV1 p)
    (hker : ∀ u : ℝ, qlo - phi ≤ u →
      |Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) - c * Real.exp (-u / 2)| ≤ κ)
    (hL : (∫ u, ‖logCrossV28 p q u‖) ≤ L) (hκ : 0 ≤ κ) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤ κ * L := by
  let lo := qlo - phi
  let hi := qhi - plo
  let K : ℝ → ℝ := fun u => Real.exp (-u / 2) / (1 - Real.exp (-2 * u))
  let F : ℝ → ℂ := fun u => (K u : ℂ) * logCrossV28 p q (-u)
  let M : ℝ → ℂ := fun u => (Real.exp (-u / 2) : ℂ) * logCrossV28 p q (-u)
  have hlo : 0 < lo := by
    dsimp [lo]
    linarith
  have hzero (u : ℝ) (hu : u ∉ Icc lo hi) : logCrossV28 p q (-u) = 0 := by
    apply AEGIS.WeilSeparatedArchBridgeV31.logCross_zero_outside p q plo phi qlo qhi (-u) hp hq
    by_cases hlow : u < lo
    · right
      dsimp [lo] at hlow
      linarith
    · have hhigh : hi < u := lt_of_not_ge (fun h => hu ⟨le_of_not_gt hlow, h⟩)
      left
      dsimp [hi] at hhigh
      linarith
  have hFfull : (∫ u in Icc lo hi, F u) = ∫ u, F u :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by simp [F, hzero u hu])
  have hFpos : (∫ u in Ioi (0 : ℝ), F u) = ∫ u, F u := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hnot : u ∉ Icc lo hi := by
      intro h
      exact hu (lt_of_lt_of_le hlo h.1)
    simp [F, hzero u hnot]
  have harch : WeilArchimedeanIntegralV1 (mixed p q) = ∫ u in Icc lo hi, F u := by
    rw [AEGIS.WeilSeparatedArchBridgeV31.separated_arch_eq_log_kernel p q plo phi qlo qhi hp hq hsep]
    exact hFpos.trans hFfull.symm
  have hMfull : (∫ u, M u) = 0 := by
    have ht := integral_neg_eq_self
      (fun u : ℝ => (Real.exp (u / 2) : ℂ) * logCrossV28 p q u) volume
    exact ht.trans (AEGIS.WeilSeparatedArchBridgeV31.logCross_plus_moment_zero
      p q plo phi qlo qhi hp hq hm)
  have hMzero : (∫ u in Icc lo hi, M u) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (f := M) (s := Icc lo hi)
      (fun u hu => by simp [M, hzero u hu])]
    exact hMfull
  have hlc : Continuous (fun u : ℝ => logCrossV28 p q (-u)) :=
    (AEGIS.WeilSeparatedArchBridgeV31.logCross_continuous p q).comp continuous_neg
  have hMc : Continuous M := by
    dsimp [M]
    exact (by fun_prop : Continuous (fun u : ℝ => (Real.exp (-u / 2) : ℂ))).mul hlc
  have hKc : ContinuousOn K (Icc lo hi) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    have hup : 0 < u := lt_of_lt_of_le hlo hu.1
    exact ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have hFc : ContinuousOn F (Icc lo hi) :=
    (Complex.continuous_ofReal.comp_continuousOn hKc).mul hlc.continuousOn
  have hcancel : (∫ u in Icc lo hi, F u) =
      ∫ u in Icc lo hi, F u - (c : ℂ) * M u := by
    rw [integral_sub hFc.integrableOn_Icc (hMc.integrableOn_Icc.const_mul _),
      integral_const_mul, hMzero, mul_zero, sub_zero]
  have hpoint (u : ℝ) (hu : u ∈ Icc lo hi) :
      ‖F u - (c : ℂ) * M u‖ ≤ κ * ‖logCrossV28 p q (-u)‖ := by
    have heq : F u - (c : ℂ) * M u =
        (((K u - c * Real.exp (-u / 2)) : ℝ) : ℂ) * logCrossV28 p q (-u) := by
      dsimp [F, M]
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hker u hu.1) (norm_nonneg _)
  have hGc : Continuous (fun u : ℝ => κ * ‖logCrossV28 p q (-u)‖) :=
    continuous_const.mul hlc.norm
  have hint : IntegrableOn (fun u : ℝ => κ * ‖logCrossV28 p q (-u)‖) (Icc lo hi) :=
    hGc.integrableOn_Icc
  have hNfull : (∫ u in Icc lo hi, ‖logCrossV28 p q (-u)‖) = ∫ u, ‖logCrossV28 p q u‖ := by
    have h1 : (∫ u in Icc lo hi, ‖logCrossV28 p q (-u)‖) = ∫ u, ‖logCrossV28 p q (-u)‖ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by simp [hzero u hu])
    rw [h1]
    exact integral_neg_eq_self (fun u : ℝ => ‖logCrossV28 p q u‖) volume
  rw [harch, hcancel]
  calc
    ‖∫ u in Icc lo hi, F u - (c : ℂ) * M u‖ ≤
        ∫ u in Icc lo hi, κ * ‖logCrossV28 p q (-u)‖ := by
      apply norm_integral_le_of_norm_le hint
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with u hu
      exact hpoint u hu
    _ = κ * ∫ u, ‖logCrossV28 p q u‖ := by
      rw [integral_const_mul, hNfull]
    _ ≤ κ * L := mul_le_mul_of_nonneg_left hL hκ

/-- V31's centred kernel (`6/5`, sup `4/25`) against the L¹ norm of the mixed correlation. -/
theorem separated_arch_norm_bound_l1
    (p q : WeilCompactSmoothGV1) (plo phi qlo qhi L : ℝ)
    (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi)
    (hgap : Real.log 2 - 1 / 32 ≤ qlo - phi)
    (hm : WeilMomentConditionsV1 p)
    (hL : (∫ u, ‖logCrossV28 p q u‖) ≤ L) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤ (4 / 25 : ℝ) * L :=
  separated_arch_norm_le_of_kernel p q plo phi qlo qhi (6 / 5) (4 / 25) L hp hq
    (by linarith [log_two_gt_one_thirty_two]) hm
    (fun u hu => AEGIS.WeilSeparatedArchBridgeV31.centered_arch_kernel_bound u (hgap.trans hu))
    hL (by norm_num)

/-- Rank-one subtraction (coefficient 1) for an arbitrary positive support gap `δ`:
`‖Arch‖ ≤ R(δ) · ∫ ‖logCross‖` with `R(δ) = exp(-5δ/2) / (1 - exp(-2δ))`. -/
theorem separated_arch_norm_bound_gap_l1
    (p q : WeilCompactSmoothGV1) (plo phi qlo qhi δ L : ℝ)
    (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi)
    (hδ : 0 < δ) (hgap : δ ≤ qlo - phi)
    (hm : WeilMomentConditionsV1 p)
    (hL : (∫ u, ‖logCrossV28 p q u‖) ≤ L) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤ archRemainderV32 δ * L := by
  apply separated_arch_norm_le_of_kernel p q plo phi qlo qhi 1 (archRemainderV32 δ) L hp hq
    (by linarith) hm _ hL (archRemainder_nonneg δ hδ)
  intro u hu
  have hdu : δ ≤ u := hgap.trans hu
  have hu0 : 0 < u := lt_of_lt_of_le hδ hdu
  rw [one_mul, AEGIS.WeilThreeBlockCrossAssemblyV30.arch_kernel_sub_rank_one u hu0]
  have hR := archRemainder_nonneg u hu0
  unfold archRemainderV32 at hR
  rw [abs_of_nonneg hR]
  exact AEGIS.WeilThreeBlockCrossAssemblyV30.arch_remainder_le_at_gap δ u hδ hdu

/-- `logLift` of a width-1/32 packet vanishes off `[a - 1/64, (a - 1/64) + 1/32]`. -/
theorem logLift_zero_off_width (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) (x : ℝ)
    (hx : x ∉ Icc (a - 1 / 64) (a - 1 / 64 + 1 / 32)) : logLift g.1 x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hxt
  have h := hw hxt
  exact hx ⟨h.1, by linarith [h.2]⟩

theorem logLift_integrable_of_width (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) : Integrable (logLift g.1) := by
  have hw' : tsupport (logLift g.1) ⊆ Icc (a - 1 / 64) (a + 1 / 64) := hw
  exact (AEGIS.WeilSeparatedArchBridgeV31.logLift_continuous g).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport _).trans hw'))

/-- The V2.5 log autocorrelation of a width-1/32 packet has `∫ ‖C_g‖ ≤ E(g)/32`. -/
theorem logCorrelation_l1_le_v32 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) :
    (∫ u, ‖AEGIS.WeilWidthArchCorrelationV25.logCorrelationV25 g u‖) ≤
      (1 / 32 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy g.1 := by
  have h := AEGIS.WeilLogCorrelationL1V1.l1_autocorr_le (logLift g.1) (a - 1 / 64) (1 / 32)
    (by norm_num) (logLift_zero_off_width g a hw) (logLift_integrable_of_width g a hw)
    (AEGIS.WeilWidthArchCorrelationV25.logLift_sq_integrable_v25 g)
  rw [logLift_energy_eq_packet_energy] at h
  exact h

theorem translated_logCross_l1_le (g : WeilCompactSmoothGV1) (a d1 d2 : ℝ)
    (hw : WidthOneThirtyTwoAt g a) :
    (∫ u, ‖logCrossV28 (translatePacket g d1) (translatePacket g d2) u‖) ≤
      (1 / 32 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy g.1 := by
  simp_rw [logCross_translate_eq_logCorrelation_v28, add_sub_assoc]
  calc (∫ u, ‖AEGIS.WeilWidthArchCorrelationV25.logCorrelationV25 g (u + (d2 - d1))‖)
      = ∫ u, ‖AEGIS.WeilWidthArchCorrelationV25.logCorrelationV25 g u‖ :=
        integral_add_right_eq_self
          (fun u => ‖AEGIS.WeilWidthArchCorrelationV25.logCorrelationV25 g u‖) (d2 - d1)
    _ ≤ _ := logCorrelation_l1_le_v32 g a hw

/-- Retained translates at relative shift `≥ log 2`: Archimedean mixed term `≤ E/200`. -/
theorem translated_arch_norm_bound_l1
    (g : WeilCompactSmoothGV1) (a d1 d2 : ℝ)
    (hw : WidthOneThirtyTwoAt g a) (hm : WeilMomentConditionsV1 g)
    (hd : Real.log 2 ≤ d2 - d1) :
    ‖WeilArchimedeanIntegralV1 (mixed (translatePacket g d1) (translatePacket g d2))‖ ≤
      (1 / 200 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy g.1 := by
  have h := separated_arch_norm_bound_l1 (translatePacket g d1) (translatePacket g d2)
    (a - 1 / 64 + d1) (a + 1 / 64 + d1) (a - 1 / 64 + d2) (a + 1 / 64 + d2) _
    (translate_logSupportIn g d1 _ _ hw) (translate_logSupportIn g d2 _ _ hw)
    (by linarith) (translate_preserves_moments g d1 hm) (translated_logCross_l1_le g a d1 d2 hw)
  exact h.trans_eq (by ring)

theorem three_arch_bounds_l1
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) (hm : WeilMomentConditionsV1 g) :
    ‖WeilArchimedeanIntegralV1 (mixed (gMinus g) (gZero g))‖ ≤
        (1 / 200 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy g.1 ∧
    ‖WeilArchimedeanIntegralV1 (mixed (gMinus g) (gPlus g))‖ ≤
        (1 / 200 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy g.1 ∧
    ‖WeilArchimedeanIntegralV1 (mixed (gZero g) (gPlus g))‖ ≤
        (1 / 200 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy g.1 := by
  refine ⟨translated_arch_norm_bound_l1 g a (-Real.log 2) 0 hw hm (by linarith), ?_, ?_⟩
  · exact translated_arch_norm_bound_l1 g a (-Real.log 2) (Real.log 2) hw hm
      (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
  · exact translated_arch_norm_bound_l1 g a 0 (Real.log 2) hw hm (by linarith)

/-- `R(D - 1/32) ≤ (960/649) · exp(-5D/2)` for every `D ≥ log 2`. -/
theorem archRemainder_le_dyadic (D : ℝ) (hD : Real.log 2 ≤ D) :
    archRemainderV32 (D - 1 / 32) ≤ (960 / 649 : ℝ) * Real.exp (-5 * D / 2) := by
  unfold archRemainderV32
  have h5 : Real.exp (5 / 64 : ℝ) < 64 / 59 := by
    calc Real.exp (5 / 64 : ℝ) < 1 / (1 - 5 / 64) :=
          Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
      _ = 64 / 59 := by norm_num
  have h16 : Real.exp (1 / 16 : ℝ) < 16 / 15 :=
    AEGIS.WeilThreeBlockAnalyticConstantsV21.exp_one_over_16_upper
  have hnum : Real.exp (-5 * (D - 1 / 32) / 2) = Real.exp (-5 * D / 2) * Real.exp (5 / 64) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hden : Real.exp (-2 * (D - 1 / 32)) = Real.exp (-2 * D) * Real.exp (1 / 16) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp (2 * Real.log 2) = (4 : ℝ) := by
    rw [two_mul, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have h4 : Real.exp (-2 * D) ≤ 1 / 4 := by
    calc Real.exp (-2 * D) ≤ Real.exp (-(2 * Real.log 2)) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 4 := by rw [Real.exp_neg, he2]; norm_num
  have hA := Real.exp_pos (-5 * D / 2)
  have hC := Real.exp_pos (1 / 16 : ℝ)
  have hprod : Real.exp (-2 * D) * Real.exp (1 / 16) ≤ 4 / 15 := by
    calc Real.exp (-2 * D) * Real.exp (1 / 16) ≤ (1 / 4) * (16 / 15) :=
          mul_le_mul h4 h16.le hC.le (by norm_num)
      _ = 4 / 15 := by norm_num
  have hd0 : (11 / 15 : ℝ) ≤ 1 - Real.exp (-2 * D) * Real.exp (1 / 16) := by linarith
  rw [hnum, hden, div_le_iff₀ (by linarith)]
  have h1 : Real.exp (-5 * D / 2) * Real.exp (5 / 64) ≤ Real.exp (-5 * D / 2) * (64 / 59) :=
    mul_le_mul_of_nonneg_left h5.le hA.le
  have h2 := mul_le_mul_of_nonneg_left hd0 hA.le
  nlinarith [h1, h2]

/-- Dyadic Archimedean decay for retained translates at shift `D = d₂ - d₁ ≥ log 2`. -/
theorem translated_arch_norm_bound_dyadic
    (g : WeilCompactSmoothGV1) (a d1 d2 : ℝ)
    (hw : WidthOneThirtyTwoAt g a) (hm : WeilMomentConditionsV1 g)
    (hd : Real.log 2 ≤ d2 - d1) :
    ‖WeilArchimedeanIntegralV1 (mixed (translatePacket g d1) (translatePacket g d2))‖ ≤
      (30 / 649 : ℝ) * Real.exp (-5 * (d2 - d1) / 2) *
        AEGIS.WeilDisjointEnergyV2.energy g.1 := by
  have hδ : 0 < d2 - d1 - 1 / 32 := by linarith [log_two_gt_one_thirty_two]
  have h := separated_arch_norm_bound_gap_l1 (translatePacket g d1) (translatePacket g d2)
    (a - 1 / 64 + d1) (a + 1 / 64 + d1) (a - 1 / 64 + d2) (a + 1 / 64 + d2)
    (d2 - d1 - 1 / 32) _
    (translate_logSupportIn g d1 _ _ hw) (translate_logSupportIn g d2 _ _ hw)
    hδ (by linarith) (translate_preserves_moments g d1 hm) (translated_logCross_l1_le g a d1 d2 hw)
  have hR := archRemainder_le_dyadic (d2 - d1) hd
  have hEL : 0 ≤ (1 / 32 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy g.1 :=
    mul_nonneg (by norm_num) (AEGIS.WeilDisjointEnergyV2.energy_nonnegative g.1)
  exact (h.trans (mul_le_mul_of_nonneg_right hR hEL)).trans_eq (by ring)

/-- The same bound at `D = k log 2`: `(30/649) · 2^(-5k/2) · E`. -/
theorem dyadic_arch_decay (g : WeilCompactSmoothGV1) (a d : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hw : WidthOneThirtyTwoAt g a) (hm : WeilMomentConditionsV1 g) :
    ‖WeilArchimedeanIntegralV1
        (mixed (translatePacket g d) (translatePacket g (d + k * Real.log 2)))‖ ≤
      (30 / 649 : ℝ) * (2 : ℝ) ^ (-(5 / 2 : ℝ) * k) *
        AEGIS.WeilDisjointEnergyV2.energy g.1 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have h := translated_arch_norm_bound_dyadic g a d (d + k * Real.log 2) hw hm
    (by nlinarith [mul_nonneg (sub_nonneg.mpr hk') hlog])
  have hpow : (2 : ℝ) ^ (-(5 / 2 : ℝ) * k) =
      Real.exp (-5 * (d + k * Real.log 2 - d) / 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hpow]
  exact h

/-! ### Two different packets -/

theorem logLift_zero_off (p : WeilCompactSmoothGV1) (lo w : ℝ) (hp : LogSupportIn p lo (lo + w))
    (x : ℝ) (hx : x ∉ Icc lo (lo + w)) : logLift p.1 x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hxt
  exact hx (hp hxt)

theorem logLift_integrable_of_support (p : WeilCompactSmoothGV1) (lo hi : ℝ)
    (hp : LogSupportIn p lo hi) : Integrable (logLift p.1) := by
  have hp' : tsupport (logLift p.1) ⊆ Icc lo hi := hp
  exact (AEGIS.WeilSeparatedArchBridgeV31.logLift_continuous p).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport _).trans hp'))

/-- Two packets of log-width `w`: `∫ ‖logCross p q‖ ≤ (w/2)(E(p) + E(q))`. -/
theorem logCross_l1_le_distinct (p q : WeilCompactSmoothGV1) (plo qlo w : ℝ) (hw : 0 ≤ w)
    (hp : LogSupportIn p plo (plo + w)) (hq : LogSupportIn q qlo (qlo + w)) :
    (∫ u, ‖logCrossV28 p q u‖) ≤
      (w / 2) * (AEGIS.WeilDisjointEnergyV2.energy p.1 +
        AEGIS.WeilDisjointEnergyV2.energy q.1) := by
  have h := AEGIS.WeilLogCorrelationL1V1.l1_crosscorr_le (logLift p.1) (logLift q.1) plo qlo w hw
    (logLift_zero_off p plo w hp) (logLift_zero_off q qlo w hq)
    (logLift_integrable_of_support p _ _ hp) (logLift_integrable_of_support q _ _ hq)
    (AEGIS.WeilWidthArchCorrelationV25.logLift_sq_integrable_v25 p)
    (AEGIS.WeilWidthArchCorrelationV25.logLift_sq_integrable_v25 q)
  rw [logLift_energy_eq_packet_energy, logLift_energy_eq_packet_energy] at h
  exact h

/-- Two packets of log-width `w` at support gap `δ > 0` (moment conditions on `p` only):
`‖Arch(mixed p q)‖ ≤ R(δ) · (w/2) · (E(p) + E(q))`. -/
theorem distinct_arch_norm_bound_gap_l1
    (p q : WeilCompactSmoothGV1) (plo qlo w δ : ℝ) (hw : 0 ≤ w)
    (hp : LogSupportIn p plo (plo + w)) (hq : LogSupportIn q qlo (qlo + w))
    (hδ : 0 < δ) (hgap : δ ≤ qlo - (plo + w))
    (hm : WeilMomentConditionsV1 p) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤
      archRemainderV32 δ * ((w / 2) *
        (AEGIS.WeilDisjointEnergyV2.energy p.1 + AEGIS.WeilDisjointEnergyV2.energy q.1)) :=
  separated_arch_norm_bound_gap_l1 p q plo (plo + w) qlo (qlo + w) δ _ hp hq hδ hgap hm
    (logCross_l1_le_distinct p q plo qlo w hw hp hq)

end AEGIS.WeilSeparatedArchL1BridgeV32

#print axioms AEGIS.WeilSeparatedArchL1BridgeV32.separated_arch_norm_le_of_kernel
#print axioms AEGIS.WeilSeparatedArchL1BridgeV32.logCorrelation_l1_le_v32
#print axioms AEGIS.WeilSeparatedArchL1BridgeV32.three_arch_bounds_l1
#print axioms AEGIS.WeilSeparatedArchL1BridgeV32.translated_arch_norm_bound_dyadic
#print axioms AEGIS.WeilSeparatedArchL1BridgeV32.dyadic_arch_decay
#print axioms AEGIS.WeilSeparatedArchL1BridgeV32.distinct_arch_norm_bound_gap_l1
