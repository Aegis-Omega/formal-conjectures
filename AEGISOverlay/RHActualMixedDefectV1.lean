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

import AEGISOverlay.RHActualLocalGramCoercivityV1

/-!
AEGIS Ω — genuine full-Weil mixed-term defect, without dropped off-diagonals.

The entire finite Gram is the original arithmetic form, not a surrogate.
For every given compact-support local smooth partition we construct genuine
moment-zero narrow atoms with 32/25 diagonal gain and prove the EXACT global
lower bound in terms of the actual mixed contribution.

The remaining universal-sign obligation is precisely control of this
genuine mixed defect. No unconditional RH statement is introduced.
-/

open Set Finset Complex
open scoped ContDiff BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHActualMixedDefectV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHGramExpansionV13

/-- Genuine off-diagonal contribution: total B-Gram real part minus all
diagonal real parts. No term is discarded or replaced. -/
def actualMixedDefect (n : ℕ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) : ℝ :=
  (∑ i, ∑ j, B (gs i) (gs j)).re -
    ∑ i, (B (gs i) (gs i)).re

/-- Pure algebraic summation of the original pointwise 32/25 diagonal
coercivity. No mixed-term bound is assumed. -/
theorem quantitative_lower_of_diagonal
    (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hd : ∀ i, (32 / 25 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re) :
    (32 / 25 : ℝ) * (∑ i, energy (gs i).1) -
      actualMixedDefect n gs ≤
        -(∑ i, ∑ j, B (gs i) (gs j)).re := by
  have hs :
      (∑ i, (32 / 25 : ℝ) * energy (gs i).1) ≤
        ∑ i, -(B (gs i) (gs i)).re :=
    Finset.sum_le_sum (fun i _ => hd i)
  have hdiag :
      (32 / 25 : ℝ) * (∑ i, energy (gs i).1) ≤
        -(∑ i, (B (gs i) (gs i)).re) := by
    rw [Finset.mul_sum]
    simpa only [Finset.sum_neg_distrib] using hs
  unfold actualMixedDefect
  linarith

/-- For every arbitrary packet and every feasible locally complete narrow
smooth partition, construct an actual finite Gram and its exact quantitative
mixed-defect lower bound. -/
theorem every_packet_actual_mixed_defect_bound
    (n : ℕ)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (L : ℝ) (hL : 0 ≤ L)
    (hs : tsupport (AEGIS.RHKreinFactorV13.lift g.1) ⊆ Icc (-L) L)
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x ∈ Icc (-L) L, ∑ i : Fin (n + 1), χ i x = 1)
    (center : Fin (n + 1) → ℝ)
    (hcut : ∀ i, tsupport (χ i) ⊆
      Icc (center i - 1 / 128) (center i + 1 / 128)) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (32 / 25 : ℝ) * (∑ i, energy (gs i).1) -
          actualMixedDefect n gs ≤
            -(WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := by
  obtain ⟨gs, hmom, hd, hpacket, hgram⟩ :=
    AEGIS.RHActualLocalGramCoercivityV1.every_packet_actual_narrow_coercive_gram
      n g hm L hL hs χ hχ hpart center hcut
  refine ⟨gs, hmom, hpacket, ?_⟩
  calc
    (32 / 25 : ℝ) * (∑ i, energy (gs i).1) -
          actualMixedDefect n gs ≤
      -(∑ i, ∑ j, B (gs i) (gs j)).re :=
        quantitative_lower_of_diagonal n gs hd
    _ = -(WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := by
      rw [hgram]

/-- The exact, separately identifiable mixed-term budget that would close
the sign of this *particular* genuine Weil Gram. It is not assumed globally. -/
theorem actual_zero_sign_of_paid_mixed_defect
    (n : ℕ) (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hdiag : ∀ i, (32 / 25 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hgram : (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
      (∑ i, ∑ j, B (gs i) (gs j)).re)
    (hbudget : actualMixedDefect n gs ≤
      (32 / 25 : ℝ) * (∑ i, energy (gs i).1)) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have hbound := quantitative_lower_of_diagonal n gs hdiag
  have hsign : (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 := by
    rw [hgram]
    linarith
  exact (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
    g hm).mp hsign


/-! ## Unconditional, actual-B control of local interacting atoms

This section does not assume any global sign. A *common* certified
1/64-width log window is stable under finite sums and complex scaling.
Applying the existing analytic diagonal inequality to u+v and u-v
controls the real off-diagonal arithmetic B(u,v) itself. No cross
coefficient is set to zero, and no mixed budget for widely separated
atoms is inferred from this strictly local estimate. -/

open AEGIS.RHKreinFactorV13

theorem narrow_width_scale
    (u : WeilCompactSmoothGV1) (z : ℂ) (center : ℝ)
    (hu : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt u center) :
    AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt
      (scalePacket z u) center := by
  change tsupport (lift (scalePacket z u).1) ⊆
    Icc (center - 1 / 128) (center + 1 / 128)
  change tsupport (lift u.1) ⊆
    Icc (center - 1 / 128) (center + 1 / 128) at hu
  have hlift : lift (scalePacket z u).1 =
      (fun x => z * lift u.1 x) := by
    funext x
    simp [lift, scalePacket, mul_left_comm, mul_assoc]
  rw [hlift]
  have hsupport : tsupport (fun x => z * lift u.1 x) ⊆
      tsupport (lift u.1) := by
    apply closure_minimal ?_ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    have hzero : lift u.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport hn
    exact hx (by simp [hzero])
  exact hsupport.trans hu

theorem narrow_width_add
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hu : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt u center)
    (hv : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt v center) :
    AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt
      (addPacket u v) center := by
  change tsupport (lift (addPacket u v).1) ⊆
    Icc (center - 1 / 128) (center + 1 / 128)
  change tsupport (lift u.1) ⊆
    Icc (center - 1 / 128) (center + 1 / 128) at hu
  change tsupport (lift v.1) ⊆
    Icc (center - 1 / 128) (center + 1 / 128) at hv
  have hlift : lift (addPacket u v).1 =
      (fun x => lift u.1 x + lift v.1 x) := by
    funext x
    simp [lift, addPacket, mul_add]
  rw [hlift]
  have hsupport :
      tsupport (fun x => lift u.1 x + lift v.1 x) ⊆
        tsupport (lift u.1) ∪ tsupport (lift v.1) := by
    apply closure_minimal ?_
      ((isClosed_tsupport _).union (isClosed_tsupport _))
    intro x hx
    by_contra hn
    have hzeroU : lift u.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport (by
        intro hxU
        exact hn (Or.inl hxU))
    have hzeroV : lift v.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport (by
        intro hxV
        exact hn (Or.inr hxV))
    exact hx (by simp [hzeroU, hzeroV])
  intro x hx
  rcases hsupport hx with hxU | hxV
  · exact hu hxU
  · exact hv hxV

/-- A genuinely narrow SUM controls the actual positive mixed interaction.
The 32/25 coercive gain for the SUM is retained as an explicit term. -/
theorem actual_mixed_re_upper_of_narrow_sum
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hw : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt
      (addPacket u v) center) :
    2 * (B u v).re +
      (32 / 25 : ℝ) * energy (addPacket u v).1 ≤
      -(B u u).re - (B v v).re := by
  have hdiag :=
    AEGIS.RHNarrowDiagonalUpgradeV2.narrow_diagonal_32_over_25_v2
      (addPacket u v) center hw
  have hgram :=
    AEGIS.RHCofinalSchurAdapterV1.actual_two_block_gram_coefficients u v
  linarith

/-- On a common certified narrow log-window, both u+v and u-v are
admissible for the existing REAL Weil diagonal inequality. Their
polarization gives a true bound on the actual mixed interaction B(u,v)
with no assumed cross-term inequality and no global RH sign premise. -/
theorem actual_mixed_re_abs_of_common_narrow_window
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hu : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt u center)
    (hv : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt v center) :
    |(B u v).re| ≤ (-(B u u).re - (B v v).re) / 2 := by
  have hwPlus := narrow_width_add u v center hu hv
  have hwMinus : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt
      (addPacket u (scalePacket (-1 : ℂ) v)) center :=
    narrow_width_add u (scalePacket (-1 : ℂ) v) center hu
      (narrow_width_scale v (-1 : ℂ) center hv)
  have hplus := actual_mixed_re_upper_of_narrow_sum u v center hwPlus
  have hminus :=
    actual_mixed_re_upper_of_narrow_sum
      u (scalePacket (-1 : ℂ) v) center hwMinus
  have hcross :
      (B u (scalePacket (-1 : ℂ) v)).re = -(B u v).re := by
    rw [B_scale_right]
    simp
  have hdiag :
      (B (scalePacket (-1 : ℂ) v) (scalePacket (-1 : ℂ) v)).re =
        (B v v).re := by
    rw [B_scale_left, B_scale_right]
    simp
  rw [hcross, hdiag] at hminus
  have heplus :
      0 ≤ (32 / 25 : ℝ) * energy (addPacket u v).1 :=
    mul_nonneg (by norm_num) (energy_nonnegative _)
  have heminus :
      0 ≤ (32 / 25 : ℝ) *
        energy (addPacket u (scalePacket (-1 : ℂ) v)).1 :=
    mul_nonneg (by norm_num) (energy_nonnegative _)
  apply abs_le.mpr
  constructor <;> linarith

end AEGIS.RHActualMixedDefectV1

#print axioms AEGIS.RHActualMixedDefectV1.quantitative_lower_of_diagonal
#print axioms AEGIS.RHActualMixedDefectV1.every_packet_actual_mixed_defect_bound
#print axioms AEGIS.RHActualMixedDefectV1.actual_zero_sign_of_paid_mixed_defect
#print axioms AEGIS.RHActualMixedDefectV1.narrow_width_scale
#print axioms AEGIS.RHActualMixedDefectV1.narrow_width_add
#print axioms AEGIS.RHActualMixedDefectV1.actual_mixed_re_upper_of_narrow_sum
#print axioms AEGIS.RHActualMixedDefectV1.actual_mixed_re_abs_of_common_narrow_window
