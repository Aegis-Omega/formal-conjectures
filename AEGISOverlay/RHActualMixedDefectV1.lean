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
import RHWindowNineOver64GlobalizationV14
import WeilFinalSignTranslationBoundV10
import WeilSeparatedArchBridgeV31

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
    simp only [AEGIS.RHKreinFactorV13.lift, scalePacket]
    ring
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
    simp only [AEGIS.RHKreinFactorV13.lift, addPacket, mul_add]
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


/-- A bound on the entire complex genuine Weil mixed entry. Apply the
same real-polarization lemma to u and i v to control its imaginary part;
then use the pinned Mathlib complex norm inequality. This controls B,
not a surrogate or its real projection only, for pairs sharing a
certified width-1/64 log window. -/
theorem actual_mixed_norm_le_of_common_narrow_window
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hu : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt u center)
    (hv : AEGIS.RHNarrowDiagonalUpgradeV2.WidthOneSixtyFourAt v center) :
    ‖B u v‖ ≤ -(B u u).re - (B v v).re := by
  have hreal :=
    actual_mixed_re_abs_of_common_narrow_window u v center hu hv
  have himag :=
    actual_mixed_re_abs_of_common_narrow_window
      u (scalePacket Complex.I v) center hu
      (narrow_width_scale v Complex.I center hv)
  have hrot :
      (B u (scalePacket Complex.I v)).re = (B u v).im := by
    rw [B_scale_right]
    simp [Complex.mul_re]
  have hdiag :
      (B (scalePacket Complex.I v) (scalePacket Complex.I v)).re =
        (B v v).re := by
    rw [B_scale_left, B_scale_right]
    simp
  rw [hrot, hdiag] at himag
  have htri := Complex.norm_le_abs_re_add_abs_im (B u v)
  linarith


/-! ## Source-locked radius 9/64 coercive mixed-term bridge

This uses the original V14 rational moment gain, not a proxy positivity
hypothesis. The mixed B identity is exact. The sum's moment and 9/64
window membership are explicit, not silently assumed. -/

open AEGIS.WeilThreeBlockTranslatedPacketsV22

theorem actual_nine_over_64_mixed_re_upper
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hm : WeilMomentConditionsV1 (addPacket u v))
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt (addPacket u v) (9 / 64) center) :
    2 * (B u v).re +
      (1 / 10 : ℝ) * energy (addPacket u v).1 ≤
      -(B u u).re - (B v v).re := by
  have hcoercive :=
    AEGIS.RHWindowNineOver64GlobalizationV14.nine_over_64_coercive
      (addPacket u v) center hw hm
  change (B (addPacket u v) (addPacket u v)).re ≤
    -(1 / 10 : ℝ) * energy (addPacket u v).1 at hcoercive
  have hgram :=
    AEGIS.RHCofinalSchurAdapterV1.actual_two_block_gram_coefficients u v
  linarith

theorem actual_nine_over_64_mixed_re_abs
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hmp : WeilMomentConditionsV1 (addPacket u v))
    (hwp : AEGIS.RHDyadicDiagonalV13.HalfWidthAt (addPacket u v) (9 / 64) center)
    (hmm : WeilMomentConditionsV1
      (addPacket u (scalePacket (-1 : ℂ) v)))
    (hwm : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (addPacket u (scalePacket (-1 : ℂ) v)) (9 / 64) center) :
    |(B u v).re| ≤ (-(B u u).re - (B v v).re) / 2 := by
  have hplus := actual_nine_over_64_mixed_re_upper u v center hmp hwp
  have hminus := actual_nine_over_64_mixed_re_upper
    u (scalePacket (-1 : ℂ) v) center hmm hwm
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
  have heplus : 0 ≤ energy (addPacket u v).1 := energy_nonnegative _
  have heminus :
      0 ≤ energy (addPacket u (scalePacket (-1 : ℂ) v)).1 :=
    energy_nonnegative _
  apply abs_le.mpr
  constructor <;> linarith


/-- Actual COMPLEX mixed coefficient at half-width 9/64.
The caller supplies moment/centered-window witnesses for the four actual
polarized sums u+v, u-v, u+i v and u-i v. None is an assumption about
B itself; no universal cofinal row bound is inferred from this theorem. -/
theorem actual_nine_over_64_mixed_norm_le
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hmp : WeilMomentConditionsV1 (addPacket u v))
    (hwp : AEGIS.RHDyadicDiagonalV13.HalfWidthAt (addPacket u v) (9 / 64) center)
    (hmm : WeilMomentConditionsV1
      (addPacket u (scalePacket (-1 : ℂ) v)))
    (hwm : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (addPacket u (scalePacket (-1 : ℂ) v)) (9 / 64) center)
    (hmi : WeilMomentConditionsV1
      (addPacket u (scalePacket Complex.I v)))
    (hwi : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (addPacket u (scalePacket Complex.I v)) (9 / 64) center)
    (hmni : WeilMomentConditionsV1
      (addPacket u (scalePacket (-Complex.I) v)))
    (hwni : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (addPacket u (scalePacket (-Complex.I) v)) (9 / 64) center) :
    ‖B u v‖ ≤ -(B u u).re - (B v v).re := by
  have hreal :=
    actual_nine_over_64_mixed_re_abs u v center hmp hwp hmm hwm
  have hiplus :=
    actual_nine_over_64_mixed_re_upper
      u (scalePacket Complex.I v) center hmi hwi
  have himinus :=
    actual_nine_over_64_mixed_re_upper
      u (scalePacket (-Complex.I) v) center hmni hwni
  have hcrossi :
      (B u (scalePacket Complex.I v)).re = (B u v).im := by
    rw [B_scale_right]
    simp [Complex.mul_re]
  have hcrossni :
      (B u (scalePacket (-Complex.I) v)).re = -(B u v).im := by
    rw [B_scale_right]
    simp [Complex.mul_re]
  have hdiagi :
      (B (scalePacket Complex.I v) (scalePacket Complex.I v)).re =
        (B v v).re := by
    rw [B_scale_left, B_scale_right]
    simp
  have hdiagn :
      (B (scalePacket (-Complex.I) v)
        (scalePacket (-Complex.I) v)).re = (B v v).re := by
    rw [B_scale_left, B_scale_right]
    simp
  rw [hcrossi, hdiagi] at hiplus
  rw [hcrossni, hdiagn] at himinus
  have hei : 0 ≤ energy (addPacket u (scalePacket Complex.I v)).1 :=
    energy_nonnegative _
  have heni : 0 ≤ energy (addPacket u (scalePacket (-Complex.I) v)).1 :=
    energy_nonnegative _
  have himag :
      |(B u v).im| ≤ (-(B u u).re - (B v v).re) / 2 := by
    apply abs_le.mpr
    constructor <;> linarith
  have htri := Complex.norm_le_abs_re_add_abs_im (B u v)
  linarith


/-! ## Exact counterpart on an arbitrary finite *common local* window

Unlike an entrywise Q16.16 majorant, this proof retains the signed
off-diagonal contributions and applies the existing *actual* strong
fine-window diagonal inequality to the whole packet sum.  The
summands may have distinct shapes and energies, but all share a
single center and a half-width 1/256 in log coordinates.

The exact counterpart concerns the full contracted Gram and its
off-diagonal defect; it does not assert a pairwise norm bound for
remote support windows or a global RH theorem. -/

open AEGIS.RHRationalNinePacketPrimeWindowV1
open AEGIS.RHGramExpansionV13

/-- A complex scalar does not enlarge a fine log-support window. -/
theorem fine_width_scale
    (u : WeilCompactSmoothGV1) (z : ℂ) (center : ℝ)
    (hu : WidthOneOneTwentyEightAt u center) :
    WidthOneOneTwentyEightAt (scalePacket z u) center := by
  change tsupport (lift (scalePacket z u).1) ⊆
    Icc (center - 1 / 256) (center + 1 / 256)
  change tsupport (lift u.1) ⊆
    Icc (center - 1 / 256) (center + 1 / 256) at hu
  have hlift : lift (scalePacket z u).1 =
      (fun x => z * lift u.1 x) := by
    funext x
    simp only [AEGIS.RHKreinFactorV13.lift, scalePacket]
    ring
  rw [hlift]
  have hs : tsupport (fun x => z * lift u.1 x) ⊆
      tsupport (lift u.1) := by
    apply closure_minimal ?_ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    have hzero : lift u.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport hn
    exact hx (by simp [hzero])
  exact hs.trans hu

/-- Two fine packets centered on the same finite window remain fine
after exact addition, independently of their relative energies. -/
theorem fine_width_add
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hu : WidthOneOneTwentyEightAt u center)
    (hv : WidthOneOneTwentyEightAt v center) :
    WidthOneOneTwentyEightAt (addPacket u v) center := by
  change tsupport (lift (addPacket u v).1) ⊆
    Icc (center - 1 / 256) (center + 1 / 256)
  change tsupport (lift u.1) ⊆
    Icc (center - 1 / 256) (center + 1 / 256) at hu
  change tsupport (lift v.1) ⊆
    Icc (center - 1 / 256) (center + 1 / 256) at hv
  have hlift : lift (addPacket u v).1 =
      (fun x => lift u.1 x + lift v.1 x) := by
    funext x
    simp only [AEGIS.RHKreinFactorV13.lift, addPacket, mul_add]
  rw [hlift]
  have hs :
      tsupport (fun x => lift u.1 x + lift v.1 x) ⊆
        tsupport (lift u.1) ∪ tsupport (lift v.1) := by
    apply closure_minimal ?_
      ((isClosed_tsupport _).union (isClosed_tsupport _))
    intro x hx
    by_contra hn
    have hu0 : lift u.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport (by
        intro hxU
        exact hn (Or.inl hxU))
    have hv0 : lift v.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport (by
        intro hxV
        exact hn (Or.inr hxV))
    exact hx (by simp [hu0, hv0])
  intro x hx
  rcases hs hx with hxU | hxV
  · exact hu hxU
  · exact hv hxV

/-- Any finite complex linear combination of arbitrary *different*
fine packets stays on their common window. This is not a theorem
about translates with different centers. -/
theorem fine_width_packetSum :
    ∀ (n : ℕ)
      (z : Fin (n + 1) → ℂ)
      (gs : Fin (n + 1) → WeilCompactSmoothGV1)
      (center : ℝ),
      (∀ i, WidthOneOneTwentyEightAt (gs i) center) →
      WidthOneOneTwentyEightAt (packetSum z gs) center := by
  intro n
  induction n with
  | zero =>
      intro z gs center hwin
      change WidthOneOneTwentyEightAt
        (scalePacket (z 0) (gs 0)) center
      exact fine_width_scale (gs 0) (z 0) center (hwin 0)
  | succ n ih =>
      intro z gs center hwin
      change WidthOneOneTwentyEightAt
        (addPacket
          (packetSum (fun i : Fin (n + 1) => z i.castSucc)
            (fun i : Fin (n + 1) => gs i.castSucc))
          (scalePacket (z (Fin.last (n + 1)))
            (gs (Fin.last (n + 1))))) center
      exact fine_width_add _ _ center
        (ih (fun i => z i.castSucc) (fun i => gs i.castSucc)
          center (fun i => hwin i.castSucc))
        (fine_width_scale _ _ center (hwin (Fin.last (n + 1))))

/-- The actual full signed Weil Gram on any common fine finite window
has the *exact* rational coercivity, for arbitrary coefficients. The
off-diagonal cancellations are not replaced by norm majorants. -/
theorem fine_local_exact_counterpart
    (n : ℕ) (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) (center : ℝ)
    (hwin : ∀ i, WidthOneOneTwentyEightAt (gs i) center) :
    (5671 / 3200 : ℝ) * energy (packetSum z gs).1 ≤
      -(B (packetSum z gs) (packetSum z gs)).re := by
  exact AEGIS.RHFineDiagonalUpgradeV3.fine_diagonal_5671_over_3200_v3
    (packetSum z gs) center
    (fine_width_packetSum n z gs center hwin)

/-- The outward-rounded *opposite-sign* Q16.16 companion to the exact
local finite-window proof. Rounding the positive diagonal gain down
cannot change the direction of this inequality. -/
theorem fine_local_q16_counterpart
    (n : ℕ) (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) (center : ℝ)
    (hwin : ∀ i, WidthOneOneTwentyEightAt (gs i) center) :
    (116142 / 65536 : ℝ) * energy (packetSum z gs).1 ≤
      -(B (packetSum z gs) (packetSum z gs)).re := by
  have hE : 0 ≤ energy (packetSum z gs).1 :=
    energy_nonnegative _
  have hround : (116142 / 65536 : ℝ) ≤ 5671 / 3200 := by
    norm_num
  exact (mul_le_mul_of_nonneg_right hround hE).trans
    (fine_local_exact_counterpart n z gs center hwin)

/-- Signed (not absolute) upper bound for the exact actual mixed defect
of an arbitrary finite family on one common fine window.  This is the
opposite-side counterpart of the global Q16.16 pairwise budget. -/
theorem fine_local_exact_mixed_defect_opposite
    (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : ℝ)
    (hwin : ∀ i, WidthOneOneTwentyEightAt (gs i) center) :
    actualMixedDefect n gs ≤
      -((5671 / 3200 : ℝ) *
        energy (packetSum (fun _ => (1 : ℂ)) gs).1) -
      ∑ i, (B (gs i) (gs i)).re := by
  have hcoercive := fine_local_exact_counterpart n
    (fun _ => (1 : ℂ)) gs center hwin
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
        (packetSum (fun _ => (1 : ℂ)) gs)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [B_packetSum]
    simp
  rw [hgram] at hcoercive
  unfold actualMixedDefect
  linarith


/-! ## Nearby but distinct fine windows: an unconditional actual-B bridge

If two fine atoms have individual log half-width 1/256 and their
centers have distance at most 35/128, their union fits exactly inside
one 9/64 half-width interval centered at their midpoint.  The pinned
9/64 analytic coercivity then bounds the genuine mixed Weil
coefficient of the two DIFFERENT atoms.

This is a finite-range bridge, NOT a claim for arbitrarily distant
windows or a universal Q16.16 producer. -/

open AEGIS.WeilFinalSignTranslationBoundV10

/-- Geometric recentering of a genuinely fine source packet: all
constants are exact rationals (1/256 + (35/128)/2 = 9/64). -/
theorem fine_width_into_nine_midpoint
    (u : WeilCompactSmoothGV1) (a b : ℝ)
    (hu : WidthOneOneTwentyEightAt u a)
    (hab : |a - b| ≤ (35 / 128 : ℝ)) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      u (9 / 64) ((a + b) / 2) := by
  change tsupport (lift u.1) ⊆
    Icc ((a + b) / 2 - 9 / 64) ((a + b) / 2 + 9 / 64)
  change tsupport (lift u.1) ⊆
    Icc (a - 1 / 256) (a + 1 / 256) at hu
  intro t ht
  obtain ⟨hlo, hhi⟩ := hu ht
  obtain ⟨hablo, habhi⟩ := abs_le.mp hab
  constructor <;> dsimp only [Set.mem_Icc] <;> linarith

/-- Multiplication by any complex scalar preserves the common 9/64
logarithmic support; the proof is about the genuine source packet. -/
theorem nine_width_scale
    (u : WeilCompactSmoothGV1) (z : ℂ) (center : ℝ)
    (hu : AEGIS.RHDyadicDiagonalV13.HalfWidthAt u (9 / 64) center) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (scalePacket z u) (9 / 64) center := by
  change tsupport (lift (scalePacket z u).1) ⊆
    Icc (center - 9 / 64) (center + 9 / 64)
  change tsupport (lift u.1) ⊆
    Icc (center - 9 / 64) (center + 9 / 64) at hu
  have hlift : lift (scalePacket z u).1 =
      (fun x => z * lift u.1 x) := by
    funext x
    simp only [AEGIS.RHKreinFactorV13.lift, scalePacket]
    ring
  rw [hlift]
  have hs : tsupport (fun x => z * lift u.1 x) ⊆
      tsupport (lift u.1) := by
    apply closure_minimal ?_ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    have hz : lift u.1 x = 0 := image_eq_zero_of_notMem_tsupport hn
    exact hx (by simp [hz])
  exact hs.trans hu

/-- Adding packets with different shapes preserves their shared
9/64 local support without assuming their mixed Weil sign. -/
theorem nine_width_add
    (u v : WeilCompactSmoothGV1) (center : ℝ)
    (hu : AEGIS.RHDyadicDiagonalV13.HalfWidthAt u (9 / 64) center)
    (hv : AEGIS.RHDyadicDiagonalV13.HalfWidthAt v (9 / 64) center) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (addPacket u v) (9 / 64) center := by
  change tsupport (lift (addPacket u v).1) ⊆
    Icc (center - 9 / 64) (center + 9 / 64)
  change tsupport (lift u.1) ⊆
    Icc (center - 9 / 64) (center + 9 / 64) at hu
  change tsupport (lift v.1) ⊆
    Icc (center - 9 / 64) (center + 9 / 64) at hv
  have hlift : lift (addPacket u v).1 =
      (fun x => lift u.1 x + lift v.1 x) := by
    funext x
    simp only [AEGIS.RHKreinFactorV13.lift, addPacket, mul_add]
  rw [hlift]
  have hs :
      tsupport (fun x => lift u.1 x + lift v.1 x) ⊆
        tsupport (lift u.1) ∪ tsupport (lift v.1) := by
    apply closure_minimal ?_
      ((isClosed_tsupport _).union (isClosed_tsupport _))
    intro x hx
    by_contra hn
    have hu0 : lift u.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport (by
        intro hxU
        exact hn (Or.inl hxU))
    have hv0 : lift v.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport (by
        intro hxV
        exact hn (Or.inr hxV))
    exact hx (by simp [hu0, hv0])
  intro x hx
  rcases hs hx with hxU | hxV
  · exact hu hxU
  · exact hv hxV

/-- Nearby distinct local packets have a common 9/64 window:
there is no assumption that they are translates of a fixed seed. -/
theorem nearby_fine_pair_shared_nine_window
    (u v : WeilCompactSmoothGV1) (a b : ℝ)
    (hu : WidthOneOneTwentyEightAt u a)
    (hv : WidthOneOneTwentyEightAt v b)
    (hab : |a - b| ≤ (35 / 128 : ℝ)) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt u (9 / 64) ((a + b) / 2) ∧
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt v (9 / 64) ((a + b) / 2) := by
  constructor
  · exact fine_width_into_nine_midpoint u a b hu hab
  · have hba : |b - a| ≤ (35 / 128 : ℝ) := by
      simpa only [abs_sub_comm] using hab
    simpa only [add_comm] using
      (fine_width_into_nine_midpoint v b a hv hba)

/-- GENUINE signed mixed-term estimate for two DISTINCT fine-window
Weil packets, from pinned unconditional radius-9/64 coercivity.
Both moment annihilations are propagated through addition. -/
theorem nearby_fine_pair_actual_mixed_signed
    (u v : WeilCompactSmoothGV1) (a b : ℝ)
    (hmu : WeilMomentConditionsV1 u)
    (hmv : WeilMomentConditionsV1 v)
    (hu : WidthOneOneTwentyEightAt u a)
    (hv : WidthOneOneTwentyEightAt v b)
    (hab : |a - b| ≤ (35 / 128 : ℝ)) :
    2 * (B u v).re + (1 / 10 : ℝ) * energy (addPacket u v).1 ≤
      -(B u u).re - (B v v).re := by
  obtain ⟨hwu, hwv⟩ := nearby_fine_pair_shared_nine_window
    u v a b hu hv hab
  exact actual_nine_over_64_mixed_re_upper u v ((a + b) / 2)
    (momentConditions_addPacket_v10 u v hmu hmv)
    (nine_width_add u v ((a + b) / 2) hwu hwv)

/-- The same signed actual-Weil estimate, conservatively rounded
down to Q16.16. No float computation or postulated inequality. -/
theorem nearby_fine_pair_actual_mixed_q16
    (u v : WeilCompactSmoothGV1) (a b : ℝ)
    (hmu : WeilMomentConditionsV1 u)
    (hmv : WeilMomentConditionsV1 v)
    (hu : WidthOneOneTwentyEightAt u a)
    (hv : WidthOneOneTwentyEightAt v b)
    (hab : |a - b| ≤ (35 / 128 : ℝ)) :
    2 * (B u v).re +
      (6553 / 65536 : ℝ) * energy (addPacket u v).1 ≤
      -(B u u).re - (B v v).re := by
  have he : 0 ≤ energy (addPacket u v).1 := energy_nonnegative _
  have hround : (6553 / 65536 : ℝ) ≤ 1 / 10 := by norm_num
  have hprod := mul_le_mul_of_nonneg_right hround he
  have hexact := nearby_fine_pair_actual_mixed_signed u v a b
    hmu hmv hu hv hab
  linarith

/-- Complex mixed norm for nearby DIFFERENT fine windows, with all
four exact polarization tests supplied by the same geometric support
and preserved moment conditions.  No cross estimate is an input. -/
theorem nearby_fine_pair_actual_mixed_norm
    (u v : WeilCompactSmoothGV1) (a b : ℝ)
    (hmu : WeilMomentConditionsV1 u)
    (hmv : WeilMomentConditionsV1 v)
    (hu : WidthOneOneTwentyEightAt u a)
    (hv : WidthOneOneTwentyEightAt v b)
    (hab : |a - b| ≤ (35 / 128 : ℝ)) :
    ‖B u v‖ ≤ -(B u u).re - (B v v).re := by
  obtain ⟨hwu, hwv⟩ := nearby_fine_pair_shared_nine_window
    u v a b hu hv hab
  let c : ℝ := (a + b) / 2
  have hpolarM (z : ℂ) :
      WeilMomentConditionsV1 (addPacket u (scalePacket z v)) :=
    momentConditions_addPacket_v10 u (scalePacket z v) hmu
      (momentConditions_scalePacket_v10 z v hmv)
  have hpolarW (z : ℂ) :
      AEGIS.RHDyadicDiagonalV13.HalfWidthAt
        (addPacket u (scalePacket z v)) (9 / 64) c :=
    nine_width_add u (scalePacket z v) c hwu
      (nine_width_scale v z c hwv)
  exact actual_nine_over_64_mixed_norm_le u v c
    (momentConditions_addPacket_v10 u v hmu hmv)
    (nine_width_add u v c hwu hwv)
    (hpolarM (-1)) (hpolarW (-1))
    (hpolarM Complex.I) (hpolarW Complex.I)
    (hpolarM (-Complex.I)) (hpolarW (-Complex.I))


/-! ## Actual distant-window ARCH control for unequal packet shapes

The existing separated support theorem bounds the real arithmetic
Archimedean integral if supplied a logCross envelope.  Here we prove
that envelope for two arbitrary, distinct packets from the exact L²
isometry, and discharge all geometric hypotheses by padding the
individual fine windows to radius 1/64.

This is a REAL ANALYTIC PRODUCER for the distant Arch term, not a
complete bound on B: the von Mangoldt prime contribution remains.
-/

open AEGIS.WeilSeparatedArchBridgeV31
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilLogCoordinateIsometryV21

/-- General distinct-packet mixed correlation, with no shared seed:
the energy bound is the arithmetic mean, avoiding sqrt/CS obligations. -/
theorem distinct_logCross_norm_le_mean_energy
    (p q : WeilCompactSmoothGV1) (u : ℝ) :
    ‖logCrossV28 p q u‖ ≤
      (energy p.1 + energy q.1) / 2 := by
  let F : ℝ → ℂ := fun v =>
    logLift p.1 (v + u) * conj (logLift q.1 v)
  let M : ℝ → ℝ := fun v =>
    (1 / 2 : ℝ) *
      (‖logLift p.1 (v + u)‖ ^ 2 + ‖logLift q.1 v‖ ^ 2)
  have hM : Integrable M := by
    unfold M
    exact ((shifted_logLift_sq_integrable_v25 p u).add
      (logLift_sq_integrable_v25 q)).const_mul (1 / 2 : ℝ)
  have hmeas : AEStronglyMeasurable F := by
    exact (((logLift_continuous p).comp (by fun_prop)).aestronglyMeasurable.mul
      ((continuous_conj.comp (logLift_continuous q)).aestronglyMeasurable))
  have hpoint : ∀ v : ℝ, ‖F v‖ ≤ M v := by
    intro v
    have hab :
        ‖logLift p.1 (v + u)‖ * ‖logLift q.1 v‖ ≤
        (1 / 2 : ℝ) *
          (‖logLift p.1 (v + u)‖ ^ 2 + ‖logLift q.1 v‖ ^ 2) := by
      nlinarith [sq_nonneg (‖logLift p.1 (v + u)‖ - ‖logLift q.1 v‖)]
    simpa [F, M, norm_mul, norm_conj] using hab
  have hF : Integrable F :=
    hM.mono' hmeas (Filter.Eventually.of_forall hpoint)
  calc
    ‖logCrossV28 p q u‖ = ‖∫ v : ℝ, F v‖ := rfl
    _ ≤ ∫ v : ℝ, ‖F v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, M v := integral_mono hF.norm hM hpoint
    _ = (1 / 2 : ℝ) *
        ((∫ v : ℝ, ‖logLift p.1 (v + u)‖ ^ 2) +
           ∫ v : ℝ, ‖logLift q.1 v‖ ^ 2) := by
          unfold M
          rw [integral_const_mul, integral_add
            (shifted_logLift_sq_integrable_v25 p u)
            (logLift_sq_integrable_v25 q)]
    _ = (energy p.1 + energy q.1) / 2 := by
          rw [shifted_logLift_sq_integral_v25,
            logLift_energy_eq_packet_energy]
          ring

/-- The actual separated ARCH term for arbitrary distinct fine local
Weil atoms, with an exact gap threshold log 2 and no postulated cross
correlation bound. The sum of energies is explicit. -/
theorem distinct_fine_far_arch_norm_le
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hgap : Real.log 2 ≤ b - a) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤
      (1 / 200 : ℝ) * (energy p.1 + energy q.1) := by
  let E : ℝ := (energy p.1 + energy q.1) / 2
  have hEp : 0 ≤ energy p.1 := energy_nonnegative p.1
  have hEq : 0 ≤ energy q.1 := energy_nonnegative q.1
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hlogp :
      LogSupportIn p (a - 1 / 64) (a + 1 / 64) := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := hp ht
    exact ⟨by linarith, by linarith⟩
  have hlogq :
      LogSupportIn q (b - 1 / 64) (b + 1 / 64) := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := hq ht
    exact ⟨by linarith, by linarith⟩
  have harch := separated_arch_norm_bound
    p q (a - 1 / 64) (a + 1 / 64)
    (b - 1 / 64) (b + 1 / 64) E
    hlogp hlogq (by linarith) (by
      norm_num [CorrelationSupportDifferenceWidthV31]
      ring) hm hE
    (fun u => distinct_logCross_norm_le_mean_energy p q u)
  dsimp [E] at harch
  convert harch using 1 <;> ring


/-- The exact off-diagonal B form of two distant, different fine atoms:
the term at 1 is actually zero by disjoint logarithmic supports. -/
theorem distinct_fine_far_mixed_one_zero
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hgap : Real.log 2 ≤ b - a) :
    mixed p q 1 = 0 := by
  have hlog : logCrossV28 p q 0 = 0 := by
    apply logCross_zero_outside p q
      (a - 1 / 256) (a + 1 / 256)
      (b - 1 / 256) (b + 1 / 256) 0 hp hq
    right
    linarith [log_two_gt_one_thirty_two]
  have h := logCross_eq_mixed_v28 p q 0
  simp only [zero_div, Real.exp_zero, Complex.ofReal_one, one_mul] at h
  exact h.symm.trans hlog

/-- Exact decomposition of the FULL distant Weil B interaction.  This
is the established ARCH bound plus the genuine remaining von Mangoldt
prime contribution, not an assumed mixed-Weil estimate and not a
claim that remote prime contributions vanish. -/
theorem distinct_fine_far_actual_B_norm_le_prime_plus_arch
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hgap : Real.log 2 ≤ b - a) :
    ‖B p q‖ ≤ ‖WeilPrimeSumV1 (mixed p q)‖ +
      (1 / 200 : ℝ) * (energy p.1 + energy q.1) := by
  have hzero := distinct_fine_far_mixed_one_zero p q a b hp hq hgap
  have harch := distinct_fine_far_arch_norm_le p q a b hp hq hm hgap
  have heq : B p q =
      WeilPrimeSumV1 (mixed p q) +
      WeilArchimedeanIntegralV1 (mixed p q) := by
    unfold B WeilExplicitRightSideV1
    rw [hzero]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add_left harch _)


/-! ## Moment-zero removal of the distant rank-one Arch kernel

Exact reuse of the source-pinned separated Arch integral identity,
support localization and weighted Mellin-moment annihilation.  Unlike
the old 1/200 energy estimate, the remaining kernel decays as
exp(-5δ/2)/(1-exp(-2δ)).  The von Mangoldt prime sum is not changed.
-/

open Set Function MeasureTheory Complex
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilSeparatedArchBridgeV31
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilLogCoordinateIsometryV21

theorem separated_arch_decay_bound
    (p q : WeilCompactSmoothGV1) (plo phi qlo qhi E : ℝ)
    (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi)
    (hgap : Real.log 2 - 1 / 32 ≤ qlo - phi)
    (δ : ℝ) (hδ : 0 < δ) (hδgap : δ ≤ qlo - phi)
    (hwidth : (qhi - plo) - (qlo - phi) = CorrelationSupportDifferenceWidthV31)
    (hm : WeilMomentConditionsV1 p) (hE : 0 ≤ E)
    (hR : ∀ u : ℝ, ‖logCrossV28 p q u‖ ≤ E) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤
      (1 / 16 : ℝ) *
        (Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ))) * E := by
  let R : ℝ := Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ))
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    exact (div_pos (Real.exp_pos _) (sub_pos.mpr
      (Real.exp_lt_one_iff.mpr (by linarith)))).le
  let lo := qlo - phi
  let hi := qhi - plo
  let K : ℝ → ℝ := fun u => Real.exp (-u / 2) / (1 - Real.exp (-2 * u))
  let F : ℝ → ℂ := fun u => (K u : ℂ) * logCrossV28 p q (-u)
  let M : ℝ → ℂ := fun u => (Real.exp (-u / 2) : ℂ) * logCrossV28 p q (-u)
  have hlo : 0 < lo := by
    dsimp [lo]
    linarith [log_two_gt_one_thirty_two]
  have hzero (u : ℝ) (hu : u ∉ Icc lo hi) : logCrossV28 p q (-u) = 0 := by
    apply logCross_zero_outside p q plo phi qlo qhi (-u) hp hq
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
    rw [separated_arch_eq_log_kernel p q plo phi qlo qhi hp hq (by dsimp [lo] at hlo; linarith)]
    exact hFpos.trans hFfull.symm
  have hMfull : (∫ u, M u) = 0 := by
    have ht := integral_neg_eq_self
      (fun u : ℝ => (Real.exp (u / 2) : ℂ) * logCrossV28 p q u) volume
    exact ht.trans (logCross_plus_moment_zero p q plo phi qlo qhi hp hq hm)
  have hMzero : (∫ u in Icc lo hi, M u) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (f := M) (s := Icc lo hi)
      (fun u hu => by simp [M, hzero u hu])]
    exact hMfull
  have hMc : Continuous M := by
    dsimp [M]
    exact (by fun_prop : Continuous (fun u : ℝ => (Real.exp (-u / 2) : ℂ))).mul
      ((logCross_continuous p q).comp continuous_neg)
  have hKc : ContinuousOn K (Icc lo hi) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    have hup : 0 < u := lt_of_lt_of_le hlo hu.1
    exact ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have hFc : ContinuousOn F (Icc lo hi) :=
    (Complex.continuous_ofReal.comp_continuousOn hKc).mul
      (((logCross_continuous p q).comp continuous_neg).continuousOn)
  have hcancel : (∫ u in Icc lo hi, F u) =
      ∫ u in Icc lo hi, F u - M u := by
    rw [integral_sub hFc.integrableOn_Icc hMc.integrableOn_Icc,
      hMzero, sub_zero]
  have hpoint (u : ℝ) (hu : u ∈ Icc lo hi) :
      ‖F u - M u‖ ≤ R * E := by
    have huPos : 0 < u := lt_of_lt_of_le hlo hu.1
    have hden : 0 < 1 - Real.exp (-2 * u) := by
      apply sub_pos.mpr
      exact Real.exp_lt_one_iff.mpr (by linarith)
    have hku : |K u - Real.exp (-u / 2)| ≤ R := by
      change |Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) -
        Real.exp (-u / 2)| ≤ R
      rw [AEGIS.WeilThreeBlockCrossAssemblyV30.arch_kernel_sub_rank_one u huPos]
      rw [abs_of_nonneg (div_nonneg (Real.exp_pos _).le hden.le)]
      exact AEGIS.WeilThreeBlockCrossAssemblyV30.arch_remainder_le_at_gap
        δ u hδ (hδgap.trans hu.1)
    have heq : F u - M u =
        (((K u - Real.exp (-u / 2)) : ℝ) : ℂ) * logCrossV28 p q (-u) := by
      dsimp [F, M]
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hku (hR (-u)) (norm_nonneg _) hRnonneg
  rw [harch, hcancel]
  calc
    ‖∫ u in Icc lo hi, F u - M u‖ ≤
        R * E * (volume.restrict (Icc lo hi)).real univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with u hu
      exact hpoint u hu
    _ = (1 / 16 : ℝ) *
      (Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ))) * E := by
      have hw : hi - lo = (1 / 16 : ℝ) := by
        simpa [CorrelationSupportDifferenceWidthV31] using hwidth
      simp [Measure.real, Real.volume_Icc, hw, R]
      <;> ring

/-- Actual distant ARCH bound after using the zero Mellin moment,
for different fine packets supported near centers a and b. The
right-hand side decreases exponentially with b-a. -/
theorem distinct_fine_far_arch_moment_decay
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hgap : Real.log 2 ≤ b - a) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤
      (1 / 32 : ℝ) *
        (Real.exp (-5 * ((b-a)-1/32) / 2) /
          (1 - Real.exp (-2 * ((b-a)-1/32)))) *
            (energy p.1 + energy q.1) := by
  let δ : ℝ := (b-a)-1/32
  let E : ℝ := (energy p.1 + energy q.1)/2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith [log_two_gt_one_thirty_two]
  have hE : 0 ≤ E := by
    dsimp [E]
    have hp0 := energy_nonnegative p.1
    have hq0 := energy_nonnegative q.1
    positivity
  have hlogp :
      LogSupportIn p (a - 1 / 64) (a + 1 / 64) := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := hp ht
    exact ⟨by linarith, by linarith⟩
  have hlogq :
      LogSupportIn q (b - 1 / 64) (b + 1 / 64) := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := hq ht
    exact ⟨by linarith, by linarith⟩
  have harch := separated_arch_decay_bound
    p q (a - 1 / 64) (a + 1 / 64)
      (b - 1 / 64) (b + 1 / 64) E
      hlogp hlogq (by linarith)
      δ hδ (by dsimp [δ]; ring)
      (by norm_num [CorrelationSupportDifferenceWidthV31]; ring)
      hm hE
      (fun u => distinct_logCross_norm_le_mean_energy p q u)
  dsimp [E, δ] at harch ⊢
  convert harch using 1 <;> ring


/-- The entire genuine distant Weil coefficient inherits the moment-zero
exponential Archimedean decay, *retaining* the von Mangoldt prime term.
This sharpens the constant 1/200 bound for sufficiently distant centers;
no bound for the remaining prime term is assumed or asserted. -/
theorem distinct_fine_far_actual_B_norm_le_prime_plus_moment_decay
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hgap : Real.log 2 ≤ b - a) :
    ‖B p q‖ ≤ ‖WeilPrimeSumV1 (mixed p q)‖ +
      (1 / 32 : ℝ) *
        (Real.exp (-5 * ((b-a)-1/32) / 2) /
          (1 - Real.exp (-2 * ((b-a)-1/32)))) *
            (energy p.1 + energy q.1) := by
  have hzero := distinct_fine_far_mixed_one_zero p q a b hp hq hgap
  have harch := distinct_fine_far_arch_moment_decay p q a b hp hq hm hgap
  have heq : B p q =
      WeilPrimeSumV1 (mixed p q) +
        WeilArchimedeanIntegralV1 (mixed p q) := by
    unfold B WeilExplicitRightSideV1
    rw [hzero]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add_left harch _)

/-- Convert an analytic estimate on the *prime part alone* into an
outward Q16.16 bound on the actual distant mixed Weil coefficient.
The source-pinned moment-zero Archimedean remainder is budgeted exactly,
not silently dropped. The prime estimate remains an explicit obligation. -/
theorem distinct_fine_far_actual_B_q16_of_prime_decay_budget
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (hgap : Real.log 2 ≤ b - a) (k : ℕ)
    (hprime :
      ‖WeilPrimeSumV1 (mixed p q)‖ ≤
        ((k : ℝ) / 65536 -
          (1 / 32 : ℝ) *
            (Real.exp (-5 * ((b-a)-1/32) / 2) /
              (1 - Real.exp (-2 * ((b-a)-1/32))))) *
          (energy p.1 + energy q.1)) :
    ‖B p q‖ ≤ ((k : ℝ) / 65536) *
      (energy p.1 + energy q.1) := by
  have h := distinct_fine_far_actual_B_norm_le_prime_plus_moment_decay
    p q a b hp hq hm hgap
  calc
    ‖B p q‖ ≤ ‖WeilPrimeSumV1 (mixed p q)‖ +
        (1 / 32 : ℝ) *
          (Real.exp (-5 * ((b-a)-1/32) / 2) /
            (1 - Real.exp (-2 * ((b-a)-1/32)))) *
              (energy p.1 + energy q.1) := h
    _ ≤ (((k : ℝ) / 65536 -
          (1 / 32 : ℝ) *
            (Real.exp (-5 * ((b-a)-1/32) / 2) /
              (1 - Real.exp (-2 * ((b-a)-1/32))))) *
          (energy p.1 + energy q.1)) +
        (1 / 32 : ℝ) *
          (Real.exp (-5 * ((b-a)-1/32) / 2) /
            (1 - Real.exp (-2 * ((b-a)-1/32)))) *
              (energy p.1 + energy q.1) :=
                add_le_add_right hprime _
    _ = ((k : ℝ) / 65536) * (energy p.1 + energy q.1) := by ring

end AEGIS.RHActualMixedDefectV1

#print axioms AEGIS.RHActualMixedDefectV1.quantitative_lower_of_diagonal
#print axioms AEGIS.RHActualMixedDefectV1.every_packet_actual_mixed_defect_bound
#print axioms AEGIS.RHActualMixedDefectV1.actual_zero_sign_of_paid_mixed_defect
#print axioms AEGIS.RHActualMixedDefectV1.narrow_width_scale
#print axioms AEGIS.RHActualMixedDefectV1.narrow_width_add
#print axioms AEGIS.RHActualMixedDefectV1.actual_mixed_re_upper_of_narrow_sum
#print axioms AEGIS.RHActualMixedDefectV1.actual_mixed_re_abs_of_common_narrow_window
#print axioms AEGIS.RHActualMixedDefectV1.actual_mixed_norm_le_of_common_narrow_window
#print axioms AEGIS.RHActualMixedDefectV1.actual_nine_over_64_mixed_re_upper
#print axioms AEGIS.RHActualMixedDefectV1.actual_nine_over_64_mixed_re_abs
#print axioms AEGIS.RHActualMixedDefectV1.actual_nine_over_64_mixed_norm_le

#print axioms AEGIS.RHActualMixedDefectV1.fine_width_scale
#print axioms AEGIS.RHActualMixedDefectV1.fine_width_add
#print axioms AEGIS.RHActualMixedDefectV1.fine_width_packetSum
#print axioms AEGIS.RHActualMixedDefectV1.fine_local_exact_counterpart
#print axioms AEGIS.RHActualMixedDefectV1.fine_local_q16_counterpart
#print axioms AEGIS.RHActualMixedDefectV1.fine_local_exact_mixed_defect_opposite

#print axioms AEGIS.RHActualMixedDefectV1.fine_width_into_nine_midpoint
#print axioms AEGIS.RHActualMixedDefectV1.nearby_fine_pair_shared_nine_window
#print axioms AEGIS.RHActualMixedDefectV1.nearby_fine_pair_actual_mixed_signed
#print axioms AEGIS.RHActualMixedDefectV1.nearby_fine_pair_actual_mixed_q16
#print axioms AEGIS.RHActualMixedDefectV1.nearby_fine_pair_actual_mixed_norm

#print axioms AEGIS.RHActualMixedDefectV1.distinct_logCross_norm_le_mean_energy
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_arch_norm_le

#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_mixed_one_zero
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_actual_B_norm_le_prime_plus_arch

#print axioms AEGIS.RHActualMixedDefectV1.separated_arch_decay_bound
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_arch_moment_decay
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_actual_B_norm_le_prime_plus_moment_decay
#print axioms AEGIS.RHActualMixedDefectV1.distinct_fine_far_actual_B_q16_of_prime_decay_budget
