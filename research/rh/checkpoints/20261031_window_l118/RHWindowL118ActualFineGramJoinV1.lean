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

import RHWindowL118ExhaustionV1
import AEGISOverlay.RHActualUniversalFineGramV1
import AEGISOverlay.RHOptimizedSchurGlobalJoinV1
import RHKreinMultiplicativeTransportV1

/-!
# AEGIS Ω: certified 11/8 window → actual finite Weil Gram signed budget

Reuses the existing unconditional L118 window certificate, actual finite fine
Gram decomposition, and exact signed-defect identity. Every real Weil mixed
entry is preserved, including prime-resonant pairs. The theorem is local:
its source packet must lie in a symmetric log window of half-width ≤ 11/16.
No universal-width positivity or unconditional RH is claimed.
-/

open Finset
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHWindowL118ActualFineGramJoinV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHGramExpansionV13

/-- A genuine fine Gram reconstruction whose entire signed off-diagonal
defect is paid by the previously certified window sign. This strengthens
the older 693/2000 alignment to the already proved 11/16 half-width. -/
theorem actual_signed_fine_gram_on_l118_window
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (L : ℝ) (hL : L ≤ 11 / 16)
    (hw : AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1 g L) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
      (center : Fin (n + 1) → ℝ),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re) ∧
      (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
        -(∑ i, (B (gs i) (gs i)).re) := by
  obtain ⟨n, gs, center, hmom, hdiag, hwidth, hpacket, hgram⟩ :=
    AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_with_support
      g hm
  have hwindow :
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 :=
    AEGIS.RHWindowL118ExhaustionV1.window_le_eleven_sixteenths hL g hm hw
  have hfull :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
         (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0 := by
    calc
      (B (packetSum (fun _ => (1 : ℂ)) gs)
         (packetSum (fun _ => (1 : ℂ)) gs)).re =
          (∑ i, ∑ j, B (gs i) (gs j)).re := by
            rw [B_packetSum]
            simp
      _ = (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re :=
        hgram.symm
      _ ≤ 0 := hwindow
  have hbudget :=
    (AEGIS.RHOptimizedSchurGlobalJoinV1.actual_signed_defect_iff_packet_nonpositive
      gs).mpr hfull
  exact ⟨n, gs, center, hmom, hdiag, hwidth, hpacket, hbudget⟩


/-! ## Cross-carrier fusion: all finite Weil decompositions, and every Krein cutoff

The original CvS L118 theorem concerns the actual source packet `g`.
These two statements carry its sign to two distinct existing exact carriers
without swapping source packets or omitting any signed mixed term.
-/

/-- For a fixed packet in the proved window, the genuine total signed mixed
budget holds for EVERY exact finite Weil reconstruction of that same packet.
No diagonal, pairwise bound, row sum, or partition-selection hypothesis. -/
theorem every_actual_finite_gram_sharp_signed_budget_on_l118_window
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (L : ℝ) (hL : L ≤ 11 / 16)
    (hw : AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1 g L)
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hg : g = packetSum (fun _ => (1 : ℂ)) gs) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
      -(∑ i, (B (gs i) (gs i)).re) := by
  have hwindow :
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 :=
    AEGIS.RHWindowL118ExhaustionV1.window_le_eleven_sixteenths hL g hm hw
  apply (AEGIS.RHOptimizedSchurGlobalJoinV1.actual_signed_defect_iff_packet_nonpositive
    gs).mpr
  rw [← hg]
  change (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0
  exact hwindow

/-- The same CvS window sign also pays the exact B(u,u)+2B(u,v)+B(v,v)
signed budget for the existing *actual* two-atom Krein reconstruction,
for EVERY smooth cutoff χ. Both atoms have the real Weil zero moments. -/
theorem actual_krein_two_block_signed_budget_on_l118_window
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (L : ℝ) (hL : L ≤ 11 / 16)
    (hw : AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1 g L)
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) :
    ∃ u v : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 u ∧
      WeilMomentConditionsV1 v ∧
      g = AEGIS.WeilMixedAlgebraV2.addPacket u v ∧
      0 ≤ -(B u u).re + 2 * (-(B u v).re) + -(B v v).re := by
  obtain ⟨u, v, hu, hv, hsum, hzero⟩ :=
    AEGIS.RHKreinMultiplicativeTransportV1.every_packet_actual_two_block_zero_quadratic
      g hm χ hχ
  have hwindow :
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 :=
    AEGIS.RHWindowL118ExhaustionV1.window_le_eleven_sixteenths hL g hm hw
  have hzero_nonnegative :
      0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
    (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      g hm).mp hwindow
  refine ⟨u, v, hu, hv, hsum, ?_⟩
  rw [hzero] at hzero_nonnegative
  exact hzero_nonnegative

end AEGIS.RHWindowL118ActualFineGramJoinV1

#print axioms AEGIS.RHWindowL118ActualFineGramJoinV1.actual_signed_fine_gram_on_l118_window
#print axioms AEGIS.RHWindowL118ActualFineGramJoinV1.every_actual_finite_gram_sharp_signed_budget_on_l118_window
#print axioms AEGIS.RHWindowL118ActualFineGramJoinV1.actual_krein_two_block_signed_budget_on_l118_window
