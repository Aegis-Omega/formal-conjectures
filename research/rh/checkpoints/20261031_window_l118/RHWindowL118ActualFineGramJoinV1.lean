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

end AEGIS.RHWindowL118ActualFineGramJoinV1

#print axioms AEGIS.RHWindowL118ActualFineGramJoinV1.actual_signed_fine_gram_on_l118_window
