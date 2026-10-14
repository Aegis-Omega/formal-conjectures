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
import AEGISOverlay.RHFiniteFinePartitionV1
import AEGISOverlay.RHActualMixedDefectV1

/-! All compact-support moment-zero Weil packets have an actual finite
fine coercive Gram decomposition. The finite smooth partition is
constructed, not supplied by the caller. All mixed entries are retained. -/

open Set Finset Complex
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHActualUniversalFineGramV1

open AEGIS.WeilMixedAlgebraV2 AEGIS.WeilDisjointEnergyV2
open AEGIS.RHGramExpansionV13

theorem every_moment_zero_packet_actual_fine_gram
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
  obtain ⟨L, hL, hs⟩ :=
    AEGIS.WeilWindowExhaustionV1.logLift_has_finite_window_v1 g
  obtain ⟨n, χ, center, hχ, hpart, hcut⟩ :=
    AEGIS.RHFiniteFinePartitionV1.exists_finite_smooth_local_partition
      L (1 / 256) (by norm_num)
  obtain ⟨gs, hmom, hdiag, hpacket, hgram⟩ :=
    AEGIS.RHActualLocalGramCoercivityV1.every_packet_actual_fine_coercive_gram
      n g hm L hL.le hs χ hχ hpart center hcut
  exact ⟨n, gs, hmom, hdiag, hpacket, hgram⟩

/-- Sum the actual fine diagonal estimates without dropping mixed terms. -/
theorem fine_mixed_defect_lower_bound
    (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hd : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re) :
    (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) -
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
        -(∑ i, ∑ j, B (gs i) (gs j)).re := by
  have hs := Finset.sum_le_sum (fun i _ => hd i)
  have hdiag :
      (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) ≤
        -(∑ i, (B (gs i) (gs i)).re) := by
    rw [Finset.mul_sum]
    simpa only [Finset.sum_neg_distrib] using hs
  unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect
  linarith

/-- An actual quantitative finite witness for every admissible packet.
There is no caller-supplied partition or mixed-term inequality. -/
theorem every_packet_actual_fine_mixed_defect_lower_bound
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) -
        AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
          -(WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := by
  obtain ⟨n, gs, hmom, hd, hpacket, hgram⟩ :=
    every_moment_zero_packet_actual_fine_gram g hm
  refine ⟨n, gs, hmom, hpacket, ?_⟩
  calc
    (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) -
        AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
      -(∑ i, ∑ j, B (gs i) (gs j)).re :=
        fine_mixed_defect_lower_bound n gs hd
    _ = -(WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := by
      rw [hgram]

end AEGIS.RHActualUniversalFineGramV1

#print axioms AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram

#print axioms AEGIS.RHActualUniversalFineGramV1.fine_mixed_defect_lower_bound
#print axioms AEGIS.RHActualUniversalFineGramV1.every_packet_actual_fine_mixed_defect_lower_bound
