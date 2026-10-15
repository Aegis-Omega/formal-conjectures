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

import AEGISOverlay.RHScaleRowCompositionV1

/-!
# Optimized actual Weil–Schur global join

This module composes the EXISTING arbitrary-packet fine Gram constructor with
the EXISTING optimized weighted-Schur bound, using the genuine Weil pairing.
The optimized Q16.16 diagonal-minus-row margin is 34727/32768.

The only new universal mathematical input is the explicit producer `hrows`,
which must bound all actual off-diagonal entries of the fine decomposition.
The premise is NOT constructed here. In particular, this module does not
assert unconditional RiemannHypothesis or provide an upstream formal_proof.
-/

open Finset
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHOptimizedSchurGlobalJoinV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHGramExpansionV13

/-- The existing optimized bound makes one actual reconstructed packet
nonpositive once the genuine mixed-entry and weighted-row estimates are
available. Unequal atom energies and arbitrary finite dimension are allowed. -/
theorem actual_packet_sum_nonpositive_of_optimized_rows
    {n : ℕ}
    (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (w : Fin (n + 1) → ℝ)
    (hc : ∀ i j, 0 ≤ c i j)
    (hzero : ∀ i, c i i = 0)
    (hsym : ∀ i j, c i j = c j i)
    (hw : ∀ i, 0 < w i)
    (hd : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤ c i j *
        (Real.sqrt (energy (gs i).1) *
          Real.sqrt (energy (gs j).1)))
    (hrow : ∀ i, ∑ j, c i j * (w j / w i) ≤
      (46688 / 65536 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0 := by
  have hopt :=
    AEGIS.RHScaleRowCompositionV1.actual_optimized_weighted_schur_unequal_energy_from_fine_diagonals
      gs (fun _ => (1 : ℂ)) c w hc hzero hsym hw hd hcross hrow
  have henergy :
      0 ≤ ∑ i : Fin (n + 1), energy (gs i).1 * ‖(1 : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (energy_nonnegative (gs i).1) (sq_nonneg _))
  have hnonpos :
      -(34727 / 32768 : ℝ) *
        (∑ i : Fin (n + 1), energy (gs i).1 * ‖(1 : ℂ)‖ ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num) henergy
  exact hopt.trans hnonpos

/-- Universal sign consumer using a *selected* finite reconstruction, not
an arbitrary partition. The starting geometry and actual Weil Gram are
constructed by the existing source theorem. The explicit hselect obligation
may replace that partition with one certified weighted-Schur reconstruction.

This choice of quantifiers is essential: arbitrary fine decompositions may
contain repeated or nearly identical atoms and need not satisfy a strict
off-diagonal row budget. No universal analytic producer is assumed proved. -/
theorem riemannHypothesis_of_optimized_actual_row_producer
    (hselect :
      ∀ (g : WeilCompactSmoothGV1)
        (hm : WeilMomentConditionsV1 g)
        (n : ℕ)
        (gs : Fin (n + 1) → WeilCompactSmoothGV1)
        (center : Fin (n + 1) → ℝ),
        (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
          (gs i) (center i)) →
        (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
          -(B (gs i) (gs i)).re) →
        g = packetSum (fun _ => (1 : ℂ)) gs →
        ∃ (m : ℕ) (selected : Fin (m + 1) → WeilCompactSmoothGV1),
          g = packetSum (fun _ => (1 : ℂ)) selected ∧
          (∀ i, (5671 / 3200 : ℝ) * energy (selected i).1 ≤
            -(B (selected i) (selected i)).re) ∧
          ∃ (c : Fin (m + 1) → Fin (m + 1) → ℝ)
            (w : Fin (m + 1) → ℝ),
            (∀ i j, 0 ≤ c i j) ∧
            (∀ i, c i i = 0) ∧
            (∀ i j, c i j = c j i) ∧
            (∀ i, 0 < w i) ∧
            (∀ i j, i ≠ j →
              ‖B (selected i) (selected j)‖ ≤ c i j *
                (Real.sqrt (energy (selected i).1) *
                  Real.sqrt (energy (selected j).1))) ∧
            (∀ i, ∑ j, c i j * (w j / w i) ≤
              (46688 / 65536 : ℝ))) :
    RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
  intro g hm
  obtain ⟨n, gs, center, _hmom, hd, hwidth, hpacket, _hgram⟩ :=
    AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_with_support g hm
  obtain ⟨m, selected, hselected, hdiag, c, w, hc, hzero, hsym, hw,
    hcross, hrow⟩ :=
    hselect g hm n gs center hwidth hd hpacket
  have hsign :=
    actual_packet_sum_nonpositive_of_optimized_rows
      selected c w hc hzero hsym hw hdiag hcross hrow
  rw [hselected]
  change (B (packetSum (fun _ => (1 : ℂ)) selected)
    (packetSum (fun _ => (1 : ℂ)) selected)).re ≤ 0
  exact hsign

end AEGIS.RHOptimizedSchurGlobalJoinV1

#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.actual_packet_sum_nonpositive_of_optimized_rows
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.riemannHypothesis_of_optimized_actual_row_producer
