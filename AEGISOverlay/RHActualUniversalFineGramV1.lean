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
import RHRestrictedWeilBridgeV13

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
  have hs :
      (∑ i, (5671 / 3200 : ℝ) * energy (gs i).1) ≤
        ∑ i, -(B (gs i) (gs i)).re :=
    Finset.sum_le_sum (fun i _ => hd i)
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


/-! ## Final exact-head consumer of the universal actual mixed budget

The localization and the full arithmetic Weil Gram are constructed
unconditionally above.  Only \`hbudget\` remains as a mathematical input.
The conclusion is the canonical Mathlib RH proposition, with no renamed
theorem or weakened endpoint.  This implication does not establish
\`hbudget\` and MUST NOT be marked as an unconditional RH proof. -/

/-- Genuine mixed-defect control on the actual fine decompositions
constructed above suffices for the canonical Riemann hypothesis.  No
unproved term is suppressed, and the only remaining hypothesis is
spelled out on the original Weil pairing. -/
theorem riemannHypothesis_of_uniform_actual_fine_mixed_budget
    (hbudget :
      ∀ (g : WeilCompactSmoothGV1), WeilMomentConditionsV1 g →
        ∀ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
          (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
            -(B (gs i) (gs i)).re) →
          g = packetSum (fun _ => (1 : ℂ)) gs →
          AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
            (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1)) :
    RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
  intro g hm
  obtain ⟨n, gs, _hmom, hdiag, hpacket, hgram⟩ :=
    every_moment_zero_packet_actual_fine_gram g hm
  have hpaid := hbudget g hm n gs hdiag hpacket
  have hlower := fine_mixed_defect_lower_bound n gs hdiag
  rw [← hgram] at hlower
  have hnonneg :
      0 ≤ (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) -
        AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs :=
    sub_nonneg.mpr hpaid
  linarith


/-! ## Q16.16 admission of all actual mixed entries, arbitrary finite dimension

A matrix of *integer* outward upper bounds is checked on every row.
The matrix need not be Toeplitz and each genuine Weil atom may have a
different energy.  Numerical rounding does NOT supply the analytic
pairwise estimates: \`hcross\` is an explicit hypothesis.  No global
claim is made until a producer constructs these certificates for every
admissible packet. -/

def actualQ16PairCost {n : ℕ}
    (cost : Fin (n + 1) → Fin (n + 1) → ℕ)
    (i j : Fin (n + 1)) : ℝ :=
  (cost i j : ℝ) / 65536

/-- Every entry of the actual Hermitian Gram, including arbitrarily
distant pairs, is charged to the integer Q16.16 budget of its row.
The row budget is checked before any sign is concluded. -/
theorem actual_mixed_defect_le_of_q16_matrix
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (cost : Fin (n + 1) → Fin (n + 1) → ℕ)
    (hsym : ∀ i j, cost i j = cost j i)
    (hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤
        actualQ16PairCost cost i j *
          (energy (gs i).1 + energy (gs j).1))
    (hrow : ∀ i, (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
       cost i j) ≤ 57430) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
       (114860 / 65536 : ℝ) * (∑ i, energy (gs i).1) := by
  let E : Fin (n + 1) → ℝ := fun i => energy (gs i).1
  let c : Fin (n + 1) → Fin (n + 1) → ℝ := actualQ16PairCost cost
  have hsplit (i : Fin (n + 1)) :
      (∑ j, (B (gs i) (gs j)).re) =
        (B (gs i) (gs i)).re +
          ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
            (B (gs i) (gs j)).re := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hdef :
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs =
        ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (B (gs i) (gs j)).re := by
    unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect
    rw [Complex.re_sum]
    simp_rw [Complex.re_sum]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    ring
  have hrows (i : Fin (n + 1)) :
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) ≤
        (57430 / 65536 : ℝ) := by
    change (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      (cost i j : ℝ) / 65536) ≤ _
    calc
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (cost i j : ℝ) / 65536) =
        ((∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          cost i j : ℕ) : ℝ) / 65536 := by
          simp only [Finset.sum_div, Nat.cast_sum]
      _ ≤ (57430 / 65536 : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hrow i) (by norm_num)
  have hoff :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (B (gs i) (gs j)).re) ≤
      ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * (E i + E j) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j hj
    have hij : i ≠ j := by
      intro h
      exact (Finset.mem_erase.mp hj).1 h.symm
    calc
      (B (gs i) (gs j)).re ≤ ‖B (gs i) (gs j)‖ :=
        Complex.re_le_norm _
      _ ≤ c i j * (E i + E j) := hcross i j hij
  have hswap :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * E j) =
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * E i) := by
    rw [AEGIS.RHGramExpansionV13.sum_erase_comm
      (fun i j => c i j * E j)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hc : c j i = c i j := by
      dsimp [c, actualQ16PairCost]
      rw [hsym j i]
    rw [hc]
  have hfactor :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * E i) =
      ∑ i, E i * (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have htwo :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j * (E i + E j)) =
      2 * (∑ i, E i * (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) := by
    calc
      _ = (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
             c i j * E i) +
          (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
             c i j * E j) := by
            simp only [mul_add, Finset.sum_add_distrib]
      _ = 2 * (∑ i, E i * (∑ j ∈
           (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) := by
            rw [hswap]
            rw [hfactor]
            ring
  have hrowtotal :
      (∑ i, E i * (∑ j ∈
        (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) ≤
      (57430 / 65536 : ℝ) * (∑ i, E i) := by
    calc
      _ ≤ ∑ i, E i * (57430 / 65536 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hrows i)
          (energy_nonnegative (gs i).1)
      _ = (57430 / 65536 : ℝ) * (∑ i, E i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  calc
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs =
        (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (B (gs i) (gs j)).re) := hdef
    _ ≤ (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          c i j * (E i + E j)) := hoff
    _ = 2 * (∑ i, E i * (∑ j ∈
          (Finset.univ : Finset (Fin (n + 1))).erase i, c i j)) := htwo
    _ ≤ 2 * ((57430 / 65536 : ℝ) * (∑ i, E i)) :=
        mul_le_mul_of_nonneg_left hrowtotal (by norm_num)
    _ = (114860 / 65536 : ℝ) * (∑ i, energy (gs i).1) := by
        dsimp [E]
        ring

/-- Q16.16 analytic input plus exact integer row checks leaves an actual
strict positive margin, even for atoms with unequal energies.  The
coercivity conclusion is for the genuine Weil quadratic form. -/
theorem actual_fine_gram_q16_coercive_of_pair_certificate
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (cost : Fin (n + 1) → Fin (n + 1) → ℕ)
    (hsym : ∀ i j, cost i j = cost j i)
    (hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤
        actualQ16PairCost cost i j *
          (energy (gs i).1 + energy (gs j).1))
    (hrow : ∀ i, (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
       cost i j) ≤ 57430) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
        (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
       -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  have hmixed := actual_mixed_defect_le_of_q16_matrix
    gs cost hsym hcross hrow
  have hlocal := fine_mixed_defect_lower_bound n gs hdiag
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
        (packetSum (fun _ => (1 : ℂ)) gs)).re =
      (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [AEGIS.RHGramExpansionV13.B_packetSum]
    simp
  rw [← hgram] at hlocal
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  have hround :
      (116142 / 65536 : ℝ) * (∑ i, energy (gs i).1) ≤
        (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) :=
    mul_le_mul_of_nonneg_right (by norm_num) hE
  linarith

/-- The full conditional Q16.16 route to the canonical RH theorem.  The
certificate producer is explicitly still required for each arbitrary
moment-zero packet and its exact fine decomposition. -/
theorem riemannHypothesis_of_universal_actual_q16_pair_certificates
    (hcert : ∀ (g : WeilCompactSmoothGV1),
      WeilMomentConditionsV1 g →
      ∀ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re) →
      g = packetSum (fun _ => (1 : ℂ)) gs →
      ∃ cost : Fin (n + 1) → Fin (n + 1) → ℕ,
        (∀ i j, cost i j = cost j i) ∧
        (∀ i j, i ≠ j →
          ‖B (gs i) (gs j)‖ ≤
            actualQ16PairCost cost i j *
              (energy (gs i).1 + energy (gs j).1)) ∧
        (∀ i, (∑ j ∈
          (Finset.univ : Finset (Fin (n + 1))).erase i,
          cost i j) ≤ 57430)) :
    RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
  intro g hm
  obtain ⟨n, gs, _hmom, hd, hg, _hgram⟩ :=
    every_moment_zero_packet_actual_fine_gram g hm
  obtain ⟨cost, hsym, hcross, hrow⟩ := hcert g hm n gs hd hg
  have hbound := actual_fine_gram_q16_coercive_of_pair_certificate
    gs cost hsym hd hcross hrow
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  rw [hg]
  change (B (packetSum (fun _ => (1 : ℂ)) gs)
    (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0
  linarith

end AEGIS.RHActualUniversalFineGramV1

#print axioms AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram

#print axioms AEGIS.RHActualUniversalFineGramV1.fine_mixed_defect_lower_bound
#print axioms AEGIS.RHActualUniversalFineGramV1.every_packet_actual_fine_mixed_defect_lower_bound

#print axioms AEGIS.RHActualUniversalFineGramV1.riemannHypothesis_of_uniform_actual_fine_mixed_budget

#print axioms AEGIS.RHActualUniversalFineGramV1.actual_mixed_defect_le_of_q16_matrix
#print axioms AEGIS.RHActualUniversalFineGramV1.actual_fine_gram_q16_coercive_of_pair_certificate
#print axioms AEGIS.RHActualUniversalFineGramV1.riemannHypothesis_of_universal_actual_q16_pair_certificates
