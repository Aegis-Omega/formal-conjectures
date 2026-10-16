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
import Mathlib.Tactic

/-!
# Exact universal fine partition + two prime-free windows + signed real rows

For each moment-zero smooth Weil packet, the existing unconditional constructor
provides an exact finite reconstruction, local width certificates and the actual
Weil Gram. On EVERY pair whose separation lies in one of the two source-proved
prime-log-free intervals, the genuinely arithmetic Weil B norm is bounded by
676/65536 times the sum of individual energies.

Other pairs, notably prime-log resonances, are NOT assigned an invented bound.
A separate explicitly stated signed-resonant certificate can then be combined
with the source-proved nonresonant estimates and the already verified
signed-real row consumer.

The final RH theorem remains conditional on producing the resonant certificate
for every source partition. This file adds no axiom, sorry or RH assumption.
-/

open Complex
open Finset
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHPrimeFreeRecompositionJoinV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHActualUniversalFineGramV1

/-- The two genuine-prime-free separation intervals where a uniform
source-proved fine-pair Q16.16 budget is available. -/
def FineLogFreeGap (d : ℝ) : Prop :=
  (35 / 128 : ℝ) ≤ d ∧
    (d < Real.log 2 - (1 / 128 : ℝ) ∨
      (Real.log 2 + (1 / 128 : ℝ) < d ∧
        d < Real.log 3 - (1 / 128 : ℝ)))

/-- Orientation-independent true-Weil pair bound for DIFFERENT fine atoms.
The packet moments are not moved across atoms unless the roles are swapped
together with the energy terms. The cost is not rounded per prime summand. -/
theorem actual_fine_pair_q16_of_log_free_gap
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hw : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i))
    (i j : Fin (n + 1))
    (hfree : FineLogFreeGap |center j - center i|) :
    ‖B (gs i) (gs j)‖ ≤
      (676 / 65536 : ℝ) * (energy (gs i).1 + energy (gs j).1) := by
  obtain ⟨hsep, hinterval⟩ := hfree
  by_cases hij : center i ≤ center j
  · have habs : |center j - center i| = center j - center i :=
      abs_of_nonneg (sub_nonneg.mpr hij)
    rw [habs] at hsep hinterval
    exact AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_q16_first_two_log_free_windows
      (gs i) (gs j) (center i) (center j)
      (hw i) (hw j) (hm i) hsep hinterval
  · have hji : center j ≤ center i :=
      le_of_lt (lt_of_not_ge hij)
    have habs : |center j - center i| = center i - center j := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr hji)
    rw [habs] at hsep hinterval
    have hb :=
      AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_q16_first_two_log_free_windows
        (gs j) (gs i) (center j) (center i)
        (hw j) (hw i) (hm j) hsep hinterval
    calc
      ‖B (gs i) (gs j)‖ = ‖B (gs j) (gs i)‖ := by
        rw [B_hermitian, Complex.norm_conj]
      _ ≤ (676 / 65536 : ℝ) *
          (energy (gs j).1 + energy (gs i).1) := hb
      _ = (676 / 65536 : ℝ) *
          (energy (gs i).1 + energy (gs j).1) := by ring

/-- Each arbitrary moment-zero Weil packet has a FINITE source-exact
decomposition, AND ALL of its prime-free fine pairs are certified.
No global row budget is presumed. -/
theorem every_packet_actual_fine_gram_with_log_free_pairs
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
      (center : Fin (n + 1) → ℝ),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re) ∧
      (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re ∧
      (∀ i j, FineLogFreeGap |center j - center i| →
        ‖B (gs i) (gs j)‖ ≤
          (676 / 65536 : ℝ) *
            (energy (gs i).1 + energy (gs j).1)) := by
  obtain ⟨n, gs, center, hmom, hdiag, hwidth, hpacket, hgram⟩ :=
    every_moment_zero_packet_actual_fine_gram_with_support g hm
  refine ⟨n, gs, center, hmom, hdiag, hwidth, hpacket, hgram, ?_⟩
  intro i j hfree
  exact actual_fine_pair_q16_of_log_free_gap gs center hmom hwidth i j hfree

/-- The EXACT mixed row: the known nonresonant cost plus an independent
signed residual for the remaining (including prime-resonant) pairs. -/
def combinedFineCost {n : ℕ}
    (center : Fin (n + 1) → ℝ)
    (residual : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) : ℝ :=
  if FineLogFreeGap |center j - center i| then
    (676 / 65536 : ℝ)
  else residual i j

/-- Symmetry of the entire certified row including resonant residuals. -/
theorem combinedFineCost_symm {n : ℕ}
    (center : Fin (n + 1) → ℝ)
    (residual : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, residual i j = residual j i)
    (i j : Fin (n + 1)) :
    combinedFineCost center residual i j =
      combinedFineCost center residual j i := by
  unfold combinedFineCost
  have habs : |center j - center i| = |center i - center j| :=
    abs_sub_comm (center j) (center i)
  rw [habs]
  by_cases hf : FineLogFreeGap |center i - center j|
  · simp [hf]
  · simp [hf, hsym i j]

/-- Complete analytic composition. All log-free pair costs come from the
actual Weil explicit formula; only prime-resonant or otherwise excluded
interactions remain in the residual. The global budget is still explicit. -/
theorem actual_source_gram_coercive_of_resonance_row
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hwidth : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i))
    (hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (residual : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, residual i j = residual j i)
    (hres : ∀ i j, i ≠ j →
      ¬ FineLogFreeGap |center j - center i| →
      (B (gs i) (gs j)).re ≤
        residual i j * (energy (gs i).1 + energy (gs j).1))
    (hrow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
        combinedFineCost center residual i j) ≤
          (57430 / 65536 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
        -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  have hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        combinedFineCost center residual i j *
          (energy (gs i).1 + energy (gs j).1) := by
    intro i j hij
    by_cases hf : FineLogFreeGap |center j - center i|
    · have hb := actual_fine_pair_q16_of_log_free_gap
        gs center hm hwidth i j hf
      calc
        (B (gs i) (gs j)).re ≤ ‖B (gs i) (gs j)‖ :=
          Complex.re_le_norm _
        _ ≤ (676 / 65536 : ℝ) *
            (energy (gs i).1 + energy (gs j).1) := hb
        _ = combinedFineCost center residual i j *
            (energy (gs i).1 + energy (gs j).1) := by
              simp only [combinedFineCost, if_pos hf]
    · simpa only [combinedFineCost, if_neg hf] using
        (hres i j hij hf)
  exact actual_fine_gram_coercive_of_signed_real_row_certificate
    gs (combinedFineCost center residual)
    (combinedFineCost_symm center residual hsym)
    hdiag hcross hrow

/-- Canonical RH handoff: the exact arbitrary-packet partition and every
log-free mixed certificate are CONSTRUCTED above. The sole analytic
producer still to be proved is for the other pair costs and their rows.
Do not confuse this conditional theorem with a proof of its hresidual. -/
theorem riemannHypothesis_of_canonical_resonance_producer
    (hresidual :
      ∀ (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
        (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
        (center : Fin (n + 1) → ℝ),
        (∀ i, WeilMomentConditionsV1 (gs i)) →
        (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
          -(B (gs i) (gs i)).re) →
        (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
          (gs i) (center i)) →
        g = packetSum (fun _ => (1 : ℂ)) gs →
        ∃ residual : Fin (n + 1) → Fin (n + 1) → ℝ,
          (∀ i j, residual i j = residual j i) ∧
          (∀ i j, i ≠ j →
            ¬ FineLogFreeGap |center j - center i| →
            (B (gs i) (gs j)).re ≤
              residual i j * (energy (gs i).1 + energy (gs j).1)) ∧
          (∀ i, (∑ j ∈
            (Finset.univ : Finset (Fin (n + 1))).erase i,
              combinedFineCost center residual i j) ≤
                (57430 / 65536 : ℝ))) :
    RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
  intro g hm
  obtain ⟨n, gs, center, hmom, hdiag, hwidth, hpacket, _hgram, _hfree⟩ :=
    every_packet_actual_fine_gram_with_log_free_pairs g hm
  obtain ⟨residual, hsym, hres, hrow⟩ :=
    hresidual g hm n gs center hmom hdiag hwidth hpacket
  have hfull := actual_source_gram_coercive_of_resonance_row
    gs center hmom hwidth hdiag residual hsym hres hrow
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  rw [hpacket]
  change (B (packetSum (fun _ => (1 : ℂ)) gs)
    (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0
  linarith

end AEGIS.RHPrimeFreeRecompositionJoinV1

#print axioms AEGIS.RHPrimeFreeRecompositionJoinV1.actual_fine_pair_q16_of_log_free_gap
#print axioms AEGIS.RHPrimeFreeRecompositionJoinV1.every_packet_actual_fine_gram_with_log_free_pairs
#print axioms AEGIS.RHPrimeFreeRecompositionJoinV1.combinedFineCost_symm
#print axioms AEGIS.RHPrimeFreeRecompositionJoinV1.actual_source_gram_coercive_of_resonance_row
#print axioms AEGIS.RHPrimeFreeRecompositionJoinV1.riemannHypothesis_of_canonical_resonance_producer
