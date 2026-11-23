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

import AEGISOverlay.RHActualUniversalFineGramV1
import WeilFineDiagonalQuadV1

/-!
AEGIS Ω — the operator's fine Gram chain with the diagonal `43/10` (Claude Lab, 2026-11-23).

`AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_with_support` constructs, for every
compactly supported moment-zero packet `g`, a finite family of atoms `gs i` with both moments and
`WidthOneOneTwentyEightAt (gs i) (center i)`, i.e. `LogSupportIn (gs i) (center i − 1/256) (center i + 1/256)`.
That is exactly the hypothesis of `AEGIS.WeilFineDiagonalQuadV1.fine_diagonal_43_over_10`, so every atom of
that decomposition satisfies `(43/10) E(gs i) ≤ −Re B(gs i, gs i)`, in place of `5671/3200`.

* `every_moment_zero_packet_fine_gram_43_10`: the same constructed decomposition with diagonal `43/10`.
* `fine_mixed_defect_lower_bound_43`, `every_packet_fine_mixed_defect_lower_bound_43`: summed without dropping
  any mixed entry.
* `riemannHypothesis_of_one_fine_mixed_budget_43_10_per_packet`: a conditional consumer. Its only input `hcert`
  asks, for every packet, for SOME width-1/128 moment-zero decomposition with mixed defect `≤ (43/10) Σ E`.
* `actual_fine_gram_coercive_of_signed_real_row_43`, `actual_far_fine_gram_coercive_of_geometric_arch_prime_row_43`:
  the operator's row/Schur consumers with the row bound relaxed from `57430/65536` (resp. `57176/65536`) to any
  `R` with `2 R + δ ≤ 43/10` (resp. `2 (R + 254/65536) + δ ≤ 43/10`).

The form quantifying over ALL decompositions is not used: the pair decomposition `h + (−h)` of
`AEGIS.RHUniformBudgetObstructionV1` refutes it for `43/10` as well, since `fine_constant_gt` makes the margin
strict. `hcert` is NOT proved. This module does not establish RH and must not be read as an unconditional proof.
-/

open Set Finset Complex
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilFineChain43V1

open AEGIS.WeilMixedAlgebraV2 AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedClosureV2
open AEGIS.RHGramExpansionV13

/-- The operator's constructed fine decomposition, with diagonal `43/10` on every atom. -/
theorem every_moment_zero_packet_fine_gram_43_10
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
      (center : Fin (n + 1) → ℝ),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, (43 / 10 : ℝ) * energy (gs i).1 ≤ -(B (gs i) (gs i)).re) ∧
      (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
  obtain ⟨n, gs, center, hmom, _, hwidth, hpacket, hgram⟩ :=
    AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_with_support g hm
  exact ⟨n, gs, center, hmom,
    fun i => AEGIS.WeilFineDiagonalQuadV1.fine_diagonal_43_over_10 (gs i) (center i) (hwidth i) (hmom i),
    hwidth, hpacket, hgram⟩

/-- Sum the `43/10` diagonal estimates; every mixed entry stays in `actualMixedDefect`. -/
theorem fine_mixed_defect_lower_bound_43
    (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hd : ∀ i, (43 / 10 : ℝ) * energy (gs i).1 ≤ -(B (gs i) (gs i)).re) :
    (43 / 10 : ℝ) * (∑ i, energy (gs i).1) -
      AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
        -(∑ i, ∑ j, B (gs i) (gs j)).re := by
  have hs :
      (∑ i, (43 / 10 : ℝ) * energy (gs i).1) ≤ ∑ i, -(B (gs i) (gs i)).re :=
    Finset.sum_le_sum (fun i _ => hd i)
  have hdiag :
      (43 / 10 : ℝ) * (∑ i, energy (gs i).1) ≤ -(∑ i, (B (gs i) (gs i)).re) := by
    rw [Finset.mul_sum]
    simpa only [Finset.sum_neg_distrib] using hs
  unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect
  linarith

/-- The quantitative witness for every admissible packet, with `43/10`. -/
theorem every_packet_fine_mixed_defect_lower_bound_43
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
      (center : Fin (n + 1) → ℝ),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (43 / 10 : ℝ) * (∑ i, energy (gs i).1) -
        AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
          -(WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := by
  obtain ⟨n, gs, center, hmom, hd, hwidth, hpacket, hgram⟩ :=
    every_moment_zero_packet_fine_gram_43_10 g hm
  refine ⟨n, gs, center, hmom, hwidth, hpacket, ?_⟩
  rw [hgram]
  exact fine_mixed_defect_lower_bound_43 n gs hd

/-- **Conditional consumer, one decomposition per packet.** If every moment-zero packet has SOME
decomposition into width-1/128 moment-zero atoms whose mixed defect is at most `(43/10) Σ E`, the canonical
Riemann hypothesis follows. The atoms' diagonal is derived (`fine_diagonal_43_over_10`), not assumed.
`hcert` is an open hypothesis. -/
theorem riemannHypothesis_of_one_fine_mixed_budget_43_10_per_packet
    (hcert : ∀ (g : WeilCompactSmoothGV1), WeilMomentConditionsV1 g →
      ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1) (center : Fin (n + 1) → ℝ),
        (∀ i, WeilMomentConditionsV1 (gs i)) ∧
        (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
          (gs i) (center i)) ∧
        g = packetSum (fun _ => (1 : ℂ)) gs ∧
        AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
          (43 / 10 : ℝ) * (∑ i, energy (gs i).1)) :
    RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
  intro g hm
  obtain ⟨n, gs, center, hmom, hwidth, hg, hbudget⟩ := hcert g hm
  have hd : ∀ i, (43 / 10 : ℝ) * energy (gs i).1 ≤ -(B (gs i) (gs i)).re := fun i =>
    AEGIS.WeilFineDiagonalQuadV1.fine_diagonal_43_over_10 (gs i) (center i) (hwidth i) (hmom i)
  have hlo := fine_mixed_defect_lower_bound_43 n gs hd
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs) (packetSum (fun _ => (1 : ℂ)) gs)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [AEGIS.RHGramExpansionV13.B_packetSum]
    simp
  rw [hg]
  change (B (packetSum (fun _ => (1 : ℂ)) gs) (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0
  linarith

/-- Signed real row certificate with the `43/10` diagonal: any symmetric real row bound `R` with
`2 R + δ ≤ 43/10` gives coercivity `−δ`. (The operator's certificate needs `R ≤ 57430/65536`.) -/
theorem actual_fine_gram_coercive_of_signed_real_row_43
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1) (center : Fin (n + 1) → ℝ)
    (hw : ∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
      (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, c i j = c j i)
    (hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤ c i j * (energy (gs i).1 + energy (gs j).1))
    (R δ : ℝ) (hR : 2 * R + δ ≤ 43 / 10)
    (hrow : ∀ i, (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) ≤ R) :
    (B (packetSum (fun _ => (1 : ℂ)) gs) (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -δ * (∑ i, energy (gs i).1) := by
  have hmixed := AEGIS.RHActualUniversalFineGramV1.actual_mixed_defect_le_of_signed_symmetric_row
    gs c R hsym hcross hrow
  have hd : ∀ i, (43 / 10 : ℝ) * energy (gs i).1 ≤ -(B (gs i) (gs i)).re := fun i =>
    AEGIS.WeilFineDiagonalQuadV1.fine_diagonal_43_over_10 (gs i) (center i) (hw i) (hm i)
  have hlocal := fine_mixed_defect_lower_bound_43 n gs hd
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs) (packetSum (fun _ => (1 : ℂ)) gs)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [AEGIS.RHGramExpansionV13.B_packetSum]
    simp
  rw [← hgram] at hlocal
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  have hround := mul_le_mul_of_nonneg_right hR hE
  linarith

/-- The operator's far geometric-Arch Schur consumer with the `43/10` diagonal: a symmetric prime row
budget `R` with `2 (R + 254/65536) + δ ≤ 43/10` gives coercivity `−δ`. (The operator's version needs
`R ≤ 57176/65536`; here, for example, `R = 2` with `δ = 29/100` is admissible.) -/
theorem actual_far_fine_gram_coercive_of_geometric_arch_prime_row_43
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1) (center : Fin (n + 1) → ℝ)
    (hw : ∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
      (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧ (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
    (primeCost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, primeCost i j = primeCost j i)
    (hprime : ∀ i j : Fin (n + 1), i < j →
      ‖WeilPrimeSumV1 (mixed (gs i) (gs j))‖ ≤
        primeCost i j * (energy (gs i).1 + energy (gs j).1))
    (R δ : ℝ) (hR : 2 * (R + 254 / 65536) + δ ≤ 43 / 10)
    (hprimeRow : ∀ i, (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      primeCost i j) ≤ R) :
    (B (packetSum (fun _ => (1 : ℂ)) gs) (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -δ * (∑ i, energy (gs i).1) := by
  let c : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j =>
    primeCost i j + (13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)
  have hc : ∀ i j, c i j = c j i := by
    intro i j
    dsimp [c]
    rw [hsym i j, Nat.dist_comm i j]
  have hforward (i j : Fin (n + 1)) (hij : i < j) :
      ‖B (gs i) (gs j)‖ ≤ c i j * (energy (gs i).1 + energy (gs j).1) := by
    obtain ⟨hk, hgap⟩ := hsep i j hij
    have hb :=
      AEGIS.RHActualMixedDefectV1.distinct_fine_far_actual_B_norm_le_prime_plus_geometric_arch
        (gs i) (gs j) (center i) (center j) (hw i) (hw j) (hm i) (Nat.dist i j) hk hgap
    dsimp [c]
    calc
      ‖B (gs i) (gs j)‖ ≤
          ‖WeilPrimeSumV1 (mixed (gs i) (gs j))‖ +
          ((13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)) *
            (energy (gs i).1 + energy (gs j).1) := hb
      _ ≤ primeCost i j * (energy (gs i).1 + energy (gs j).1) +
          ((13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)) *
            (energy (gs i).1 + energy (gs j).1) :=
              add_le_add (hprime i j hij) le_rfl
      _ = (primeCost i j + (13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)) *
          (energy (gs i).1 + energy (gs j).1) := by ring
  have hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤ c i j * (energy (gs i).1 + energy (gs j).1) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact hforward i j hijlt
    · have hb := hforward j i hjilt
      rw [B_hermitian, norm_conj]
      simpa only [hc j i, add_comm (energy (gs j).1) (energy (gs i).1)] using hb
  have hrowc : ∀ i, (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) ≤
      R + 254 / 65536 := by
    intro i
    calc
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) =
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, primeCost i j) +
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          (13 / 384 : ℝ) * ((2 / 37 : ℝ) ^ Nat.dist i j)) := by
            simp only [c, Finset.sum_add_distrib]
      _ ≤ R + 254 / 65536 :=
        add_le_add (hprimeRow i) (AEGIS.RHActualUniversalFineGramV1.geometric_arch_row_q16 i)
  have hmixed := AEGIS.RHActualUniversalFineGramV1.actual_mixed_defect_le_of_real_symmetric_row
    gs c (R + 254 / 65536) hc hcross hrowc
  have hd : ∀ i, (43 / 10 : ℝ) * energy (gs i).1 ≤ -(B (gs i) (gs i)).re := fun i =>
    AEGIS.WeilFineDiagonalQuadV1.fine_diagonal_43_over_10 (gs i) (center i) (hw i) (hm i)
  have hlocal := fine_mixed_defect_lower_bound_43 n gs hd
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs) (packetSum (fun _ => (1 : ℂ)) gs)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [AEGIS.RHGramExpansionV13.B_packetSum]
    simp
  rw [← hgram] at hlocal
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  have hround := mul_le_mul_of_nonneg_right hR hE
  linarith

end AEGIS.WeilFineChain43V1

#print axioms AEGIS.WeilFineChain43V1.every_moment_zero_packet_fine_gram_43_10
#print axioms AEGIS.WeilFineChain43V1.every_packet_fine_mixed_defect_lower_bound_43
#print axioms AEGIS.WeilFineChain43V1.riemannHypothesis_of_one_fine_mixed_budget_43_10_per_packet
#print axioms AEGIS.WeilFineChain43V1.actual_fine_gram_coercive_of_signed_real_row_43
#print axioms AEGIS.WeilFineChain43V1.actual_far_fine_gram_coercive_of_geometric_arch_prime_row_43
