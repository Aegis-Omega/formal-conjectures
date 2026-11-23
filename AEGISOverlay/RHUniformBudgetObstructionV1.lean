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
import RHFineDiagonalUpgradeV3

/-!
# The uniform fine mixed budget is false

`RHActualUniversalFineGramV1.riemannHypothesis_of_uniform_actual_fine_mixed_budget` derives RH
from `hbudget`: for every moment-zero packet and *every* decomposition into atoms with the
diagonal margin `5671/3200`, the mixed defect is at most `5671/3200` times the total energy.
`UniformFineMixedBudget` is that hypothesis, verbatim, and `not_uniformFineMixedBudget` refutes it.

* `pair_defect`: the decomposition `h + (-h)` of the zero packet has mixed defect
  `-2 Re B(h,h)`, while its budget is `2 · (5671/3200) · E(h)`.
* `budget_forces_equality`: so the hypothesis forces `-Re B(h,h) ≤ (5671/3200) E(h)` for every
  atom with the margin, i.e. equality in the margin.
* `gFine_strict`: the fine atom `gFine` has the margin strictly, since its energy is positive
  and the diagonal constant floor `32449/31500 > 103/100` is strict.

The consumer theorem can therefore never be applied. Nothing here concerns RH itself, or the
existential per-packet budget of `riemannHypothesis_of_one_actual_mixed_budget_per_packet`,
which `RHOptimizedSchurGlobalJoinV1.rh_iff_one_actual_sharp_signed_budget` shows equivalent to RH.
-/

open Set Finset Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace AEGIS.RHUniformBudgetObstructionV1

open AEGIS.WeilMixedAlgebraV2 AEGIS.WeilDisjointEnergyV2 AEGIS.RHGramExpansionV13
open AEGIS.RHActualMixedDefectV1 AEGIS.RHFineMomentPacketV3 AEGIS.RHRationalNinePacketPrimeWindowV1
open AEGIS.RHFineDiagonalUpgradeV3 AEGIS.WeilWidthDiagonalArchFrontierV24
open AEGIS.WeilDiagonalKernelReductionV21 AEGIS.WeilThreeBlockAnalyticConstantsV21

/-- The hypothesis `hbudget` of `riemannHypothesis_of_uniform_actual_fine_mixed_budget`. -/
def UniformFineMixedBudget : Prop :=
  ∀ (g : WeilCompactSmoothGV1), WeilMomentConditionsV1 g →
    ∀ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤ -(B (gs i) (gs i)).re) →
      g = packetSum (fun _ => (1 : ℂ)) gs →
      actualMixedDefect n gs ≤ (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1)

/-- `UniformFineMixedBudget` is exactly the premise of the consumer theorem. -/
theorem consumer_of_budget (h : UniformFineMixedBudget) : RiemannHypothesis :=
  AEGIS.RHActualUniversalFineGramV1.riemannHypothesis_of_uniform_actual_fine_mixed_budget h

/-- The atoms `h` and `-h`. -/
def pairGs (h : WeilCompactSmoothGV1) : Fin 2 → WeilCompactSmoothGV1 :=
  ![h, scalePacket (-1) h]

theorem pairSum_apply (h : WeilCompactSmoothGV1) :
    (packetSum (fun _ => (1 : ℂ)) (pairGs h)).1 = 0 := by
  funext x
  simp [packetSum, pairGs, addPacket, scalePacket]

theorem pairSum_moments (h : WeilCompactSmoothGV1) :
    WeilMomentConditionsV1 (packetSum (fun _ => (1 : ℂ)) (pairGs h)) := by
  unfold WeilMomentConditionsV1
  rw [pairSum_apply]
  simp

theorem energy_neg (h : WeilCompactSmoothGV1) :
    energy (scalePacket (-1) h).1 = energy h.1 := by
  simp [energy, scalePacket]

theorem B_neg_neg (h : WeilCompactSmoothGV1) :
    B (scalePacket (-1) h) (scalePacket (-1) h) = B h h := by
  rw [B_scale_left, B_scale_right]
  simp

/-- The mixed defect of `h + (-h)`. -/
theorem pair_defect (h : WeilCompactSmoothGV1) :
    actualMixedDefect 1 (pairGs h) = -2 * (B h h).re := by
  unfold actualMixedDefect
  simp [pairGs, Fin.sum_univ_succ, B_scale_left, B_scale_right]
  ring

/-- The uniform budget forces equality in the diagonal margin of every atom. -/
theorem budget_forces_equality (hb : UniformFineMixedBudget) (h : WeilCompactSmoothGV1)
    (hd : (5671 / 3200 : ℝ) * energy h.1 ≤ -(B h h).re) :
    -(B h h).re ≤ (5671 / 3200 : ℝ) * energy h.1 := by
  have hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (pairGs h i).1 ≤
      -(B (pairGs h i) (pairGs h i)).re := by
    intro i
    fin_cases i
    · exact hd
    · simpa [pairGs, energy_neg, B_neg_neg] using hd
  have := hb _ (pairSum_moments h) 1 (pairGs h) hdiag rfl
  rw [pair_defect, Fin.sum_univ_two] at this
  simp only [pairGs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    energy_neg] at this
  linarith

theorem gFine_energy_pos : 0 < energy gFine.1 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp gFine_ne_zero_v3
  have hc : Continuous gFine.1 := gFine.2.1.continuous
  unfold energy
  have hcs : HasCompactSupport (fun t => ‖gFine.1 t‖ ^ 2) :=
    gFine.2.2.1.norm.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x)
    (hc.norm.pow 2) hcs (fun t => by positivity) ?_
  simpa using hx

/-- `gFine` has the diagonal margin strictly. -/
theorem gFine_strict :
    (5671 / 3200 : ℝ) * energy gFine.1 < -(B gFine gFine).re := by
  have hw := gFine_width_one_one_twenty_eight_v1
  have hp := width_diagonal_prime_sum_zero_v24 gFine 0 (fine_implies_retained_v3 gFine 0 hw)
  have hE := gFine_energy_pos
  have hf : (103 / 100 : ℝ) < diagonalTailV24 - diagonalKappaV21 - diagonalSmallV21 := by
    have ht := diagonal_tail_gt_six_log_two_v24
    have hc := diagonal_constant_floor
    have hn := certificate_diagonal_threshold
    unfold diagonalKappaV21 diagonalSmallV21
    linarith
  have hm := mul_lt_mul_of_pos_left hf hE
  have hb := fine_arch_budget_upgrade_v3 gFine 0 hw
  rw [actual_diagonal_rhs_decomposition gFine hp]
  nlinarith

/-- **The uniform fine mixed budget is false.** -/
theorem not_uniformFineMixedBudget : ¬ UniformFineMixedBudget := by
  intro hb
  have := budget_forces_equality hb gFine gFine_strict.le
  linarith [gFine_strict]

end AEGIS.RHUniformBudgetObstructionV1

#print axioms AEGIS.RHUniformBudgetObstructionV1.consumer_of_budget
#print axioms AEGIS.RHUniformBudgetObstructionV1.pair_defect
#print axioms AEGIS.RHUniformBudgetObstructionV1.budget_forces_equality
#print axioms AEGIS.RHUniformBudgetObstructionV1.gFine_strict
#print axioms AEGIS.RHUniformBudgetObstructionV1.not_uniformFineMixedBudget
