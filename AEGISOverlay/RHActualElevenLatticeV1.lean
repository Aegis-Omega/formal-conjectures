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
import RHFeshbachWeilClosureV2
import RHRationalGapTenPrimeBoundV1
import AEGISOverlay.RHWeightedSchurV1

/-! Actual eleven-translate Weil Gram certificate. The source-pinned
gap-1 through gap-10 analytic estimates discharge every mixed entry.
The domain is eleven translates of one fine moment-zero packet. -/

open Set Finset Complex
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHActualElevenLatticeV1

open AEGIS.WeilMixedAlgebraV2 AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHRationalNinePacketPrimeWindowV1
open AEGIS.RHRationalGapNinePrimeBoundV1
open AEGIS.RHRationalGapTenPrimeBoundV1
open AEGIS.RHFineDiagonalUpgradeV3
open AEGIS.RHGramExpansionV13

def elevenCost (k : ℕ) : ℝ :=
  if k = 9 then 57 / 100 else
  if k = 10 then 837 / 3700 else 1 / 100

theorem elevenCost_nonnegative (k : ℕ) : 0 ≤ elevenCost k := by
  unfold elevenCost
  split_ifs <;> norm_num

theorem lattice_gap_bound
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneOneTwentyEightAt g a)
    (hm : WeilMomentConditionsV1 g) (i k : ℕ)
    (hk : 1 ≤ k) (hk' : k ≤ 10) :
    ‖B (translatePacket g (qNineShiftV1 i))
      (translatePacket g (qNineShiftV1 (i + k)))‖ ≤
        elevenCost k * energy g.1 := by
  interval_cases k
  · simpa [elevenCost] using shift_gap_one_B_norm_v1 g a hw hm i
  · simpa [elevenCost] using shift_gap_two_B_norm_v1 g a hw hm i
  · simpa [elevenCost] using shift_gap_three_B_norm_v1 g a hw hm i
  · simpa [elevenCost] using shift_gap_four_B_norm_v1 g a hw hm i
  · simpa [elevenCost] using shift_gap_five_B_norm_v1 g a hw hm i
  · simpa [elevenCost] using shift_gap_six_B_norm_v1 g a hw hm i
  · simpa [elevenCost] using shift_gap_seven_B_norm_v1 g a hw hm i
  · simpa [elevenCost] using shift_gap_eight_B_norm_v1 g a hw hm i
  · rw [B_translate_eq_of_gap_nine_v1 g
      (qNineShiftV1 i) (qNineShiftV1 (i + 9)) 0 gapNineV1
      (by simpa [gapNineV1] using qNineShift_gap_v1 i 9)]
    simpa [elevenCost] using gap_nine_B_norm_v1 g a hw hm
  · rw [B_translate_eq_of_gap_nine_v1 g
      (qNineShiftV1 i) (qNineShiftV1 (i + 10)) 0 gapTenV1
      (by simpa [gapTenV1] using qNineShift_gap_v1 i 10)]
    simpa [elevenCost] using gap_ten_B_norm_v1 g a hw hm

def elevenAtoms (g : WeilCompactSmoothGV1) (i : Fin 11) :
    WeilCompactSmoothGV1 := translatePacket g (qNineShiftV1 i)

theorem all_actual_eleven_mixed_bounds
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneOneTwentyEightAt g a)
    (hm : WeilMomentConditionsV1 g) :
    ∀ i j : Fin 11, i ≠ j →
      ‖B (elevenAtoms g i) (elevenAtoms g j)‖ ≤
        elevenCost (Nat.dist i j) * energy g.1 := by
  have upper (i j : Fin 11) (hij : (i : ℕ) < j) :
      ‖B (elevenAtoms g i) (elevenAtoms g j)‖ ≤
        elevenCost (Nat.dist i j) * energy g.1 := by
    have hi := i.isLt
    have hj := j.isLt
    have hk : 1 ≤ (j : ℕ) - i := by omega
    have hk' : (j : ℕ) - i ≤ 10 := by omega
    have hadd : (i : ℕ) + ((j : ℕ) - i) = j := by omega
    simpa only [elevenAtoms, hadd, Nat.dist_eq_sub_of_le hij.le] using
      lattice_gap_bound g a hw hm i ((j : ℕ) - i) hk hk'
  intro i j hij
  by_cases hlt : (i : ℕ) < j
  · exact upper i j hlt
  · have hrev : (j : ℕ) < i := by
      have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      omega
    rw [B_hermitian, norm_conj, Nat.dist_comm]
    exact upper j i hrev

theorem all_actual_eleven_diagonal_bounds
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneOneTwentyEightAt g a) :
    ∀ i : Fin 11, (5671 / 3200 : ℝ) * energy g.1 ≤
      -(B (elevenAtoms g i) (elevenAtoms g i)).re := by
  intro i
  have hs := translate_logSupportIn g (qNineShiftV1 i)
    (a - 1 / 256) (a + 1 / 256) hw
  have hwidth : WidthOneOneTwentyEightAt
      (elevenAtoms g i) (a + qNineShiftV1 i) := by
    change LogSupportIn (translatePacket g (qNineShiftV1 i))
      (a + qNineShiftV1 i - 1 / 256) (a + qNineShiftV1 i + 1 / 256)
    convert hs using 1 <;> ring
  have hd := fine_diagonal_5671_over_3200_v3
    (elevenAtoms g i) (a + qNineShiftV1 i) hwidth
  simpa only [elevenAtoms, translate_energy] using hd

/-- The actual arithmetic form of every complex linear combination of
the eleven lattice translates has the required sign. All mixed-entry
hypotheses are derived above, including the genuine prime-power gaps. -/
theorem actual_eleven_lattice_arithmetic_nonpositive
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneOneTwentyEightAt g a)
    (hm : WeilMomentConditionsV1 g) (z : Fin 11 → ℂ) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 (packetSum z (elevenAtoms g)))).re ≤ 0 := by
  apply AEGIS.RHFeshbachWeilClosureV2.actual_gram_arithmetic_nonpositive
    z (elevenAtoms g) (5671 / 3200) (energy g.1)
    (energy_nonnegative g.1) elevenCost elevenCost_nonnegative
    (all_actual_eleven_diagonal_bounds g a hw)
    (all_actual_eleven_mixed_bounds g a hw hm)
  norm_num [elevenCost, Finset.sum_Icc_succ_top]

/-- The actual eleven-row maximum agrees with the source SOS budget. -/
theorem eleven_row_bound (i : Fin 11) :
    rowSum elevenCost i ≤ (1621 / 1850 : ℝ) := by
  unfold rowSum
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  fin_cases i <;> norm_num [Fin.sum_univ_succ, elevenCost, Nat.dist]

/-- Bind the exact 106083/118400 finite margin to the actual analytic packets. -/
theorem actual_eleven_lattice_coercive
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneOneTwentyEightAt g a)
    (hm : WeilMomentConditionsV1 g) (z : Fin 11 → ℂ) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 (packetSum z (elevenAtoms g)))).re ≤
        -(106083 / 118400 : ℝ) * energy g.1 * ∑ i, ‖z i‖ ^ 2 := by
  have h := gram_re_le z (elevenAtoms g)
    (5671 / 3200) (energy g.1) (1621 / 1850)
    (energy_nonnegative g.1) elevenCost elevenCost_nonnegative
    (all_actual_eleven_diagonal_bounds g a hw)
    (all_actual_eleven_mixed_bounds g a hw hm) eleven_row_bound
  have hmargin : (5671 / 3200 : ℝ) - 1621 / 1850 =
      106083 / 118400 := by norm_num
  rw [hmargin] at h
  change (B (packetSum z (elevenAtoms g)) (packetSum z (elevenAtoms g))).re ≤ _
  exact h

/-- Exact integer inequalities for outward Q16.16 rounding. -/
theorem q16_integer_certificate :
    (116142 * 3200 : ℕ) ≤ 5671 * 65536 ∧
    (65536 : ℕ) ≤ 656 * 100 ∧
    (57 * 65536 : ℕ) ≤ 37356 * 100 ∧
    (837 * 65536 : ℕ) ≤ 14826 * 3700 ∧
    (2 * (8 * 656 + 37356 + 14826) + 1282 : ℕ) = 116142 := by
  decide

/-- Upper-rounded analytic gap costs, at scale 2^16. -/
def q16Cost (k : ℕ) : ℝ :=
  if k = 9 then 37356 / 65536 else
  if k = 10 then 14826 / 65536 else 656 / 65536

theorem q16Cost_nonnegative (k : ℕ) : 0 ≤ q16Cost k := by
  unfold q16Cost
  split_ifs <;> norm_num

theorem elevenCost_le_q16Cost (k : ℕ) : elevenCost k ≤ q16Cost k := by
  unfold elevenCost q16Cost
  split_ifs <;> norm_num

/-- The full conservative row budget retains a strictly positive margin. -/
theorem q16_budget_exact :
    (116142 / 65536 : ℝ) - 2 * ∑ k ∈ Finset.Icc 1 10, q16Cost k =
      641 / 32768 := by
  norm_num [q16Cost, Finset.sum_Icc_succ_top]

/-- Evaluate each of the eleven actual rows instead of doubling all gap costs. -/
theorem q16_row_bound (i : Fin 11) :
    rowSum q16Cost i ≤ (57430 / 65536 : ℝ) := by
  unfold rowSum
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  fin_cases i <;> norm_num [Fin.sum_univ_succ, q16Cost, Nat.dist]

/-- Actual Weil coercivity after outward rounding of every analytic cost.
The seed and translation domain are the same as the exact analytic certificate. -/
theorem actual_eleven_lattice_q16_coercive
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneOneTwentyEightAt g a)
    (hm : WeilMomentConditionsV1 g) (z : Fin 11 → ℂ) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 (packetSum z (elevenAtoms g)))).re ≤
        -(7339 / 8192 : ℝ) * energy g.1 * ∑ i, ‖z i‖ ^ 2 := by
  have he := energy_nonnegative g.1
  have hd : ∀ i : Fin 11, (116142 / 65536 : ℝ) * energy g.1 ≤
      -(B (elevenAtoms g i) (elevenAtoms g i)).re := by
    intro i
    exact (mul_le_mul_of_nonneg_right
      (by norm_num : (116142 / 65536 : ℝ) ≤ 5671 / 3200) he).trans
        (all_actual_eleven_diagonal_bounds g a hw i)
  have hx : ∀ i j : Fin 11, i ≠ j →
      ‖B (elevenAtoms g i) (elevenAtoms g j)‖ ≤
        q16Cost (Nat.dist i j) * energy g.1 := by
    intro i j hij
    exact (all_actual_eleven_mixed_bounds g a hw hm i j hij).trans
      (mul_le_mul_of_nonneg_right (elevenCost_le_q16Cost _) he)
  have h := gram_re_le z (elevenAtoms g)
    (116142 / 65536) (energy g.1) (57430 / 65536)
    he q16Cost q16Cost_nonnegative hd hx q16_row_bound
  have hmargin : (116142 / 65536 : ℝ) - 57430 / 65536 =
      7339 / 8192 := by norm_num
  rw [hmargin] at h
  change (B (packetSum z (elevenAtoms g)) (packetSum z (elevenAtoms g))).re ≤ _
  exact h

/-- Positive rational Schur weights; endpoints and near-endpoints retain
larger weights to pay the source gap-9 and gap-10 costs. -/
def elevenSchurWeight (i : Fin 11) : ℝ :=
  if (i : ℕ) = 0 ∨ (i : ℕ) = 10 then 89 else if (i : ℕ) = 1 ∨ (i : ℕ) = 9 then 74 else 5

theorem elevenSchurWeight_positive (i : Fin 11) : 0 < elevenSchurWeight i := by
  unfold elevenSchurWeight
  split_ifs <;> norm_num

/-- The diagonal is excluded. All 110 oriented mixed entries are retained. -/
def elevenSchurCost (i j : Fin 11) : ℝ :=
  if Nat.dist i j = 0 then 0 else q16Cost (Nat.dist i j)

def elevenWeightUnits (i : Fin 11) : ℕ :=
  if (i : ℕ) = 0 ∨ (i : ℕ) = 10 then 89 else
  if (i : ℕ) = 1 ∨ (i : ℕ) = 9 then 74 else 5

def elevenCostUnits (i j : Fin 11) : ℕ :=
  if Nat.dist i j = 0 then 0 else
  if Nat.dist i j = 9 then 37356 else if Nat.dist i j = 10 then 14826 else 656

theorem eleven_weighted_integer_certificate : ∀ i : Fin 11,
    (∑ j, elevenCostUnits i j * elevenWeightUnits j) ≤
      46708 * elevenWeightUnits i := by decide

theorem eleven_weighted_row_bound (i : Fin 11) :
    (∑ j, elevenSchurCost i j * (elevenSchurWeight j / elevenSchurWeight i)) ≤
      (46708 / 65536 : ℝ) := by
  have hcast (j : Fin 11) : elevenSchurWeight j = (elevenWeightUnits j : ℝ) := by
    unfold elevenSchurWeight elevenWeightUnits
    split_ifs <;> norm_num
  have hcost (j : Fin 11) :
      elevenSchurCost i j = (elevenCostUnits i j : ℝ) / 65536 := by
    unfold elevenSchurCost elevenCostUnits q16Cost
    split_ifs <;> norm_num
  have hw : (0 : ℝ) < (elevenWeightUnits i : ℝ) := by
    rw [← hcast]
    exact elevenSchurWeight_positive i
  have hreal : (∑ j, (elevenCostUnits i j : ℝ) * (elevenWeightUnits j : ℝ)) ≤
      46708 * (elevenWeightUnits i : ℝ) := by
    exact_mod_cast eleven_weighted_integer_certificate i
  simp_rw [hcost, hcast]
  have heq : (∑ j, (elevenCostUnits i j : ℝ) / 65536 *
      ((elevenWeightUnits j : ℝ) / (elevenWeightUnits i : ℝ))) =
      (∑ j, (elevenCostUnits i j : ℝ) * (elevenWeightUnits j : ℝ)) /
        (65536 * (elevenWeightUnits i : ℝ)) := by
    rw [sum_div]
    apply sum_congr rfl
    intro j _
    field_simp
  rw [heq]
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 65536) hw)).2
  nlinarith

theorem eleven_weighted_margin :
    (116142 / 65536 : ℝ) - 46708 / 65536 = 34717 / 32768 := by norm_num


/-- Stronger source-bound eleven-block coercivity. Every mixed estimate is
supplied by the existing analytic lattice lemmas, with no new analytic premise.
This finite translate class is not asserted to cover arbitrary packets. -/
theorem actual_eleven_lattice_weighted_q16_coercive
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneOneTwentyEightAt g a)
    (hm : WeilMomentConditionsV1 g) (z : Fin 11 → ℂ) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 (packetSum z (elevenAtoms g)))).re ≤
        -(34717 / 32768 : ℝ) * energy g.1 * ∑ i, ‖z i‖ ^ 2 := by
  have he := energy_nonnegative g.1
  have hd : ∀ i : Fin 11, (116142 / 65536 : ℝ) * energy g.1 ≤
      -(B (elevenAtoms g i) (elevenAtoms g i)).re := by
    intro i
    exact (mul_le_mul_of_nonneg_right
      (by norm_num : (116142 / 65536 : ℝ) ≤ 5671 / 3200) he).trans
        (all_actual_eleven_diagonal_bounds g a hw i)
  have hc : ∀ i j, 0 ≤ elevenSchurCost i j := by
    intro i j
    unfold elevenSchurCost
    split_ifs
    · exact le_rfl
    · exact q16Cost_nonnegative _
  have hx : ∀ i j : Fin 11, i ≠ j →
      ‖B (elevenAtoms g i) (elevenAtoms g j)‖ ≤ elevenSchurCost i j * energy g.1 := by
    intro i j hij
    have hdist : Nat.dist (i : ℕ) (j : ℕ) ≠ 0 := by
      intro h
      exact hij (Fin.ext (Nat.eq_of_dist_eq_zero h))
    rw [elevenSchurCost, if_neg hdist]
    exact (all_actual_eleven_mixed_bounds g a hw hm i j hij).trans
      (mul_le_mul_of_nonneg_right (elevenCost_le_q16Cost _) he)
  have hs : ∀ i j, elevenSchurCost i j = elevenSchurCost j i := by
    intro i j
    simp only [elevenSchurCost, Nat.dist_comm]
  have h := AEGIS.WeightedSchur.weighted_gram
    (fun i j => B (elevenAtoms g i) (elevenAtoms g j)) z
    elevenSchurCost elevenSchurWeight (116142 / 65536) (energy g.1)
    (46708 / 65536) he hc (fun i => by simp [elevenSchurCost]) hs
    elevenSchurWeight_positive hd hx eleven_weighted_row_bound
  rw [eleven_weighted_margin] at h
  change (B (packetSum z (elevenAtoms g)) (packetSum z (elevenAtoms g))).re ≤ _
  rw [B_packetSum]
  exact h

end AEGIS.RHActualElevenLatticeV1

#print axioms AEGIS.RHActualElevenLatticeV1.lattice_gap_bound
#print axioms AEGIS.RHActualElevenLatticeV1.all_actual_eleven_mixed_bounds
#print axioms AEGIS.RHActualElevenLatticeV1.all_actual_eleven_diagonal_bounds
#print axioms AEGIS.RHActualElevenLatticeV1.actual_eleven_lattice_arithmetic_nonpositive

#print axioms AEGIS.RHActualElevenLatticeV1.q16_integer_certificate
#print axioms AEGIS.RHActualElevenLatticeV1.elevenCost_le_q16Cost
#print axioms AEGIS.RHActualElevenLatticeV1.q16_budget_exact
#print axioms AEGIS.RHActualElevenLatticeV1.actual_eleven_lattice_q16_coercive

#print axioms AEGIS.RHActualElevenLatticeV1.q16_row_bound

#print axioms AEGIS.RHActualElevenLatticeV1.eleven_row_bound
#print axioms AEGIS.RHActualElevenLatticeV1.actual_eleven_lattice_coercive

#print axioms AEGIS.RHActualElevenLatticeV1.eleven_weighted_row_bound
#print axioms AEGIS.RHActualElevenLatticeV1.actual_eleven_lattice_weighted_q16_coercive

#print axioms AEGIS.RHActualElevenLatticeV1.eleven_weighted_integer_certificate
