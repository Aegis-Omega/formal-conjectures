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

end AEGIS.RHActualElevenLatticeV1

#print axioms AEGIS.RHActualElevenLatticeV1.lattice_gap_bound
#print axioms AEGIS.RHActualElevenLatticeV1.all_actual_eleven_mixed_bounds
#print axioms AEGIS.RHActualElevenLatticeV1.all_actual_eleven_diagonal_bounds
#print axioms AEGIS.RHActualElevenLatticeV1.actual_eleven_lattice_arithmetic_nonpositive
