import RHIndependentFineGapNineTenV1
import Mathlib.Algebra.QuadraticDiscriminant
import AEGISOverlay.RHActualElevenLatticeV1
import AEGISOverlay.RHMixedBudgetRefinementV1

/-!
The existing eleven-lattice geometry with eleven independent packet shapes.
All prime-window and Archimedean inputs are actual source-backed producers;
the previous same-mother assumption is removed. The original Schur weights
and costs are reused. This theorem has a specified eleven-window domain.
-/

open Complex Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace AEGIS.RHIndependentElevenCompositionV1

open AEGIS.WeilMixedAlgebraV2 AEGIS.WeilMixedClosureV2
open AEGIS.WeilDisjointEnergyV2 AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHRationalNinePacketPrimeWindowV1
open AEGIS.RHActualMixedDefectV1 AEGIS.RHActualElevenLatticeV1
open AEGIS.RHFineDiagonalUpgradeV3 AEGIS.RHGramExpansionV13
open AEGIS.RHIndependentFinePrimeWindowV1
open AEGIS.RHIndependentFineGapNineTenV1
open AEGIS.RHMixedBudgetRefinementV1

theorem log_two_le_lattice_gap (k : ℕ) (hk : 1 ≤ k) :
    Real.log 2 ≤ Real.log (qNineV1 ^ k) := by
  have hlog : Real.log 2 < Real.log qNineV1 :=
    (Real.log_lt_log_iff (by norm_num) (by norm_num [qNineV1])).2
      (by norm_num [qNineV1])
  have hpos : 0 < Real.log qNineV1 := Real.log_pos (by norm_num [qNineV1])
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [log_qNine_pow_v1]
  nlinarith

theorem lattice_gap_independent_mean_bound
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p) (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 10)
    (hgap : b - a = Real.log (qNineV1 ^ k)) :
    ‖B p q‖ ≤ elevenCost k * ((energy p.1 + energy q.1) / 2) := by
  have hlarge : Real.log 2 ≤ b - a := by
    rw [hgap]
    exact log_two_le_lattice_gap k hk
  have hsep : (1 / 128 : ℝ) < b - a :=
    lt_of_lt_of_le (by
      have h := AEGIS.WeilThreeBlockAnalyticConstantsV21.log_two_lower
      linarith) hlarge
  by_cases hk8 : k ≤ 8
  · have hvm : ∀ m : ℕ, 0 < m →
        |Real.log (m : ℝ) - (b - a)| ≤ 1 / 128 →
          ArithmeticFunction.vonMangoldt m = 0 := by
      intro m hmpos hwin
      rw [hgap] at hwin
      interval_cases k
      · exact gap_one_vonMangoldt_zero_v1 hmpos hwin
      · exact gap_two_vonMangoldt_zero_v1 hmpos hwin
      · exact gap_three_vonMangoldt_zero_v1 hmpos hwin
      · exact gap_four_vonMangoldt_zero_v1 hmpos hwin
      · exact gap_five_vonMangoldt_zero_v1 hmpos hwin
      · exact gap_six_vonMangoldt_zero_v1 hmpos hwin
      · exact gap_seven_vonMangoldt_zero_v1 hmpos hwin
      · exact gap_eight_vonMangoldt_zero_v1 hmpos hwin
    have hz := prime_sum_zero_of_fine_window_vonMangoldt p q a b hp hq hsep hvm
    have hb := distinct_fine_far_actual_B_norm_le_prime_plus_arch p q a b hp hq hm hlarge
    rw [hz, norm_zero, zero_add] at hb
    have h9 : k ≠ 9 := by omega
    have h10 : k ≠ 10 := by omega
    simp only [elevenCost, if_neg h9, if_neg h10]
    linarith
  · have hcases : k = 9 ∨ k = 10 := by omega
    rcases hcases with rfl | rfl
    · simpa [elevenCost] using gap_nine_independent_B_norm p q a b hp hq hm hgap
    · simpa [elevenCost] using gap_ten_independent_B_norm p q a b hp hq hm hgap

/-- The usual rescaling argument as the existing discriminant theorem.
It includes zero energies, without division or a limiting argument. -/
theorem norm_le_sqrt_energy_of_scaled_mean
    (p q : WeilCompactSmoothGV1) (c : ℝ) (hc : 0 ≤ c)
    (hmean : ∀ r : ℝ, ‖B (scalePacket (r : ℂ) p) q‖ ≤
      c * ((energy (scalePacket (r : ℂ) p).1 + energy q.1) / 2)) :
    ‖B p q‖ ≤ c * (Real.sqrt (energy p.1) * Real.sqrt (energy q.1)) := by
  have hpoly : ∀ r : ℝ, 0 ≤
      (c * energy p.1) * (r * r) + (-2 * ‖B p q‖) * r + c * energy q.1 := by
    intro r
    have h := hmean r
    rw [B_scale_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      energy_scale_real] at h
    have hl := mul_le_mul_of_nonneg_right (le_abs_self r) (norm_nonneg (B p q))
    nlinarith
  have hd := discrim_le_zero hpoly
  simp only [discrim] at hd
  have hsq : ‖B p q‖ ^ 2 ≤ c ^ 2 * (energy p.1 * energy q.1) := by nlinarith
  have ht : (c * (Real.sqrt (energy p.1) * Real.sqrt (energy q.1))) ^ 2 =
      c ^ 2 * (energy p.1 * energy q.1) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (energy_nonnegative _),
      Real.sq_sqrt (energy_nonnegative _)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))).mp (by
      rw [ht]
      exact hsq)

theorem lattice_gap_independent_sqrt_bound
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p) (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 10)
    (hgap : b - a = Real.log (qNineV1 ^ k)) :
    ‖B p q‖ ≤ elevenCost k *
      (Real.sqrt (energy p.1) * Real.sqrt (energy q.1)) := by
  apply norm_le_sqrt_energy_of_scaled_mean p q (elevenCost k)
    (elevenCost_nonnegative k)
  intro r
  exact lattice_gap_independent_mean_bound (scalePacket (r : ℂ) p) q a b
    (fine_width_scale p (r : ℂ) a hp) hq
    (AEGIS.WeilFinalSignTranslationBoundV10.momentConditions_scalePacket_v10 (r : ℂ) p hm)
    k hk hk' hgap

theorem all_independent_eleven_mixed_bounds
    (gs : Fin 11 → WeilCompactSmoothGV1) (a : ℝ)
    (hw : ∀ i, WidthOneOneTwentyEightAt (gs i) (a + qNineShiftV1 i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i)) :
    ∀ i j : Fin 11, i ≠ j → ‖B (gs i) (gs j)‖ ≤
      elevenCost (Nat.dist i j) *
        (Real.sqrt (energy (gs i).1) * Real.sqrt (energy (gs j).1)) := by
  have upper (i j : Fin 11) (hij : (i : ℕ) < j) :
      ‖B (gs i) (gs j)‖ ≤ elevenCost (Nat.dist i j) *
        (Real.sqrt (energy (gs i).1) * Real.sqrt (energy (gs j).1)) := by
    have hk : 1 ≤ (j : ℕ) - i := by omega
    have hk' : (j : ℕ) - i ≤ 10 := by omega
    have hadd : (i : ℕ) + ((j : ℕ) - i) = j := by omega
    have hgap : (a + qNineShiftV1 j) - (a + qNineShiftV1 i) =
        Real.log (qNineV1 ^ ((j : ℕ) - i)) := by
      have h := qNineShift_gap_v1 i ((j : ℕ) - i)
      rw [hadd] at h
      linarith
    simpa only [Nat.dist_eq_sub_of_le hij.le] using
      lattice_gap_independent_sqrt_bound (gs i) (gs j)
        (a + qNineShiftV1 i) (a + qNineShiftV1 j) (hw i) (hw j) (hm i)
        ((j : ℕ) - i) hk hk' hgap
  intro i j hij
  by_cases hlt : (i : ℕ) < j
  · exact upper i j hlt
  · have hrev : (j : ℕ) < i := by
      have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      omega
    rw [B_hermitian, norm_conj, Nat.dist_comm,
      mul_comm (Real.sqrt (energy (gs i).1))]
    exact upper j i hrev

/-- Supply the actual cross estimates to the existing independent-eleven
consumer recovered at b41de111. The old exact row certificate, diagonals,
and full Gram proof are reused without reconstruction. -/
theorem actual_independent_eleven_coercive
    (gs : Fin 11 → WeilCompactSmoothGV1) (a : ℝ)
    (hw : ∀ i, WidthOneOneTwentyEightAt (gs i) a)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i)) (z : Fin 11 → ℂ) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 (packetSum z (independentElevenAtoms gs)))).re ≤
        -(1203957 / 1136000 : ℝ) * ∑ i, energy (gs i).1 * ‖z i‖ ^ 2 := by
  have hwidth : ∀ i, WidthOneOneTwentyEightAt
      (independentElevenAtoms gs i) (a + qNineShiftV1 i) := by
    intro i
    have hs := translate_logSupportIn (gs i) (qNineShiftV1 i)
      (a - 1 / 256) (a + 1 / 256) (hw i)
    change LogSupportIn (translatePacket (gs i) (qNineShiftV1 i))
      (a + qNineShiftV1 i - 1 / 256) (a + qNineShiftV1 i + 1 / 256)
    convert hs using 1 <;> ring
  have hmom : ∀ i, WeilMomentConditionsV1 (independentElevenAtoms gs i) := by
    intro i
    exact AEGIS.WeilThreeBlockTranslatedPacketsV22.translate_preserves_moments
      (gs i) (qNineShiftV1 i) (hm i)
  apply independent_eleven_exact_coercive_of_actual_cross gs a hw ?_ z
  intro i j hij
  have h := all_independent_eleven_mixed_bounds
    (independentElevenAtoms gs) a hwidth hmom i j hij
  have hdist : Nat.dist (i : ℕ) j ≠ 0 := by
    intro hz
    exact hij (Fin.ext (Nat.eq_of_dist_eq_zero hz))
  simpa only [independentElevenExactCost, if_neg hdist,
    independentElevenAtoms, translate_energy] using h

end AEGIS.RHIndependentElevenCompositionV1

#print axioms AEGIS.RHIndependentElevenCompositionV1.lattice_gap_independent_mean_bound
#print axioms AEGIS.RHIndependentElevenCompositionV1.norm_le_sqrt_energy_of_scaled_mean
#print axioms AEGIS.RHIndependentElevenCompositionV1.lattice_gap_independent_sqrt_bound
#print axioms AEGIS.RHIndependentElevenCompositionV1.all_independent_eleven_mixed_bounds
#print axioms AEGIS.RHIndependentElevenCompositionV1.actual_independent_eleven_coercive
