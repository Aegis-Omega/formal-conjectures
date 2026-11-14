import RHIndependentFinePrimeWindowV1
import RHIndependentFinePrimeNormV1
import RHRationalGapTenPrimeBoundV1

/-!
Port of the existing gap-nine/ten finite-window arithmetic to independent
packet shapes. The integer envelopes and square-root denominators are reused
from the pinned PR721 sources. Scalar certificates formerly private in those
sources are exposed here by the same bounded prime-power checker; no new
prime estimate, common mother, or mixed Weil-sign assumption is introduced.
-/

open Complex
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHIndependentFineGapNineTenV1

open AEGIS.WeilMixedClosureV2 AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHRationalNinePacketPrimeWindowV1
open AEGIS.RHRationalGapNinePrimeBoundV1
open AEGIS.RHRationalGapTenPrimeBoundV1
open AEGIS.RHIndependentFinePrimeSupportV1
open AEGIS.RHIndependentFinePrimeWindowV1
open AEGIS.RHIndependentFinePrimeNormV1
open AEGIS.RHActualMixedDefectV1

theorem prime_term_norm_le_scalar
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : LogSupportIn p (a - 1 / 256) (a + 1 / 256))
    (hq : LogSupportIn q (b - 1 / 256) (b + 1 / 256))
    (hsep : (1 / 128 : ℝ) < b - a) (n : ℕ)
    (N L : ℝ) (hN : 0 < N) (hNm : N ^ 2 ≤ (n + 1 : ℕ))
    (hL : ArithmeticFunction.vonMangoldt (n + 1) ≤ L) :
    ‖WeilPrimeTermV1 (mixed p q) n‖ ≤
      (L / N) * ((energy p.1 + energy q.1) / 2) := by
  have hz := mixed_nat_zero_of_fine_separation p q a b hp hq hsep
    (n + 1) (by omega)
  have hr := reciprocal_mixed_norm_le_of_square_le p q (n + 1)
    (by omega) N hN hNm
  have heq : WeilPrimeTermV1 (mixed p q) n =
      (ArithmeticFunction.vonMangoldt (n + 1) : ℂ) *
        ((1 / ((n + 1 : ℕ) : ℂ)) * mixed p q (((n + 1 : ℕ) : ℝ)⁻¹)) := by
    simp only [WeilPrimeTermV1, hz, zero_add]
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hL0 : 0 ≤ L := ArithmeticFunction.vonMangoldt_nonneg.trans hL
  calc
    _ ≤ L * ((1 / N) * ((energy p.1 + energy q.1) / 2)) :=
      mul_le_mul hL hr (norm_nonneg _) hL0
    _ = _ := by ring

theorem gap_nine_scalar_window
    {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - gapNineV1| ≤ (1 / 128 : ℝ))
    (h673 : m ≠ 673) (h677 : m ≠ 677) :
    ArithmeticFunction.vonMangoldt m = 0 := by
  obtain ⟨hlo, hhi⟩ := gap_nine_candidate_range_v1 hm hwin
  apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac m).mp hpp
  interval_cases m
  all_goals
    first
    | exact h673 rfl
    | exact h677 rfl
    | norm_num at hk
      interval_cases k <;> norm_num at heq

theorem gap_ten_scalar_window
    {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - gapTenV1| ≤ (1 / 128 : ℝ))
    (h1399 : m ≠ 1399) :
    ArithmeticFunction.vonMangoldt m = 0 := by
  obtain ⟨hlo, hhi⟩ := gap_ten_candidate_range_v1 hm hwin
  apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
  intro hpp
  obtain ⟨k, hk, hkpos, heq⟩ :=
    (isPrimePow_nat_iff_bounded_log_minFac m).mp hpp
  interval_cases m
  all_goals
    first
    | exact h1399 rfl
    | norm_num at hk
      interval_cases k <;> norm_num at heq

theorem gap_nine_independent_prime_sum
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b) (hgap : b - a = gapNineV1) :
    WeilPrimeSumV1 (mixed p q) =
      WeilPrimeTermV1 (mixed p q) 672 + WeilPrimeTermV1 (mixed p q) 676 := by
  have hsep : (1 / 128 : ℝ) < b - a := by rw [hgap]; exact gapNine_pos_v1
  have h := prime_sum_eq_sum_of_fine_window_vonMangoldt
    p q a b hp hq hsep {672, 676} (by
      intro n hn hwin
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      rw [hgap] at hwin
      exact gap_nine_scalar_window (by omega) hwin (by omega) (by omega))
  simpa using h

theorem gap_ten_independent_prime_sum
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b) (hgap : b - a = gapTenV1) :
    WeilPrimeSumV1 (mixed p q) = WeilPrimeTermV1 (mixed p q) 1398 := by
  have hsep : (1 / 128 : ℝ) < b - a := by rw [hgap]; exact gapTen_pos_v1
  have h := prime_sum_eq_sum_of_fine_window_vonMangoldt
    p q a b hp hq hsep {1398} (by
      intro n hn hwin
      simp only [Finset.mem_singleton] at hn
      rw [hgap] at hwin
      exact gap_ten_scalar_window (by omega) hwin (by omega))
  simpa using h

private theorem log_673_le_seven : Real.log 673 ≤ 7 := by
  have h : Real.log 673 < Real.log 1024 :=
    (Real.log_lt_log_iff (by norm_num) (by norm_num)).2 (by norm_num)
  rw [show (1024 : ℝ) = 2 ^ (10 : ℕ) by norm_num, Real.log_pow] at h
  norm_num at h
  nlinarith [AEGIS.WeilThreeBlockAnalyticConstantsV21.log_two_upper]

private theorem log_677_le_seven : Real.log 677 ≤ 7 := by
  have h : Real.log 677 < Real.log 1024 :=
    (Real.log_lt_log_iff (by norm_num) (by norm_num)).2 (by norm_num)
  rw [show (1024 : ℝ) = 2 ^ (10 : ℕ) by norm_num, Real.log_pow] at h
  norm_num at h
  nlinarith [AEGIS.WeilThreeBlockAnalyticConstantsV21.log_two_upper]

private theorem log_1399_le_eight : Real.log 1399 ≤ 8 := by
  have h : Real.log 1399 < Real.log 2048 :=
    (Real.log_lt_log_iff (by norm_num) (by norm_num)).2 (by norm_num)
  rw [show (2048 : ℝ) = 2 ^ (11 : ℕ) by norm_num, Real.log_pow] at h
  norm_num at h
  nlinarith [AEGIS.WeilThreeBlockAnalyticConstantsV21.log_two_upper]

theorem gap_nine_independent_prime_norm
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b) (hgap : b - a = gapNineV1) :
    ‖WeilPrimeSumV1 (mixed p q)‖ ≤
      (14 / 25 : ℝ) * ((energy p.1 + energy q.1) / 2) := by
  have hsep : (1 / 128 : ℝ) < b - a := by rw [hgap]; exact gapNine_pos_v1
  have h673 := prime_term_norm_le_scalar p q a b hp hq hsep 672 25 7
    (by norm_num) (by norm_num) (by
      rw [show (672 + 1 : ℕ) = 673 by norm_num,
        ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 673)]
      exact log_673_le_seven)
  have h677 := prime_term_norm_le_scalar p q a b hp hq hsep 676 25 7
    (by norm_num) (by norm_num) (by
      rw [show (676 + 1 : ℕ) = 677 by norm_num,
        ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 677)]
      exact log_677_le_seven)
  rw [gap_nine_independent_prime_sum p q a b hp hq hgap]
  have hsum := norm_add_le (WeilPrimeTermV1 (mixed p q) 672)
    (WeilPrimeTermV1 (mixed p q) 676)
  linarith

theorem gap_ten_independent_prime_norm
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b) (hgap : b - a = gapTenV1) :
    ‖WeilPrimeSumV1 (mixed p q)‖ ≤
      (8 / 37 : ℝ) * ((energy p.1 + energy q.1) / 2) := by
  have hsep : (1 / 128 : ℝ) < b - a := by rw [hgap]; exact gapTen_pos_v1
  rw [gap_ten_independent_prime_sum p q a b hp hq hgap]
  exact prime_term_norm_le_scalar p q a b hp hq hsep 1398 37 8
    (by norm_num) (by norm_num) (by
      rw [show (1398 + 1 : ℕ) = 1399 by norm_num,
        ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 1399)]
      exact log_1399_le_eight)

theorem gap_nine_independent_B_norm
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p) (hgap : b - a = gapNineV1) :
    ‖AEGIS.WeilMixedAlgebraV2.B p q‖ ≤
      (57 / 100 : ℝ) * ((energy p.1 + energy q.1) / 2) := by
  have ha := distinct_fine_far_actual_B_norm_le_prime_plus_arch p q a b hp hq hm
    (by rw [hgap]; exact log_two_le_gapNine_v1)
  have hpq := gap_nine_independent_prime_norm p q a b hp hq hgap
  linarith

theorem gap_ten_independent_B_norm
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p) (hgap : b - a = gapTenV1) :
    ‖AEGIS.WeilMixedAlgebraV2.B p q‖ ≤
      (837 / 3700 : ℝ) * ((energy p.1 + energy q.1) / 2) := by
  have ha := distinct_fine_far_actual_B_norm_le_prime_plus_arch p q a b hp hq hm
    (by rw [hgap]; exact log_two_le_gapTen_v1)
  have hpq := gap_ten_independent_prime_norm p q a b hp hq hgap
  linarith

end AEGIS.RHIndependentFineGapNineTenV1

#print axioms AEGIS.RHIndependentFineGapNineTenV1.prime_term_norm_le_scalar
#print axioms AEGIS.RHIndependentFineGapNineTenV1.gap_nine_independent_prime_sum
#print axioms AEGIS.RHIndependentFineGapNineTenV1.gap_ten_independent_prime_sum
#print axioms AEGIS.RHIndependentFineGapNineTenV1.gap_nine_independent_B_norm
#print axioms AEGIS.RHIndependentFineGapNineTenV1.gap_ten_independent_B_norm
