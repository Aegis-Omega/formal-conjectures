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

import WeilSevenBlockCombV1
import WeilDiagonalQuadMomentV1

/-!
AEGIS Ω — the eight-block dyadic comb at width 1/32, with the gap-7 resonances (Claude Lab, 2026-11-22).

Blocks `blk g j = T_{j log 2} g`, `j = 0, …, 7`, for `g` of log-width `1/32` with both moments. Compared with
`WeilSevenBlockCombV1`:
* the diagonal is `59/20 · E` (`WeilDiagonalQuadMomentV1.width_diagonal_59_over_20`, quadratic gain plus
  moments) instead of `109/50 · E`;
* gap `k = 7` is admitted. Its log-window contains the prime powers `125 = 5³`, `127`, `128 = 2⁷` and `131`
  (`prime_window7`); `126, 129, 130, 132` have `Λ = 0`. Off the centre the mixed value is not known exactly, so
  each term is bounded through `e^{u/2} mixed(e^u) = C(u + d₂ − d₁)` and `‖C‖ ≤ E` (`term_norm_le`):
  `‖Λ(m) m⁻¹ mixed(1/m)‖ ≤ Λ(m) m^{−1/2} E`. The four masses sum to at most `1.06115`
  (`prime_sum7_norm`), so `‖B‖ ≤ (1067/1000) E` at gap 7;
* the Schur test is unweighted: the largest row sum of the ceilings is `2.586 ≤ 13/5`.

Result (`eight_block_gram_bound`): `Re Σ z_i conj(z_j) B(blk g i, blk g j) ≤ −(1/4) · E · Σ ‖z_i‖²`.

Fixed-width comb class only. Not RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilEightBlockCombV1

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilArchimedeanCothTailV1
open AEGIS.WeilFiveBlockCombV1
open AEGIS.WeilSevenBlockCombV1

/-- In the log-window of gap `7` every positive integer is `125, 127, 128, 131` or has `Λ = 0`. -/
theorem prime_window7 {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - ((7 : ℕ) : ℝ) * Real.log 2| ≤ 1 / 32) :
    m = 125 ∨ m = 127 ∨ m = 128 ∨ m = 131 ∨ ArithmeticFunction.vonMangoldt m = 0 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := abs_le.mp hwin
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ ((7 : ℕ) : ℝ) * Real.log 2 + 1 / 32 by linarith [habs.2])
  have hlo := Real.exp_le_exp.mpr
    (show ((7 : ℕ) : ℝ) * Real.log 2 - 1 / 32 ≤ Real.log (m : ℝ) by linarith [habs.1])
  have h2k : Real.exp (((7 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ 7 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, h2k] at hup
  rw [sub_eq_add_neg, Real.exp_add, h2k] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have e1 := mul_lt_mul_of_pos_left exp_one_div_32_lt (by norm_num : (0 : ℝ) < 2 ^ 7)
  have e2 := mul_lt_mul_of_pos_left exp_neg_one_div_32_gt (by norm_num : (0 : ℝ) < 2 ^ 7)
  have hlt : (m : ℝ) < 2 ^ 7 * (65 / 63) := by linarith
  have hgt : (2 : ℝ) ^ 7 * (63 / 65) < m := by linarith
  norm_num at hlt hgt
  have h1 : m < 133 := by exact_mod_cast (show (m : ℝ) < 133 by linarith)
  have h2 : 124 < m := by exact_mod_cast (show (124 : ℝ) < m by linarith)
  interval_cases m
  · left; rfl
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 2) (q := 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 3) (q := 43) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 2) (q := 5) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · right; right; right; left; rfl
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 2) (q := 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

/-- **One prime term off the centre.** `‖Λ(m) (mixed(m) + m⁻¹ mixed(1/m))‖ ≤ Λ(m) m^{−1/2} E`. -/
theorem term_norm_le (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    {i j : ℕ} (hij : i < j) (n : ℕ) :
    ‖WeilPrimeTermV1 (mixed (blk g i) (blk g j)) n‖ ≤
      ArithmeticFunction.vonMangoldt (n + 1) * Real.exp (-Real.log ((n + 1 : ℕ) : ℝ) / 2) * energy g.1 := by
  have hp := blk_mixed_nat_zero g a hw hij (n + 1) (by omega)
  have hmpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hE := energy_nonnegative g.1
  set q := Real.exp (-Real.log ((n + 1 : ℕ) : ℝ) / 2) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hqq : q * q = (((n + 1 : ℕ) : ℝ))⁻¹ := by
    rw [hq, ← Real.exp_add,
      show -Real.log ((n + 1 : ℕ) : ℝ) / 2 + -Real.log ((n + 1 : ℕ) : ℝ) / 2 = -Real.log ((n + 1 : ℕ) : ℝ) by
        ring, Real.exp_neg, Real.exp_log hmpos]
  have hid : (q : ℂ) * mixed (blk g i) (blk g j) (((n + 1 : ℕ) : ℝ)⁻¹) =
      logCorrelationV25 g (-Real.log ((n + 1 : ℕ) : ℝ) + (j : ℝ) * Real.log 2 - (i : ℝ) * Real.log 2) := by
    have h := exp_half_mul_mixed_translate_v28 g ((i : ℝ) * Real.log 2) ((j : ℝ) * Real.log 2)
      (-Real.log ((n + 1 : ℕ) : ℝ))
    rw [Real.exp_neg (Real.log _), Real.exp_log hmpos] at h
    exact h
  have hC := norm_logCorrelation_le_energy_v25 g
    (-Real.log ((n + 1 : ℕ) : ℝ) + (j : ℝ) * Real.log 2 - (i : ℝ) * Real.log 2)
  rw [← hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0] at hC
  have hL : 0 ≤ ArithmeticFunction.vonMangoldt (n + 1) := ArithmeticFunction.vonMangoldt_nonneg
  simp only [WeilPrimeTermV1, hp, zero_add]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL, norm_div, norm_one,
    Complex.norm_natCast]
  have hmn : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) = q * q := by rw [hqq, one_div]
  rw [hmn]
  have hx : q * q * ‖mixed (blk g i) (blk g j) (((n + 1 : ℕ) : ℝ)⁻¹)‖ ≤ q * energy g.1 := by
    have := mul_le_mul_of_nonneg_left hC hq0.le
    nlinarith
  calc ArithmeticFunction.vonMangoldt (n + 1) * (q * q * ‖mixed (blk g i) (blk g j) (((n + 1 : ℕ) : ℝ)⁻¹)‖)
      ≤ ArithmeticFunction.vonMangoldt (n + 1) * (q * energy g.1) := mul_le_mul_of_nonneg_left hx hL
    _ = ArithmeticFunction.vonMangoldt (n + 1) * q * energy g.1 := by ring

/-- `log 128 = 7 log 2`. -/
theorem log_128 : Real.log 128 = 7 * Real.log 2 := by
  rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
  norm_num

/-- `log m ≤ 7 log 2 + (m/128 − 1)`. -/
theorem log_le_of_128 (m : ℝ) (hm : 0 < m) : Real.log m ≤ 7 * Real.log 2 + (m / 128 - 1) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m / 128 by positivity)
  rw [Real.log_div hm.ne' (by norm_num), log_128] at h
  linarith

theorem q_le (m r : ℝ) (hm : 0 < m) (hr : 0 < r) (hmr : 1 / m ≤ r ^ 2) :
    Real.exp (-Real.log m / 2) ≤ r := by
  set q := Real.exp (-Real.log m / 2) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hqq : q * q = 1 / m := by
    rw [hq, ← Real.exp_add, show -Real.log m / 2 + -Real.log m / 2 = -Real.log m by ring, Real.exp_neg,
      Real.exp_log hm, one_div]
  nlinarith

theorem mass_125 :
    ArithmeticFunction.vonMangoldt (124 + 1) * Real.exp (-Real.log ((124 + 1 : ℕ) : ℝ) / 2) ≤
      14398 / 100000 := by
  have e : ((124 + 1 : ℕ) : ℝ) = 125 := by norm_num
  have hv : ArithmeticFunction.vonMangoldt (124 + 1) = Real.log 125 / 3 := by
    rw [show (124 + 1 : ℕ) = 5 ^ 3 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num),
      show (125 : ℝ) = 5 ^ 3 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [e, hv]
  have hl := log_le_of_128 125 (by norm_num)
  have hl2 := Real.log_two_lt_d9
  have hq := q_le 125 (8945 / 100000) (by norm_num) (by norm_num) (by norm_num)
  have hpos : 0 ≤ Real.log 125 / 3 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 125 by norm_num)
    positivity
  have hb : Real.log 125 / 3 ≤ 16095310 / 10000000 := by
    have : Real.log 125 ≤ 7 * 0.6931471808 + (125 / 128 - 1) := by linarith
    linarith
  calc Real.log 125 / 3 * Real.exp (-Real.log 125 / 2) ≤ 16095310 / 10000000 * (8945 / 100000) :=
        mul_le_mul hb hq (Real.exp_pos _).le (by norm_num)
    _ ≤ 14398 / 100000 := by norm_num

theorem mass_127 :
    ArithmeticFunction.vonMangoldt (126 + 1) * Real.exp (-Real.log ((126 + 1 : ℕ) : ℝ) / 2) ≤
      42988 / 100000 := by
  have e : ((126 + 1 : ℕ) : ℝ) = 127 := by norm_num
  have hv : ArithmeticFunction.vonMangoldt (126 + 1) = Real.log 127 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [e, hv]
  have hl := log_le_of_128 127 (by norm_num)
  have hl2 := Real.log_two_lt_d9
  have hq := q_le 127 (8874 / 100000) (by norm_num) (by norm_num) (by norm_num)
  have hpos : 0 ≤ Real.log 127 := Real.log_nonneg (by norm_num)
  have hb : Real.log 127 ≤ 48442178 / 10000000 := by linarith
  calc Real.log 127 * Real.exp (-Real.log 127 / 2) ≤ 48442178 / 10000000 * (8874 / 100000) :=
        mul_le_mul hb hq (Real.exp_pos _).le (by norm_num)
    _ ≤ 42988 / 100000 := by norm_num

theorem mass_128 :
    ArithmeticFunction.vonMangoldt (127 + 1) * Real.exp (-Real.log ((127 + 1 : ℕ) : ℝ) / 2) ≤
      6127 / 100000 := by
  have e : ((127 + 1 : ℕ) : ℝ) = 128 := by norm_num
  have hv : ArithmeticFunction.vonMangoldt (127 + 1) = Real.log 2 := by
    rw [show (127 + 1 : ℕ) = 2 ^ 7 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  rw [e, hv]
  have hl2 := Real.log_two_lt_d9
  have hq := q_le 128 (8839 / 100000) (by norm_num) (by norm_num) (by norm_num)
  have hpos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc Real.log 2 * Real.exp (-Real.log 128 / 2) ≤ 0.6931471808 * (8839 / 100000) :=
        mul_le_mul hl2.le hq (Real.exp_pos _).le (by norm_num)
    _ ≤ 6127 / 100000 := by norm_num

theorem mass_131 :
    ArithmeticFunction.vonMangoldt (130 + 1) * Real.exp (-Real.log ((130 + 1 : ℕ) : ℝ) / 2) ≤
      42602 / 100000 := by
  have e : ((130 + 1 : ℕ) : ℝ) = 131 := by norm_num
  have hv : ArithmeticFunction.vonMangoldt (130 + 1) = Real.log 131 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [e, hv]
  have hl := log_le_of_128 131 (by norm_num)
  have hl2 := Real.log_two_lt_d9
  have hq := q_le 131 (8738 / 100000) (by norm_num) (by norm_num) (by norm_num)
  have hpos : 0 ≤ Real.log 131 := Real.log_nonneg (by norm_num)
  have hb : Real.log 131 ≤ 48754678 / 10000000 := by linarith
  calc Real.log 131 * Real.exp (-Real.log 131 / 2) ≤ 48754678 / 10000000 * (8738 / 100000) :=
        mul_le_mul hb hq (Real.exp_pos _).le (by norm_num)
    _ ≤ 42602 / 100000 := by norm_num

/-- **Gap-7 prime sum**, by the resonance masses. -/
theorem prime_sum7_norm (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    {i j : ℕ} (hij : i < j) (hk : j - i = 7) :
    ‖WeilPrimeSumV1 (mixed (blk g i) (blk g j))‖ ≤ (106115 / 100000) * energy g.1 := by
  have hE := energy_nonnegative g.1
  set T := WeilPrimeTermV1 (mixed (blk g i) (blk g j)) with hT
  have hzero : ∀ n ∉ ({124, 126, 127, 130} : Finset ℕ), T n = 0 := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    have hp := blk_mixed_nat_zero g a hw hij (n + 1) (by omega)
    by_cases hwin : |Real.log ((n + 1 : ℕ) : ℝ) - ((j - i : ℕ) : ℝ) * Real.log 2| ≤ 1 / 32
    · rw [hk] at hwin
      rcases prime_window7 (by omega) hwin with h | h | h | h | h
      · exact absurd (by omega : n = 124) hn.1
      · exact absurd (by omega : n = 126) hn.2.1
      · exact absurd (by omega : n = 127) hn.2.2.1
      · exact absurd (by omega : n = 130) hn.2.2.2
      · simp only [hT, WeilPrimeTermV1, h, Complex.ofReal_zero, zero_mul]
    · have hi := blk_mixed_inv_zero_of_far g a hw hij (n + 1) (by omega) (lt_of_not_ge hwin)
      simp only [hT, WeilPrimeTermV1, hp, hi, mul_zero, add_zero]
  unfold WeilPrimeSumV1
  rw [← hT, tsum_eq_sum hzero]
  have hs : (∑ n ∈ ({124, 126, 127, 130} : Finset ℕ), T n) = T 124 + (T 126 + (T 127 + T 130)) := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [hs]
  have t1 := term_norm_le g a hw hij 124
  have t2 := term_norm_le g a hw hij 126
  have t3 := term_norm_le g a hw hij 127
  have t4 := term_norm_le g a hw hij 130
  have m1 := mul_le_mul_of_nonneg_right mass_125 hE
  have m2 := mul_le_mul_of_nonneg_right mass_127 hE
  have m3 := mul_le_mul_of_nonneg_right mass_128 hE
  have m4 := mul_le_mul_of_nonneg_right mass_131 hE
  have n1 := norm_add_le (T 127) (T 130)
  have n2 := norm_add_le (T 126) (T 127 + T 130)
  have n3 := norm_add_le (T 124) (T 126 + (T 127 + T 130))
  linarith

/-- Rational ceilings at gaps `1, …, 7`. -/
def cbar8 : ℕ → ℝ
  | 1 => 101 / 200
  | 2 => 71 / 200
  | 3 => 51 / 200
  | 4 => 9 / 50
  | 5 => 13 / 100
  | 6 => 47 / 500
  | 7 => 1067 / 1000
  | _ => 0

theorem cbar8_eq (k : ℕ) (hk1 : 1 ≤ k) (hk6 : k ≤ 6) : cbar8 k = cbar7 k := by
  interval_cases k <;> rfl

theorem blk_cross_norm_gap7 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) {i j : ℕ} (hij : i < j) (hk : j - i = 7) :
    ‖B (blk g i) (blk g j)‖ ≤ cbar8 7 * energy g.1 := by
  have hE := energy_nonnegative g.1
  have hzero : mixed (blk g i) (blk g j) 1 = 0 := by
    simpa using blk_mixed_nat_zero g a hw hij 1 one_pos
  have hji : (1 : ℝ) ≤ (j : ℝ) - i := by
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harch := AEGIS.WeilSeparatedArchL1BridgeV32.translated_arch_norm_bound_l1 g a
    ((i : ℝ) * Real.log 2) ((j : ℝ) * Real.log 2) hw hm (by nlinarith)
  have harch' : ‖WeilArchimedeanIntegralV1 (mixed (blk g i) (blk g j))‖ ≤ (1 / 200 : ℝ) * energy g.1 := harch
  have hprime := prime_sum7_norm g a hw hij hk
  unfold B WeilExplicitRightSideV1
  rw [hzero, mul_zero, add_zero]
  calc ‖WeilPrimeSumV1 (mixed (blk g i) (blk g j)) + WeilArchimedeanIntegralV1 (mixed (blk g i) (blk g j))‖
      ≤ ‖WeilPrimeSumV1 (mixed (blk g i) (blk g j))‖ +
          ‖WeilArchimedeanIntegralV1 (mixed (blk g i) (blk g j))‖ := norm_add_le _ _
    _ ≤ cbar8 7 * energy g.1 := by
        simp only [cbar8]
        linarith

theorem blk_cross_norm_lt8 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) {i j : ℕ} (hij : i < j) (hk : j - i ≤ 7) :
    ‖B (blk g i) (blk g j)‖ ≤ cbar8 (j - i) * energy g.1 := by
  by_cases h7 : j - i = 7
  · rw [h7]
    exact blk_cross_norm_gap7 g a hw hm hij h7
  · rw [cbar8_eq (j - i) (by omega) (by omega)]
    exact blk_cross_norm_lt7 g a hw hm hij (by omega)

theorem blk_cross_norm8 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) (i j : Fin 8) (hij : i ≠ j) :
    ‖B (blk g i) (blk g j)‖ ≤ cbar8 (Nat.dist i j) * energy g.1 := by
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = j => hij (Fin.ext h)) with h | h
  · have hd : Nat.dist i j = j - i := by unfold Nat.dist; omega
    rw [hd]
    exact blk_cross_norm_lt8 g a hw hm h (by omega)
  · have hd : Nat.dist i j = i - j := by unfold Nat.dist; omega
    rw [hd, B_hermitian, Complex.norm_conj]
    exact blk_cross_norm_lt8 g a hw hm h (by omega)

theorem blk_diag8 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) (j : ℕ) :
    (59 / 20 : ℝ) * energy g.1 ≤ -(B (blk g j) (blk g j)).re := by
  have h := AEGIS.WeilDiagonalQuadMomentV1.width_diagonal_59_over_20 (blk g j) _ (blk_width g a hw j)
    (translate_preserves_moments g _ hm)
  rwa [blk_energy] at h

/-- Unweighted Schur test for the eight ceilings: largest row sum `2.586 ≤ 13/5`. -/
theorem eight_ceiling_quadratic (x0 x1 x2 x3 x4 x5 x6 x7 : ℝ) :
    2 * ((101 / 200) * (x0 * x1 + x1 * x2 + x2 * x3 + x3 * x4 + x4 * x5 + x5 * x6 + x6 * x7) +
      (71 / 200) * (x0 * x2 + x1 * x3 + x2 * x4 + x3 * x5 + x4 * x6 + x5 * x7) +
      (51 / 200) * (x0 * x3 + x1 * x4 + x2 * x5 + x3 * x6 + x4 * x7) +
      (9 / 50) * (x0 * x4 + x1 * x5 + x2 * x6 + x3 * x7) + (13 / 100) * (x0 * x5 + x1 * x6 + x2 * x7) +
      (47 / 500) * (x0 * x6 + x1 * x7) + (1067 / 1000) * (x0 * x7)) ≤
      (13 / 5) * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2 + x6 ^ 2 + x7 ^ 2) := by
  nlinarith [sq_nonneg (x0 - x1), sq_nonneg (x1 - x2), sq_nonneg (x2 - x3), sq_nonneg (x3 - x4),
    sq_nonneg (x4 - x5), sq_nonneg (x5 - x6), sq_nonneg (x6 - x7),
    sq_nonneg (x0 - x2), sq_nonneg (x1 - x3), sq_nonneg (x2 - x4), sq_nonneg (x3 - x5),
    sq_nonneg (x4 - x6), sq_nonneg (x5 - x7),
    sq_nonneg (x0 - x3), sq_nonneg (x1 - x4), sq_nonneg (x2 - x5), sq_nonneg (x3 - x6), sq_nonneg (x4 - x7),
    sq_nonneg (x0 - x4), sq_nonneg (x1 - x5), sq_nonneg (x2 - x6), sq_nonneg (x3 - x7),
    sq_nonneg (x0 - x5), sq_nonneg (x1 - x6), sq_nonneg (x2 - x7),
    sq_nonneg (x0 - x6), sq_nonneg (x1 - x7), sq_nonneg (x0 - x7),
    sq_nonneg x0, sq_nonneg x1, sq_nonneg x2, sq_nonneg x3, sq_nonneg x4, sq_nonneg x5, sq_nonneg x6,
    sq_nonneg x7]

/-- **Eight-block comb at width 1/32.** -/
theorem eight_block_gram_bound (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) (z : Fin 8 → ℂ) :
    (∑ i : Fin 8, ∑ j : Fin 8, z i * star (z j) * B (blk g i) (blk g j)).re ≤
      -(1 / 4 : ℝ) * energy g.1 * ∑ i : Fin 8, ‖z i‖ ^ 2 := by
  have hE := energy_nonnegative g.1
  have hterm : ∀ i j : Fin 8, (z i * star (z j) * B (blk g i) (blk g j)).re ≤
      ‖z i‖ * ‖z j‖ * ((if Nat.dist i j = 0 then -(59 / 20 : ℝ) else cbar8 (Nat.dist i j)) *
        energy g.1) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos (Nat.dist_self _), re_diag]
      have hd := blk_diag8 g a hw hm i
      nlinarith [sq_nonneg ‖z i‖, mul_nonneg (sq_nonneg ‖z i‖) hE]
    · have hd : Nat.dist i j ≠ 0 := by
        intro h
        apply hij
        apply Fin.ext
        unfold Nat.dist at h
        omega
      rw [if_neg hd]
      calc (z i * star (z j) * B (blk g i) (blk g j)).re
          ≤ ‖z i * star (z j) * B (blk g i) (blk g j)‖ := Complex.re_le_norm _
        _ = ‖z i‖ * ‖z j‖ * ‖B (blk g i) (blk g j)‖ := by simp only [norm_mul, norm_star]
        _ ≤ ‖z i‖ * ‖z j‖ * (cbar8 (Nat.dist i j) * energy g.1) :=
            mul_le_mul_of_nonneg_left (blk_cross_norm8 g a hw hm i j hij)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  calc (∑ i : Fin 8, ∑ j : Fin 8, (z i * star (z j) * B (blk g i) (blk g j)).re)
      ≤ ∑ i : Fin 8, ∑ j : Fin 8,
          ‖z i‖ * ‖z j‖ * ((if Nat.dist i j = 0 then -(59 / 20 : ℝ) else cbar8 (Nat.dist i j)) *
            energy g.1) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ ≤ -(1 / 4 : ℝ) * energy g.1 * ∑ i : Fin 8, ‖z i‖ ^ 2 := by
        have hq := eight_ceiling_quadratic ‖z 0‖ ‖z 1‖ ‖z 2‖ ‖z 3‖ ‖z 4‖ ‖z 5‖ ‖z 6‖ ‖z 7‖
        simp only [Fin.sum_univ_eight]
        norm_num [cbar8, Nat.dist]
        nlinarith [mul_le_mul_of_nonneg_left hq hE, sq_nonneg ‖z 0‖, sq_nonneg ‖z 1‖, sq_nonneg ‖z 2‖,
          sq_nonneg ‖z 3‖, sq_nonneg ‖z 4‖, sq_nonneg ‖z 5‖, sq_nonneg ‖z 6‖, sq_nonneg ‖z 7‖,
          mul_nonneg hE (sq_nonneg ‖z 0‖), mul_nonneg hE (sq_nonneg ‖z 1‖),
          mul_nonneg hE (sq_nonneg ‖z 2‖), mul_nonneg hE (sq_nonneg ‖z 3‖),
          mul_nonneg hE (sq_nonneg ‖z 4‖), mul_nonneg hE (sq_nonneg ‖z 5‖),
          mul_nonneg hE (sq_nonneg ‖z 6‖), mul_nonneg hE (sq_nonneg ‖z 7‖)]

end AEGIS.WeilEightBlockCombV1

#print axioms AEGIS.WeilEightBlockCombV1.prime_window7
#print axioms AEGIS.WeilEightBlockCombV1.prime_sum7_norm
#print axioms AEGIS.WeilEightBlockCombV1.eight_block_gram_bound
