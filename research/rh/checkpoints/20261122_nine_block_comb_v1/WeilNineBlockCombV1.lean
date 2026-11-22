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

import WeilEightBlockCombV1

/-!
AEGIS Ω — the nine-block dyadic comb at width 1/32, with the gap-7 and gap-8 resonances (Claude Lab, 2026-11-22).

Blocks `blk g j = T_{j log 2} g`, `j = 0, …, 8`, for `g` of log-width `1/32` with both moments. Compared with
`WeilEightBlockCombV1`:
* the diagonal is stated as `299/100 · E` (`width_diagonal_299_over_100`; same constant as
  `WeilDiagonalQuadMomentV1.diagonal_quad_moment_v1`, with the sharper `e^{−1/32} > 63/65`);
* gap `k = 8` is admitted. Its log-window contains the prime powers `251`, `256 = 2⁸`, `257` and `263`
  (`prime_window8`); the other integers `249, …, 264` have `Λ = 0`. The four masses `Λ(m) m^{−1/2}` sum to at
  most `1.081922` (`prime_sum8_norm`), so `‖B‖ ≤ (10870/10000) E` at gap 8;
* the ceilings at gaps `1, …, 7` are sharpened to within `10⁻⁴` of `log 2 · 2^{−k/2} + 1/200` and
  `1.06115 + 1/200` (`cbar9`);
* the Schur test is weighted; its largest weighted row sum is `2.96594 ≤ 297/100` (spectral radius `2.96527`).

Result (`nine_block_gram_bound`): `Re Σ z_i conj(z_j) B(blk g i, blk g j) ≤ −(1/50) · E · Σ ‖z_i‖²`.

Fixed-width comb class only. Not RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilNineBlockCombV1

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilArchimedeanCothTailV1
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilWidthDiagonalArchFrontierV24
open AEGIS.WeilFiveBlockCombV1
open AEGIS.WeilSevenBlockCombV1
open AEGIS.WeilEightBlockCombV1

theorem quad_constant_gt_299 :
    (299 / 100 : ℝ) < diagonalTailV24 - diagonalKappaV21 - diagonalSmallV21 +
      Real.exp (-(1 / 32)) * (Real.log 2 + 4 / 3 - 1 / 2048) := by
  have hfloor := AEGIS.WeilThreeBlockAnalyticConstantsV21.diagonal_constant_floor
  have htail := diagonal_tail_gt_six_log_two_v24
  have hl := AEGIS.WeilThreeBlockAnalyticConstantsV21.log_two_lower
  have hc := exp_neg_one_div_32_gt
  have hprod : (63 / 65 : ℝ) * (693 / 1000 + 4 / 3 - 1 / 2048) ≤
      Real.exp (-(1 / 32)) * (Real.log 2 + 4 / 3 - 1 / 2048) :=
    mul_le_mul hc.le (by linarith) (by norm_num) (Real.exp_pos _).le
  unfold diagonalKappaV21 diagonalSmallV21
  linarith

/-- **Width-1/32 moment-zero diagonal, `299/100`.** -/
theorem width_diagonal_299_over_100 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) :
    (299 / 100 : ℝ) * energy g.1 ≤ -(B g g).re := by
  have h := AEGIS.WeilDiagonalQuadMomentV1.diagonal_quad_moment_v1 g a hw hm
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hmul := mul_le_mul_of_nonneg_left quad_constant_gt_299.le hE
  linarith

/-- Rational ceilings at gaps `1, …, 8`. -/
def cbar9 : ℕ → ℝ
  | 1 => 4952 / 10000
  | 2 => 3516 / 10000
  | 3 => 2501 / 10000
  | 4 => 1783 / 10000
  | 5 => 1276 / 10000
  | 6 => 917 / 10000
  | 7 => 10662 / 10000
  | 8 => 10870 / 10000
  | _ => 0

theorem prime_coeff_le9 (k : ℕ) (hk1 : 1 ≤ k) (hk6 : k ≤ 6) :
    Real.log 2 * Real.exp (-((k : ℝ) * Real.log 2 / 2)) + 1 / 200 ≤ cbar9 k := by
  set q := Real.exp (-(Real.log 2 / 2)) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hqq : q * q = 1 / 2 := by
    rw [hqdef, ← Real.exp_add, show -(Real.log 2 / 2) + -(Real.log 2 / 2) = -Real.log 2 by ring,
      Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hq : q ≤ 70711 / 100000 := by nlinarith
  have hpow : Real.exp (-((k : ℝ) * Real.log 2 / 2)) = q ^ k := by
    rw [hqdef, ← Real.exp_nat_mul]
    congr 1
    ring
  have hl := Real.log_two_lt_d9
  rw [hpow]
  have hqk : q ^ k ≤ (70711 / 100000 : ℝ) ^ k := pow_le_pow_left₀ hq0.le hq k
  have hb : Real.log 2 * q ^ k ≤ 0.6931471808 * (70711 / 100000 : ℝ) ^ k :=
    mul_le_mul hl.le hqk (pow_nonneg hq0.le k) (by norm_num)
  interval_cases k <;> simp only [cbar9] <;> norm_num at hb ⊢ <;> linarith

theorem blk_cross_norm_lt9 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) {i j : ℕ} (hij : i < j) (hk : j - i ≤ 6) :
    ‖B (blk g i) (blk g j)‖ ≤ cbar9 (j - i) * energy g.1 := by
  have hE := energy_nonnegative g.1
  have hzero : mixed (blk g i) (blk g j) 1 = 0 := by
    simpa using blk_mixed_nat_zero g a hw hij 1 one_pos
  have hprime := blk_prime_sum6 g a hw hij hk
  have hji : (1 : ℝ) ≤ (j : ℝ) - i := by
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harch := AEGIS.WeilSeparatedArchL1BridgeV32.translated_arch_norm_bound_l1 g a
    ((i : ℝ) * Real.log 2) ((j : ℝ) * Real.log 2) hw hm (by nlinarith)
  have hcoef := prime_coeff_le9 (j - i) (by omega) hk
  have hpn : ‖WeilPrimeSumV1 (mixed (blk g i) (blk g j))‖ =
      Real.log 2 * Real.exp (-(((j - i : ℕ) : ℝ) * Real.log 2 / 2)) * energy g.1 := by
    rw [hprime, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact mul_nonneg (mul_nonneg hl0.le (Real.exp_pos _).le) hE
  unfold B WeilExplicitRightSideV1
  rw [hzero, mul_zero, add_zero]
  calc ‖WeilPrimeSumV1 (mixed (blk g i) (blk g j)) + WeilArchimedeanIntegralV1 (mixed (blk g i) (blk g j))‖
      ≤ ‖WeilPrimeSumV1 (mixed (blk g i) (blk g j))‖ +
          ‖WeilArchimedeanIntegralV1 (mixed (blk g i) (blk g j))‖ := norm_add_le _ _
    _ ≤ Real.log 2 * Real.exp (-(((j - i : ℕ) : ℝ) * Real.log 2 / 2)) * energy g.1 +
          (1 / 200 : ℝ) * energy g.1 := by
        rw [hpn]
        exact add_le_add (le_refl _) harch
    _ ≤ cbar9 (j - i) * energy g.1 := by nlinarith [mul_le_mul_of_nonneg_right hcoef hE]

/-- In the log-window of gap `8` every positive integer is `251, 256, 257, 263` or has `Λ = 0`. -/
theorem prime_window8 {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - ((8 : ℕ) : ℝ) * Real.log 2| ≤ 1 / 32) :
    m = 251 ∨ m = 256 ∨ m = 257 ∨ m = 263 ∨ ArithmeticFunction.vonMangoldt m = 0 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := abs_le.mp hwin
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ ((8 : ℕ) : ℝ) * Real.log 2 + 1 / 32 by linarith [habs.2])
  have hlo := Real.exp_le_exp.mpr
    (show ((8 : ℕ) : ℝ) * Real.log 2 - 1 / 32 ≤ Real.log (m : ℝ) by linarith [habs.1])
  have h2k : Real.exp (((8 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ 8 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, h2k] at hup
  rw [sub_eq_add_neg, Real.exp_add, h2k] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have e1 := mul_lt_mul_of_pos_left exp_one_div_32_lt (by norm_num : (0 : ℝ) < 2 ^ 8)
  have e2 := mul_lt_mul_of_pos_left exp_neg_one_div_32_gt (by norm_num : (0 : ℝ) < 2 ^ 8)
  have hlt : (m : ℝ) < 2 ^ 8 * (65 / 63) := by linarith
  have hgt : (2 : ℝ) ^ 8 * (63 / 65) < m := by linarith
  norm_num at hlt hgt
  have h1 : m < 265 := by exact_mod_cast (show (m : ℝ) < 265 by linarith)
  have h2 : 248 < m := by exact_mod_cast (show (248 : ℝ) < m by linarith)
  interval_cases m
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 3) (q := 83) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 2) (q := 5) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · left; rfl
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 2) (q := 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 11) (q := 23) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 2) (q := 127) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 3) (q := 5) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 2) (q := 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 7) (q := 37) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 2) (q := 5) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 3) (q := 29) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 2) (q := 131) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · right; right; right; left; rfl
  · right; right; right; right
    exact vonMangoldt_eq_zero_of_two_primes (p := 2) (q := 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

/-- `log 256 = 8 log 2`. -/
theorem log_256 : Real.log 256 = 8 * Real.log 2 := by
  rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
  norm_num

/-- `log m ≤ 8 log 2 + (m/256 − 1)`. -/
theorem log_le_of_256 (m : ℝ) (hm : 0 < m) : Real.log m ≤ 8 * Real.log 2 + (m / 256 - 1) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m / 256 by positivity)
  rw [Real.log_div hm.ne' (by norm_num), log_256] at h
  linarith

theorem mass_251 :
    ArithmeticFunction.vonMangoldt (250 + 1) * Real.exp (-Real.log ((250 + 1 : ℕ) : ℝ) / 2) ≤
      34878 / 100000 := by
  have e : ((250 + 1 : ℕ) : ℝ) = 251 := by norm_num
  have hv : ArithmeticFunction.vonMangoldt (250 + 1) = Real.log 251 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [e, hv]
  have hl := log_le_of_256 251 (by norm_num)
  have hl2 := Real.log_two_lt_d9
  have hq := q_le 251 (6312 / 100000) (by norm_num) (by norm_num) (by norm_num)
  have hb : Real.log 251 ≤ 55256462 / 10000000 := by linarith
  calc Real.log 251 * Real.exp (-Real.log 251 / 2) ≤ 55256462 / 10000000 * (6312 / 100000) :=
        mul_le_mul hb hq (Real.exp_pos _).le (by norm_num)
    _ ≤ 34878 / 100000 := by norm_num

theorem mass_256 :
    ArithmeticFunction.vonMangoldt (255 + 1) * Real.exp (-Real.log ((255 + 1 : ℕ) : ℝ) / 2) ≤
      43322 / 1000000 := by
  have e : ((255 + 1 : ℕ) : ℝ) = 256 := by norm_num
  have hv : ArithmeticFunction.vonMangoldt (255 + 1) = Real.log 2 := by
    rw [show (255 + 1 : ℕ) = 2 ^ 8 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  rw [e, hv]
  have hl2 := Real.log_two_lt_d9
  have hq := q_le 256 (1 / 16) (by norm_num) (by norm_num) (by norm_num)
  calc Real.log 2 * Real.exp (-Real.log 256 / 2) ≤ 0.6931471808 * (1 / 16) :=
        mul_le_mul hl2.le hq (Real.exp_pos _).le (by norm_num)
    _ ≤ 43322 / 1000000 := by norm_num

theorem mass_257 :
    ArithmeticFunction.vonMangoldt (256 + 1) * Real.exp (-Real.log ((256 + 1 : ℕ) : ℝ) / 2) ≤
      34616 / 100000 := by
  have e : ((256 + 1 : ℕ) : ℝ) = 257 := by norm_num
  have hv : ArithmeticFunction.vonMangoldt (256 + 1) = Real.log 257 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [e, hv]
  have hl := log_le_of_256 257 (by norm_num)
  have hl2 := Real.log_two_lt_d9
  have hq := q_le 257 (6238 / 100000) (by norm_num) (by norm_num) (by norm_num)
  have hpos : 0 ≤ Real.log 257 := Real.log_nonneg (by norm_num)
  have hb : Real.log 257 ≤ 55490837 / 10000000 := by linarith
  calc Real.log 257 * Real.exp (-Real.log 257 / 2) ≤ 55490837 / 10000000 * (6238 / 100000) :=
        mul_le_mul hb hq (Real.exp_pos _).le (by norm_num)
    _ ≤ 34616 / 100000 := by norm_num

theorem mass_263 :
    ArithmeticFunction.vonMangoldt (262 + 1) * Real.exp (-Real.log ((262 + 1 : ℕ) : ℝ) / 2) ≤
      34366 / 100000 := by
  have e : ((262 + 1 : ℕ) : ℝ) = 263 := by norm_num
  have hv : ArithmeticFunction.vonMangoldt (262 + 1) = Real.log 263 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [e, hv]
  have hl := log_le_of_256 263 (by norm_num)
  have hl2 := Real.log_two_lt_d9
  have hq := q_le 263 (6167 / 100000) (by norm_num) (by norm_num) (by norm_num)
  have hpos : 0 ≤ Real.log 263 := Real.log_nonneg (by norm_num)
  have hb : Real.log 263 ≤ 55725212 / 10000000 := by linarith
  calc Real.log 263 * Real.exp (-Real.log 263 / 2) ≤ 55725212 / 10000000 * (6167 / 100000) :=
        mul_le_mul hb hq (Real.exp_pos _).le (by norm_num)
    _ ≤ 34366 / 100000 := by norm_num

/-- **Gap-8 prime sum**, by the resonance masses. -/
theorem prime_sum8_norm (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    {i j : ℕ} (hij : i < j) (hk : j - i = 8) :
    ‖WeilPrimeSumV1 (mixed (blk g i) (blk g j))‖ ≤ (1081922 / 1000000) * energy g.1 := by
  have hE := energy_nonnegative g.1
  set T := WeilPrimeTermV1 (mixed (blk g i) (blk g j)) with hT
  have hzero : ∀ n ∉ ({250, 255, 256, 262} : Finset ℕ), T n = 0 := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    have hp := blk_mixed_nat_zero g a hw hij (n + 1) (by omega)
    by_cases hwin : |Real.log ((n + 1 : ℕ) : ℝ) - ((j - i : ℕ) : ℝ) * Real.log 2| ≤ 1 / 32
    · rw [hk] at hwin
      rcases prime_window8 (by omega) hwin with h | h | h | h | h
      · exact absurd (by omega : n = 250) hn.1
      · exact absurd (by omega : n = 255) hn.2.1
      · exact absurd (by omega : n = 256) hn.2.2.1
      · exact absurd (by omega : n = 262) hn.2.2.2
      · simp only [hT, WeilPrimeTermV1, h, Complex.ofReal_zero, zero_mul]
    · have hi := blk_mixed_inv_zero_of_far g a hw hij (n + 1) (by omega) (lt_of_not_ge hwin)
      simp only [hT, WeilPrimeTermV1, hp, hi, mul_zero, add_zero]
  unfold WeilPrimeSumV1
  rw [← hT, tsum_eq_sum hzero]
  have hs : (∑ n ∈ ({250, 255, 256, 262} : Finset ℕ), T n) = T 250 + (T 255 + (T 256 + T 262)) := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [hs]
  have t1 := term_norm_le g a hw hij 250
  have t2 := term_norm_le g a hw hij 255
  have t3 := term_norm_le g a hw hij 256
  have t4 := term_norm_le g a hw hij 262
  have m1 := mul_le_mul_of_nonneg_right mass_251 hE
  have m2 := mul_le_mul_of_nonneg_right mass_256 hE
  have m3 := mul_le_mul_of_nonneg_right mass_257 hE
  have m4 := mul_le_mul_of_nonneg_right mass_263 hE
  have n1 := norm_add_le (T 256) (T 262)
  have n2 := norm_add_le (T 255) (T 256 + T 262)
  have n3 := norm_add_le (T 250) (T 255 + (T 256 + T 262))
  linarith

/-- Gaps `7` and `8`: prime masses plus the Archimedean `E/200`. -/
theorem blk_cross_norm_gap78 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) {i j : ℕ} (hij : i < j) (hk : j - i = 7 ∨ j - i = 8) :
    ‖B (blk g i) (blk g j)‖ ≤ cbar9 (j - i) * energy g.1 := by
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
  have hprime : ‖WeilPrimeSumV1 (mixed (blk g i) (blk g j))‖ ≤ (cbar9 (j - i) - 1 / 200) * energy g.1 := by
    rcases hk with h7 | h8
    · rw [h7]
      have := prime_sum7_norm g a hw hij h7
      simp only [cbar9]
      nlinarith
    · rw [h8]
      have := prime_sum8_norm g a hw hij h8
      simp only [cbar9]
      nlinarith
  unfold B WeilExplicitRightSideV1
  rw [hzero, mul_zero, add_zero]
  calc ‖WeilPrimeSumV1 (mixed (blk g i) (blk g j)) + WeilArchimedeanIntegralV1 (mixed (blk g i) (blk g j))‖
      ≤ ‖WeilPrimeSumV1 (mixed (blk g i) (blk g j))‖ +
          ‖WeilArchimedeanIntegralV1 (mixed (blk g i) (blk g j))‖ := norm_add_le _ _
    _ ≤ cbar9 (j - i) * energy g.1 := by linarith

theorem blk_cross_norm_le8 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) {i j : ℕ} (hij : i < j) (hk : j - i ≤ 8) :
    ‖B (blk g i) (blk g j)‖ ≤ cbar9 (j - i) * energy g.1 := by
  by_cases h6 : j - i ≤ 6
  · exact blk_cross_norm_lt9 g a hw hm hij h6
  · exact blk_cross_norm_gap78 g a hw hm hij (by omega)

theorem blk_cross_norm9 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) (i j : Fin 9) (hij : i ≠ j) :
    ‖B (blk g i) (blk g j)‖ ≤ cbar9 (Nat.dist i j) * energy g.1 := by
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = j => hij (Fin.ext h)) with h | h
  · have hd : Nat.dist i j = j - i := by unfold Nat.dist; omega
    rw [hd]
    exact blk_cross_norm_le8 g a hw hm h (by omega)
  · have hd : Nat.dist i j = i - j := by unfold Nat.dist; omega
    rw [hd, B_hermitian, Complex.norm_conj]
    exact blk_cross_norm_le8 g a hw hm h (by omega)

theorem blk_diag9 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) (j : ℕ) :
    (299 / 100 : ℝ) * energy g.1 ≤ -(B (blk g j) (blk g j)).re := by
  have h := width_diagonal_299_over_100 (blk g j) _ (blk_width g a hw j)
    (translate_preserves_moments g _ hm)
  rwa [blk_energy] at h

theorem sum_fin9 (f : Fin 9 → ℝ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_eight]
  rfl

/-- Weighted Schur test for the nine ceilings, weights `(1, 829/1000, 577/1000, 59/100, 297/500, 59/100,
577/1000, 829/1000, 1)`: largest weighted row sum `2.96594 ≤ 297/100`. -/
theorem nine_ceiling_quadratic (x0 x1 x2 x3 x4 x5 x6 x7 x8 : ℝ) :
    2 * ((4952 / 10000) * (x0 * x1 + x1 * x2 + x2 * x3 + x3 * x4 + x4 * x5 + x5 * x6 + x6 * x7 + x7 * x8) +
      (3516 / 10000) * (x0 * x2 + x1 * x3 + x2 * x4 + x3 * x5 + x4 * x6 + x5 * x7 + x6 * x8) +
      (2501 / 10000) * (x0 * x3 + x1 * x4 + x2 * x5 + x3 * x6 + x4 * x7 + x5 * x8) +
      (1783 / 10000) * (x0 * x4 + x1 * x5 + x2 * x6 + x3 * x7 + x4 * x8) +
      (1276 / 10000) * (x0 * x5 + x1 * x6 + x2 * x7 + x3 * x8) +
      (917 / 10000) * (x0 * x6 + x1 * x7 + x2 * x8) +
      (10662 / 10000) * (x0 * x7 + x1 * x8) +
      (10870 / 10000) * (x0 * x8)) ≤
      (297 / 100) * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2 + x6 ^ 2 + x7 ^ 2 + x8 ^ 2) := by
  linarith [sq_nonneg ((829 / 1000) * x0 - (1) * x1),
    sq_nonneg ((577 / 1000) * x0 - (1) * x2),
    sq_nonneg ((59 / 100) * x0 - (1) * x3),
    sq_nonneg ((297 / 500) * x0 - (1) * x4),
    sq_nonneg ((59 / 100) * x0 - (1) * x5),
    sq_nonneg ((577 / 1000) * x0 - (1) * x6),
    sq_nonneg ((829 / 1000) * x0 - (1) * x7),
    sq_nonneg ((1) * x0 - (1) * x8),
    sq_nonneg ((577 / 1000) * x1 - (829 / 1000) * x2),
    sq_nonneg ((59 / 100) * x1 - (829 / 1000) * x3),
    sq_nonneg ((297 / 500) * x1 - (829 / 1000) * x4),
    sq_nonneg ((59 / 100) * x1 - (829 / 1000) * x5),
    sq_nonneg ((577 / 1000) * x1 - (829 / 1000) * x6),
    sq_nonneg ((829 / 1000) * x1 - (829 / 1000) * x7),
    sq_nonneg ((1) * x1 - (829 / 1000) * x8),
    sq_nonneg ((59 / 100) * x2 - (577 / 1000) * x3),
    sq_nonneg ((297 / 500) * x2 - (577 / 1000) * x4),
    sq_nonneg ((59 / 100) * x2 - (577 / 1000) * x5),
    sq_nonneg ((577 / 1000) * x2 - (577 / 1000) * x6),
    sq_nonneg ((829 / 1000) * x2 - (577 / 1000) * x7),
    sq_nonneg ((1) * x2 - (577 / 1000) * x8),
    sq_nonneg ((297 / 500) * x3 - (59 / 100) * x4),
    sq_nonneg ((59 / 100) * x3 - (59 / 100) * x5),
    sq_nonneg ((577 / 1000) * x3 - (59 / 100) * x6),
    sq_nonneg ((829 / 1000) * x3 - (59 / 100) * x7),
    sq_nonneg ((1) * x3 - (59 / 100) * x8),
    sq_nonneg ((59 / 100) * x4 - (297 / 500) * x5),
    sq_nonneg ((577 / 1000) * x4 - (297 / 500) * x6),
    sq_nonneg ((829 / 1000) * x4 - (297 / 500) * x7),
    sq_nonneg ((1) * x4 - (297 / 500) * x8),
    sq_nonneg ((577 / 1000) * x5 - (59 / 100) * x6),
    sq_nonneg ((829 / 1000) * x5 - (59 / 100) * x7),
    sq_nonneg ((1) * x5 - (59 / 100) * x8),
    sq_nonneg ((829 / 1000) * x6 - (577 / 1000) * x7),
    sq_nonneg ((1) * x6 - (577 / 1000) * x8),
    sq_nonneg ((1) * x7 - (829 / 1000) * x8),
    sq_nonneg x0,
    sq_nonneg x1,
    sq_nonneg x2,
    sq_nonneg x3,
    sq_nonneg x4,
    sq_nonneg x5,
    sq_nonneg x6,
    sq_nonneg x7,
    sq_nonneg x8]

set_option maxHeartbeats 1600000 in
/-- **Nine-block comb at width 1/32.** -/
theorem nine_block_gram_bound (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) (z : Fin 9 → ℂ) :
    (∑ i : Fin 9, ∑ j : Fin 9, z i * star (z j) * B (blk g i) (blk g j)).re ≤
      -(1 / 50 : ℝ) * energy g.1 * ∑ i : Fin 9, ‖z i‖ ^ 2 := by
  have hE := energy_nonnegative g.1
  have hterm : ∀ i j : Fin 9, (z i * star (z j) * B (blk g i) (blk g j)).re ≤
      ‖z i‖ * ‖z j‖ * ((if Nat.dist i j = 0 then -(299 / 100 : ℝ) else cbar9 (Nat.dist i j)) *
        energy g.1) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos (Nat.dist_self _), re_diag]
      have hd := blk_diag9 g a hw hm i
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
        _ ≤ ‖z i‖ * ‖z j‖ * (cbar9 (Nat.dist i j) * energy g.1) :=
            mul_le_mul_of_nonneg_left (blk_cross_norm9 g a hw hm i j hij)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  calc (∑ i : Fin 9, ∑ j : Fin 9, (z i * star (z j) * B (blk g i) (blk g j)).re)
      ≤ ∑ i : Fin 9, ∑ j : Fin 9,
          ‖z i‖ * ‖z j‖ * ((if Nat.dist i j = 0 then -(299 / 100 : ℝ) else cbar9 (Nat.dist i j)) *
            energy g.1) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ ≤ -(1 / 50 : ℝ) * energy g.1 * ∑ i : Fin 9, ‖z i‖ ^ 2 := by
        have hq := nine_ceiling_quadratic ‖z 0‖ ‖z 1‖ ‖z 2‖ ‖z 3‖ ‖z 4‖ ‖z 5‖ ‖z 6‖ ‖z 7‖ ‖z 8‖
        simp only [sum_fin9]
        norm_num [cbar9, Nat.dist]
        linarith [mul_le_mul_of_nonneg_left hq hE, sq_nonneg ‖z 0‖, sq_nonneg ‖z 1‖, sq_nonneg ‖z 2‖, sq_nonneg ‖z 3‖, sq_nonneg ‖z 4‖, sq_nonneg ‖z 5‖, sq_nonneg ‖z 6‖, sq_nonneg ‖z 7‖, sq_nonneg ‖z 8‖,
          mul_nonneg hE (sq_nonneg ‖z 0‖),
          mul_nonneg hE (sq_nonneg ‖z 1‖),
          mul_nonneg hE (sq_nonneg ‖z 2‖),
          mul_nonneg hE (sq_nonneg ‖z 3‖),
          mul_nonneg hE (sq_nonneg ‖z 4‖),
          mul_nonneg hE (sq_nonneg ‖z 5‖),
          mul_nonneg hE (sq_nonneg ‖z 6‖),
          mul_nonneg hE (sq_nonneg ‖z 7‖),
          mul_nonneg hE (sq_nonneg ‖z 8‖)]

end AEGIS.WeilNineBlockCombV1

#print axioms AEGIS.WeilNineBlockCombV1.prime_window8
#print axioms AEGIS.WeilNineBlockCombV1.prime_sum8_norm
#print axioms AEGIS.WeilNineBlockCombV1.nine_block_gram_bound
