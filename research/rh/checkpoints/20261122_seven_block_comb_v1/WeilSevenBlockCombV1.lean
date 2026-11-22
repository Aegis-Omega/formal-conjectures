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

import WeilFiveBlockCombV1
import WeilDiagonalMomentGainV1

/-!
AEGIS Ω — the seven-block dyadic comb at width 1/32 (Claude Lab, 2026-11-22).

Blocks `blk g j = T_{j log 2} g`, `j = 0, …, 6`, for `g` of log-width `1/32` with both moments. Compared with
`WeilFiveBlockCombV1`:
* the diagonal is `109/50 · E` (`WeilDiagonalMomentGainV1.width_diagonal_109_over_50`, mean gain plus moments)
  instead of `17/10 · E`;
* gaps `k = 5, 6` are admitted. Their log-windows also contain `33` (`k = 5`) and `63, 65, 66` (`k = 6`); these are
  not prime powers, so `Λ` vanishes on them (`prime_window`) and the prime part is still exactly
  `log 2 · 2^{−k/2} · E`;
* the weighted Schur test uses weights `(7/10, 17/20, 19/20, 1, 19/20, 17/20, 7/10)`; its largest weighted row sum
  is `1.97 ≤ 2`.

Result (`seven_block_gram_bound`): `Re Σ z_i conj(z_j) B(blk g i, blk g j) ≤ −(1/10) · E · Σ ‖z_i‖²`.
At gap `7` other prime powers (`125, 127, 131`) enter the window; that is the resonance frontier.

Fixed-width comb class only. Not RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilSevenBlockCombV1

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilArchimedeanCothTailV1
open AEGIS.WeilFiveBlockCombV1

theorem vonMangoldt_eq_zero_of_two_primes {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpn : p ∣ n) (hqn : q ∣ n) : ArithmeticFunction.vonMangoldt n = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
  intro h
  obtain ⟨r, _, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp h
  exact hpq ((huniq p ⟨hp, hpn⟩).trans (huniq q ⟨hq, hqn⟩).symm)

/-- In the log-window of a gap `k ≤ 6` every positive integer is `2^k` or has `Λ = 0`. -/
theorem prime_window {m k : ℕ} (hm : 0 < m) (hk : k ≤ 6)
    (hwin : |Real.log (m : ℝ) - (k : ℝ) * Real.log 2| ≤ 1 / 32) :
    m = 2 ^ k ∨ ArithmeticFunction.vonMangoldt m = 0 := by
  by_cases hk4 : k ≤ 4
  · exact Or.inl (nat_eq_pow_of_log_window hm hk4 hwin)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := abs_le.mp hwin
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ (k : ℝ) * Real.log 2 + 1 / 32 by linarith [habs.2])
  have hlo := Real.exp_le_exp.mpr
    (show (k : ℝ) * Real.log 2 - 1 / 32 ≤ Real.log (m : ℝ) by linarith [habs.1])
  have h2k : Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, h2k] at hup
  rw [sub_eq_add_neg, Real.exp_add, h2k] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have hpk0 : (0 : ℝ) < 2 ^ k := by positivity
  have e1 := mul_lt_mul_of_pos_left exp_one_div_32_lt hpk0
  have e2 := mul_lt_mul_of_pos_left exp_neg_one_div_32_gt hpk0
  have hlt : (m : ℝ) < 2 ^ k * (65 / 63) := by linarith
  have hgt : (2 : ℝ) ^ k * (63 / 65) < m := by linarith
  have hk56 : k = 5 ∨ k = 6 := by omega
  rcases hk56 with rfl | rfl
  · norm_num at hlt hgt
    have h1 : m < 34 := by exact_mod_cast (show (m : ℝ) < 34 by linarith)
    have h2 : 31 < m := by exact_mod_cast (show (31 : ℝ) < m by linarith)
    interval_cases m
    · left; norm_num
    · right
      exact vonMangoldt_eq_zero_of_two_primes (p := 3) (q := 11) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
  · norm_num at hlt hgt
    have h1 : m < 67 := by exact_mod_cast (show (m : ℝ) < 67 by linarith)
    have h2 : 62 < m := by exact_mod_cast (show (62 : ℝ) < m by linarith)
    interval_cases m
    · right
      exact vonMangoldt_eq_zero_of_two_primes (p := 3) (q := 7) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
    · left; norm_num
    · right
      exact vonMangoldt_eq_zero_of_two_primes (p := 5) (q := 13) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
    · right
      exact vonMangoldt_eq_zero_of_two_primes (p := 2) (q := 3) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)

theorem blk_mixed_inv_zero_of_far (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    {i j : ℕ} (hij : i < j) (m : ℕ) (hm : 0 < m)
    (hfar0 : (1 / 32 : ℝ) < |Real.log (m : ℝ) - ((j - i : ℕ) : ℝ) * Real.log 2|) :
    mixed (blk g i) (blk g j) ((m : ℝ)⁻¹) = 0 := by
  have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - i := by rw [Nat.cast_sub hij.le]
  have harg : -Real.log (m : ℝ) + (j : ℝ) * Real.log 2 - (i : ℝ) * Real.log 2 =
      -(Real.log (m : ℝ) - ((j - i : ℕ) : ℝ) * Real.log 2) := by
    rw [hcast]
    ring
  have hfar : (1 / 32 : ℝ) < |-Real.log (m : ℝ) + (j : ℝ) * Real.log 2 - (i : ℝ) * Real.log 2| := by
    rw [harg, abs_neg]
    exact hfar0
  have hz := mixed_translate_zero_of_width_v28 g a ((i : ℝ) * Real.log 2) ((j : ℝ) * Real.log 2)
    (-Real.log (m : ℝ)) hw hfar
  rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hm)] at hz
  exact hz

/-- **Exact prime part** at gap `k = j − i ≤ 6`. -/
theorem blk_prime_sum6 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    {i j : ℕ} (hij : i < j) (hk : j - i ≤ 6) :
    WeilPrimeSumV1 (mixed (blk g i) (blk g j)) =
      ((Real.log 2 * Real.exp (-(((j - i : ℕ) : ℝ) * Real.log 2 / 2)) * energy g.1 : ℝ) : ℂ) := by
  have hk1 : 1 ≤ j - i := by omega
  have h2 : 1 ≤ 2 ^ (j - i) := Nat.one_le_two_pow
  unfold WeilPrimeSumV1
  rw [tsum_eq_single (2 ^ (j - i) - 1)]
  · have hm : 2 ^ (j - i) - 1 + 1 = 2 ^ (j - i) := Nat.sub_add_cancel h2
    simp only [WeilPrimeTermV1, hm]
    have hp := blk_mixed_nat_zero g a hw hij (2 ^ (j - i)) (by omega)
    have hc := blk_mixed_center g hij
    have hv : ArithmeticFunction.vonMangoldt (2 ^ (j - i)) = Real.log 2 := by
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega)]
      exact_mod_cast ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
    rw [hp, hc, hv]
    have h2k : ((2 ^ (j - i) : ℕ) : ℝ) = Real.exp (((j - i : ℕ) : ℝ) * Real.log 2 / 2) *
        Real.exp (((j - i : ℕ) : ℝ) * Real.log 2 / 2) := by
      rw [← Real.exp_add, show ((j - i : ℕ) : ℝ) * Real.log 2 / 2 + ((j - i : ℕ) : ℝ) * Real.log 2 / 2 =
          ((j - i : ℕ) : ℝ) * Real.log 2 by ring, Real.exp_nat_mul, Real.exp_log (by norm_num)]
      push_cast
      ring
    have hreal : Real.log 2 * (0 + 1 / ((2 ^ (j - i) : ℕ) : ℝ) *
        (Real.exp (((j - i : ℕ) : ℝ) * Real.log 2 / 2) * energy g.1)) =
        Real.log 2 * Real.exp (-(((j - i : ℕ) : ℝ) * Real.log 2 / 2)) * energy g.1 := by
      rw [h2k, Real.exp_neg]
      field_simp
      ring
    rw [← hreal]
    push_cast
    ring
  · intro n hn
    have hne : n + 1 ≠ 2 ^ (j - i) := by
      intro h
      apply hn
      omega
    have hp := blk_mixed_nat_zero g a hw hij (n + 1) (by omega)
    by_cases hwin : |Real.log ((n + 1 : ℕ) : ℝ) - ((j - i : ℕ) : ℝ) * Real.log 2| ≤ 1 / 32
    · rcases prime_window (by omega) hk hwin with h | h
      · exact absurd h hne
      · simp only [WeilPrimeTermV1, h, Complex.ofReal_zero, zero_mul]
    · have hi := blk_mixed_inv_zero_of_far g a hw hij (n + 1) (by omega) (lt_of_not_ge hwin)
      simp only [WeilPrimeTermV1, hp, hi, mul_zero, add_zero]

/-- Rational ceilings at gaps `1, …, 6`. -/
def cbar7 : ℕ → ℝ
  | 1 => 101 / 200
  | 2 => 71 / 200
  | 3 => 51 / 200
  | 4 => 9 / 50
  | 5 => 13 / 100
  | _ => 47 / 500

theorem prime_coeff_le7 (k : ℕ) (hk1 : 1 ≤ k) (hk6 : k ≤ 6) :
    Real.log 2 * Real.exp (-((k : ℝ) * Real.log 2 / 2)) + 1 / 200 ≤ cbar7 k := by
  set q := Real.exp (-(Real.log 2 / 2)) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hqq : q * q = 1 / 2 := by
    rw [hqdef, ← Real.exp_add, show -(Real.log 2 / 2) + -(Real.log 2 / 2) = -Real.log 2 by ring,
      Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hq : q ≤ 7072 / 10000 := by nlinarith
  have hpow : Real.exp (-((k : ℝ) * Real.log 2 / 2)) = q ^ k := by
    rw [hqdef, ← Real.exp_nat_mul]
    congr 1
    ring
  have hl := Real.log_two_lt_d9
  rw [hpow]
  have hqk : q ^ k ≤ (7072 / 10000 : ℝ) ^ k := pow_le_pow_left₀ hq0.le hq k
  have hb : Real.log 2 * q ^ k ≤ 0.6931471808 * (7072 / 10000 : ℝ) ^ k :=
    mul_le_mul hl.le hqk (pow_nonneg hq0.le k) (by norm_num)
  interval_cases k <;> simp only [cbar7] <;> norm_num at hb ⊢ <;> linarith

theorem blk_cross_norm_lt7 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) {i j : ℕ} (hij : i < j) (hk : j - i ≤ 6) :
    ‖B (blk g i) (blk g j)‖ ≤ cbar7 (j - i) * energy g.1 := by
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
  have hcoef := prime_coeff_le7 (j - i) (by omega) hk
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
    _ ≤ cbar7 (j - i) * energy g.1 := by nlinarith [mul_le_mul_of_nonneg_right hcoef hE]

theorem blk_cross_norm7 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) (i j : Fin 7) (hij : i ≠ j) :
    ‖B (blk g i) (blk g j)‖ ≤ cbar7 (Nat.dist i j) * energy g.1 := by
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = j => hij (Fin.ext h)) with h | h
  · have hd : Nat.dist i j = j - i := by unfold Nat.dist; omega
    rw [hd]
    exact blk_cross_norm_lt7 g a hw hm h (by omega)
  · have hd : Nat.dist i j = i - j := by unfold Nat.dist; omega
    rw [hd, B_hermitian, Complex.norm_conj]
    exact blk_cross_norm_lt7 g a hw hm h (by omega)

theorem blk_diag7 (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) (j : ℕ) :
    (109 / 50 : ℝ) * energy g.1 ≤ -(B (blk g j) (blk g j)).re := by
  have h := AEGIS.WeilDiagonalMomentGainV1.width_diagonal_109_over_50 (blk g j) _ (blk_width g a hw j)
    (translate_preserves_moments g _ hm)
  rwa [blk_energy] at h

/-- Weighted Schur test, weights `(7/10, 17/20, 19/20, 1, 19/20, 17/20, 7/10)`. -/
theorem seven_ceiling_quadratic (x0 x1 x2 x3 x4 x5 x6 : ℝ) :
    2 * ((101 / 200) * (x0 * x1 + x1 * x2 + x2 * x3 + x3 * x4 + x4 * x5 + x5 * x6) +
      (71 / 200) * (x0 * x2 + x1 * x3 + x2 * x4 + x3 * x5 + x4 * x6) +
      (51 / 200) * (x0 * x3 + x1 * x4 + x2 * x5 + x3 * x6) +
      (9 / 50) * (x0 * x4 + x1 * x5 + x2 * x6) + (13 / 100) * (x0 * x5 + x1 * x6) +
      (47 / 500) * (x0 * x6)) ≤
      2 * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2 + x6 ^ 2) := by
  nlinarith [sq_nonneg ((17 / 20) * x0 - (7 / 10) * x1), sq_nonneg ((19 / 20) * x0 - (7 / 10) * x2),
    sq_nonneg (1 * x0 - (7 / 10) * x3), sq_nonneg ((19 / 20) * x0 - (7 / 10) * x4),
    sq_nonneg ((17 / 20) * x0 - (7 / 10) * x5), sq_nonneg ((7 / 10) * x0 - (7 / 10) * x6),
    sq_nonneg ((19 / 20) * x1 - (17 / 20) * x2), sq_nonneg (1 * x1 - (17 / 20) * x3),
    sq_nonneg ((19 / 20) * x1 - (17 / 20) * x4), sq_nonneg ((17 / 20) * x1 - (17 / 20) * x5),
    sq_nonneg ((7 / 10) * x1 - (17 / 20) * x6),
    sq_nonneg (1 * x2 - (19 / 20) * x3), sq_nonneg ((19 / 20) * x2 - (19 / 20) * x4),
    sq_nonneg ((17 / 20) * x2 - (19 / 20) * x5), sq_nonneg ((7 / 10) * x2 - (19 / 20) * x6),
    sq_nonneg ((19 / 20) * x3 - 1 * x4), sq_nonneg ((17 / 20) * x3 - 1 * x5),
    sq_nonneg ((7 / 10) * x3 - 1 * x6),
    sq_nonneg ((17 / 20) * x4 - (19 / 20) * x5), sq_nonneg ((7 / 10) * x4 - (19 / 20) * x6),
    sq_nonneg ((7 / 10) * x5 - (17 / 20) * x6),
    sq_nonneg x0, sq_nonneg x1, sq_nonneg x2, sq_nonneg x3, sq_nonneg x4, sq_nonneg x5, sq_nonneg x6]

/-- **Seven-block comb at width 1/32.** -/
theorem seven_block_gram_bound (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) (z : Fin 7 → ℂ) :
    (∑ i : Fin 7, ∑ j : Fin 7, z i * star (z j) * B (blk g i) (blk g j)).re ≤
      -(1 / 10 : ℝ) * energy g.1 * ∑ i : Fin 7, ‖z i‖ ^ 2 := by
  have hE := energy_nonnegative g.1
  have hterm : ∀ i j : Fin 7, (z i * star (z j) * B (blk g i) (blk g j)).re ≤
      ‖z i‖ * ‖z j‖ * ((if Nat.dist i j = 0 then -(109 / 50 : ℝ) else cbar7 (Nat.dist i j)) *
        energy g.1) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos (Nat.dist_self _), re_diag]
      have hd := blk_diag7 g a hw hm i
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
        _ ≤ ‖z i‖ * ‖z j‖ * (cbar7 (Nat.dist i j) * energy g.1) :=
            mul_le_mul_of_nonneg_left (blk_cross_norm7 g a hw hm i j hij)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  calc (∑ i : Fin 7, ∑ j : Fin 7, (z i * star (z j) * B (blk g i) (blk g j)).re)
      ≤ ∑ i : Fin 7, ∑ j : Fin 7,
          ‖z i‖ * ‖z j‖ * ((if Nat.dist i j = 0 then -(109 / 50 : ℝ) else cbar7 (Nat.dist i j)) *
            energy g.1) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ ≤ -(1 / 10 : ℝ) * energy g.1 * ∑ i : Fin 7, ‖z i‖ ^ 2 := by
        have hq := seven_ceiling_quadratic ‖z 0‖ ‖z 1‖ ‖z 2‖ ‖z 3‖ ‖z 4‖ ‖z 5‖ ‖z 6‖
        simp only [Fin.sum_univ_seven]
        norm_num [cbar7, Nat.dist]
        nlinarith [mul_le_mul_of_nonneg_left hq hE, sq_nonneg ‖z 0‖, sq_nonneg ‖z 1‖, sq_nonneg ‖z 2‖,
          sq_nonneg ‖z 3‖, sq_nonneg ‖z 4‖, sq_nonneg ‖z 5‖, sq_nonneg ‖z 6‖,
          mul_nonneg hE (sq_nonneg ‖z 0‖), mul_nonneg hE (sq_nonneg ‖z 1‖),
          mul_nonneg hE (sq_nonneg ‖z 2‖), mul_nonneg hE (sq_nonneg ‖z 3‖),
          mul_nonneg hE (sq_nonneg ‖z 4‖), mul_nonneg hE (sq_nonneg ‖z 5‖),
          mul_nonneg hE (sq_nonneg ‖z 6‖)]

end AEGIS.WeilSevenBlockCombV1

#print axioms AEGIS.WeilSevenBlockCombV1.prime_window
#print axioms AEGIS.WeilSevenBlockCombV1.blk_prime_sum6
#print axioms AEGIS.WeilSevenBlockCombV1.seven_block_gram_bound
