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

import WeilSeparatedArchL1BridgeV32
import WeilDiagonalLogGainV1

/-!
AEGIS Ω — the five-block dyadic comb at width 1/32 (Claude Lab, 2026-11-22).

The blocks are `blk g j = T_{j log 2} g` for `j = 0, …, 4`, where `g` has log-width `1/32` (`WidthOneThirtyTwoAt`)
and both moments. This is step 3 of `research/rh/atomic_map_v1` §4.5 (AEGIS-OMEGA PR #835).

* Isolation (`nat_eq_pow_of_log_window`): for a gap `k ≤ 4` the only positive integer whose logarithm lies within
  `1/32` of `k log 2` is `2^k`. So the mixed correlation of blocks `i < j` meets the prime sum only at `2^{j−i}`.
* Exact prime part (`blk_prime_sum`): `log 2 · 2^{−k/2} · E`.
* Archimedean part: `≤ E/200` (`WeilSeparatedArchL1BridgeV32.translated_arch_norm_bound_l1`).
* Diagonal: `17/10 · E` (`WeilDiagonalLogGainV1.width_diagonal_17_over_10`), no moments needed there.
* Assembly (`five_block_gram_bound`): a weighted Schur test with weights `(4/5, 19/20, 1, 19/20, 4/5)` bounds the
  off-diagonal part by `8/5 · E · Σ ‖z_i‖²`, so the Gram form is `≤ −(1/10) · E · Σ ‖z_i‖²`.

With `RHGramExpansionV13.B_packetSum` the left side is `Re B(Σ z_i T_i g, Σ z_i T_i g)`.

Fixed-width comb class only. Not the full test-function class, no window statement, not RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilFiveBlockCombV1

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilArchimedeanCothTailV1

/-- Block `j` of the dyadic comb: the translate of `g` by `j log 2`. -/
def blk (g : WeilCompactSmoothGV1) (j : ℕ) : WeilCompactSmoothGV1 :=
  translatePacket g ((j : ℝ) * Real.log 2)

theorem blk_energy (g : WeilCompactSmoothGV1) (j : ℕ) : energy (blk g j).1 = energy g.1 :=
  translate_energy g _

theorem blk_width (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a) (j : ℕ) :
    WidthOneThirtyTwoAt (blk g j) (a + (j : ℝ) * Real.log 2) := by
  have h := translate_logSupportIn g ((j : ℝ) * Real.log 2) _ _ hw
  change LogSupportIn (translatePacket g ((j : ℝ) * Real.log 2))
    (a + (j : ℝ) * Real.log 2 - 1 / 64) (a + (j : ℝ) * Real.log 2 + 1 / 64)
  convert h using 1 <;> ring

/-- Only `2^k` lies in the log-window of radius `1/32` around `k log 2`, for `k ≤ 4`. -/
theorem nat_eq_pow_of_log_window {m k : ℕ} (hm : 0 < m) (hk : k ≤ 4)
    (hwin : |Real.log (m : ℝ) - (k : ℝ) * Real.log 2| ≤ 1 / 32) : m = 2 ^ k := by
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
  have hpk : (2 : ℝ) ^ k ≤ 16 := by
    calc (2 : ℝ) ^ k ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hk
      _ = 16 := by norm_num
  have hpk0 : (0 : ℝ) < 2 ^ k := by positivity
  have e1 := mul_lt_mul_of_pos_left exp_one_div_32_lt hpk0
  have e2 := mul_lt_mul_of_pos_left exp_neg_one_div_32_gt hpk0
  have hlt : (m : ℝ) < 2 ^ k + 1 := by nlinarith
  have hgt : (2 : ℝ) ^ k < m + 1 := by nlinarith
  have hlt' : m < 2 ^ k + 1 := by exact_mod_cast hlt
  have hgt' : 2 ^ k < m + 1 := by exact_mod_cast hgt
  omega

theorem blk_mixed_nat_zero (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    {i j : ℕ} (hij : i < j) (m : ℕ) (hm : 0 < m) :
    mixed (blk g i) (blk g j) (m : ℝ) = 0 := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hL := log_two_gt_one_thirty_two
  have hji : (1 : ℝ) ≤ (j : ℝ) - i := by
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    linarith
  have hprod : Real.log 2 ≤ ((j : ℝ) - i) * Real.log 2 := by nlinarith
  have harg : 0 < Real.log (m : ℝ) + (j : ℝ) * Real.log 2 - (i : ℝ) * Real.log 2 := by nlinarith
  have hfar : (1 / 32 : ℝ) < |Real.log (m : ℝ) + (j : ℝ) * Real.log 2 - (i : ℝ) * Real.log 2| := by
    rw [abs_of_pos harg]
    nlinarith
  have hz := mixed_translate_zero_of_width_v28 g a ((i : ℝ) * Real.log 2) ((j : ℝ) * Real.log 2)
    (Real.log (m : ℝ)) hw hfar
  rw [Real.exp_log (by exact_mod_cast hm)] at hz
  exact hz

theorem blk_mixed_inv_nat_zero (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    {i j : ℕ} (hij : i < j) (hk : j - i ≤ 4) (m : ℕ) (hm : 0 < m) (hne : m ≠ 2 ^ (j - i)) :
    mixed (blk g i) (blk g j) ((m : ℝ)⁻¹) = 0 := by
  have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - i := by rw [Nat.cast_sub hij.le]
  have hfar0 : (1 / 32 : ℝ) < |Real.log (m : ℝ) - ((j - i : ℕ) : ℝ) * Real.log 2| := by
    by_contra hnot
    exact hne (nat_eq_pow_of_log_window hm hk (le_of_not_gt hnot))
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

/-- The value of the mixed correlation at the resonant sample `2^{−k}`. -/
theorem blk_mixed_center (g : WeilCompactSmoothGV1) {i j : ℕ} (hij : i < j) :
    mixed (blk g i) (blk g j) (((2 ^ (j - i) : ℕ) : ℝ)⁻¹) =
      (Real.exp (((j - i : ℕ) : ℝ) * Real.log 2 / 2) : ℂ) * (energy g.1 : ℂ) := by
  have h := mixed_translate_center_v28 g ((i : ℝ) * Real.log 2) ((j : ℝ) * Real.log 2)
  have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - i := by rw [Nat.cast_sub hij.le]
  have hx : Real.exp ((i : ℝ) * Real.log 2 - (j : ℝ) * Real.log 2) = (((2 ^ (j - i) : ℕ) : ℝ))⁻¹ := by
    rw [show (i : ℝ) * Real.log 2 - (j : ℝ) * Real.log 2 = -(((j - i : ℕ) : ℝ) * Real.log 2) by
        rw [hcast]; ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    push_cast
    ring
  rw [hx] at h
  have hc : (Real.exp (((j - i : ℕ) : ℝ) * Real.log 2 / 2) : ℂ) *
      (Real.exp (((i : ℝ) * Real.log 2 - (j : ℝ) * Real.log 2) / 2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, hcast]
    rw [show ((j : ℝ) - i) * Real.log 2 / 2 + ((i : ℝ) * Real.log 2 - (j : ℝ) * Real.log 2) / 2 = 0 by ring,
      Real.exp_zero, Complex.ofReal_one]
  change (Real.exp (((i : ℝ) * Real.log 2 - (j : ℝ) * Real.log 2) / 2) : ℂ) *
    mixed (blk g i) (blk g j) (((2 ^ (j - i) : ℕ) : ℝ))⁻¹ = (energy g.1 : ℂ) at h
  calc mixed (blk g i) (blk g j) (((2 ^ (j - i) : ℕ) : ℝ)⁻¹)
      = (Real.exp (((j - i : ℕ) : ℝ) * Real.log 2 / 2) : ℂ) *
          ((Real.exp (((i : ℝ) * Real.log 2 - (j : ℝ) * Real.log 2) / 2) : ℂ) *
            mixed (blk g i) (blk g j) (((2 ^ (j - i) : ℕ) : ℝ)⁻¹)) := by
        rw [← mul_assoc, hc, one_mul]
    _ = (Real.exp (((j - i : ℕ) : ℝ) * Real.log 2 / 2) : ℂ) * (energy g.1 : ℂ) := by rw [h]

/-- **Exact prime part** of a cross block at gap `k = j − i ≤ 4`. -/
theorem blk_prime_sum (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    {i j : ℕ} (hij : i < j) (hk : j - i ≤ 4) :
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
    have hpos : 0 < Real.exp (((j - i : ℕ) : ℝ) * Real.log 2 / 2) := Real.exp_pos _
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
    have hi := blk_mixed_inv_nat_zero g a hw hij hk (n + 1) (by omega) hne
    simp only [WeilPrimeTermV1, hp, hi, mul_zero, add_zero]

/-- Rational ceilings for the cross blocks at gap `k`: prime part plus `1/200`. -/
def cbar : ℕ → ℝ
  | 1 => 101 / 200
  | 2 => 71 / 200
  | 3 => 51 / 200
  | _ => 9 / 50

theorem prime_coeff_le (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    Real.log 2 * Real.exp (-((k : ℝ) * Real.log 2 / 2)) + 1 / 200 ≤ cbar k := by
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
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [hpow]
  have hqk : q ^ k ≤ (7072 / 10000 : ℝ) ^ k := pow_le_pow_left₀ hq0.le hq k
  have hb : Real.log 2 * q ^ k ≤ 0.6931471808 * (7072 / 10000 : ℝ) ^ k :=
    mul_le_mul hl.le hqk (pow_nonneg hq0.le k) (by norm_num)
  interval_cases k <;> simp only [cbar] <;> norm_num at hb ⊢ <;> linarith

theorem blk_cross_norm_lt (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) {i j : ℕ} (hij : i < j) (hk : j - i ≤ 4) :
    ‖B (blk g i) (blk g j)‖ ≤ cbar (j - i) * energy g.1 := by
  have hE := energy_nonnegative g.1
  have hzero : mixed (blk g i) (blk g j) 1 = 0 := by
    simpa using blk_mixed_nat_zero g a hw hij 1 one_pos
  have hprime := blk_prime_sum g a hw hij hk
  have hji : (1 : ℝ) ≤ (j : ℝ) - i := by
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harch := AEGIS.WeilSeparatedArchL1BridgeV32.translated_arch_norm_bound_l1 g a
    ((i : ℝ) * Real.log 2) ((j : ℝ) * Real.log 2) hw hm (by nlinarith)
  have hcoef := prime_coeff_le (j - i) (by omega) hk
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
    _ ≤ cbar (j - i) * energy g.1 := by nlinarith [mul_le_mul_of_nonneg_right hcoef hE]

/-- Cross bound for any two distinct blocks of the five. -/
theorem blk_cross_norm (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) (i j : Fin 5) (hij : i ≠ j) :
    ‖B (blk g i) (blk g j)‖ ≤ cbar (Nat.dist i j) * energy g.1 := by
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = j => hij (Fin.ext h)) with h | h
  · have hd : Nat.dist i j = j - i := by unfold Nat.dist; omega
    rw [hd]
    exact blk_cross_norm_lt g a hw hm h (by omega)
  · have hd : Nat.dist i j = i - j := by unfold Nat.dist; omega
    rw [hd, B_hermitian, Complex.norm_conj]
    exact blk_cross_norm_lt g a hw hm h (by omega)

theorem blk_diag (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a) (j : ℕ) :
    (17 / 10 : ℝ) * energy g.1 ≤ -(B (blk g j) (blk g j)).re := by
  have h := AEGIS.WeilDiagonalLogGainV1.width_diagonal_17_over_10 (blk g j) _ (blk_width g a hw j)
  rwa [blk_energy] at h

/-- Weighted Schur test for the ceilings `cbar`, weights `(4/5, 19/20, 1, 19/20, 4/5)`. -/
theorem five_ceiling_quadratic (x0 x1 x2 x3 x4 : ℝ) :
    2 * ((101 / 200) * (x0 * x1 + x1 * x2 + x2 * x3 + x3 * x4) +
      (71 / 200) * (x0 * x2 + x1 * x3 + x2 * x4) + (51 / 200) * (x0 * x3 + x1 * x4) +
      (9 / 50) * (x0 * x4)) ≤
      (8 / 5) * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) := by
  nlinarith [sq_nonneg ((19 / 20) * x0 - (4 / 5) * x1), sq_nonneg (1 * x0 - (4 / 5) * x2),
    sq_nonneg ((19 / 20) * x0 - (4 / 5) * x3), sq_nonneg ((4 / 5) * x0 - (4 / 5) * x4),
    sq_nonneg (1 * x1 - (19 / 20) * x2), sq_nonneg ((19 / 20) * x1 - (19 / 20) * x3),
    sq_nonneg ((4 / 5) * x1 - (19 / 20) * x4), sq_nonneg ((19 / 20) * x2 - 1 * x3),
    sq_nonneg ((4 / 5) * x2 - 1 * x4), sq_nonneg ((4 / 5) * x3 - (19 / 20) * x4),
    sq_nonneg x0, sq_nonneg x1, sq_nonneg x2, sq_nonneg x3, sq_nonneg x4]

theorem re_diag (z w : ℂ) : (z * star z * w).re = ‖z‖ ^ 2 * w.re := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_ofReal_mul]

/-- **Five-block comb at width 1/32.** -/
theorem five_block_gram_bound (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (hm : WeilMomentConditionsV1 g) (z : Fin 5 → ℂ) :
    (∑ i : Fin 5, ∑ j : Fin 5, z i * star (z j) * B (blk g i) (blk g j)).re ≤
      -(1 / 10 : ℝ) * energy g.1 * ∑ i : Fin 5, ‖z i‖ ^ 2 := by
  have hE := energy_nonnegative g.1
  have hterm : ∀ i j : Fin 5, (z i * star (z j) * B (blk g i) (blk g j)).re ≤
      ‖z i‖ * ‖z j‖ * ((if Nat.dist i j = 0 then -(17 / 10 : ℝ) else cbar (Nat.dist i j)) * energy g.1) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos (Nat.dist_self _), re_diag]
      have hd := blk_diag g a hw i
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
        _ ≤ ‖z i‖ * ‖z j‖ * (cbar (Nat.dist i j) * energy g.1) :=
            mul_le_mul_of_nonneg_left (blk_cross_norm g a hw hm i j hij)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  calc (∑ i : Fin 5, ∑ j : Fin 5, (z i * star (z j) * B (blk g i) (blk g j)).re)
      ≤ ∑ i : Fin 5, ∑ j : Fin 5,
          ‖z i‖ * ‖z j‖ * ((if Nat.dist i j = 0 then -(17 / 10 : ℝ) else cbar (Nat.dist i j)) * energy g.1) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ ≤ -(1 / 10 : ℝ) * energy g.1 * ∑ i : Fin 5, ‖z i‖ ^ 2 := by
        have hq := five_ceiling_quadratic ‖z 0‖ ‖z 1‖ ‖z 2‖ ‖z 3‖ ‖z 4‖
        simp only [Fin.sum_univ_five]
        norm_num [cbar, Nat.dist]
        nlinarith [mul_le_mul_of_nonneg_left hq hE]

end AEGIS.WeilFiveBlockCombV1

#print axioms AEGIS.WeilFiveBlockCombV1.nat_eq_pow_of_log_window
#print axioms AEGIS.WeilFiveBlockCombV1.blk_prime_sum
#print axioms AEGIS.WeilFiveBlockCombV1.blk_cross_norm
#print axioms AEGIS.WeilFiveBlockCombV1.five_block_gram_bound
