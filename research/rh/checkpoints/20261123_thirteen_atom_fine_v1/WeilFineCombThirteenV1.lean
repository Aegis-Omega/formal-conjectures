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

import WeilNineBlockMultiV1
import WeilFineDiagonalQuadV1

/-!
AEGIS Ω — thirteen independent atoms of log-width 1/128 on the dyadic lattice (Claude Lab, 2026-11-22).

Blocks `f_j = T_{j log 2} g_j`, `j = 0, …, 12`, where every `g_j` has `LogSupportIn g_j (a − 1/256) (a + 1/256)`
(one common `a`) and both moments. Compared with `WeilNineBlockMultiV1`:
* the diagonal is `43/10 · E` (`WeilFineDiagonalQuadV1.fine_diagonal_43_over_10`);
* the prime windows have radius `1/128` (`fine_logCross_zero`, `fine_mixed_inv_far`), so far fewer prime powers
  enter: only `2^k` for `k ≤ 7`; then `{256, 257}`, `{509, 512}`, `{1019, 1021, 1024, 1031}`,
  `{2039, 2048, 2053, 2063}` and eight prime powers in `[4065, 4128]` at gaps `8, …, 12` (`fwin1`, …, `fwin12`);
* each term is bounded by `Λ(m) m^{−1/2}` times the weighted Cauchy–Schwarz form (`term_norm_le2`), and the masses
  per gap are `pbar13 k` (`fps1`, …, `fps12`); the Archimedean cross term is `(E(p) + E(q))/400` (`arch2`);
* the Schur weights are `wv13`; the largest row coefficient is `3.6682 ≤ 37/10`.

Result (`thirteen_atom_gram_bound`): `Re Σ_{i,j} B(f_i, f_j) ≤ −(3/5) Σ_j E(g_j)`.

Dyadic multi-atom class at width 1/128 only. Not RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilFineCombThirteenV1

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilArchimedeanCothTailV1
open AEGIS.WeilFiveBlockCombV1
open AEGIS.WeilSevenBlockCombV1
open AEGIS.WeilEightBlockCombV1
open AEGIS.WeilNineBlockMultiV1

theorem exp_fine_upper : Real.exp (1 / 128) < 10079 / 10000 := by
  have h := Real.exp_bound (x := (1 / 128 : ℝ)) (by norm_num) (n := 3) (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero] at h
  norm_num at h
  rw [abs_le] at h
  linarith [h.2]

theorem exp_fine_lower : (9922 / 10000 : ℝ) < Real.exp (-(1 / 128)) := by
  have h := Real.exp_bound (x := (-(1 / 128) : ℝ)) (by norm_num) (n := 3) (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero] at h
  norm_num at h
  rw [abs_le] at h
  linarith [h.1]

theorem log_le_pow2 (k : ℕ) (m : ℝ) (hm : 0 < m) : Real.log m ≤ k * Real.log 2 + (m / 2 ^ k - 1) := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m / 2 ^ k by positivity)
  rw [Real.log_div hm.ne' hp.ne', Real.log_pow] at h
  linarith

theorem fine_logCross_zero (p q : WeilCompactSmoothGV1) (a u : ℝ)
    (hp : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hq : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    (hu : (1 / 128 : ℝ) < |u|) : logCrossV28 p q u = 0 := by
  unfold logCrossV28
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  by_cases h0 : logLift q.1 v = 0
  · simp [h0]
  · by_cases h1 : logLift p.1 (v + u) = 0
    · simp [h1]
    · have hv := hq (subset_tsupport _ h0)
      have hvu := hp (subset_tsupport _ h1)
      have habs : |u| ≤ (1 / 128 : ℝ) := by
        rw [abs_le]
        constructor <;> linarith [hv.1, hv.2, hvu.1, hvu.2]
      exact False.elim ((not_le_of_gt hu) habs)

theorem fine_mixed_zero (p q : WeilCompactSmoothGV1) (a d1 d2 u : ℝ)
    (hp : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hq : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    (hu : (1 / 128 : ℝ) < |u + d2 - d1|) :
    mixed (translatePacket p d1) (translatePacket q d2) (Real.exp u) = 0 := by
  have h := logCross_eq_mixed_v28 (translatePacket p d1) (translatePacket q d2) u
  rw [logCross_translate2, fine_logCross_zero p q a _ hp hq hu] at h
  have he : (Real.exp (u / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  exact (mul_eq_zero.mp h.symm).resolve_left he

theorem fine_mixed_inv_far (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hp : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hq : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    {i j : ℕ} (hij : i < j) (m : ℕ) (hm : 0 < m)
    (hfar0 : (1 / 128 : ℝ) < |Real.log (m : ℝ) - ((j - i : ℕ) : ℝ) * Real.log 2|) :
    mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))
      ((m : ℝ)⁻¹) = 0 := by
  have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - i := by rw [Nat.cast_sub hij.le]
  have harg : -Real.log (m : ℝ) + (j : ℝ) * Real.log 2 - (i : ℝ) * Real.log 2 =
      -(Real.log (m : ℝ) - ((j - i : ℕ) : ℝ) * Real.log 2) := by
    rw [hcast]
    ring
  have hfar : (1 / 128 : ℝ) < |-Real.log (m : ℝ) + (j : ℝ) * Real.log 2 - (i : ℝ) * Real.log 2| := by
    rw [harg, abs_neg]
    exact hfar0
  have hz := fine_mixed_zero p q a ((i : ℝ) * Real.log 2) ((j : ℝ) * Real.log 2) (-Real.log (m : ℝ)) hp hq hfar
  rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hm)] at hz
  exact hz

theorem tsum_fine_eq (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hpf : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hqf : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    {i j : ℕ} (hij : i < j) (k : ℕ) (hk : j - i = k) (s : Finset ℕ)
    (hw : ∀ n : ℕ, |Real.log ((n + 1 : ℕ) : ℝ) - ((k : ℕ) : ℝ) * Real.log 2| ≤ 1 / 128 →
      n ∈ s ∨ ArithmeticFunction.vonMangoldt (n + 1) = 0) :
    WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2))
        (translatePacket q ((j : ℝ) * Real.log 2))) =
      ∑ n ∈ s, WeilPrimeTermV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2))
        (translatePacket q ((j : ℝ) * Real.log 2))) n := by
  unfold WeilPrimeSumV1
  apply tsum_eq_sum
  intro n hn
  have hp0 := mixed_nat_zero2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij (n + 1) (by omega)
  by_cases hwin : |Real.log ((n + 1 : ℕ) : ℝ) - ((j - i : ℕ) : ℝ) * Real.log 2| ≤ 1 / 128
  · rw [hk] at hwin
    rcases hw n hwin with h | h
    · exact absurd h hn
    · simp only [WeilPrimeTermV1, h, Complex.ofReal_zero, zero_mul]
  · have hi := fine_mixed_inv_far p q a hpf hqf hij (n + 1) (by omega) (lt_of_not_ge hwin)
    simp only [WeilPrimeTermV1, hp0, hi, mul_zero, add_zero]


/-- `Λ m = 0` from two distinct prime factors `p, q` of `m`. -/
macro "vm0 " p:num q:num : tactic =>
  `(tactic| exact AEGIS.WeilSevenBlockCombV1.vonMangoldt_eq_zero_of_two_primes (p := $p) (q := $q)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- Mass of `2^k`. -/
theorem fmass_pow2 (k n : ℕ) (hn : n + 1 = 2 ^ k) (hk : k ≠ 0) (rq r : ℝ) (hrq0 : 0 < rq)
    (hrq : 1 / ((n + 1 : ℕ) : ℝ) ≤ rq ^ 2) (hr : 0.6931471808 * rq ≤ r) :
    ArithmeticFunction.vonMangoldt (n + 1) * Real.exp (-Real.log ((n + 1 : ℕ) : ℝ) / 2) ≤ r := by
  have hv : ArithmeticFunction.vonMangoldt (n + 1) = Real.log 2 := by
    rw [hn, ArithmeticFunction.vonMangoldt_apply_pow hk,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  rw [hv]
  have hl2 := Real.log_two_lt_d9
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hq := q_le _ rq hpos hrq0 hrq
  calc Real.log 2 * Real.exp (-Real.log ((n + 1 : ℕ) : ℝ) / 2) ≤ 0.6931471808 * rq :=
        mul_le_mul hl2.le hq (Real.exp_pos _).le (by norm_num)
    _ ≤ r := hr

/-- Mass of a prime `n + 1` near `2^k`. -/
theorem fmass_prime (k n : ℕ) (hp : (n + 1).Prime) (B rq r : ℝ)
    (hB : (k : ℝ) * 0.6931471808 + (((n + 1 : ℕ) : ℝ) / 2 ^ k - 1) ≤ B) (hrq0 : 0 < rq)
    (hrq : 1 / ((n + 1 : ℕ) : ℝ) ≤ rq ^ 2) (hr : B * rq ≤ r) :
    ArithmeticFunction.vonMangoldt (n + 1) * Real.exp (-Real.log ((n + 1 : ℕ) : ℝ) / 2) ≤ r := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hl := log_le_pow2 k _ hpos
  have hl2 := Real.log_two_lt_d9
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hb : Real.log ((n + 1 : ℕ) : ℝ) ≤ B := by nlinarith
  have hq := q_le _ rq hpos hrq0 hrq
  have hlog0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 n)
  calc Real.log ((n + 1 : ℕ) : ℝ) * Real.exp (-Real.log ((n + 1 : ℕ) : ℝ) / 2) ≤ B * rq :=
        mul_le_mul hb hq (Real.exp_pos _).le (hlog0.trans hb)
    _ ≤ r := hr


theorem fwin1 {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - ((1 : ℕ) : ℝ) * Real.log 2| ≤ 1 / 128) :
    ArithmeticFunction.vonMangoldt m = 0 ∨ m = 2 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := abs_le.mp hwin
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ ((1 : ℕ) : ℝ) * Real.log 2 + 1 / 128 by linarith [habs.2])
  have hlo := Real.exp_le_exp.mpr
    (show ((1 : ℕ) : ℝ) * Real.log 2 - 1 / 128 ≤ Real.log (m : ℝ) by linarith [habs.1])
  have h2k : Real.exp (((1 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ 1 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, h2k] at hup
  rw [sub_eq_add_neg, Real.exp_add, h2k] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have e1 := mul_lt_mul_of_pos_left exp_fine_upper (by norm_num : (0 : ℝ) < 2 ^ 1)
  have e2 := mul_lt_mul_of_pos_left exp_fine_lower (by norm_num : (0 : ℝ) < 2 ^ 1)
  have hlt : (m : ℝ) < 2 ^ 1 * (10079 / 10000) := by linarith
  have hgt : (2 : ℝ) ^ 1 * (9922 / 10000) < m := by linarith
  norm_num at hlt hgt
  have h1 : m < 3 := by exact_mod_cast (show (m : ℝ) < 3 by linarith)
  have h2 : 1 < m := by exact_mod_cast (show (1 : ℝ) < m by linarith)
  interval_cases m
  · right; rfl

theorem fwin2 {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - ((2 : ℕ) : ℝ) * Real.log 2| ≤ 1 / 128) :
    ArithmeticFunction.vonMangoldt m = 0 ∨ m = 4 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := abs_le.mp hwin
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ ((2 : ℕ) : ℝ) * Real.log 2 + 1 / 128 by linarith [habs.2])
  have hlo := Real.exp_le_exp.mpr
    (show ((2 : ℕ) : ℝ) * Real.log 2 - 1 / 128 ≤ Real.log (m : ℝ) by linarith [habs.1])
  have h2k : Real.exp (((2 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ 2 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, h2k] at hup
  rw [sub_eq_add_neg, Real.exp_add, h2k] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have e1 := mul_lt_mul_of_pos_left exp_fine_upper (by norm_num : (0 : ℝ) < 2 ^ 2)
  have e2 := mul_lt_mul_of_pos_left exp_fine_lower (by norm_num : (0 : ℝ) < 2 ^ 2)
  have hlt : (m : ℝ) < 2 ^ 2 * (10079 / 10000) := by linarith
  have hgt : (2 : ℝ) ^ 2 * (9922 / 10000) < m := by linarith
  norm_num at hlt hgt
  have h1 : m < 5 := by exact_mod_cast (show (m : ℝ) < 5 by linarith)
  have h2 : 3 < m := by exact_mod_cast (show (3 : ℝ) < m by linarith)
  interval_cases m
  · right; rfl

theorem fwin3 {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - ((3 : ℕ) : ℝ) * Real.log 2| ≤ 1 / 128) :
    ArithmeticFunction.vonMangoldt m = 0 ∨ m = 8 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := abs_le.mp hwin
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ ((3 : ℕ) : ℝ) * Real.log 2 + 1 / 128 by linarith [habs.2])
  have hlo := Real.exp_le_exp.mpr
    (show ((3 : ℕ) : ℝ) * Real.log 2 - 1 / 128 ≤ Real.log (m : ℝ) by linarith [habs.1])
  have h2k : Real.exp (((3 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ 3 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, h2k] at hup
  rw [sub_eq_add_neg, Real.exp_add, h2k] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have e1 := mul_lt_mul_of_pos_left exp_fine_upper (by norm_num : (0 : ℝ) < 2 ^ 3)
  have e2 := mul_lt_mul_of_pos_left exp_fine_lower (by norm_num : (0 : ℝ) < 2 ^ 3)
  have hlt : (m : ℝ) < 2 ^ 3 * (10079 / 10000) := by linarith
  have hgt : (2 : ℝ) ^ 3 * (9922 / 10000) < m := by linarith
  norm_num at hlt hgt
  have h1 : m < 9 := by exact_mod_cast (show (m : ℝ) < 9 by linarith)
  have h2 : 7 < m := by exact_mod_cast (show (7 : ℝ) < m by linarith)
  interval_cases m
  · right; rfl

theorem fwin4 {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - ((4 : ℕ) : ℝ) * Real.log 2| ≤ 1 / 128) :
    ArithmeticFunction.vonMangoldt m = 0 ∨ m = 16 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := abs_le.mp hwin
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ ((4 : ℕ) : ℝ) * Real.log 2 + 1 / 128 by linarith [habs.2])
  have hlo := Real.exp_le_exp.mpr
    (show ((4 : ℕ) : ℝ) * Real.log 2 - 1 / 128 ≤ Real.log (m : ℝ) by linarith [habs.1])
  have h2k : Real.exp (((4 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ 4 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, h2k] at hup
  rw [sub_eq_add_neg, Real.exp_add, h2k] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have e1 := mul_lt_mul_of_pos_left exp_fine_upper (by norm_num : (0 : ℝ) < 2 ^ 4)
  have e2 := mul_lt_mul_of_pos_left exp_fine_lower (by norm_num : (0 : ℝ) < 2 ^ 4)
  have hlt : (m : ℝ) < 2 ^ 4 * (10079 / 10000) := by linarith
  have hgt : (2 : ℝ) ^ 4 * (9922 / 10000) < m := by linarith
  norm_num at hlt hgt
  have h1 : m < 17 := by exact_mod_cast (show (m : ℝ) < 17 by linarith)
  have h2 : 15 < m := by exact_mod_cast (show (15 : ℝ) < m by linarith)
  interval_cases m
  · right; rfl

theorem fwin5 {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - ((5 : ℕ) : ℝ) * Real.log 2| ≤ 1 / 128) :
    ArithmeticFunction.vonMangoldt m = 0 ∨ m = 32 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := abs_le.mp hwin
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ ((5 : ℕ) : ℝ) * Real.log 2 + 1 / 128 by linarith [habs.2])
  have hlo := Real.exp_le_exp.mpr
    (show ((5 : ℕ) : ℝ) * Real.log 2 - 1 / 128 ≤ Real.log (m : ℝ) by linarith [habs.1])
  have h2k : Real.exp (((5 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ 5 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, h2k] at hup
  rw [sub_eq_add_neg, Real.exp_add, h2k] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have e1 := mul_lt_mul_of_pos_left exp_fine_upper (by norm_num : (0 : ℝ) < 2 ^ 5)
  have e2 := mul_lt_mul_of_pos_left exp_fine_lower (by norm_num : (0 : ℝ) < 2 ^ 5)
  have hlt : (m : ℝ) < 2 ^ 5 * (10079 / 10000) := by linarith
  have hgt : (2 : ℝ) ^ 5 * (9922 / 10000) < m := by linarith
  norm_num at hlt hgt
  have h1 : m < 33 := by exact_mod_cast (show (m : ℝ) < 33 by linarith)
  have h2 : 31 < m := by exact_mod_cast (show (31 : ℝ) < m by linarith)
  interval_cases m
  · right; rfl

theorem fwin6 {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - ((6 : ℕ) : ℝ) * Real.log 2| ≤ 1 / 128) :
    ArithmeticFunction.vonMangoldt m = 0 ∨ m = 64 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := abs_le.mp hwin
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ ((6 : ℕ) : ℝ) * Real.log 2 + 1 / 128 by linarith [habs.2])
  have hlo := Real.exp_le_exp.mpr
    (show ((6 : ℕ) : ℝ) * Real.log 2 - 1 / 128 ≤ Real.log (m : ℝ) by linarith [habs.1])
  have h2k : Real.exp (((6 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ 6 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, h2k] at hup
  rw [sub_eq_add_neg, Real.exp_add, h2k] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have e1 := mul_lt_mul_of_pos_left exp_fine_upper (by norm_num : (0 : ℝ) < 2 ^ 6)
  have e2 := mul_lt_mul_of_pos_left exp_fine_lower (by norm_num : (0 : ℝ) < 2 ^ 6)
  have hlt : (m : ℝ) < 2 ^ 6 * (10079 / 10000) := by linarith
  have hgt : (2 : ℝ) ^ 6 * (9922 / 10000) < m := by linarith
  norm_num at hlt hgt
  have h1 : m < 65 := by exact_mod_cast (show (m : ℝ) < 65 by linarith)
  have h2 : 63 < m := by exact_mod_cast (show (63 : ℝ) < m by linarith)
  interval_cases m
  · right; rfl

theorem fwin7 {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - ((7 : ℕ) : ℝ) * Real.log 2| ≤ 1 / 128) :
    ArithmeticFunction.vonMangoldt m = 0 ∨ m = 128 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := abs_le.mp hwin
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ ((7 : ℕ) : ℝ) * Real.log 2 + 1 / 128 by linarith [habs.2])
  have hlo := Real.exp_le_exp.mpr
    (show ((7 : ℕ) : ℝ) * Real.log 2 - 1 / 128 ≤ Real.log (m : ℝ) by linarith [habs.1])
  have h2k : Real.exp (((7 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ 7 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, h2k] at hup
  rw [sub_eq_add_neg, Real.exp_add, h2k] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have e1 := mul_lt_mul_of_pos_left exp_fine_upper (by norm_num : (0 : ℝ) < 2 ^ 7)
  have e2 := mul_lt_mul_of_pos_left exp_fine_lower (by norm_num : (0 : ℝ) < 2 ^ 7)
  have hlt : (m : ℝ) < 2 ^ 7 * (10079 / 10000) := by linarith
  have hgt : (2 : ℝ) ^ 7 * (9922 / 10000) < m := by linarith
  norm_num at hlt hgt
  have h1 : m < 130 := by exact_mod_cast (show (m : ℝ) < 130 by linarith)
  have h2 : 127 < m := by exact_mod_cast (show (127 : ℝ) < m by linarith)
  interval_cases m
  · right; rfl
  · left; vm0 3 43

theorem fwin8 {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - ((8 : ℕ) : ℝ) * Real.log 2| ≤ 1 / 128) :
    ArithmeticFunction.vonMangoldt m = 0 ∨ m = 256 ∨ m = 257 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := abs_le.mp hwin
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ ((8 : ℕ) : ℝ) * Real.log 2 + 1 / 128 by linarith [habs.2])
  have hlo := Real.exp_le_exp.mpr
    (show ((8 : ℕ) : ℝ) * Real.log 2 - 1 / 128 ≤ Real.log (m : ℝ) by linarith [habs.1])
  have h2k : Real.exp (((8 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ 8 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, h2k] at hup
  rw [sub_eq_add_neg, Real.exp_add, h2k] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have e1 := mul_lt_mul_of_pos_left exp_fine_upper (by norm_num : (0 : ℝ) < 2 ^ 8)
  have e2 := mul_lt_mul_of_pos_left exp_fine_lower (by norm_num : (0 : ℝ) < 2 ^ 8)
  have hlt : (m : ℝ) < 2 ^ 8 * (10079 / 10000) := by linarith
  have hgt : (2 : ℝ) ^ 8 * (9922 / 10000) < m := by linarith
  norm_num at hlt hgt
  have h1 : m < 259 := by exact_mod_cast (show (m : ℝ) < 259 by linarith)
  have h2 : 254 < m := by exact_mod_cast (show (254 : ℝ) < m by linarith)
  interval_cases m
  · left; vm0 3 5
  · right; left; rfl
  · right; right; rfl
  · left; vm0 2 3

theorem fwin9 {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - ((9 : ℕ) : ℝ) * Real.log 2| ≤ 1 / 128) :
    ArithmeticFunction.vonMangoldt m = 0 ∨ m = 509 ∨ m = 512 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := abs_le.mp hwin
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ ((9 : ℕ) : ℝ) * Real.log 2 + 1 / 128 by linarith [habs.2])
  have hlo := Real.exp_le_exp.mpr
    (show ((9 : ℕ) : ℝ) * Real.log 2 - 1 / 128 ≤ Real.log (m : ℝ) by linarith [habs.1])
  have h2k : Real.exp (((9 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ 9 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, h2k] at hup
  rw [sub_eq_add_neg, Real.exp_add, h2k] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have e1 := mul_lt_mul_of_pos_left exp_fine_upper (by norm_num : (0 : ℝ) < 2 ^ 9)
  have e2 := mul_lt_mul_of_pos_left exp_fine_lower (by norm_num : (0 : ℝ) < 2 ^ 9)
  have hlt : (m : ℝ) < 2 ^ 9 * (10079 / 10000) := by linarith
  have hgt : (2 : ℝ) ^ 9 * (9922 / 10000) < m := by linarith
  norm_num at hlt hgt
  have h1 : m < 517 := by exact_mod_cast (show (m : ℝ) < 517 by linarith)
  have h2 : 508 < m := by exact_mod_cast (show (508 : ℝ) < m by linarith)
  interval_cases m
  · right; left; rfl
  · left; vm0 2 3
  · left; vm0 7 73
  · right; right; rfl
  · left; vm0 3 19
  · left; vm0 2 257
  · left; vm0 5 103
  · left; vm0 2 3

theorem fwin10 {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - ((10 : ℕ) : ℝ) * Real.log 2| ≤ 1 / 128) :
    ArithmeticFunction.vonMangoldt m = 0 ∨ m = 1019 ∨ m = 1021 ∨ m = 1024 ∨ m = 1031 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := abs_le.mp hwin
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ ((10 : ℕ) : ℝ) * Real.log 2 + 1 / 128 by linarith [habs.2])
  have hlo := Real.exp_le_exp.mpr
    (show ((10 : ℕ) : ℝ) * Real.log 2 - 1 / 128 ≤ Real.log (m : ℝ) by linarith [habs.1])
  have h2k : Real.exp (((10 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ 10 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, h2k] at hup
  rw [sub_eq_add_neg, Real.exp_add, h2k] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have e1 := mul_lt_mul_of_pos_left exp_fine_upper (by norm_num : (0 : ℝ) < 2 ^ 10)
  have e2 := mul_lt_mul_of_pos_left exp_fine_lower (by norm_num : (0 : ℝ) < 2 ^ 10)
  have hlt : (m : ℝ) < 2 ^ 10 * (10079 / 10000) := by linarith
  have hgt : (2 : ℝ) ^ 10 * (9922 / 10000) < m := by linarith
  norm_num at hlt hgt
  have h1 : m < 1033 := by exact_mod_cast (show (m : ℝ) < 1033 by linarith)
  have h2 : 1016 < m := by exact_mod_cast (show (1016 : ℝ) < m by linarith)
  interval_cases m
  · left; vm0 3 113
  · left; vm0 2 509
  · right; left; rfl
  · left; vm0 2 3
  · right; right; left; rfl
  · left; vm0 2 7
  · left; vm0 3 11
  · right; right; right; left; rfl
  · left; vm0 5 41
  · left; vm0 2 3
  · left; vm0 13 79
  · left; vm0 2 257
  · left; vm0 3 7
  · left; vm0 2 5
  · right; right; right; right; rfl
  · left; vm0 2 3

theorem fwin11 {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - ((11 : ℕ) : ℝ) * Real.log 2| ≤ 1 / 128) :
    ArithmeticFunction.vonMangoldt m = 0 ∨ m = 2039 ∨ m = 2048 ∨ m = 2053 ∨ m = 2063 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := abs_le.mp hwin
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ ((11 : ℕ) : ℝ) * Real.log 2 + 1 / 128 by linarith [habs.2])
  have hlo := Real.exp_le_exp.mpr
    (show ((11 : ℕ) : ℝ) * Real.log 2 - 1 / 128 ≤ Real.log (m : ℝ) by linarith [habs.1])
  have h2k : Real.exp (((11 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ 11 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, h2k] at hup
  rw [sub_eq_add_neg, Real.exp_add, h2k] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have e1 := mul_lt_mul_of_pos_left exp_fine_upper (by norm_num : (0 : ℝ) < 2 ^ 11)
  have e2 := mul_lt_mul_of_pos_left exp_fine_lower (by norm_num : (0 : ℝ) < 2 ^ 11)
  have hlt : (m : ℝ) < 2 ^ 11 * (10079 / 10000) := by linarith
  have hgt : (2 : ℝ) ^ 11 * (9922 / 10000) < m := by linarith
  norm_num at hlt hgt
  have h1 : m < 2065 := by exact_mod_cast (show (m : ℝ) < 2065 by linarith)
  have h2 : 2032 < m := by exact_mod_cast (show (2032 : ℝ) < m by linarith)
  interval_cases m
  · left; vm0 19 107
  · left; vm0 2 3
  · left; vm0 5 11
  · left; vm0 2 509
  · left; vm0 3 7
  · left; vm0 2 1019
  · right; left; rfl
  · left; vm0 2 3
  · left; vm0 13 157
  · left; vm0 2 1021
  · left; vm0 3 227
  · left; vm0 2 7
  · left; vm0 5 409
  · left; vm0 2 3
  · left; vm0 23 89
  · right; right; left; rfl
  · left; vm0 3 683
  · left; vm0 2 5
  · left; vm0 7 293
  · left; vm0 2 3
  · right; right; right; left; rfl
  · left; vm0 2 13
  · left; vm0 3 5
  · left; vm0 2 257
  · left; vm0 11 17
  · left; vm0 2 3
  · left; vm0 29 71
  · left; vm0 2 5
  · left; vm0 3 229
  · left; vm0 2 1031
  · right; right; right; right; rfl
  · left; vm0 2 3

theorem fwin12 {m : ℕ} (hm : 0 < m)
    (hwin : |Real.log (m : ℝ) - ((12 : ℕ) : ℝ) * Real.log 2| ≤ 1 / 128) :
    ArithmeticFunction.vonMangoldt m = 0 ∨ m = 4073 ∨ m = 4079 ∨ m = 4091 ∨ m = 4093 ∨ m = 4096 ∨ m = 4099 ∨ m = 4111 ∨ m = 4127 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have habs := abs_le.mp hwin
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ ((12 : ℕ) : ℝ) * Real.log 2 + 1 / 128 by linarith [habs.2])
  have hlo := Real.exp_le_exp.mpr
    (show ((12 : ℕ) : ℝ) * Real.log 2 - 1 / 128 ≤ Real.log (m : ℝ) by linarith [habs.1])
  have h2k : Real.exp (((12 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ 12 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.exp_add, h2k] at hup
  rw [sub_eq_add_neg, Real.exp_add, h2k] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have e1 := mul_lt_mul_of_pos_left exp_fine_upper (by norm_num : (0 : ℝ) < 2 ^ 12)
  have e2 := mul_lt_mul_of_pos_left exp_fine_lower (by norm_num : (0 : ℝ) < 2 ^ 12)
  have hlt : (m : ℝ) < 2 ^ 12 * (10079 / 10000) := by linarith
  have hgt : (2 : ℝ) ^ 12 * (9922 / 10000) < m := by linarith
  norm_num at hlt hgt
  have h1 : m < 4129 := by exact_mod_cast (show (m : ℝ) < 4129 by linarith)
  have h2 : 4064 < m := by exact_mod_cast (show (4064 : ℝ) < m by linarith)
  interval_cases m
  · left; vm0 3 5
  · left; vm0 2 19
  · left; vm0 7 83
  · left; vm0 2 3
  · left; vm0 13 313
  · left; vm0 2 5
  · left; vm0 3 23
  · left; vm0 2 509
  · right; left; rfl
  · left; vm0 2 3
  · left; vm0 5 163
  · left; vm0 2 1019
  · left; vm0 3 151
  · left; vm0 2 2039
  · right; right; left; rfl
  · left; vm0 2 3
  · left; vm0 7 11
  · left; vm0 2 13
  · left; vm0 3 1361
  · left; vm0 2 1021
  · left; vm0 5 19
  · left; vm0 2 3
  · left; vm0 61 67
  · left; vm0 2 7
  · left; vm0 3 29
  · left; vm0 2 5
  · right; right; right; left; rfl
  · left; vm0 2 3
  · right; right; right; right; left; rfl
  · left; vm0 2 23
  · left; vm0 3 5
  · right; right; right; right; right; left; rfl
  · left; vm0 17 241
  · left; vm0 2 3
  · right; right; right; right; right; right; left; rfl
  · left; vm0 2 5
  · left; vm0 3 1367
  · left; vm0 2 7
  · left; vm0 11 373
  · left; vm0 2 3
  · left; vm0 5 821
  · left; vm0 2 2053
  · left; vm0 3 37
  · left; vm0 2 13
  · left; vm0 7 587
  · left; vm0 2 3
  · right; right; right; right; right; right; right; left; rfl
  · left; vm0 2 257
  · left; vm0 3 457
  · left; vm0 2 11
  · left; vm0 5 823
  · left; vm0 2 3
  · left; vm0 23 179
  · left; vm0 2 29
  · left; vm0 3 1373
  · left; vm0 2 5
  · left; vm0 13 317
  · left; vm0 2 3
  · left; vm0 7 19
  · left; vm0 2 1031
  · left; vm0 3 5
  · left; vm0 2 2063
  · right; right; right; right; right; right; right; right; rfl
  · left; vm0 2 3

theorem fps1 (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hpf : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hqf : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    {i j : ℕ} (hij : i < j) (hk : j - i = 1) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      (24507 / 50000) * ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
  have hS := S_nonneg p q α β hα hβ
  set S := (β / α * energy p.1 + α / β * energy q.1) / 2 with hSdef
  rw [tsum_fine_eq p q a hpf hqf hij 1 hk ({1} : Finset ℕ) (fun n hwin => by
      rcases fwin1 (by omega) hwin with h | h
      · right; exact h
      · left; simp; omega)]
  set T := WeilPrimeTermV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))) with hT
  rw [Finset.sum_singleton]
  have t0 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 1 α β hα hβ
  rw [← hSdef, ← hT] at t0
  have m0 := mul_le_mul_of_nonneg_right (fmass_pow2 1 1 (by norm_num) (by norm_num) (70711 / 100000)
    (122533 / 250000) (by norm_num) (by norm_num) (by norm_num)) hS
  linarith

theorem fps2 (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hpf : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hqf : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    {i j : ℕ} (hij : i < j) (hk : j - i = 2) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      (17329 / 50000) * ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
  have hS := S_nonneg p q α β hα hβ
  set S := (β / α * energy p.1 + α / β * energy q.1) / 2 with hSdef
  rw [tsum_fine_eq p q a hpf hqf hij 2 hk ({3} : Finset ℕ) (fun n hwin => by
      rcases fwin2 (by omega) hwin with h | h
      · right; exact h
      · left; simp; omega)]
  set T := WeilPrimeTermV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))) with hT
  rw [Finset.sum_singleton]
  have t0 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 3 α β hα hβ
  rw [← hSdef, ← hT] at t0
  have m0 := mul_le_mul_of_nonneg_right (fmass_pow2 2 3 (by norm_num) (by norm_num) (1 / 2)
    (173287 / 500000) (by norm_num) (by norm_num) (by norm_num)) hS
  linarith

theorem fps3 (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hpf : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hqf : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    {i j : ℕ} (hij : i < j) (hk : j - i = 3) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      (6127 / 25000) * ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
  have hS := S_nonneg p q α β hα hβ
  set S := (β / α * energy p.1 + α / β * energy q.1) / 2 with hSdef
  rw [tsum_fine_eq p q a hpf hqf hij 3 hk ({7} : Finset ℕ) (fun n hwin => by
      rcases fwin3 (by omega) hwin with h | h
      · right; exact h
      · left; simp; omega)]
  set T := WeilPrimeTermV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))) with hT
  rw [Finset.sum_singleton]
  have t0 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 7 α β hα hβ
  rw [← hSdef, ← hT] at t0
  have m0 := mul_le_mul_of_nonneg_right (fmass_pow2 3 7 (by norm_num) (by norm_num) (8839 / 25000)
    (24507 / 100000) (by norm_num) (by norm_num) (by norm_num)) hS
  linarith

theorem fps4 (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hpf : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hqf : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    {i j : ℕ} (hij : i < j) (hk : j - i = 4) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      (17329 / 100000) * ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
  have hS := S_nonneg p q α β hα hβ
  set S := (β / α * energy p.1 + α / β * energy q.1) / 2 with hSdef
  rw [tsum_fine_eq p q a hpf hqf hij 4 hk ({15} : Finset ℕ) (fun n hwin => by
      rcases fwin4 (by omega) hwin with h | h
      · right; exact h
      · left; simp; omega)]
  set T := WeilPrimeTermV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))) with hT
  rw [Finset.sum_singleton]
  have t0 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 15 α β hα hβ
  rw [← hSdef, ← hT] at t0
  have m0 := mul_le_mul_of_nonneg_right (fmass_pow2 4 15 (by norm_num) (by norm_num) (1 / 4)
    (173287 / 1000000) (by norm_num) (by norm_num) (by norm_num)) hS
  linarith

theorem fps5 (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hpf : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hqf : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    {i j : ℕ} (hij : i < j) (hk : j - i = 5) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      (6127 / 50000) * ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
  have hS := S_nonneg p q α β hα hβ
  set S := (β / α * energy p.1 + α / β * energy q.1) / 2 with hSdef
  rw [tsum_fine_eq p q a hpf hqf hij 5 hk ({31} : Finset ℕ) (fun n hwin => by
      rcases fwin5 (by omega) hwin with h | h
      · right; exact h
      · left; simp; omega)]
  set T := WeilPrimeTermV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))) with hT
  rw [Finset.sum_singleton]
  have t0 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 31 α β hα hβ
  rw [← hSdef, ← hT] at t0
  have m0 := mul_le_mul_of_nonneg_right (fmass_pow2 5 31 (by norm_num) (by norm_num) (8839 / 50000)
    (24507 / 200000) (by norm_num) (by norm_num) (by norm_num)) hS
  linarith

theorem fps6 (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hpf : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hqf : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    {i j : ℕ} (hij : i < j) (hk : j - i = 6) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      (1733 / 20000) * ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
  have hS := S_nonneg p q α β hα hβ
  set S := (β / α * energy p.1 + α / β * energy q.1) / 2 with hSdef
  rw [tsum_fine_eq p q a hpf hqf hij 6 hk ({63} : Finset ℕ) (fun n hwin => by
      rcases fwin6 (by omega) hwin with h | h
      · right; exact h
      · left; simp; omega)]
  set T := WeilPrimeTermV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))) with hT
  rw [Finset.sum_singleton]
  have t0 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 63 α β hα hβ
  rw [← hSdef, ← hT] at t0
  have m0 := mul_le_mul_of_nonneg_right (fmass_pow2 6 63 (by norm_num) (by norm_num) (1 / 8)
    (21661 / 250000) (by norm_num) (by norm_num) (by norm_num)) hS
  linarith

theorem fps7 (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hpf : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hqf : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    {i j : ℕ} (hij : i < j) (hk : j - i = 7) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      (6127 / 100000) * ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
  have hS := S_nonneg p q α β hα hβ
  set S := (β / α * energy p.1 + α / β * energy q.1) / 2 with hSdef
  rw [tsum_fine_eq p q a hpf hqf hij 7 hk ({127} : Finset ℕ) (fun n hwin => by
      rcases fwin7 (by omega) hwin with h | h
      · right; exact h
      · left; simp; omega)]
  set T := WeilPrimeTermV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))) with hT
  rw [Finset.sum_singleton]
  have t0 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 127 α β hα hβ
  rw [← hSdef, ← hT] at t0
  have m0 := mul_le_mul_of_nonneg_right (fmass_pow2 7 127 (by norm_num) (by norm_num) (8839 / 100000)
    (15317 / 250000) (by norm_num) (by norm_num) (by norm_num)) hS
  linarith

theorem fps8 (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hpf : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hqf : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    {i j : ℕ} (hij : i < j) (hk : j - i = 8) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      (9737 / 25000) * ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
  have hS := S_nonneg p q α β hα hβ
  set S := (β / α * energy p.1 + α / β * energy q.1) / 2 with hSdef
  rw [tsum_fine_eq p q a hpf hqf hij 8 hk ({255, 256} : Finset ℕ) (fun n hwin => by
      rcases fwin8 (by omega) hwin with h | h | h
      · right; exact h
      · left; simp; omega
      · left; simp; omega)]
  set T := WeilPrimeTermV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))) with hT
  have hs : (∑ n ∈ ({255, 256} : Finset ℕ), T n) = T 255 + T 256 := by
    rw [Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [hs]
  have t0 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 255 α β hα hβ
  have t1 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 256 α β hα hβ
  rw [← hSdef, ← hT] at t0 t1
  have m0 := mul_le_mul_of_nonneg_right (fmass_pow2 8 255 (by norm_num) (by norm_num) (1 / 16)
    (21661 / 500000) (by norm_num) (by norm_num) (by norm_num)) hS
  have m1 := mul_le_mul_of_nonneg_right (fmass_prime 8 256 (by norm_num) (13872709241 / 2500000000)
    (3119 / 50000) (43269 / 125000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hS
  have n0 := norm_add_le (T 255) (T 256)
  linarith

theorem fps9 (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hpf : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hqf : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    {i j : ℕ} (hij : i < j) (hk : j - i = 9) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      (30693 / 100000) * ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
  have hS := S_nonneg p q α β hα hβ
  set S := (β / α * energy p.1 + α / β * energy q.1) / 2 with hSdef
  rw [tsum_fine_eq p q a hpf hqf hij 9 hk ({508, 511} : Finset ℕ) (fun n hwin => by
      rcases fwin9 (by omega) hwin with h | h | h
      · right; exact h
      · left; simp; omega
      · left; simp; omega)]
  set T := WeilPrimeTermV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))) with hT
  have hs : (∑ n ∈ ({508, 511} : Finset ℕ), T n) = T 508 + T 511 := by
    rw [Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [hs]
  have t0 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 508 α β hα hβ
  have t1 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 511 α β hα hβ
  rw [← hSdef, ← hT] at t0 t1
  have m0 := mul_le_mul_of_nonneg_right (fmass_prime 9 508 (by norm_num) (31162326261 / 5000000000)
    (4433 / 100000) (138143 / 500000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hS
  have m1 := mul_le_mul_of_nonneg_right (fmass_pow2 9 511 (by norm_num) (by norm_num) (221 / 5000)
    (15319 / 500000) (by norm_num) (by norm_num) (by norm_num)) hS
  have n0 := norm_add_le (T 508) (T 511)
  linarith

theorem fps10 (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hpf : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hqf : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    {i j : ℕ} (hij : i < j) (hk : j - i = 10) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      (67167 / 100000) * ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
  have hS := S_nonneg p q α β hα hβ
  set S := (β / α * energy p.1 + α / β * energy q.1) / 2 with hSdef
  rw [tsum_fine_eq p q a hpf hqf hij 10 hk ({1018, 1020, 1023, 1030} : Finset ℕ) (fun n hwin => by
      rcases fwin10 (by omega) hwin with h | h | h | h | h
      · right; exact h
      · left; simp; omega
      · left; simp; omega
      · left; simp; omega
      · left; simp; omega)]
  set T := WeilPrimeTermV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))) with hT
  have hs : (∑ n ∈ ({1018, 1020, 1023, 1030} : Finset ℕ), T n) = T 1018 + (T 1020 + (T 1023 + T 1030)) := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [hs]
  have t0 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 1018 α β hα hβ
  have t1 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 1020 α β hα hβ
  have t2 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 1023 α β hα hβ
  have t3 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 1030 α β hα hβ
  rw [← hSdef, ← hT] at t0 t1 t2 t3
  have m0 := mul_le_mul_of_nonneg_right (fmass_prime 10 1018 (by norm_num) (13853177991 / 2000000000)
    (3133 / 100000) (217011 / 1000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hS
  have m1 := mul_le_mul_of_nonneg_right (fmass_prime 10 1020 (by norm_num) (13857084241 / 2000000000)
    (313 / 10000) (6777 / 31250) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hS
  have m2 := mul_le_mul_of_nonneg_right (fmass_pow2 10 1023 (by norm_num) (by norm_num) (1 / 32)
    (21661 / 1000000) (by norm_num) (by norm_num) (by norm_num)) hS
  have m3 := mul_le_mul_of_nonneg_right (fmass_prime 10 1030 (by norm_num) (13876615491 / 2000000000)
    (623 / 20000) (216129 / 1000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hS
  have n2 := norm_add_le (T 1023) (T 1030)
  have n1 := norm_add_le (T 1020) (T 1023 + T 1030)
  have n0 := norm_add_le (T 1018) (T 1020 + (T 1023 + T 1030))
  linarith

theorem fps11 (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hpf : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hqf : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    {i j : ℕ} (hij : i < j) (hk : j - i = 11) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      (52057 / 100000) * ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
  have hS := S_nonneg p q α β hα hβ
  set S := (β / α * energy p.1 + α / β * energy q.1) / 2 with hSdef
  rw [tsum_fine_eq p q a hpf hqf hij 11 hk ({2038, 2047, 2052, 2062} : Finset ℕ) (fun n hwin => by
      rcases fwin11 (by omega) hwin with h | h | h | h | h
      · right; exact h
      · left; simp; omega
      · left; simp; omega
      · left; simp; omega
      · left; simp; omega)]
  set T := WeilPrimeTermV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))) with hT
  have hs : (∑ n ∈ ({2038, 2047, 2052, 2062} : Finset ℕ), T n) = T 2038 + (T 2047 + (T 2052 + T 2062)) := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [hs]
  have t0 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 2038 α β hα hβ
  have t1 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 2047 α β hα hβ
  have t2 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 2052 α β hα hβ
  have t3 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 2062 α β hα hβ
  rw [← hSdef, ← hT] at t0 t1 t2 t3
  have m0 := mul_le_mul_of_nonneg_right (fmass_prime 11 2038 (by norm_num) (152404489151 / 20000000000)
    (443 / 20000) (42197 / 250000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hS
  have m1 := mul_le_mul_of_nonneg_right (fmass_pow2 11 2047 (by norm_num) (by norm_num) (221 / 10000)
    (15319 / 1000000) (by norm_num) (by norm_num) (by norm_num)) hS
  have m2 := mul_le_mul_of_nonneg_right (fmass_prime 11 2052 (by norm_num) (152541207901 / 20000000000)
    (69 / 3125) (84203 / 500000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hS
  have m3 := mul_le_mul_of_nonneg_right (fmass_prime 11 2062 (by norm_num) (152638864151 / 20000000000)
    (1101 / 50000) (21007 / 125000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hS
  have n2 := norm_add_le (T 2052) (T 2062)
  have n1 := norm_add_le (T 2047) (T 2052 + T 2062)
  have n0 := norm_add_le (T 2038) (T 2047 + (T 2052 + T 2062))
  linarith

theorem fps12 (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hpf : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hqf : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    {i j : ℕ} (hij : i < j) (hk : j - i = 12) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      (92081 / 100000) * ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
  have hS := S_nonneg p q α β hα hβ
  set S := (β / α * energy p.1 + α / β * energy q.1) / 2 with hSdef
  rw [tsum_fine_eq p q a hpf hqf hij 12 hk ({4072, 4078, 4090, 4092, 4095, 4098, 4110, 4126} : Finset ℕ) (fun n hwin => by
      rcases fwin12 (by omega) hwin with h | h | h | h | h | h | h | h | h
      · right; exact h
      · left; simp; omega
      · left; simp; omega
      · left; simp; omega
      · left; simp; omega
      · left; simp; omega
      · left; simp; omega
      · left; simp; omega
      · left; simp; omega)]
  set T := WeilPrimeTermV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))) with hT
  have hs : (∑ n ∈ ({4072, 4078, 4090, 4092, 4095, 4098, 4110, 4126} : Finset ℕ), T n) = T 4072 + (T 4078 + (T 4090 + (T 4092 + (T 4095 + (T 4098 + (T 4110 + T 4126)))))) := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [hs]
  have t0 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 4072 α β hα hβ
  have t1 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 4078 α β hα hβ
  have t2 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 4090 α β hα hβ
  have t3 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 4092 α β hα hβ
  have t4 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 4095 α β hα hβ
  have t5 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 4098 α β hα hβ
  have t6 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 4110 α β hα hβ
  have t7 := term_norm_le2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 4126 α β hα hβ
  rw [← hSdef, ← hT] at t0 t1 t2 t3 t4 t5 t6 t7
  have m0 := mul_le_mul_of_nonneg_right (fmass_prime 12 4072 (by norm_num) (332486037409 / 40000000000)
    (1567 / 100000) (32563 / 250000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hS
  have m1 := mul_le_mul_of_nonneg_right (fmass_prime 12 4078 (by norm_num) (332544631159 / 40000000000)
    (783 / 50000) (8137 / 62500) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hS
  have m2 := mul_le_mul_of_nonneg_right (fmass_prime 12 4090 (by norm_num) (332661818659 / 40000000000)
    (391 / 25000) (130071 / 1000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hS
  have m3 := mul_le_mul_of_nonneg_right (fmass_prime 12 4092 (by norm_num) (332681349909 / 40000000000)
    (391 / 25000) (130079 / 1000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hS
  have m4 := mul_le_mul_of_nonneg_right (fmass_pow2 12 4095 (by norm_num) (by norm_num) (1563 / 100000)
    (5417 / 500000) (by norm_num) (by norm_num) (by norm_num)) hS
  have m5 := mul_le_mul_of_nonneg_right (fmass_prime 12 4098 (by norm_num) (332739943659 / 40000000000)
    (781 / 50000) (25987 / 200000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hS
  have m6 := mul_le_mul_of_nonneg_right (fmass_prime 12 4110 (by norm_num) (332857131159 / 40000000000)
    (39 / 2500) (25963 / 200000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hS
  have m7 := mul_le_mul_of_nonneg_right (fmass_prime 12 4126 (by norm_num) (333013381159 / 40000000000)
    (1557 / 100000) (64813 / 500000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hS
  have n6 := norm_add_le (T 4110) (T 4126)
  have n5 := norm_add_le (T 4098) (T 4110 + T 4126)
  have n4 := norm_add_le (T 4095) (T 4098 + (T 4110 + T 4126))
  have n3 := norm_add_le (T 4092) (T 4095 + (T 4098 + (T 4110 + T 4126)))
  have n2 := norm_add_le (T 4090) (T 4092 + (T 4095 + (T 4098 + (T 4110 + T 4126))))
  have n1 := norm_add_le (T 4078) (T 4090 + (T 4092 + (T 4095 + (T 4098 + (T 4110 + T 4126)))))
  have n0 := norm_add_le (T 4072) (T 4078 + (T 4090 + (T 4092 + (T 4095 + (T 4098 + (T 4110 + T 4126))))))
  linarith

/-- Prime ceilings at gaps `1, …, 12`. -/
def pbar13 : ℕ → ℝ
  | 1 => 24507 / 50000
  | 2 => 17329 / 50000
  | 3 => 6127 / 25000
  | 4 => 17329 / 100000
  | 5 => 6127 / 50000
  | 6 => 1733 / 20000
  | 7 => 6127 / 100000
  | 8 => 9737 / 25000
  | 9 => 30693 / 100000
  | 10 => 67167 / 100000
  | 11 => 52057 / 100000
  | 12 => 92081 / 100000
  | _ => 0

theorem fine_cross (p q : WeilCompactSmoothGV1) (a : ℝ)
    (hpf : LogSupportIn p (a - 1 / 256) (a + 1 / 256)) (hqf : LogSupportIn q (a - 1 / 256) (a + 1 / 256))
    (hmp : WeilMomentConditionsV1 p) {i j : ℕ} (hij : i < j) (hk : j - i ≤ 12) (α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β) :
    ‖B (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))‖ ≤
      pbar13 (j - i) * ((β / α * energy p.1 + α / β * energy q.1) / 2) +
        (1 / 400 : ℝ) * (energy p.1 + energy q.1) := by
  have hzero : mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)) 1 = 0 := by
    simpa using mixed_nat_zero2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
      (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hij 1 one_pos
  have harch := arch2 p q a (AEGIS.WeilFineDiagonalQuadV1.fine_retained p a hpf)
    (AEGIS.WeilFineDiagonalQuadV1.fine_retained q a hqf) hmp hij
  have hprime : ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      pbar13 (j - i) * ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
    rcases (show j - i = 1 ∨ j - i = 2 ∨ j - i = 3 ∨ j - i = 4 ∨ j - i = 5 ∨ j - i = 6 ∨ j - i = 7 ∨ j - i = 8 ∨ j - i = 9 ∨ j - i = 10 ∨ j - i = 11 ∨ j - i = 12 by omega) with h | h | h | h | h | h | h | h | h | h | h | h
    · rw [h]
      simp only [pbar13]
      exact fps1 p q a hpf hqf hij h α β hα hβ
    · rw [h]
      simp only [pbar13]
      exact fps2 p q a hpf hqf hij h α β hα hβ
    · rw [h]
      simp only [pbar13]
      exact fps3 p q a hpf hqf hij h α β hα hβ
    · rw [h]
      simp only [pbar13]
      exact fps4 p q a hpf hqf hij h α β hα hβ
    · rw [h]
      simp only [pbar13]
      exact fps5 p q a hpf hqf hij h α β hα hβ
    · rw [h]
      simp only [pbar13]
      exact fps6 p q a hpf hqf hij h α β hα hβ
    · rw [h]
      simp only [pbar13]
      exact fps7 p q a hpf hqf hij h α β hα hβ
    · rw [h]
      simp only [pbar13]
      exact fps8 p q a hpf hqf hij h α β hα hβ
    · rw [h]
      simp only [pbar13]
      exact fps9 p q a hpf hqf hij h α β hα hβ
    · rw [h]
      simp only [pbar13]
      exact fps10 p q a hpf hqf hij h α β hα hβ
    · rw [h]
      simp only [pbar13]
      exact fps11 p q a hpf hqf hij h α β hα hβ
    · rw [h]
      simp only [pbar13]
      exact fps12 p q a hpf hqf hij h α β hα hβ
  unfold B WeilExplicitRightSideV1
  rw [hzero, mul_zero, add_zero]
  calc ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))) + WeilArchimedeanIntegralV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖
      ≤ ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖ + ‖WeilArchimedeanIntegralV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)))‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hprime harch

theorem fine_diag (p : WeilCompactSmoothGV1) (a : ℝ) (hpf : LogSupportIn p (a - 1 / 256) (a + 1 / 256))
    (hmp : WeilMomentConditionsV1 p) (d : ℝ) :
    (B (translatePacket p d) (translatePacket p d)).re ≤ -((43 / 10 : ℝ) * energy p.1) := by
  have hf' : LogSupportIn (translatePacket p d) (a + d - 1 / 256) (a + d + 1 / 256) := by
    have h := translate_logSupportIn p d _ _ hpf
    convert h using 1 <;> ring
  have h := AEGIS.WeilFineDiagonalQuadV1.fine_diagonal_43_over_10 (translatePacket p d) (a + d) hf'
    (translate_preserves_moments p d hmp)
  rw [translate_energy] at h
  linarith

/-- Schur weights. -/
def wv13 : ℕ → ℝ
  | 0 => 1
  | 1 => 112 / 125
  | 2 => 423 / 500
  | 3 => 143 / 200
  | 4 => 329 / 500
  | 5 => 571 / 1000
  | 6 => 569 / 1000
  | 7 => 571 / 1000
  | 8 => 329 / 500
  | 9 => 143 / 200
  | 10 => 423 / 500
  | 11 => 112 / 125
  | _ => 1

theorem wv13_pos (n : ℕ) : 0 < wv13 n := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> simp [wv13]

/-- The translated family. -/
def tp13 (g : Fin 13 → WeilCompactSmoothGV1) (j : Fin 13) : WeilCompactSmoothGV1 :=
  translatePacket (g j) (((j : ℕ) : ℝ) * Real.log 2)

theorem sum_fin13 (f : Fin 13 → ℝ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc,
    Fin.sum_univ_castSucc, Fin.sum_univ_eight]
  rfl

theorem hterm13 (g : Fin 13 → WeilCompactSmoothGV1) (a : ℝ)
    (hpf : ∀ j, LogSupportIn (g j) (a - 1 / 256) (a + 1 / 256)) (hm : ∀ j, WeilMomentConditionsV1 (g j))
    (i j : Fin 13) :
    (B (tp13 g i) (tp13 g j)).re ≤
      if Nat.dist i j = 0 then -((43 / 10 : ℝ) * energy (g i).1) else
        pbar13 (Nat.dist i j) *
          ((wv13 j / wv13 i * energy (g i).1 + wv13 i / wv13 j * energy (g j).1) / 2) +
        (1 / 400 : ℝ) * (energy (g i).1 + energy (g j).1) := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos (Nat.dist_self _)]
    exact fine_diag (g i) a (hpf i) (hm i) _
  · have hd : Nat.dist i j ≠ 0 := by
      intro h
      apply hij
      apply Fin.ext
      unfold Nat.dist at h
      omega
    rw [if_neg hd]
    refine (Complex.re_le_norm _).trans ?_
    rcases lt_or_gt_of_ne (fun h : (i : ℕ) = j => hij (Fin.ext h)) with h | h
    · have hdist : Nat.dist i j = j - i := by unfold Nat.dist; omega
      rw [hdist]
      exact fine_cross (g i) (g j) a (hpf i) (hpf j) (hm i) h (by omega) (wv13 i) (wv13 j) (wv13_pos _)
        (wv13_pos _)
    · have hdist : Nat.dist i j = i - j := by unfold Nat.dist; omega
      rw [hdist]
      unfold tp13
      rw [B_hermitian, Complex.norm_conj]
      have hc := fine_cross (g j) (g i) a (hpf j) (hpf i) (hm j) h (by omega) (wv13 j) (wv13 i)
        (wv13_pos _) (wv13_pos _)
      linarith

set_option maxHeartbeats 12800000 in
/-- **Thirteen independent atoms of log-width 1/128 on the dyadic lattice.** -/
theorem thirteen_atom_gram_bound (g : Fin 13 → WeilCompactSmoothGV1) (a : ℝ)
    (hpf : ∀ j, LogSupportIn (g j) (a - 1 / 256) (a + 1 / 256)) (hm : ∀ j, WeilMomentConditionsV1 (g j)) :
    (∑ i : Fin 13, ∑ j : Fin 13, B (tp13 g i) (tp13 g j)).re ≤
      -(3 / 5 : ℝ) * ∑ j : Fin 13, energy (g j).1 := by
  have hE : ∀ j, 0 ≤ energy (g j).1 := fun j => energy_nonnegative (g j).1
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  calc (∑ i : Fin 13, ∑ j : Fin 13, (B (tp13 g i) (tp13 g j)).re)
      ≤ ∑ i : Fin 13, ∑ j : Fin 13,
          (if Nat.dist i j = 0 then -((43 / 10 : ℝ) * energy (g i).1) else
            pbar13 (Nat.dist i j) *
              ((wv13 j / wv13 i * energy (g i).1 + wv13 i / wv13 j * energy (g j).1) / 2) +
            (1 / 400 : ℝ) * (energy (g i).1 + energy (g j).1)) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm13 g a hpf hm i j))
    _ ≤ -(3 / 5 : ℝ) * ∑ j : Fin 13, energy (g j).1 := by
        simp only [sum_fin13]
        norm_num [pbar13, wv13, Nat.dist]
        linarith [hE 0, hE 1, hE 2, hE 3, hE 4, hE 5, hE 6, hE 7, hE 8, hE 9, hE 10, hE 11, hE 12]

end AEGIS.WeilFineCombThirteenV1

#print axioms AEGIS.WeilFineCombThirteenV1.fwin12
#print axioms AEGIS.WeilFineCombThirteenV1.fine_cross
#print axioms AEGIS.WeilFineCombThirteenV1.thirteen_atom_gram_bound
