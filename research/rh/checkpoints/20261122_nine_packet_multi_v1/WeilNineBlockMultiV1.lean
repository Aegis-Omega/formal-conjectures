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

import WeilNineBlockCombV1

/-!
AEGIS Ω — nine independent packets on the dyadic lattice at width 1/32 (Claude Lab, 2026-11-22).

`WeilNineBlockCombV1` treats `Σ z_j T_{j log 2} g` for one packet `g`. Here the nine blocks carry nine
independent packets: `f_j = T_{j log 2} g_j`, `j = 0, …, 8`, where every `g_j` has log-support in
`[a − 1/64, a + 1/64]` (one common `a`) and both moments. The comb is the special case `g_j = z_j g`.

What changes for two different packets `p, q`:
* `logCross (T_{d₁} p) (T_{d₂} q) u = logCross p q (u + d₂ − d₁)` (`logCross_translate2`), and `logCross p q`
  vanishes for `|u| > 1/32` (`logCross_zero2`). So the prime windows are the same as for the comb.
* At the centre the value is no longer the energy. Every prime term is bounded through the weighted
  Cauchy–Schwarz inequality `‖logCross p q s‖ ≤ ((β/α) E(p) + (α/β) E(q))/2` (`cross_norm_le2`).
* The Archimedean cross term is `≤ (E(p) + E(q))/400` (V32, `logCross_l1_le_distinct`).

The weights of the Schur test enter through `α, β`: `wv = (1, 827/1000, 571/1000, 583/1000, 587/1000,
583/1000, 571/1000, 827/1000, 1)`. With the prime ceilings `cbar9 k − 1/200`, the coefficient of `E(g_i)` is at
most `−299/100 + 2.96911 < −1/50`.

Result (`nine_packet_gram_bound`): `Re Σ_{i,j} B(f_i, f_j) ≤ −(1/50) Σ_j E(g_j)`.

Dyadic multi-packet class at width 1/32 only. Not RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilNineBlockMultiV1

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
open AEGIS.WeilNineBlockCombV1

theorem tw2 (p : WeilCompactSmoothGV1) (a d : ℝ) (hw : WidthOneThirtyTwoAt p a) :
    WidthOneThirtyTwoAt (translatePacket p d) (a + d) := by
  have h := translate_logSupportIn p d _ _ hw
  change LogSupportIn (translatePacket p d) (a + d - 1 / 64) (a + d + 1 / 64)
  convert h using 1 <;> ring

theorem logCross_translate2 (p q : WeilCompactSmoothGV1) (d1 d2 u : ℝ) :
    logCrossV28 (translatePacket p d1) (translatePacket q d2) u = logCrossV28 p q (u + d2 - d1) := by
  unfold logCrossV28
  simp_rw [logLift_translate]
  let F : ℝ → ℂ := fun w => logLift p.1 (w + (u + d2 - d1)) * conj (logLift q.1 w)
  calc (∫ v : ℝ, logLift p.1 (v + u - d1) * conj (logLift q.1 (v - d2)))
      = ∫ v : ℝ, F (v + (-d2)) := by
        apply integral_congr_ae
        filter_upwards [] with v
        dsimp [F]
        rw [show v + -d2 + (u + d2 - d1) = v + u - d1 by ring, show v + -d2 = v - d2 by ring]
    _ = ∫ w : ℝ, F w := integral_add_right_eq_self F (-d2)
    _ = ∫ w : ℝ, logLift p.1 (w + (u + d2 - d1)) * conj (logLift q.1 w) := rfl

theorem logCross_zero2 (p q : WeilCompactSmoothGV1) (a u : ℝ) (hp : WidthOneThirtyTwoAt p a)
    (hq : WidthOneThirtyTwoAt q a) (hu : (1 / 32 : ℝ) < |u|) : logCrossV28 p q u = 0 := by
  unfold logCrossV28
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  by_cases h0 : logLift q.1 v = 0
  · simp [h0]
  · by_cases h1 : logLift p.1 (v + u) = 0
    · simp [h1]
    · have hv := hq (subset_tsupport _ h0)
      have hvu := hp (subset_tsupport _ h1)
      have habs : |u| ≤ (1 / 32 : ℝ) := by
        rw [abs_le]
        constructor <;> linarith [hv.1, hv.2, hvu.1, hvu.2]
      exact False.elim ((not_le_of_gt hu) habs)

theorem mixed_zero2 (p q : WeilCompactSmoothGV1) (a d1 d2 u : ℝ) (hp : WidthOneThirtyTwoAt p a)
    (hq : WidthOneThirtyTwoAt q a) (hu : (1 / 32 : ℝ) < |u + d2 - d1|) :
    mixed (translatePacket p d1) (translatePacket q d2) (Real.exp u) = 0 := by
  have h := logCross_eq_mixed_v28 (translatePacket p d1) (translatePacket q d2) u
  rw [logCross_translate2, logCross_zero2 p q a _ hp hq hu] at h
  have he : (Real.exp (u / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  exact (mul_eq_zero.mp h.symm).resolve_left he

/-- **Weighted Cauchy–Schwarz** for the cross correlation of two packets. -/
theorem cross_norm_le2 (p q : WeilCompactSmoothGV1) (s α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖logCrossV28 p q s‖ ≤ (β / α * energy p.1 + α / β * energy q.1) / 2 := by
  have I1 : Integrable (fun v => β / α * ‖logLift p.1 (v + s)‖ ^ 2) :=
    (shifted_logLift_sq_integrable_v25 p s).const_mul _
  have I2 : Integrable (fun v => α / β * ‖logLift q.1 v‖ ^ 2) := (logLift_sq_integrable_v25 q).const_mul _
  have I12 : Integrable (fun v => β / α * ‖logLift p.1 (v + s)‖ ^ 2 + α / β * ‖logLift q.1 v‖ ^ 2) :=
    I1.add I2
  have hM : Integrable (fun v => (β / α * ‖logLift p.1 (v + s)‖ ^ 2 + α / β * ‖logLift q.1 v‖ ^ 2) / 2) :=
    I12.div_const 2
  have hpt : ∀ v, ‖logLift p.1 (v + s) * conj (logLift q.1 v)‖ ≤
      (β / α * ‖logLift p.1 (v + s)‖ ^ 2 + α / β * ‖logLift q.1 v‖ ^ 2) / 2 := by
    intro v
    rw [norm_mul, Complex.norm_conj]
    set x := ‖logLift p.1 (v + s)‖
    set y := ‖logLift q.1 v‖
    have key : (β / α * x ^ 2 + α / β * y ^ 2) / 2 - x * y = (β * x - α * y) ^ 2 / (2 * α * β) := by
      field_simp
      ring
    have h0 : 0 ≤ (β * x - α * y) ^ 2 / (2 * α * β) := by positivity
    linarith
  have e1 : (∫ v, (β / α * ‖logLift p.1 (v + s)‖ ^ 2 + α / β * ‖logLift q.1 v‖ ^ 2) / 2) =
      (∫ v, (β / α * ‖logLift p.1 (v + s)‖ ^ 2 + α / β * ‖logLift q.1 v‖ ^ 2)) / 2 := integral_div _ _
  have e2 : (∫ v, (β / α * ‖logLift p.1 (v + s)‖ ^ 2 + α / β * ‖logLift q.1 v‖ ^ 2)) =
      (∫ v, β / α * ‖logLift p.1 (v + s)‖ ^ 2) + ∫ v, α / β * ‖logLift q.1 v‖ ^ 2 := integral_add I1 I2
  have e3 : (∫ v, β / α * ‖logLift p.1 (v + s)‖ ^ 2) = β / α * ∫ v, ‖logLift p.1 (v + s)‖ ^ 2 :=
    integral_const_mul _ _
  have e4 : (∫ v, α / β * ‖logLift q.1 v‖ ^ 2) = α / β * ∫ v, ‖logLift q.1 v‖ ^ 2 :=
    integral_const_mul _ _
  calc ‖logCrossV28 p q s‖ = ‖∫ v, logLift p.1 (v + s) * conj (logLift q.1 v)‖ := rfl
    _ ≤ ∫ v, (β / α * ‖logLift p.1 (v + s)‖ ^ 2 + α / β * ‖logLift q.1 v‖ ^ 2) / 2 :=
        norm_integral_le_of_norm_le hM (Filter.Eventually.of_forall hpt)
    _ = (β / α * energy p.1 + α / β * energy q.1) / 2 := by
        rw [e1, e2, e3, e4, shifted_logLift_sq_integral_v25, logLift_energy_eq_packet_energy]

theorem mixed_nat_zero2 (p q : WeilCompactSmoothGV1) (a : ℝ) (hp : WidthOneThirtyTwoAt p a)
    (hq : WidthOneThirtyTwoAt q a) {i j : ℕ} (hij : i < j) (m : ℕ) (hm : 0 < m) :
    mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2)) (m : ℝ) = 0 := by
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
  have hz := mixed_zero2 p q a ((i : ℝ) * Real.log 2) ((j : ℝ) * Real.log 2) (Real.log (m : ℝ)) hp hq hfar
  rw [Real.exp_log (by exact_mod_cast hm)] at hz
  exact hz

theorem mixed_inv_far2 (p q : WeilCompactSmoothGV1) (a : ℝ) (hp : WidthOneThirtyTwoAt p a)
    (hq : WidthOneThirtyTwoAt q a) {i j : ℕ} (hij : i < j) (m : ℕ) (hm : 0 < m)
    (hfar0 : (1 / 32 : ℝ) < |Real.log (m : ℝ) - ((j - i : ℕ) : ℝ) * Real.log 2|) :
    mixed (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))
      ((m : ℝ)⁻¹) = 0 := by
  have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - i := by rw [Nat.cast_sub hij.le]
  have harg : -Real.log (m : ℝ) + (j : ℝ) * Real.log 2 - (i : ℝ) * Real.log 2 =
      -(Real.log (m : ℝ) - ((j - i : ℕ) : ℝ) * Real.log 2) := by
    rw [hcast]
    ring
  have hfar : (1 / 32 : ℝ) < |-Real.log (m : ℝ) + (j : ℝ) * Real.log 2 - (i : ℝ) * Real.log 2| := by
    rw [harg, abs_neg]
    exact hfar0
  have hz := mixed_zero2 p q a ((i : ℝ) * Real.log 2) ((j : ℝ) * Real.log 2) (-Real.log (m : ℝ)) hp hq hfar
  rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hm)] at hz
  exact hz

/-- One prime term for two different packets. -/
theorem term_norm_le2 (p q : WeilCompactSmoothGV1) (a : ℝ) (hp : WidthOneThirtyTwoAt p a)
    (hq : WidthOneThirtyTwoAt q a) {i j : ℕ} (hij : i < j) (n : ℕ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖WeilPrimeTermV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2))
        (translatePacket q ((j : ℝ) * Real.log 2))) n‖ ≤
      ArithmeticFunction.vonMangoldt (n + 1) * Real.exp (-Real.log ((n + 1 : ℕ) : ℝ) / 2) *
        ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
  have hp0 := mixed_nat_zero2 p q a hp hq hij (n + 1) (by omega)
  have hmpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  set S := (β / α * energy p.1 + α / β * energy q.1) / 2 with hS
  set r := Real.exp (-Real.log ((n + 1 : ℕ) : ℝ) / 2) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hrr : r * r = (((n + 1 : ℕ) : ℝ))⁻¹ := by
    rw [hr, ← Real.exp_add,
      show -Real.log ((n + 1 : ℕ) : ℝ) / 2 + -Real.log ((n + 1 : ℕ) : ℝ) / 2 = -Real.log ((n + 1 : ℕ) : ℝ) by
        ring, Real.exp_neg, Real.exp_log hmpos]
  have hid : (r : ℂ) * mixed (translatePacket p ((i : ℝ) * Real.log 2))
      (translatePacket q ((j : ℝ) * Real.log 2)) (((n + 1 : ℕ) : ℝ)⁻¹) =
      logCrossV28 p q (-Real.log ((n + 1 : ℕ) : ℝ) + (j : ℝ) * Real.log 2 - (i : ℝ) * Real.log 2) := by
    have h := logCross_eq_mixed_v28 (translatePacket p ((i : ℝ) * Real.log 2))
      (translatePacket q ((j : ℝ) * Real.log 2)) (-Real.log ((n + 1 : ℕ) : ℝ))
    rw [logCross_translate2, Real.exp_neg (Real.log _), Real.exp_log hmpos] at h
    exact h.symm
  have hC := cross_norm_le2 p q
    (-Real.log ((n + 1 : ℕ) : ℝ) + (j : ℝ) * Real.log 2 - (i : ℝ) * Real.log 2) α β hα hβ
  rw [← hS, ← hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] at hC
  have hL : 0 ≤ ArithmeticFunction.vonMangoldt (n + 1) := ArithmeticFunction.vonMangoldt_nonneg
  simp only [WeilPrimeTermV1, hp0, zero_add]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL, norm_div, norm_one,
    Complex.norm_natCast]
  have hmn : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) = r * r := by rw [hrr, one_div]
  rw [hmn]
  have hx : r * r * ‖mixed (translatePacket p ((i : ℝ) * Real.log 2))
      (translatePacket q ((j : ℝ) * Real.log 2)) (((n + 1 : ℕ) : ℝ)⁻¹)‖ ≤ r * S := by
    have := mul_le_mul_of_nonneg_left hC hr0.le
    nlinarith
  calc ArithmeticFunction.vonMangoldt (n + 1) * (r * r * ‖mixed (translatePacket p ((i : ℝ) * Real.log 2))
        (translatePacket q ((j : ℝ) * Real.log 2)) (((n + 1 : ℕ) : ℝ)⁻¹)‖)
      ≤ ArithmeticFunction.vonMangoldt (n + 1) * (r * S) := mul_le_mul_of_nonneg_left hx hL
    _ = ArithmeticFunction.vonMangoldt (n + 1) * r * S := by ring

theorem S_nonneg (p q : WeilCompactSmoothGV1) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    0 ≤ (β / α * energy p.1 + α / β * energy q.1) / 2 := by
  have h1 := energy_nonnegative p.1
  have h2 := energy_nonnegative q.1
  positivity

/-- Prime sum at gap `k ≤ 6`: only `2^k` contributes. -/
theorem prime_sum_small2 (p q : WeilCompactSmoothGV1) (a : ℝ) (hp : WidthOneThirtyTwoAt p a)
    (hq : WidthOneThirtyTwoAt q a) {i j : ℕ} (hij : i < j) (hk : j - i ≤ 6) (α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β) :
    ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2))
        (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      Real.log 2 * Real.exp (-(((j - i : ℕ) : ℝ) * Real.log 2 / 2)) *
        ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
  have h2 : 1 ≤ 2 ^ (j - i) := Nat.one_le_two_pow
  unfold WeilPrimeSumV1
  rw [tsum_eq_single (2 ^ (j - i) - 1)]
  · have h := term_norm_le2 p q a hp hq hij (2 ^ (j - i) - 1) α β hα hβ
    have hm : 2 ^ (j - i) - 1 + 1 = 2 ^ (j - i) := Nat.sub_add_cancel h2
    have hv : ArithmeticFunction.vonMangoldt (2 ^ (j - i)) = Real.log 2 := by
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega)]
      exact_mod_cast ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
    have hlog : Real.log (((2 ^ (j - i) : ℕ)) : ℝ) = ((j - i : ℕ) : ℝ) * Real.log 2 := by
      push_cast
      rw [Real.log_pow]
    rw [hm, hv, hlog, neg_div] at h
    exact h
  · intro n hn
    have hne : n + 1 ≠ 2 ^ (j - i) := by
      intro h
      apply hn
      omega
    have hp0 := mixed_nat_zero2 p q a hp hq hij (n + 1) (by omega)
    by_cases hwin : |Real.log ((n + 1 : ℕ) : ℝ) - ((j - i : ℕ) : ℝ) * Real.log 2| ≤ 1 / 32
    · rcases prime_window (by omega) hk hwin with h | h
      · exact absurd h hne
      · simp only [WeilPrimeTermV1, h, Complex.ofReal_zero, zero_mul]
    · have hi := mixed_inv_far2 p q a hp hq hij (n + 1) (by omega) (lt_of_not_ge hwin)
      simp only [WeilPrimeTermV1, hp0, hi, mul_zero, add_zero]

/-- Prime sum at gaps `7` and `8`, by the resonance masses. -/
theorem prime_sum78_2 (p q : WeilCompactSmoothGV1) (a : ℝ) (hp : WidthOneThirtyTwoAt p a)
    (hq : WidthOneThirtyTwoAt q a) {i j : ℕ} (hij : i < j) (hk : j - i = 7 ∨ j - i = 8) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) :
    ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2))
        (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      (cbar9 (j - i) - 1 / 200) * ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
  have hS := S_nonneg p q α β hα hβ
  set S := (β / α * energy p.1 + α / β * energy q.1) / 2 with hSdef
  set T := WeilPrimeTermV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2))
    (translatePacket q ((j : ℝ) * Real.log 2))) with hT
  have hzero : ∀ (s : Finset ℕ) (k : ℕ), j - i = k →
      (∀ n : ℕ, |Real.log ((n + 1 : ℕ) : ℝ) - ((k : ℕ) : ℝ) * Real.log 2| ≤ 1 / 32 →
        n ∈ s ∨ ArithmeticFunction.vonMangoldt (n + 1) = 0) →
      ∀ n ∉ s, T n = 0 := by
    intro s k hk' hwk n hn
    have hp0 := mixed_nat_zero2 p q a hp hq hij (n + 1) (by omega)
    by_cases hwin : |Real.log ((n + 1 : ℕ) : ℝ) - ((j - i : ℕ) : ℝ) * Real.log 2| ≤ 1 / 32
    · rw [hk'] at hwin
      rcases hwk n hwin with h | h
      · exact absurd h hn
      · simp only [hT, WeilPrimeTermV1, h, Complex.ofReal_zero, zero_mul]
    · have hi := mixed_inv_far2 p q a hp hq hij (n + 1) (by omega) (lt_of_not_ge hwin)
      simp only [hT, WeilPrimeTermV1, hp0, hi, mul_zero, add_zero]
  unfold WeilPrimeSumV1
  rw [← hT]
  rcases hk with h7 | h8
  · have hz := hzero {124, 126, 127, 130} 7 h7 (fun n hwin => by
      rcases prime_window7 (by omega) hwin with h | h | h | h | h
      · left; simp; omega
      · left; simp; omega
      · left; simp; omega
      · left; simp; omega
      · right; exact h)
    rw [tsum_eq_sum hz]
    have hs : (∑ n ∈ ({124, 126, 127, 130} : Finset ℕ), T n) = T 124 + (T 126 + (T 127 + T 130)) := by
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
    rw [hs, h7]
    have t1 := term_norm_le2 p q a hp hq hij 124 α β hα hβ
    have t2 := term_norm_le2 p q a hp hq hij 126 α β hα hβ
    have t3 := term_norm_le2 p q a hp hq hij 127 α β hα hβ
    have t4 := term_norm_le2 p q a hp hq hij 130 α β hα hβ
    rw [← hSdef, ← hT] at t1 t2 t3 t4
    have m1 := mul_le_mul_of_nonneg_right mass_125 hS
    have m2 := mul_le_mul_of_nonneg_right mass_127 hS
    have m3 := mul_le_mul_of_nonneg_right mass_128 hS
    have m4 := mul_le_mul_of_nonneg_right mass_131 hS
    have n1 := norm_add_le (T 127) (T 130)
    have n2 := norm_add_le (T 126) (T 127 + T 130)
    have n3 := norm_add_le (T 124) (T 126 + (T 127 + T 130))
    simp only [cbar9]
    linarith
  · have hz := hzero {250, 255, 256, 262} 8 h8 (fun n hwin => by
      rcases prime_window8 (by omega) hwin with h | h | h | h | h
      · left; simp; omega
      · left; simp; omega
      · left; simp; omega
      · left; simp; omega
      · right; exact h)
    rw [tsum_eq_sum hz]
    have hs : (∑ n ∈ ({250, 255, 256, 262} : Finset ℕ), T n) = T 250 + (T 255 + (T 256 + T 262)) := by
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
    rw [hs, h8]
    have t1 := term_norm_le2 p q a hp hq hij 250 α β hα hβ
    have t2 := term_norm_le2 p q a hp hq hij 255 α β hα hβ
    have t3 := term_norm_le2 p q a hp hq hij 256 α β hα hβ
    have t4 := term_norm_le2 p q a hp hq hij 262 α β hα hβ
    rw [← hSdef, ← hT] at t1 t2 t3 t4
    have m1 := mul_le_mul_of_nonneg_right mass_251 hS
    have m2 := mul_le_mul_of_nonneg_right mass_256 hS
    have m3 := mul_le_mul_of_nonneg_right mass_257 hS
    have m4 := mul_le_mul_of_nonneg_right mass_263 hS
    have n1 := norm_add_le (T 256) (T 262)
    have n2 := norm_add_le (T 255) (T 256 + T 262)
    have n3 := norm_add_le (T 250) (T 255 + (T 256 + T 262))
    simp only [cbar9]
    linarith

/-- Archimedean cross term of two different packets at relative shift `≥ log 2`. -/
theorem arch2 (p q : WeilCompactSmoothGV1) (a : ℝ) (hp : WidthOneThirtyTwoAt p a)
    (hq : WidthOneThirtyTwoAt q a) (hmp : WeilMomentConditionsV1 p) {i j : ℕ} (hij : i < j) :
    ‖WeilArchimedeanIntegralV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2))
        (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤ (1 / 400 : ℝ) * (energy p.1 + energy q.1) := by
  set d1 := (i : ℝ) * Real.log 2
  set d2 := (j : ℝ) * Real.log 2
  have hji : (1 : ℝ) ≤ (j : ℝ) - i := by
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : Real.log 2 ≤ d2 - d1 := by
    simp only [d1, d2]
    nlinarith
  have hp' := tw2 p a d1 hp
  have hq' := tw2 q a d2 hq
  have hp2 : LogSupportIn (translatePacket p d1) (a + d1 - 1 / 64) (a + d1 - 1 / 64 + 1 / 32) := by
    have e : a + d1 - 1 / 64 + 1 / 32 = a + d1 + 1 / 64 := by ring
    rw [e]
    exact hp'
  have hq2 : LogSupportIn (translatePacket q d2) (a + d2 - 1 / 64) (a + d2 - 1 / 64 + 1 / 32) := by
    have e : a + d2 - 1 / 64 + 1 / 32 = a + d2 + 1 / 64 := by ring
    rw [e]
    exact hq'
  have hL := AEGIS.WeilSeparatedArchL1BridgeV32.logCross_l1_le_distinct (translatePacket p d1)
    (translatePacket q d2) (a + d1 - 1 / 64) (a + d2 - 1 / 64) (1 / 32) (by norm_num) hp2 hq2
  rw [translate_energy, translate_energy] at hL
  have h := AEGIS.WeilSeparatedArchL1BridgeV32.separated_arch_norm_bound_l1 (translatePacket p d1)
    (translatePacket q d2) (a + d1 - 1 / 64) (a + d1 + 1 / 64) (a + d2 - 1 / 64) (a + d2 + 1 / 64) _
    hp' hq' (by linarith) (translate_preserves_moments p d1 hmp) hL
  calc ‖WeilArchimedeanIntegralV1 (mixed (translatePacket p d1) (translatePacket q d2))‖
      ≤ (4 / 25 : ℝ) * ((1 / 32) / 2 * (energy p.1 + energy q.1)) := h
    _ = (1 / 400 : ℝ) * (energy p.1 + energy q.1) := by ring

/-- **Cross term of two different packets**, gaps `1, …, 8`. -/
theorem cross2 (p q : WeilCompactSmoothGV1) (a : ℝ) (hp : WidthOneThirtyTwoAt p a)
    (hq : WidthOneThirtyTwoAt q a) (hmp : WeilMomentConditionsV1 p) {i j : ℕ} (hij : i < j)
    (hk : j - i ≤ 8) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ‖B (translatePacket p ((i : ℝ) * Real.log 2)) (translatePacket q ((j : ℝ) * Real.log 2))‖ ≤
      (cbar9 (j - i) - 1 / 200) * ((β / α * energy p.1 + α / β * energy q.1) / 2) +
        (1 / 400 : ℝ) * (energy p.1 + energy q.1) := by
  have hS := S_nonneg p q α β hα hβ
  have hzero : mixed (translatePacket p ((i : ℝ) * Real.log 2))
      (translatePacket q ((j : ℝ) * Real.log 2)) 1 = 0 := by
    simpa using mixed_nat_zero2 p q a hp hq hij 1 one_pos
  have harch := arch2 p q a hp hq hmp hij
  have hprime : ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2))
      (translatePacket q ((j : ℝ) * Real.log 2)))‖ ≤
      (cbar9 (j - i) - 1 / 200) * ((β / α * energy p.1 + α / β * energy q.1) / 2) := by
    by_cases h6 : j - i ≤ 6
    · have h := prime_sum_small2 p q a hp hq hij h6 α β hα hβ
      have hc := prime_coeff_le9 (j - i) (by omega) h6
      have hc' : Real.log 2 * Real.exp (-(((j - i : ℕ) : ℝ) * Real.log 2 / 2)) ≤ cbar9 (j - i) - 1 / 200 := by
        linarith
      exact h.trans (mul_le_mul_of_nonneg_right hc' hS)
    · exact prime_sum78_2 p q a hp hq hij (by omega) α β hα hβ
  unfold B WeilExplicitRightSideV1
  rw [hzero, mul_zero, add_zero]
  calc ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2))
        (translatePacket q ((j : ℝ) * Real.log 2))) +
        WeilArchimedeanIntegralV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2))
          (translatePacket q ((j : ℝ) * Real.log 2)))‖
      ≤ ‖WeilPrimeSumV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2))
          (translatePacket q ((j : ℝ) * Real.log 2)))‖ +
        ‖WeilArchimedeanIntegralV1 (mixed (translatePacket p ((i : ℝ) * Real.log 2))
          (translatePacket q ((j : ℝ) * Real.log 2)))‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hprime harch

theorem diag2 (p : WeilCompactSmoothGV1) (a : ℝ) (hp : WidthOneThirtyTwoAt p a)
    (hmp : WeilMomentConditionsV1 p) (d : ℝ) :
    (B (translatePacket p d) (translatePacket p d)).re ≤ -((299 / 100 : ℝ) * energy p.1) := by
  have h := width_diagonal_299_over_100 (translatePacket p d) (a + d) (tw2 p a d hp)
    (translate_preserves_moments p d hmp)
  rw [translate_energy] at h
  linarith

/-- Schur weights. -/
def wv : ℕ → ℝ
  | 0 => 1
  | 1 => 827 / 1000
  | 2 => 571 / 1000
  | 3 => 583 / 1000
  | 4 => 587 / 1000
  | 5 => 583 / 1000
  | 6 => 571 / 1000
  | 7 => 827 / 1000
  | _ => 1

theorem wv_pos (n : ℕ) : 0 < wv n := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n <;> simp [wv]

/-- The translated family. -/
def tp (g : Fin 9 → WeilCompactSmoothGV1) (j : Fin 9) : WeilCompactSmoothGV1 :=
  translatePacket (g j) (((j : ℕ) : ℝ) * Real.log 2)

theorem hterm2 (g : Fin 9 → WeilCompactSmoothGV1) (a : ℝ) (hw : ∀ j, WidthOneThirtyTwoAt (g j) a)
    (hm : ∀ j, WeilMomentConditionsV1 (g j)) (i j : Fin 9) :
    (B (tp g i) (tp g j)).re ≤
      if Nat.dist i j = 0 then -((299 / 100 : ℝ) * energy (g i).1) else
        (cbar9 (Nat.dist i j) - 1 / 200) *
          ((wv j / wv i * energy (g i).1 + wv i / wv j * energy (g j).1) / 2) +
        (1 / 400 : ℝ) * (energy (g i).1 + energy (g j).1) := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos (Nat.dist_self _)]
    exact diag2 (g i) a (hw i) (hm i) _
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
      exact cross2 (g i) (g j) a (hw i) (hw j) (hm i) h (by omega) (wv i) (wv j) (wv_pos _) (wv_pos _)
    · have hdist : Nat.dist i j = i - j := by unfold Nat.dist; omega
      rw [hdist]
      unfold tp
      rw [B_hermitian, Complex.norm_conj]
      have hc := cross2 (g j) (g i) a (hw j) (hw i) (hm j) h (by omega) (wv j) (wv i) (wv_pos _) (wv_pos _)
      linarith

set_option maxHeartbeats 1600000 in
/-- **Nine independent packets on the dyadic lattice at width 1/32.** -/
theorem nine_packet_gram_bound (g : Fin 9 → WeilCompactSmoothGV1) (a : ℝ)
    (hw : ∀ j, WidthOneThirtyTwoAt (g j) a) (hm : ∀ j, WeilMomentConditionsV1 (g j)) :
    (∑ i : Fin 9, ∑ j : Fin 9, B (tp g i) (tp g j)).re ≤ -(1 / 50 : ℝ) * ∑ j : Fin 9, energy (g j).1 := by
  have hE : ∀ j, 0 ≤ energy (g j).1 := fun j => energy_nonnegative (g j).1
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  calc (∑ i : Fin 9, ∑ j : Fin 9, (B (tp g i) (tp g j)).re)
      ≤ ∑ i : Fin 9, ∑ j : Fin 9,
          (if Nat.dist i j = 0 then -((299 / 100 : ℝ) * energy (g i).1) else
            (cbar9 (Nat.dist i j) - 1 / 200) *
              ((wv j / wv i * energy (g i).1 + wv i / wv j * energy (g j).1) / 2) +
            (1 / 400 : ℝ) * (energy (g i).1 + energy (g j).1)) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm2 g a hw hm i j))
    _ ≤ -(1 / 50 : ℝ) * ∑ j : Fin 9, energy (g j).1 := by
        simp only [sum_fin9]
        norm_num [cbar9, wv, Nat.dist]
        linarith [hE 0, hE 1, hE 2, hE 3, hE 4, hE 5, hE 6, hE 7, hE 8]

end AEGIS.WeilNineBlockMultiV1

#print axioms AEGIS.WeilNineBlockMultiV1.cross_norm_le2
#print axioms AEGIS.WeilNineBlockMultiV1.cross2
#print axioms AEGIS.WeilNineBlockMultiV1.nine_packet_gram_bound
