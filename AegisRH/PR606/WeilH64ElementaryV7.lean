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
import Mathlib

/-!
# OPTIMUS V7 (H64 contractive Weil packets): the elementary layer

The finite and one-variable facts behind the V7 row margin `1475/6144`:

* `herm_form_ge`: a Hermitian row margin `δ ≤ Re K_ii − Σ_{j≠i} ‖K_ij‖` bounds the form
  `Re Σ z_i K_ij conj(z_j)` below by `δ Σ ‖z_i‖²` (Gershgorin for Hermitian forms);
* `two_y_le`: `2y ≤ (1+y)(1+y²)` for `y ≥ 0` (the diagonal integrand is at most `1` near `0`);
* `w_le`: `e^{−u/2}/(1−e^{−2u}) ≤ 1 + 1/(2u)` for `u > 0`, and `w_le_two` for `u ≥ 1/2`;
* `tele_prod`: `∏_{m=1}^{n} (2m+1)/(2m−1) = 2n+1`, and `row_product_le`: `(2j+1)(63−2j) ≤ 1023`;
* `log_1023_lt`: `log 1023 < 7`; `prime_coeff_lt`: `log 2/√2 < 1/2`;
* `diag_lower`: `13/3 − 1/2048 < −(log(4π) + γ + 1/2048 + log(1/4096))`;
* `margin_eq`: `13/3 − 1/2048 − (31/1024 + 7/2 + 1/2 + 1/16) = 1475/6144`.

No integral of the Weil functional is evaluated here, and nothing about RH is claimed.
-/

open Finset Complex
open scoped ComplexConjugate BigOperators

namespace AEGIS.WeilH64ElementaryV7

/-- The off-diagonal row weight `Σ_{j≠i} ‖K_ij‖`, written over all `j`. -/
noncomputable def off {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ι → ℂ) (i j : ι) : ℝ :=
  if j = i then 0 else ‖K i j‖

theorem off_symm {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ι → ι → ℂ} (hK : ∀ i j, K j i = conj (K i j)) (i j : ι) :
    off K i j = off K j i := by
  unfold off
  by_cases h : j = i
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), hK, Complex.norm_conj]

theorem off_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ι → ℂ) (i j : ι) : 0 ≤ off K i j := by
  unfold off; split_ifs <;> positivity

/-- One entry of the form, bounded below. -/
theorem entry_ge {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ι → ℂ) (z : ι → ℂ) (i j : ι) :
    (if j = i then (K i i).re * ‖z i‖ ^ 2 else 0) - off K i j * (‖z i‖ ^ 2 + ‖z j‖ ^ 2) / 2 ≤
      (z i * K i j * conj (z j)).re := by
  by_cases h : j = i
  · subst h
    have e : z j * K j j * conj (z j) = K j j * ((‖z j‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm (z j), mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [if_true, off, sub_zero, zero_mul, zero_div, e, Complex.re_mul_ofReal, le_refl]
  · simp only [if_neg h, off, zero_sub]
    have h1 : -‖z i * K i j * conj (z j)‖ ≤ (z i * K i j * conj (z j)).re := by
      have := Complex.abs_re_le_norm (z i * K i j * conj (z j))
      linarith [neg_abs_le (z i * K i j * conj (z j)).re]
    have h2 : ‖z i * K i j * conj (z j)‖ = ‖K i j‖ * (‖z i‖ * ‖z j‖) := by
      rw [norm_mul, norm_mul, Complex.norm_conj]; ring
    have h3 : ‖z i‖ * ‖z j‖ ≤ (‖z i‖ ^ 2 + ‖z j‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖z i‖ - ‖z j‖)]
    have h4 : ‖K i j‖ * (‖z i‖ * ‖z j‖) ≤ ‖K i j‖ * ((‖z i‖ ^ 2 + ‖z j‖ ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    have : -(‖K i j‖ * (‖z i‖ ^ 2 + ‖z j‖ ^ 2) / 2) ≤ -‖z i * K i j * conj (z j)‖ := by
      rw [h2]; linarith
    linarith

/-- **Gershgorin for Hermitian forms.** -/
theorem herm_form_ge {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ι → ℂ) (hK : ∀ i j, K j i = conj (K i j)) {δ : ℝ}
    (hrow : ∀ i, δ ≤ (K i i).re - ∑ j, off K i j) (z : ι → ℂ) :
    δ * ∑ i, ‖z i‖ ^ 2 ≤ (∑ i, ∑ j, z i * K i j * conj (z j)).re := by
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ univ) => entry_ge K z i j
  refine le_trans ?_ hsum
  have hdiag : ∀ i : ι, ∑ j, (if j = i then (K i i).re * ‖z i‖ ^ 2 else 0) =
      (K i i).re * ‖z i‖ ^ 2 := fun i => by simp
  have hswap : ∑ i : ι, ∑ j : ι, off K i j * ‖z j‖ ^ 2 =
      ∑ i : ι, ∑ j : ι, off K i j * ‖z i‖ ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [off_symm hK]
  have hsplit : ∑ i : ι, ∑ j : ι,
      ((if j = i then (K i i).re * ‖z i‖ ^ 2 else 0) - off K i j * (‖z i‖ ^ 2 + ‖z j‖ ^ 2) / 2) =
      ∑ i : ι, ((K i i).re - ∑ j, off K i j) * ‖z i‖ ^ 2 := by
    have e1 : ∀ i : ι, ∑ j : ι,
        ((if j = i then (K i i).re * ‖z i‖ ^ 2 else 0) - off K i j * (‖z i‖ ^ 2 + ‖z j‖ ^ 2) / 2) =
        (K i i).re * ‖z i‖ ^ 2 - (∑ j, off K i j * ‖z i‖ ^ 2) / 2 - (∑ j, off K i j * ‖z j‖ ^ 2) / 2 := by
      intro i
      rw [Finset.sum_sub_distrib, hdiag, Finset.sum_div, Finset.sum_div, sub_sub, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [e1]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, hswap]
    have hA : ∑ i : ι, ((K i i).re - ∑ j, off K i j) * ‖z i‖ ^ 2 =
        ∑ i : ι, (K i i).re * ‖z i‖ ^ 2 - ∑ i : ι, ∑ j, off K i j * ‖z i‖ ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sub_mul, Finset.sum_mul]
    rw [hA]
    ring
  rw [hsplit, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)

/-- The diagonal integrand is at most `1` on the short window: `2y ≤ (1+y)(1+y²)`. -/
theorem two_y_le {y : ℝ} (hy : 0 ≤ y) : 2 * y ≤ (1 + y) * (1 + y ^ 2) := by
  nlinarith [sq_nonneg (y - 1 / 2), pow_nonneg hy 3]

/-- The Archimedean weight `w(u) = e^{−u/2}/(1−e^{−2u})` is at most `1 + 1/(2u)`. -/
theorem w_le {u : ℝ} (hu : 0 < u) :
    Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) ≤ 1 + 1 / (2 * u) := by
  have hx : 0 < 2 * u := by linarith
  have he : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos : 0 < 1 - Real.exp (-2 * u) := by linarith
  -- 1 - e^{-x} ≥ x/(1+x), from 1 + x ≤ e^x
  have h1 : 2 * u / (1 + 2 * u) ≤ 1 - Real.exp (-2 * u) := by
    have hex : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
    have hinv : Real.exp (-2 * u) ≤ 1 / (1 + 2 * u) := by
      rw [show -2 * u = -(2 * u) by ring, Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by linarith) hex
    have : 1 - 1 / (1 + 2 * u) = 2 * u / (1 + 2 * u) := by field_simp; ring
    linarith
  have h2 : Real.exp (-u / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [div_le_iff₀ hpos]
  have h3 : (1 + 1 / (2 * u)) * (2 * u / (1 + 2 * u)) = 1 := by field_simp; ring
  have h4 : (1 + 1 / (2 * u)) * (2 * u / (1 + 2 * u)) ≤ (1 + 1 / (2 * u)) * (1 - Real.exp (-2 * u)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

/-- Across the clusters (`u ≥ 1/2`) the weight is at most `2`. -/
theorem w_le_two {u : ℝ} (hu : 1 / 2 ≤ u) : Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) ≤ 2 := by
  have h := w_le (show 0 < u by linarith)
  have : 1 / (2 * u) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  linarith

/-- The telescoping product of the same-cluster logarithm ratios. -/
theorem tele_prod (n : ℕ) :
    ∏ m ∈ Finset.Icc 1 n, ((2 * (m : ℝ) + 1) / (2 * m - 1)) = 2 * n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    push_cast
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have : (2 * ((n : ℝ) + 1) - 1) ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring

/-- The largest row product in a cluster of `32`. -/
theorem row_product_le {j : ℕ} (hj : j ≤ 31) : (2 * j + 1) * (2 * (31 - j) + 1) ≤ 1023 := by
  interval_cases j <;> norm_num

theorem log_1023_lt : Real.log 1023 < 7 := by
  have h1 : Real.log 1023 < Real.log 1024 := Real.log_lt_log (by norm_num) (by norm_num)
  have h2 : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
  have h3 := Real.log_two_lt_d9
  linarith

theorem prime_coeff_lt : Real.log 2 / Real.sqrt 2 < 1 / 2 := by
  have hs : (7 / 5 : ℝ) < Real.sqrt 2 := by
    rw [show (7 / 5 : ℝ) = Real.sqrt ((7 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hl := Real.log_two_lt_d9
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- **The diagonal constant**: `K_ii ≥ −(log 4π + γ + 2R + log R)` exceeds `13/3 − 1/2048` at `R = 1/4096`. -/
theorem diag_lower :
    (13 : ℝ) / 3 - 1 / 2048 <
      -(Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + 1 / 2048 + Real.log (1 / 4096)) := by
  have hpi : Real.log (4 * Real.pi) < Real.log 16 :=
    Real.log_lt_log (by positivity) (by linarith [Real.pi_lt_d2])
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have h4096 : Real.log (1 / 4096) = -(12 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]; norm_num
  have hg := Real.eulerMascheroniConstant_lt_two_thirds
  have hl := Real.log_two_gt_d9
  rw [h4096]
  linarith

/-- **The V7 row margin.** -/
theorem margin_eq : (13 : ℝ) / 3 - 1 / 2048 - (31 / 1024 + 7 / 2 + 1 / 2 + 1 / 16) = 1475 / 6144 := by
  norm_num

end AEGIS.WeilH64ElementaryV7

#print axioms AEGIS.WeilH64ElementaryV7.herm_form_ge
#print axioms AEGIS.WeilH64ElementaryV7.w_le
#print axioms AEGIS.WeilH64ElementaryV7.tele_prod
#print axioms AEGIS.WeilH64ElementaryV7.diag_lower
#print axioms AEGIS.WeilH64ElementaryV7.prime_coeff_lt
