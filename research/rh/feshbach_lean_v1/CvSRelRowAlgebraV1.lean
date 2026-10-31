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
# Perturbation inequalities for finite Hermitian forms

Window-free lemmas for comparing a quadratic form with entries known only up to explicit errors:

* `normSq_add_le`: `‖x + y‖² ≤ (1 + η)‖x‖² + (1 + 1/η)‖y‖²`;
* `cs_sum`: `‖Σ x_n g_n‖² ≤ (Σ ‖x_n‖²)(Σ g_n²)` for real `g`;
* `schur_vec`: if `‖z_n‖ ≤ Σ_m e_nm ‖v_m‖` with row sums `≤ Rr` and column sums `≤ Rc`, then
  `Σ ‖z_n‖² ≤ Rr Rc Σ ‖v_m‖²` (Schur test);
* `schur_bilin`: if `|X_nm| ≤ e_nm` with `e` symmetric and row sums `≤ R`, then
  `‖Σ_{n,m} x_n conj(y_m) X_nm‖² ≤ R² (Σ ‖x‖²)(Σ ‖y‖²)`.

Not RH.
-/

open Finset
open scoped ComplexConjugate

namespace AEGIS.CvSRelRowAlgebraV1


/-- `‖x + y‖² ≤ (1 + η)‖x‖² + (1 + 1/η)‖y‖²` for `η > 0`. -/
theorem normSq_add_le (x y : ℂ) {η : ℝ} (hη : 0 < η) :
    ‖x + y‖ ^ 2 ≤ (1 + η) * ‖x‖ ^ 2 + (1 + 1 / η) * ‖y‖ ^ 2 := by
  have h1 := norm_add_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have key : 2 * ‖x‖ * ‖y‖ ≤ η * ‖x‖ ^ 2 + 1 / η * ‖y‖ ^ 2 := by
    have h3 : 0 ≤ (η * ‖x‖ - ‖y‖) ^ 2 := sq_nonneg _
    have e : η * ‖x‖ ^ 2 + 1 / η * ‖y‖ ^ 2 - 2 * ‖x‖ * ‖y‖ = (η * ‖x‖ - ‖y‖) ^ 2 / η := by
      field_simp
      ring
    have : 0 ≤ (η * ‖x‖ - ‖y‖) ^ 2 / η := div_nonneg h3 hη.le
    linarith
  nlinarith

/-- Cauchy–Schwarz for a complex vector against a real one. -/
theorem cs_sum {ι : Type*} (F : Finset ι) (x : ι → ℂ) (g : ι → ℝ) :
    ‖∑ n ∈ F, x n * (g n : ℂ)‖ ^ 2 ≤ (∑ n ∈ F, ‖x n‖ ^ 2) * ∑ n ∈ F, g n ^ 2 := by
  have h1 : ‖∑ n ∈ F, x n * (g n : ℂ)‖ ≤ ∑ n ∈ F, ‖x n‖ * |g n| := by
    refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq F (fun n => ‖x n‖) (fun n => |g n|)
  simp only [sq_abs] at h2
  have h0 : 0 ≤ ∑ n ∈ F, ‖x n‖ * |g n| := sum_nonneg fun n _ => by positivity
  calc ‖∑ n ∈ F, x n * (g n : ℂ)‖ ^ 2 ≤ (∑ n ∈ F, ‖x n‖ * |g n|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- Weighted Cauchy–Schwarz: `(Σ w a b)² ≤ (Σ w a²)(Σ w b²)` for `w ≥ 0`. -/
theorem cs_weighted {ι : Type*} (F : Finset ι) (w a b : ι → ℝ) (hw : ∀ n ∈ F, 0 ≤ w n) :
    (∑ n ∈ F, w n * (a n * b n)) ^ 2 ≤ (∑ n ∈ F, w n * a n ^ 2) * ∑ n ∈ F, w n * b n ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq F (fun n => √(w n) * a n) (fun n => √(w n) * b n)
  have e1 : ∀ n ∈ F, √(w n) * a n * (√(w n) * b n) = w n * (a n * b n) := fun n hn => by
    rw [show √(w n) * a n * (√(w n) * b n) = (√(w n) * √(w n)) * (a n * b n) by ring,
      Real.mul_self_sqrt (hw n hn)]
  have e2 : ∀ (c : ι → ℝ), ∀ n ∈ F, (√(w n) * c n) ^ 2 = w n * c n ^ 2 := fun c n hn => by
    rw [mul_pow, Real.sq_sqrt (hw n hn)]
  rw [sum_congr rfl e1, sum_congr rfl (e2 a), sum_congr rfl (e2 b)] at h
  exact h

/-- **Schur test.** If `‖z_n‖ ≤ Σ_m e_nm ‖v_m‖` with `e ≥ 0`, row sums `≤ Rr` and column sums
`≤ Rc`, then `Σ ‖z_n‖² ≤ Rr Rc Σ ‖v_m‖²`. -/
theorem schur_vec {ι κ : Type*} (A : Finset ι) (B : Finset κ) (z : ι → ℂ) (v : κ → ℂ)
    (e : ι → κ → ℝ) {Rr Rc : ℝ} (hRr : 0 ≤ Rr) (he : ∀ n ∈ A, ∀ m ∈ B, 0 ≤ e n m)
    (hz : ∀ n ∈ A, ‖z n‖ ≤ ∑ m ∈ B, e n m * ‖v m‖)
    (hrow : ∀ n ∈ A, ∑ m ∈ B, e n m ≤ Rr) (hcol : ∀ m ∈ B, ∑ n ∈ A, e n m ≤ Rc) :
    ∑ n ∈ A, ‖z n‖ ^ 2 ≤ Rr * Rc * ∑ m ∈ B, ‖v m‖ ^ 2 := by
  have step : ∀ n ∈ A, ‖z n‖ ^ 2 ≤ Rr * ∑ m ∈ B, e n m * ‖v m‖ ^ 2 := by
    intro n hn
    have h1 : ‖z n‖ ^ 2 ≤ (∑ m ∈ B, e n m * ‖v m‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hz n hn) 2
    have h2 := cs_weighted B (e n) (fun _ => 1) (fun m => ‖v m‖) (he n hn)
    simp only [one_mul, one_pow, mul_one] at h2
    have h3 : 0 ≤ ∑ m ∈ B, e n m * ‖v m‖ ^ 2 :=
      sum_nonneg fun m hm => mul_nonneg (he n hn m hm) (sq_nonneg _)
    calc ‖z n‖ ^ 2 ≤ (∑ m ∈ B, e n m * ‖v m‖) ^ 2 := h1
      _ ≤ (∑ m ∈ B, e n m) * ∑ m ∈ B, e n m * ‖v m‖ ^ 2 := h2
      _ ≤ Rr * ∑ m ∈ B, e n m * ‖v m‖ ^ 2 := mul_le_mul_of_nonneg_right (hrow n hn) h3
  calc ∑ n ∈ A, ‖z n‖ ^ 2 ≤ ∑ n ∈ A, Rr * ∑ m ∈ B, e n m * ‖v m‖ ^ 2 := sum_le_sum step
    _ = Rr * ∑ m ∈ B, ‖v m‖ ^ 2 * ∑ n ∈ A, e n m := by
        rw [← mul_sum, sum_comm]
        congr 1
        exact sum_congr rfl fun m _ => by rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
    _ ≤ Rr * ∑ m ∈ B, ‖v m‖ ^ 2 * Rc :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun m hm =>
          mul_le_mul_of_nonneg_left (hcol m hm) (sq_nonneg _)) hRr
    _ = Rr * Rc * ∑ m ∈ B, ‖v m‖ ^ 2 := by rw [← sum_mul]; ring

/-- **Schur bound for a Hermitian form.** If `|X_nm| ≤ e_nm`, `e` is symmetric and its row sums
are `≤ R`, then `‖Σ x_n conj(y_m) X_nm‖² ≤ R² (Σ ‖x‖²)(Σ ‖y‖²)`. -/
theorem schur_bilin {ι : Type*} (F : Finset ι) (X e : ι → ι → ℝ) {R : ℝ}
    (hX : ∀ n ∈ F, ∀ m ∈ F, |X n m| ≤ e n m) (hsym : ∀ n ∈ F, ∀ m ∈ F, e n m = e m n)
    (hrow : ∀ n ∈ F, ∑ m ∈ F, e n m ≤ R) (x y : ι → ℂ) :
    ‖∑ n ∈ F, ∑ m ∈ F, x n * conj (y m) * (X n m : ℂ)‖ ^ 2 ≤
      R ^ 2 * ((∑ n ∈ F, ‖x n‖ ^ 2) * ∑ m ∈ F, ‖y m‖ ^ 2) := by
  have he : ∀ n ∈ F, ∀ m ∈ F, 0 ≤ e n m := fun n hn m hm => (abs_nonneg _).trans (hX n hn m hm)
  set P := F ×ˢ F
  have h1 : ‖∑ n ∈ F, ∑ m ∈ F, x n * conj (y m) * (X n m : ℂ)‖ ≤
      ∑ p ∈ P, e p.1 p.2 * (‖x p.1‖ * ‖y p.2‖) := by
    rw [sum_product]
    refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => (norm_sum_le _ _).trans
      (sum_le_sum fun m hm => ?_))
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    calc ‖x n‖ * ‖y m‖ * |X n m| ≤ ‖x n‖ * ‖y m‖ * e n m :=
          mul_le_mul_of_nonneg_left (hX n hn m hm) (by positivity)
      _ = e n m * (‖x n‖ * ‖y m‖) := by ring
  have hP : ∀ p ∈ P, 0 ≤ e p.1 p.2 := fun p hp => by
    rw [mem_product] at hp; exact he _ hp.1 _ hp.2
  have h2 := cs_weighted P (fun p => e p.1 p.2) (fun p => ‖x p.1‖) (fun p => ‖y p.2‖) hP
  have hx : ∑ p ∈ P, e p.1 p.2 * ‖x p.1‖ ^ 2 ≤ R * ∑ n ∈ F, ‖x n‖ ^ 2 := by
    rw [sum_product, mul_sum]
    refine sum_le_sum fun n hn => ?_
    dsimp only
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow n hn) (sq_nonneg _)
  have hy : ∑ p ∈ P, e p.1 p.2 * ‖y p.2‖ ^ 2 ≤ R * ∑ m ∈ F, ‖y m‖ ^ 2 := by
    rw [sum_product_right, mul_sum]
    refine sum_le_sum fun m hm => ?_
    dsimp only
    rw [← sum_mul]
    have : ∑ n ∈ F, e n m ≤ R := by
      rw [sum_congr rfl fun n hn => hsym n hn m hm]; exact hrow m hm
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hx0 : 0 ≤ ∑ p ∈ P, e p.1 p.2 * ‖x p.1‖ ^ 2 :=
    sum_nonneg fun p hp => mul_nonneg (hP p hp) (sq_nonneg _)
  have hy0 : 0 ≤ ∑ p ∈ P, e p.1 p.2 * ‖y p.2‖ ^ 2 :=
    sum_nonneg fun p hp => mul_nonneg (hP p hp) (sq_nonneg _)
  calc ‖∑ n ∈ F, ∑ m ∈ F, x n * conj (y m) * (X n m : ℂ)‖ ^ 2
      ≤ (∑ p ∈ P, e p.1 p.2 * (‖x p.1‖ * ‖y p.2‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ p ∈ P, e p.1 p.2 * ‖x p.1‖ ^ 2) * ∑ p ∈ P, e p.1 p.2 * ‖y p.2‖ ^ 2 := h2
    _ ≤ (R * ∑ n ∈ F, ‖x n‖ ^ 2) * (R * ∑ m ∈ F, ‖y m‖ ^ 2) :=
        mul_le_mul hx hy hy0 (hx0.trans hx)
    _ = R ^ 2 * ((∑ n ∈ F, ‖x n‖ ^ 2) * ∑ m ∈ F, ‖y m‖ ^ 2) := by ring

end AEGIS.CvSRelRowAlgebraV1

#print axioms AEGIS.CvSRelRowAlgebraV1.normSq_add_le
#print axioms AEGIS.CvSRelRowAlgebraV1.cs_sum
#print axioms AEGIS.CvSRelRowAlgebraV1.cs_weighted
#print axioms AEGIS.CvSRelRowAlgebraV1.schur_vec
#print axioms AEGIS.CvSRelRowAlgebraV1.schur_bilin
