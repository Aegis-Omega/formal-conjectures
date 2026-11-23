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
import CvSRelRowOutL43V1

/-!
# The Gram row tail `|m| > 200` at `L = 4/3`

`tail_le`: `gramTail M (4/3) F a 13 (7/10) 200 ≤ Re Σ_{n,m ∈ F} â_n conj(â_m) (⌊T1q X(n,m)/2^64⌋ +
⌊T2q Gt(n,m)/2^64⌋)/2^128 + ε_T Σ_F |â_n|²` with `X(n,m) = ⌊tq n tq m Gt(n,m)/2^98⌋`. The kernel
`G = gramUp 200` is symmetric and positive on `F` (`G_psd`, from `gram_tail_le`), which gives
the split `g(x + y) ≤ (1 + η) g(x) + (1 + 1/η) g(y)` (`psd_split`); `Gt/2^128` is `G` within
`1100/2^128` (`hLit` is `2^128 H` within one unit per term). Not RH.
-/

open Finset
open scoped ComplexConjugate
open AEGIS.CvSRelRowDataL43V1 AEGIS.CvSRelRowBoxL43V1 AEGIS.CvSRelRowFormL43V1
  AEGIS.CvSRelRowErrL43V1 AEGIS.CvSRelRowAlgebraV1 AEGIS.CvSRelRowHarmV1 AEGIS.CvSRelRowQL43V1
  AEGIS.CvSRelRowKtL43V1 AEGIS.CvSRelRowOutL43V1 AEGIS.CvSRowTailV1 AEGIS.CvSGramTailV1

noncomputable section

namespace AEGIS.CvSRelRowTailL43V1

set_option maxRecDepth 100000

/-! ## The kernel `gramUp 200` on `F` -/

abbrev G : ℤ → ℤ → ℝ := gramUp 200

theorem G_psd (v : ℤ → ℂ) : 0 ≤ gform F v G := by
  have hF : ∀ n ∈ F, |(n : ℝ)| ≤ (70 : ℕ) := fun n hn => by
    rw [mem_Icc] at hn
    have h1 : (-70 : ℝ) ≤ n := by exact_mod_cast hn.1
    have h2 : (n : ℝ) ≤ 70 := by exact_mod_cast hn.2
    rw [abs_le]
    push_cast
    exact ⟨h1, h2⟩
  exact (sum_nonneg fun _ _ => sq_nonneg _).trans (gram_tail_le hF (by norm_num) v 0)

theorem G_symm (n m : ℤ) : G n m = G m n := by
  simp only [G, gramUp]
  by_cases h : n = m
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    have hd : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    have hd' : (m : ℝ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm h)
    rw [div_eq_div_iff hd hd']
    ring

/-- The bilinear form of `G`. -/
def gb (x y : ℤ → ℂ) : ℝ := (∑ n ∈ F, ∑ m ∈ F, x n * conj (y m) * (G n m : ℂ)).re

theorem gb_symm (x y : ℤ → ℂ) : gb y x = gb x y := by
  simp only [gb]
  rw [← Complex.conj_re, map_sum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun n _ => ?_
  rw [map_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal, G_symm]
  ring

theorem expand (x y : ℤ → ℂ) (α β : ℝ) :
    gform F (fun n => (α : ℂ) * x n + (β : ℂ) * y n) G =
      α ^ 2 * gform F x G + α * β * (gb x y + gb y x) + β ^ 2 * gform F y G := by
  have e : ∑ n ∈ F, ∑ m ∈ F, ((α : ℂ) * x n + (β : ℂ) * y n) * conj ((α : ℂ) * x m + (β : ℂ) * y m) *
      (G n m : ℂ) =
      ((α ^ 2 : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, x n * conj (x m) * (G n m : ℂ)) +
      ((α * β : ℝ) : ℂ) * ((∑ n ∈ F, ∑ m ∈ F, x n * conj (y m) * (G n m : ℂ)) +
        ∑ n ∈ F, ∑ m ∈ F, y n * conj (x m) * (G n m : ℂ)) +
      ((β ^ 2 : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, y n * conj (y m) * (G n m : ℂ)) := by
    simp only [mul_add, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_
    simp only [map_add, map_mul, Complex.conj_ofReal]
    push_cast
    ring
  simp only [gform, gb]
  rw [e]
  simp only [Complex.add_re, Complex.re_ofReal_mul]

/-- **The split of a positive form.** -/
theorem psd_split (x y : ℤ → ℂ) {η : ℝ} (hη : 0 < η) :
    gform F (fun n => x n + y n) G ≤ (1 + η) * gform F x G + (1 + 1 / η) * gform F y G := by
  have h1 := expand x y 1 1
  have h2 := expand x y η (-1)
  have p := G_psd (fun n => (η : ℂ) * x n + ((-1 : ℝ) : ℂ) * y n)
  rw [h2] at p
  have e1 : (fun n => ((1 : ℝ) : ℂ) * x n + ((1 : ℝ) : ℂ) * y n) = fun n => x n + y n := by
    funext n; push_cast; ring
  rw [e1] at h1
  rw [h1, gb_symm x y]
  rw [gb_symm x y] at p
  have gx := G_psd x
  have gy := G_psd y
  have key : 2 * gb x y ≤ η * gform F x G + 1 / η * gform F y G := by
    have : 2 * η * gb x y ≤ η ^ 2 * gform F x G + gform F y G := by linarith
    have e : η * gform F x G + 1 / η * gform F y G = (η ^ 2 * gform F x G + gform F y G) / η := by
      field_simp
    rw [e, le_div_iff₀ hη]
    linarith
  linarith

/-! ## Entry bounds -/

theorem G_abs_le {n m : ℤ} (hn : n ∈ F) (hm : m ∈ F) : |G n m| ≤ 2 := by
  rw [mem_Icc] at hn hm
  simp only [G, gramUp]
  split_ifs with h
  · subst h
    have a1 : (0 : ℝ) < (200 : ℕ) - n + 1 / 2 := by push_cast; have : (n : ℝ) ≤ 70 := by exact_mod_cast hn.2
                                                    linarith
    have a2 : (0 : ℝ) < (200 : ℕ) + n + 1 / 2 := by push_cast; have : (-70 : ℝ) ≤ n := by exact_mod_cast hn.1
                                                    linarith
    have b1 : 1 / ((200 : ℕ) - (n : ℝ) + 1 / 2) ≤ 1 := by
      rw [div_le_one a1]; push_cast; have : (n : ℝ) ≤ 70 := by exact_mod_cast hn.2
      linarith
    have b2 : 1 / ((200 : ℕ) + (n : ℝ) + 1 / 2) ≤ 1 := by
      rw [div_le_one a2]; push_cast; have : (-70 : ℝ) ≤ n := by exact_mod_cast hn.1
      linarith
    rw [abs_of_nonneg (by positivity)]
    linarith
  · have hd : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    have hp : 0 < |(n : ℝ) - m| := abs_pos.mpr hd
    rw [abs_div, div_le_iff₀ hp]
    have hn1 : (-70 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hn2 : (n : ℝ) ≤ 70 := by exact_mod_cast hn.2
    have hm1 : (-70 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hm2 : (m : ℝ) ≤ 70 := by exact_mod_cast hm.2
    have c1 := H_sub_abs_le (x := ((200 : ℕ) : ℤ) - m) (y := ((200 : ℕ) : ℤ) - n) (by push_cast; omega)
      (by push_cast; omega) (c := 1) one_pos (by push_cast; linarith) (by push_cast; linarith)
    have c2 := H_sub_abs_le (x := ((200 : ℕ) : ℤ) + n) (y := ((200 : ℕ) : ℤ) + m) (by push_cast; omega)
      (by push_cast; omega) (c := 1) one_pos (by push_cast; linarith) (by push_cast; linarith)
    have e1 : |((((200 : ℕ) : ℤ) - m : ℤ) : ℝ) - ((((200 : ℕ) : ℤ) - n : ℤ) : ℝ)| = |(n : ℝ) - m| := by
      push_cast; rw [show (200 : ℝ) - m - (200 - n) = n - m by ring]
    have e2 : |((((200 : ℕ) : ℤ) + n : ℤ) : ℝ) - ((((200 : ℕ) : ℤ) + m : ℤ) : ℝ)| = |(n : ℝ) - m| := by
      push_cast; rw [show (200 : ℝ) + n - (200 + m) = n - m by ring]
    rw [e1, div_one] at c1
    rw [e2, div_one] at c2
    have := abs_add_le (H (((200 : ℕ) : ℤ) - m) - H (((200 : ℕ) : ℤ) - n))
      (H (((200 : ℕ) : ℤ) + n) - H (((200 : ℕ) : ℤ) + m))
    linarith

/-- `hLit` is `2^128 H` within one unit per term. -/
theorem hLit_err : ∀ k : ℕ, k ≤ 271 →
    |((hLit.getD k 0 : ℤ) : ℝ) - 2 ^ 128 * ((harmonic k : ℚ) : ℝ)| ≤ (k : ℝ) := by
  obtain ⟨h0, hs⟩ := h_ok
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hs
  intro k
  induction k with
  | zero => intro _; rw [h0]; simp
  | succ k ih =>
    intro hk
    have step := hs k (by omega)
    set q : ℤ := 2 ^ 128 / ((k : ℤ) + 1) with hq
    have r := ediv_err (2 ^ 128) ((k : ℤ) + 1) (by omega)
    rw [← hq] at r
    have r' : |(2 : ℝ) ^ 128 * (1 / ((k : ℝ) + 1)) - (q : ℝ)| < 1 := by
      have e1 : ((2 ^ 128 : ℤ) : ℝ) / (((k : ℤ) + 1 : ℤ) : ℝ) = (2 : ℝ) ^ 128 * (1 / ((k : ℝ) + 1)) := by
        push_cast; ring
      rw [e1] at r; exact r
    have A : ((hLit.getD (k + 1) 0 : ℤ) : ℝ) = ((hLit.getD k 0 : ℤ) : ℝ) + (q : ℝ) := by
      rw [step]; push_cast; ring
    have B : ((harmonic (k + 1) : ℚ) : ℝ) = ((harmonic k : ℚ) : ℝ) + 1 / ((k : ℝ) + 1) := by
      rw [harmonic_succ]; push_cast; ring
    rw [A, B]
    have ih' := ih (by omega)
    rw [abs_le] at ih' ⊢
    rw [abs_lt] at r'
    push_cast
    constructor <;> linarith [ih'.1, ih'.2, r'.1, r'.2]

theorem hq_err {u : ℤ} (h0 : 0 ≤ u) (h1 : u ≤ 270) : |(hq u : ℝ) - 2 ^ 128 * H u| ≤ 270 := by
  have := hLit_err u.toNat (by omega)
  simp only [hq, H]
  refine this.trans ?_
  have : (u.toNat : ℝ) ≤ 270 := by exact_mod_cast (show u.toNat ≤ 270 by omega)
  exact this

theorem Gt_err_lt {n m : ℤ} (hn : n ∈ F) (hm : m ∈ F) (h : m < n) :
    |(Gt n m : ℝ) / 2 ^ 128 - G n m| ≤ 1100 / 2 ^ 128 := by
  rw [mem_Icc] at hn hm
  have hne : n ≠ m := by omega
  have hk : (0 : ℝ) < (n : ℝ) - m := by
    have : (m : ℝ) < n := by exact_mod_cast h
    linarith
  have hk1 : (1 : ℝ) ≤ (n : ℝ) - m := by
    have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    linarith
  have eG : Gt n m = (hq (200 - m) - hq (200 - n) + (hq (200 + n) - hq (200 + m))) / (n - m) := by
    simp only [Gt, if_neg hne, if_pos h]
  have eU : G n m = (H (200 - m) - H (200 - n) + (H (200 + n) - H (200 + m))) / ((n : ℝ) - m) := by
    simp only [G, gramUp, if_neg hne]
    push_cast
    rfl
  rw [eG, eU]
  set N : ℤ := hq (200 - m) - hq (200 - n) + (hq (200 + n) - hq (200 + m))
  set U : ℝ := H (200 - m) - H (200 - n) + (H (200 + n) - H (200 + m))
  have hN : |(N : ℝ) - 2 ^ 128 * U| ≤ 1080 := by
    have a1 := hq_err (u := 200 - m) (by omega) (by omega)
    have a2 := hq_err (u := 200 - n) (by omega) (by omega)
    have a3 := hq_err (u := 200 + n) (by omega) (by omega)
    have a4 := hq_err (u := 200 + m) (by omega) (by omega)
    have e : (N : ℝ) - 2 ^ 128 * U = ((hq (200 - m) : ℝ) - 2 ^ 128 * H (200 - m)) -
        ((hq (200 - n) : ℝ) - 2 ^ 128 * H (200 - n)) + (((hq (200 + n) : ℝ) - 2 ^ 128 * H (200 + n)) -
        ((hq (200 + m) : ℝ) - 2 ^ 128 * H (200 + m))) := by
      simp only [N, U]; push_cast; ring
    rw [e]
    rw [abs_le] at a1 a2 a3 a4 ⊢
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
  have r := ediv_err N (n - m) (by omega)
  have e2 : ((N / (n - m) : ℤ) : ℝ) / 2 ^ 128 - U / ((n : ℝ) - m) =
      ((((N / (n - m) : ℤ) : ℝ) - (N : ℝ) / ((n - m : ℤ) : ℝ)) +
        ((N : ℝ) - 2 ^ 128 * U) / ((n : ℝ) - m)) / 2 ^ 128 := by
    push_cast; field_simp; ring
  rw [e2, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 128)]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine (abs_add_le _ _).trans ?_
  rw [abs_sub_comm] at r
  have h3 : |((N : ℝ) - 2 ^ 128 * U) / ((n : ℝ) - m)| ≤ 1080 := by
    rw [abs_div, abs_of_pos hk]
    exact (div_le_self (abs_nonneg _) hk1).trans hN
  linarith

theorem Gt_err {n m : ℤ} (hn : n ∈ F) (hm : m ∈ F) :
    |(Gt n m : ℝ) / 2 ^ 128 - G n m| ≤ 1100 / 2 ^ 128 := by
  rcases lt_trichotomy m n with h | h | h
  · exact Gt_err_lt hn hm h
  · subst h
    rw [mem_Icc] at hn
    set q1 : ℤ := 2 ^ 129 / (401 - 2 * m) with hq1
    set q2 : ℤ := 2 ^ 129 / (401 + 2 * m) with hq2
    have eG : Gt m m = q1 + q2 := by simp only [Gt, if_true, hq1, hq2]
    have eU : G m m = 1 / (((200 : ℕ) : ℝ) - m + 1 / 2) + 1 / (((200 : ℕ) : ℝ) + m + 1 / 2) := by
      rw [show G m m = gramUp 200 m m from rfl, gramUp, if_pos rfl]
    rw [eG, eU]
    have r1 := ediv_err (2 ^ 129) (401 - 2 * m) (by omega)
    have r2 := ediv_err (2 ^ 129) (401 + 2 * m) (by omega)
    rw [← hq1] at r1
    rw [← hq2] at r2
    have hm1 : (-70 : ℝ) ≤ m := by exact_mod_cast hn.1
    have hm2 : (m : ℝ) ≤ 70 := by exact_mod_cast hn.2
    have d1 : (401 : ℝ) - 2 * m ≠ 0 := by intro h; linarith
    have d2 : (401 : ℝ) + 2 * m ≠ 0 := by intro h; linarith
    have d3 : (200 : ℝ) - m + 1 / 2 ≠ 0 := by intro h; linarith
    have d4 : (200 : ℝ) + m + 1 / 2 ≠ 0 := by intro h; linarith
    have e : ((q1 + q2 : ℤ) : ℝ) / 2 ^ 128 -
        (1 / (((200 : ℕ) : ℝ) - m + 1 / 2) + 1 / (((200 : ℕ) : ℝ) + m + 1 / 2)) =
        (((q1 : ℝ) - ((2 ^ 129 : ℤ) : ℝ) / (((401 - 2 * m : ℤ)) : ℝ)) +
          ((q2 : ℝ) - ((2 ^ 129 : ℤ) : ℝ) / (((401 + 2 * m : ℤ)) : ℝ))) / 2 ^ 128 := by
      have f1 : 1 / ((200 : ℝ) - m + 1 / 2) = 2 / (401 - 2 * m) := by
        rw [div_eq_div_iff d3 d1]; ring
      have f2 : 1 / ((200 : ℝ) + m + 1 / 2) = 2 / (401 + 2 * m) := by
        rw [div_eq_div_iff d4 d2]; ring
      push_cast
      rw [f1, f2]
      field_simp
      ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 128)]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    refine (abs_add_le _ _).trans ?_
    rw [abs_sub_comm] at r1 r2
    linarith
  · rw [AEGIS.CvSRelRowPsdL43V1.Gt_symm, G_symm]
    exact Gt_err_lt hm hn h

/-! ## The tail -/

def epsT : ℝ :=
  (T1q : ℝ) / 2 ^ 64 * (141 * (144 * (1100 / 2 ^ 128) + 1 / 2 ^ 128)) + 141 / 2 ^ 128 +
  ((T2q : ℝ) / 2 ^ 64 * (141 * (1100 / 2 ^ 128)) + 141 / 2 ^ 128) +
  LP * (1 + 7 / 10) * (1 + 1 / eta) * (282 * (12 * theta + rho) ^ 2) +
  LP * ((1 + 1 / (7 / 10)) * 13 ^ 2) * (1 + 1 / eta) * (282 * theta ^ 2)

theorem T1_ge : (1 + eta) * (1 + 7 / 10) * ((4 / 3 : ℝ) / Real.pi) ^ 2 ≤ (T1q : ℝ) / 2 ^ 64 := by
  have h1 := Real.pi_gt_d20
  rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
  have l : (3.14159265358979323846 : ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith
  norm_num [eta, T1q] at l ⊢
  nlinarith

theorem T2_ge : (1 + eta) * ((1 + 1 / (7 / 10)) * 13 ^ 2) * ((4 / 3 : ℝ) / Real.pi) ^ 2 ≤
    (T2q : ℝ) / 2 ^ 64 := by
  have h1 := Real.pi_gt_d20
  rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
  have l : (3.14159265358979323846 : ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith
  norm_num [eta, T2q] at l ⊢
  nlinarith

theorem gform_le_R (v : ℤ → ℂ) : gform F v G ≤ 282 * (nrm v * nrm v) := by
  have h := bilin_le G (fun _ _ => (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 282)
    (fun n hn m hm => G_abs_le hn hm) (fun _ _ _ _ => rfl) (fun n _ => by simp; norm_num) v v
  have := Complex.re_le_norm (∑ n ∈ F, ∑ m ∈ F, v n * conj (v m) * (G n m : ℂ))
  simp only [gform]
  linarith

/-- A form against an integer table within `δ` per entry. -/
theorem form_cmp (b : ℤ → ℂ) (A B : ℤ → ℤ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ n ∈ F, ∀ m ∈ F, |A n m - B n m| ≤ δ) :
    (∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * (A n m : ℂ)).re ≤
      (∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * (B n m : ℂ)).re + 141 * δ * (nrm b * nrm b) := by
  have hb := bilin_le (R := 141 * δ) (fun n m => A n m - B n m) (fun _ _ => δ) (by positivity) h
    (fun _ _ _ _ => rfl)
    (fun n _ => by simp) b b
  have e : (∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * (A n m : ℂ)) =
      (∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * (B n m : ℂ)) +
        ∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * ((A n m - B n m : ℝ) : ℂ) := by
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_
    push_cast; ring
  rw [e, Complex.add_re]
  have := Complex.re_le_norm (∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * ((A n m - B n m : ℝ) : ℂ))
  have : 141 * δ * nrm b * nrm b = 141 * δ * (nrm b * nrm b) := by ring
  linarith

/-- The scaled table `⌊c X/2^64⌋/2^128` against `(c/2^64) X/2^128`. -/
theorem scale_err (c X : ℤ) :
    |(c : ℝ) / 2 ^ 64 * ((X : ℝ) / 2 ^ 128) - ((c * X / 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128| ≤ 1 / 2 ^ 128 := by
  have h := ediv_err (c * X) (2 ^ 64) (by norm_num)
  have e : (c : ℝ) / 2 ^ 64 * ((X : ℝ) / 2 ^ 128) - ((c * X / 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128 =
      (((c * X : ℤ) : ℝ) / ((2 ^ 64 : ℤ) : ℝ) - ((c * X / 2 ^ 64 : ℤ) : ℝ)) / 2 ^ 128 := by
    push_cast; ring
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 128)]
  exact div_le_div_of_nonneg_right h.le (by positivity)

/-- **The Gram row tail.** -/
theorem tail_le (M : ℕ) (hM : 3 ≤ M) (c : Fin 139 → ℂ) :
    gramTail M (4 / 3) F (acoef c) 13 (7 / 10) 200 ≤
      (∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (ahat c m) *
        (((((T1q * (tq n * tq m * Gt n m / 2 ^ 98) / 2 ^ 64 : ℤ) : ℝ) +
          ((T2q * Gt n m / 2 ^ 64 : ℤ) : ℝ)) / 2 ^ 128 : ℝ) : ℂ)).re +
      epsT * ∑ n ∈ F, ‖ahat c n‖ ^ 2 := by
  set b := ahat c
  set a := acoef c
  set LT2 := ((4 / 3 : ℝ) / Real.pi) ^ 2
  have hLT2 : 0 ≤ LT2 := sq_nonneg _
  have hLP : LT2 ≤ LP := by
    have := LP_ge; have := eta_pos
    have : LT2 ≤ (1 + eta) * LT2 := by have := mul_nonneg eta_pos.le hLT2; linarith
    linarith
  have hη := eta_pos
  set x1 : ℤ → ℂ := fun n => b n * (th n : ℂ)
  set d1 : ℤ → ℂ := fun n => a n * (tau M (4 / 3) n : ℂ) - x1 n
  set d0 : ℤ → ℂ := fun n => a n - b n
  -- the two splits
  have s1 : gform F (fun n => a n * (tau M (4 / 3) n : ℂ)) G ≤
      (1 + eta) * gform F x1 G + (1 + 1 / eta) * gform F d1 G := by
    have := psd_split x1 d1 hη
    have e : (fun n => x1 n + d1 n) = fun n => a n * (tau M (4 / 3) n : ℂ) := by
      funext n; simp only [d1]; ring
    rwa [e] at this
  have s0 : gform F a G ≤ (1 + eta) * gform F b G + (1 + 1 / eta) * gform F d0 G := by
    have := psd_split b d0 hη
    have e : (fun n => b n + d0 n) = a := by funext n; simp only [d0]; ring
    rwa [e] at this
  -- the small parts
  have hrho : 0 ≤ 12 * theta + rho := by
    have := theta_nonneg; have : 0 ≤ rho := by simp only [rho]; norm_num [rhoq]
    linarith
  have nd1 : nrm d1 ≤ (12 * theta + rho) * nrm b := by
    refine nrm_le_of hrho fun n hn => ?_
    rw [mem_Icc] at hn
    obtain ⟨ht, -⟩ := tau_low hM hn.1 hn.2
    have hta := tau_abs_all hM (n := n) (by omega)
    have e : d1 n = (a n - b n) * (tau M (4 / 3) n : ℂ) + b n * ((tau M (4 / 3) n - th n : ℝ) : ℂ) := by
      simp only [d1, x1]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : ‖a n - b n‖ * |tau M (4 / 3) n| ≤ theta * ‖b n‖ * 12 :=
      mul_le_mul (a_sub_ahat c n) hta (abs_nonneg _) (mul_nonneg theta_nonneg (norm_nonneg _))
    have h2 : ‖b n‖ * |tau M (4 / 3) n - th n| ≤ ‖b n‖ * rho := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    linarith
  have nd0 : nrm d0 ≤ theta * nrm b := nrm_le_of theta_nonneg fun n _ => a_sub_ahat c n
  have g1 := gform_le_R d1
  have g0 := gform_le_R d0
  have hb0 := nrm_nonneg b
  have q1 : nrm d1 * nrm d1 ≤ (12 * theta + rho) ^ 2 * (nrm b * nrm b) := by
    have := mul_le_mul nd1 nd1 (nrm_nonneg _) (by positivity); linarith
  have q0 : nrm d0 * nrm d0 ≤ theta ^ 2 * (nrm b * nrm b) := by
    have := mul_le_mul nd0 nd0 (nrm_nonneg _) (mul_nonneg theta_nonneg hb0); linarith
  -- the main parts against the tables
  have gx1 : gform F x1 G =
      (∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * ((th n * th m * G n m : ℝ) : ℂ)).re := by
    simp only [gform, x1]
    congr 1
    refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_
    simp only [map_mul, Complex.conj_ofReal]; push_cast; ring
  set X : ℤ → ℤ → ℤ := fun n m => tq n * tq m * Gt n m / 2 ^ 98
  have c1 := form_cmp b (fun n m => th n * th m * G n m) (fun n m => (X n m : ℝ) / 2 ^ 128)
    (δ := 144 * (1100 / 2 ^ 128) + 1 / 2 ^ 128) (by positivity) (fun n hn m hm => by
      have t1 := th_le hn
      have t2 := th_le hm
      have hg := Gt_err hn hm
      have r := ediv_err (tq n * tq m * Gt n m) (2 ^ 98) (by norm_num)
      have e : th n * th m * G n m - (X n m : ℝ) / 2 ^ 128 =
          th n * th m * (G n m - (Gt n m : ℝ) / 2 ^ 128) +
            (((tq n * tq m * Gt n m : ℤ) : ℝ) / ((2 ^ 98 : ℤ) : ℝ) - (X n m : ℝ)) / 2 ^ 128 := by
        simp only [th]; push_cast; ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_sub_comm (G n m), abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 128)]
      have hp : |th n| * |th m| ≤ 144 := by
        have := mul_le_mul t1 t2 (abs_nonneg _) (by norm_num); linarith
      have h1 : |th n| * |th m| * |(Gt n m : ℝ) / 2 ^ 128 - G n m| ≤ 144 * (1100 / 2 ^ 128) :=
        mul_le_mul hp hg (abs_nonneg _) (by norm_num)
      have h2 : |((tq n * tq m * Gt n m : ℤ) : ℝ) / ((2 ^ 98 : ℤ) : ℝ) - (X n m : ℝ)| / 2 ^ 128 ≤
          1 / 2 ^ 128 := div_le_div_of_nonneg_right r.le (by positivity)
      linarith)
  have c1' := form_cmp b (fun n m => (T1q : ℝ) / 2 ^ 64 * ((X n m : ℝ) / 2 ^ 128))
    (fun n m => ((T1q * X n m / 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128) (δ := 1 / 2 ^ 128) (by positivity)
    (fun n _ m _ => scale_err T1q (X n m))
  have c2 := form_cmp b G (fun n m => (Gt n m : ℝ) / 2 ^ 128) (δ := 1100 / 2 ^ 128) (by positivity)
    (fun n hn m hm => by rw [abs_sub_comm]; exact Gt_err hn hm)
  have c2' := form_cmp b (fun n m => (T2q : ℝ) / 2 ^ 64 * ((Gt n m : ℝ) / 2 ^ 128))
    (fun n m => ((T2q * Gt n m / 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128) (δ := 1 / 2 ^ 128) (by positivity)
    (fun n _ m _ => scale_err T2q (Gt n m))
  -- scalar pull-outs
  have pull : ∀ (r : ℝ) (A : ℤ → ℤ → ℝ),
      (∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * ((r * A n m : ℝ) : ℂ)).re =
        r * (∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * (A n m : ℂ)).re := by
    intro r A
    rw [← Complex.re_ofReal_mul, mul_sum]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun m _ => ?_
    push_cast; ring
  rw [pull] at c1' c2'
  have hT1 : (0 : ℝ) ≤ (T1q : ℝ) / 2 ^ 64 := by norm_num [T1q]
  have hT2 : (0 : ℝ) ≤ (T2q : ℝ) / 2 ^ 64 := by norm_num [T2q]
  have px1 := G_psd x1
  have pb := G_psd b
  have T1g := T1_ge
  have T2g := T2_ge
  -- the target, split
  have tgt : (∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) *
        (((((T1q * (tq n * tq m * Gt n m / 2 ^ 98) / 2 ^ 64 : ℤ) : ℝ) +
          ((T2q * Gt n m / 2 ^ 64 : ℤ) : ℝ)) / 2 ^ 128 : ℝ) : ℂ)).re =
      (∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * ((((T1q * X n m / 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128 : ℝ) : ℂ)).re +
      (∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * ((((T2q * Gt n m / 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128 : ℝ) : ℂ)).re := by
    rw [← Complex.add_re, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    simp only [X]
    push_cast; ring
  rw [tgt, ← nrm_sq b]
  simp only [gramTail]
  rw [gx1] at px1 s1
  -- combine
  set A1 := (∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * ((th n * th m * G n m : ℝ) : ℂ)).re
  set A0 := gform F b G
  have k1 : LT2 * ((1 + 7 / 10) * ((1 + eta) * A1)) ≤ (T1q : ℝ) / 2 ^ 64 * A1 := by
    have := mul_le_mul_of_nonneg_right T1g px1; linarith
  have k0 : LT2 * ((1 + 1 / (7 / 10)) * 13 ^ 2 * ((1 + eta) * A0)) ≤ (T2q : ℝ) / 2 ^ 64 * A0 := by
    have := mul_le_mul_of_nonneg_right T2g pb; linarith
  have hA0 : gform F b G = (∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * (G n m : ℂ)).re := rfl
  have e1 : LT2 * ((1 + 7 / 10) * ((1 + 1 / eta) * gform F d1 G)) ≤
      LP * (1 + 7 / 10) * (1 + 1 / eta) * (282 * (12 * theta + rho) ^ 2) * (nrm b * nrm b) := by
    have hc : 0 ≤ (1 + 7 / 10 : ℝ) * (1 + 1 / eta) := by norm_num [eta]
    have g1' : gform F d1 G ≤ 282 * ((12 * theta + rho) ^ 2 * (nrm b * nrm b)) := g1.trans (by linarith)
    have hgd := G_psd d1
    calc LT2 * ((1 + 7 / 10) * ((1 + 1 / eta) * gform F d1 G))
        = LT2 * ((1 + 7 / 10) * (1 + 1 / eta) * gform F d1 G) := by ring
      _ ≤ LP * ((1 + 7 / 10) * (1 + 1 / eta) * (282 * ((12 * theta + rho) ^ 2 * (nrm b * nrm b)))) :=
          mul_le_mul hLP (mul_le_mul_of_nonneg_left g1' hc) (mul_nonneg hc hgd) LP_pos.le
      _ = _ := by ring
  have e0 : LT2 * ((1 + 1 / (7 / 10)) * 13 ^ 2 * ((1 + 1 / eta) * gform F d0 G)) ≤
      LP * ((1 + 1 / (7 / 10)) * 13 ^ 2) * (1 + 1 / eta) * (282 * theta ^ 2) * (nrm b * nrm b) := by
    have hc : 0 ≤ (1 + 1 / (7 / 10) : ℝ) * 13 ^ 2 * (1 + 1 / eta) := by norm_num [eta]
    have g0' : gform F d0 G ≤ 282 * (theta ^ 2 * (nrm b * nrm b)) := g0.trans (by linarith)
    have hgd := G_psd d0
    calc LT2 * ((1 + 1 / (7 / 10)) * 13 ^ 2 * ((1 + 1 / eta) * gform F d0 G))
        = LT2 * ((1 + 1 / (7 / 10)) * 13 ^ 2 * (1 + 1 / eta) * gform F d0 G) := by ring
      _ ≤ LP * ((1 + 1 / (7 / 10)) * 13 ^ 2 * (1 + 1 / eta) * (282 * (theta ^ 2 * (nrm b * nrm b)))) :=
          mul_le_mul hLP (mul_le_mul_of_nonneg_left g0' hc) (mul_nonneg hc hgd) LP_pos.le
      _ = _ := by ring
  have m1 : (T1q : ℝ) / 2 ^ 64 * A1 ≤
      (T1q : ℝ) / 2 ^ 64 * ((∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * (((X n m : ℝ) / 2 ^ 128 : ℝ) : ℂ)).re +
        141 * (144 * (1100 / 2 ^ 128) + 1 / 2 ^ 128) * (nrm b * nrm b)) :=
    mul_le_mul_of_nonneg_left c1 hT1
  have m2 : (T2q : ℝ) / 2 ^ 64 * A0 ≤
      (T2q : ℝ) / 2 ^ 64 * ((∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * (((Gt n m : ℝ) / 2 ^ 128 : ℝ) : ℂ)).re +
        141 * (1100 / 2 ^ 128) * (nrm b * nrm b)) :=
    mul_le_mul_of_nonneg_left c2 hT2
  have hs1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left s1 (by norm_num : (0 : ℝ) ≤ 1 + 7 / 10)) hLT2
  have hs0 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left s0 (by norm_num : (0 : ℝ) ≤ (1 + 1 / (7 / 10)) * 13 ^ 2)) hLT2
  simp only [epsT]
  linarith [hs1, hs0, k1, k0, e1, e0, m1, m2, c1', c2']

end AEGIS.CvSRelRowTailL43V1

end

#print axioms AEGIS.CvSRelRowTailL43V1.tail_le
