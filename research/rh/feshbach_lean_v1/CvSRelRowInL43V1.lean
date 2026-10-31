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
import CvSRelRowInvL43V1

/-!
# The rows `|m| ≤ 70` at `L = 4/3`: a rank-two residual

With `y_m = crossRow m`, `g₀ = 1/f`, `g₁ = m/f` and the dyadic `g̃_j = gv j/2^100` (`|g_j − g̃_j| ≤
10^-15 |g̃_j|`, `g_close`), put `N_j = Σ_F y g_j`, `D_j = Σ_F g̃_j g_j`, `α_j = N_j/D_j`,
`r = α₀ g̃₀ + α₁ g̃₁` and `x = (y − r)/f`. By parity `Σ_F x = Σ_F k x_k = 0`, so the atoms
reproduce `x` (`inv_coeff`) and the residual of the rows is exactly `r` (`resid_eq`), with
`Σ_F |r|² = |α₀|² A₀ + |α₁|² A₁`, `A_j = Σ_F g̃_j²`. Against the kernel rows `Vq`:
`|N_j − Σ_n â_n Vq_j(n)/2^138| ≤ Δ |â| |g̃_j|` (`N_close`). `in_le` is the resulting bound
`γ₀ |N₀''|² + γ₁ |N₁''|² + ε_in Σ |â|²`. Not RH.
-/

open Finset
open scoped ComplexConjugate
open AEGIS.CvSRelRowDataL43V1 AEGIS.CvSRelRowBoxL43V1 AEGIS.CvSRelRowFormL43V1
  AEGIS.CvSRelRowErrL43V1 AEGIS.CvSRelRowAlgebraV1 AEGIS.CvSRelRowHarmV1 AEGIS.CvSRelRowQL43V1
  AEGIS.CvSRelRowKtL43V1 AEGIS.CvSRelRowOutL43V1 AEGIS.CvSRelRowInvL43V1 AEGIS.CvSRowTailV1
  AEGIS.CvSCrossCertV1 AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSMomentBasisV1

noncomputable section

namespace AEGIS.CvSRelRowInL43V1

set_option maxRecDepth 100000

/-! ## Lists over `F` -/

theorem list_range_sum {R : Type*} [AddCommMonoid R] (g : ℕ → R) (n : ℕ) :
    ((List.range n).map g).sum = ∑ k ∈ range n, g k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem range_F_sum {R : Type*} [AddCommMonoid R] (f : ℤ → R) :
    ∑ k ∈ range 141, f ((k : ℤ) - 70) = ∑ m ∈ F, f m := by
  refine sum_nbij' (fun k => (k : ℤ) - 70) (fun m => (m + 70).toNat) ?_ ?_ ?_ ?_ ?_
  · intro k hk; rw [mem_range] at hk; rw [mem_Icc]; omega
  · intro m hm; rw [mem_Icc] at hm; rw [mem_range]; omega
  · intro k _; omega
  · intro m hm; rw [mem_Icc] at hm; omega
  · intro k _; rfl

theorem list_F_sum {R : Type*} [AddCommMonoid R] (f : ℤ → R) :
    ((List.range 141).map fun (b : ℕ) => f ((b : ℤ) - 70)).sum = ∑ m ∈ F, f m := by
  rw [list_range_sum (fun b : ℕ => f ((b : ℤ) - 70)), range_F_sum]

/-! ## The vectors `g_j` and `g̃_j` -/

def gam : ℝ := 1 / 10 ^ 15

def gr (j : ℕ) (m : ℤ) : ℝ := (if j = 0 then 1 else (m : ℝ)) / fr m

def gtr (j : ℕ) (m : ℤ) : ℝ := (gv j m : ℝ) / 2 ^ 100

theorem fr_le (m : ℤ) : fr m ≤ -1 / 4 := by
  simp only [fr]
  have : 0 ≤ Real.pi ^ 2 * (m : ℝ) ^ 2 := by positivity
  linarith

theorem fr_ne (m : ℤ) : fr m ≠ 0 := by have := fr_le m; intro h; linarith

theorem fr_neg (m : ℤ) : fr (-m) = fr m := by simp only [fr]; push_cast; ring

theorem phi_neg (m : ℤ) : phi (-m) = phi m := by simp only [phi]; ring

theorem phi_lt (m : ℤ) : phi m < 0 := by
  have h : (0 : ℤ) ≤ 9 * SI * m * m := by
    rw [show 9 * SI * m * m = (9 * SI) * (m * m) by ring]
    exact mul_nonneg (by norm_num [SI]) (mul_self_nonneg m)
  simp only [phi]
  have : (0 : ℤ) < 2 ^ 70 := by norm_num
  linarith

theorem g1_eq {m : ℤ} (hm : m ∈ F) : g1 m = 2 ^ 172 / phi m :=
  ok_at (P := fun x => g1 x = 2 ^ 172 / phi x) g_ok hm

theorem neg_mem {m : ℤ} (hm : m ∈ F) : -m ∈ F := by
  rw [mem_Icc] at hm ⊢; omega

theorem g1_neg {m : ℤ} (hm : m ∈ F) : g1 (-m) = g1 m := by
  rw [g1_eq (neg_mem hm), g1_eq hm, phi_neg]

theorem g1_big_ok : (List.range 141).all (fun (i : ℕ) => decide (2 ^ 83 ≤ |g1 ((i : ℤ) - 70)|)) = true := by
  decide +kernel

theorem g1_big {m : ℤ} (hm : m ∈ F) : 2 ^ 83 ≤ |g1 m| :=
  ok_at (P := fun x => 2 ^ 83 ≤ |g1 x|) g1_big_ok hm

theorem gtr_one (m : ℤ) : gtr 1 m = (m : ℝ) * gtr 0 m := by
  simp only [gtr, gv]; push_cast; ring

theorem gr_one (m : ℤ) : gr 1 m = (m : ℝ) * gr 0 m := by
  simp only [gr]; norm_num; ring

theorem gtr0_eq (m : ℤ) : gtr 0 m = (g1 m : ℝ) / 2 ^ 100 := by
  simp [gtr, gv]

theorem gr0_eq (m : ℤ) : gr 0 m = 1 / fr m := by
  simp [gr]

theorem gtr_neg {m : ℤ} (hm : m ∈ F) : gtr 0 (-m) = gtr 0 m := by
  rw [gtr0_eq, gtr0_eq, g1_neg hm]

theorem gr_neg (m : ℤ) : gr 0 (-m) = gr 0 m := by
  rw [gr0_eq, gr0_eq, fr_neg]

/-- `g̃₀` is `1/f` within the relative error `10^-15`. -/
theorem g_close0 {m : ℤ} (hm : m ∈ F) : |gr 0 m - gtr 0 m| ≤ gam * |gtr 0 m| := by
  have hs0 := fr_sub m
  set fh : ℝ := (phi m : ℝ) / 2 ^ 72 with hfh_def
  have hs : |fr m - fh| ≤ theta * |fh| := hs0
  have hphi : (phi m : ℝ) < 0 := by exact_mod_cast phi_lt m
  have hfh : fh < 0 := by rw [hfh_def]; exact div_neg_of_neg_of_pos hphi (by positivity)
  have hth : theta = 1 / 10 ^ 19 := rfl
  have hth0 : 0 < 1 - theta := by rw [hth]; norm_num
  have hthp : 0 ≤ theta := by rw [hth]; norm_num
  have hfr0 : 0 < |fr m| := abs_pos.mpr (fr_ne m)
  have hfh0 : 0 < |fh| := abs_pos.mpr hfh.ne
  have hfr_ge : (1 - theta) * |fh| ≤ |fr m| := by
    have := abs_sub_abs_le_abs_sub fh (fr m)
    rw [abs_sub_comm] at this
    linarith
  have h1 : |1 / fr m - 1 / fh| ≤ theta / (1 - theta) * (1 / |fh|) := by
    have e : 1 / fr m - 1 / fh = (fh - fr m) / (fr m * fh) := by
      field_simp [fr_ne m, hfh.ne]
    rw [e, abs_div, abs_mul, abs_sub_comm, div_le_iff₀ (mul_pos hfr0 hfh0)]
    have e2 : theta / (1 - theta) * (1 / |fh|) * (|fr m| * |fh|) = theta / (1 - theta) * |fr m| := by
      field_simp
    rw [e2]
    have : theta * |fh| ≤ theta / (1 - theta) * |fr m| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hth0]
      have := mul_le_mul_of_nonneg_left hfr_ge hthp
      linarith
    linarith
  have h2 : |1 / fh - gtr 0 m| ≤ 1 / 2 ^ 100 := by
    have r := ediv_err (2 ^ 172) (phi m) (phi_lt m).ne
    have e : 1 / fh - gtr 0 m = (((2 ^ 172 : ℤ) : ℝ) / ((phi m : ℤ) : ℝ) - ((2 ^ 172 / phi m : ℤ) : ℝ)) / 2 ^ 100 := by
      rw [hfh_def, gtr0_eq, g1_eq hm]
      have : ((phi m : ℤ) : ℝ) ≠ 0 := hphi.ne
      push_cast
      field_simp
      ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 100)]
    exact div_le_div_of_nonneg_right r.le (by positivity)
  have hG : 1 / 2 ^ 17 ≤ |gtr 0 m| := by
    have hb := g1_big hm
    rw [gtr0_eq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 100), le_div_iff₀ (by positivity)]
    have : ((2 ^ 83 : ℤ) : ℝ) ≤ |((g1 m : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast hb
    push_cast at this
    have e : (1 : ℝ) / 2 ^ 17 * 2 ^ 100 = 2 ^ 83 := by norm_num
    linarith
  have h3 : 1 / |fh| ≤ |gtr 0 m| + 1 / 2 ^ 100 := by
    have : 1 / |fh| = |1 / fh| := by rw [one_div, one_div, abs_inv]
    rw [this]
    have := abs_sub_abs_le_abs_sub (1 / fh) (gtr 0 m)
    linarith
  have tri : |gr 0 m - gtr 0 m| ≤ |1 / fr m - 1 / fh| + |1 / fh - gtr 0 m| := by
    have e : gr 0 m - gtr 0 m = (1 / fr m - 1 / fh) + (1 / fh - gtr 0 m) := by
      rw [gr0_eq]; ring
    rw [e]; exact abs_add_le _ _
  have hk : theta / (1 - theta) ≤ 2 / 10 ^ 19 := by rw [hth]; norm_num
  have hk0 : 0 ≤ theta / (1 - theta) := by rw [hth]; norm_num
  have hGa := abs_nonneg (gtr 0 m)
  have m1 : theta / (1 - theta) * (1 / |fh|) ≤ 2 / 10 ^ 19 * (|gtr 0 m| + 1 / 2 ^ 100) :=
    mul_le_mul hk h3 (by positivity) (by norm_num)
  simp only [gam]
  linarith

theorem g_close {j : ℕ} (hj : j < 2) {m : ℤ} (hm : m ∈ F) :
    |gr j m - gtr j m| ≤ gam * |gtr j m| := by
  interval_cases j
  · exact g_close0 hm
  · rw [gr_one, gtr_one, ← mul_sub, abs_mul, abs_mul]
    have := g_close0 hm
    have h0 := abs_nonneg (m : ℝ)
    calc |(m : ℝ)| * |gr 0 m - gtr 0 m| ≤ |(m : ℝ)| * (gam * |gtr 0 m|) := mul_le_mul_of_nonneg_left this h0
      _ = gam * (|(m : ℝ)| * |gtr 0 m|) := by ring

/-! ## The norms of `g̃_j` -/

def gtc (j : ℕ) : ℤ → ℂ := fun m => ((gtr j m : ℝ) : ℂ)

def grc (j : ℕ) : ℤ → ℂ := fun m => ((gr j m : ℝ) : ℂ)

def Aj (j : ℕ) : ℝ := ∑ m ∈ F, gtr j m ^ 2

theorem nrm_gtc (j : ℕ) : nrm (gtc j) * nrm (gtc j) = Aj j := by
  rw [nrm_sq]
  refine sum_congr rfl fun m _ => ?_
  rw [gtc, Complex.norm_real, Real.norm_eq_abs, sq_abs]

def A0lit : ℤ := 25717915641775372769817626412773722413965712375139825018729556
def A1lit : ℤ := 10471673010186883139929184767099851336793720089568357635378

theorem A_ok : ((List.range 141).map fun (b : ℕ) => gv 0 ((b : ℤ) - 70) ^ 2).sum = A0lit ∧
    ((List.range 141).map fun (b : ℕ) => gv 1 ((b : ℤ) - 70) ^ 2).sum = A1lit := by
  constructor <;> decide +kernel

theorem Aj_eq {j : ℕ} (hj : j < 2) : Aj j = (if j = 0 then (A0lit : ℝ) else (A1lit : ℝ)) / 2 ^ 200 := by
  have hl : ∀ jj, (((List.range 141).map fun (b : ℕ) => gv jj ((b : ℤ) - 70) ^ 2).sum : ℝ) =
      (Aj jj) * 2 ^ 200 := by
    intro jj
    have e0 : ((((List.range 141).map fun (b : ℕ) => gv jj ((b : ℤ) - 70) ^ 2).sum : ℤ) : ℝ) =
        ((List.range 141).map fun (b : ℕ) => ((gv jj ((b : ℤ) - 70) ^ 2 : ℤ) : ℝ)).sum := by
      rw [Int.cast_list_sum, List.map_map]; rfl
    rw [e0, list_F_sum (fun m => ((gv jj m ^ 2 : ℤ) : ℝ)), Aj, sum_mul]
    refine sum_congr rfl fun m _ => ?_
    simp only [gtr]; push_cast; ring
  interval_cases j
  · have := hl 0; rw [A_ok.1] at this; rw [if_pos rfl, this]; field_simp
  · have := hl 1; rw [A_ok.2] at this; rw [if_neg one_ne_zero, this]; field_simp

theorem Aj_ge {j : ℕ} (hj : j < 2) : 1 / 2 ^ 10 ≤ Aj j := by
  rw [Aj_eq hj]
  interval_cases j <;> norm_num [A0lit, A1lit]

theorem nrm_gtc_ge {j : ℕ} (hj : j < 2) : 1 / 32 ≤ nrm (gtc j) := by
  have h := Aj_ge hj
  rw [← nrm_gtc] at h
  have := nrm_nonneg (gtc j)
  nlinarith

theorem nrm_grc {j : ℕ} (hj : j < 2) : nrm (grc j) ≤ (1 + gam) * nrm (gtc j) :=
  nrm_le_of (by norm_num [gam]) fun m hm => by
    simp only [grc, gtc, Complex.norm_real, Real.norm_eq_abs]
    have := g_close hj hm
    have := abs_sub_abs_le_abs_sub (gr j m) (gtr j m)
    linarith

theorem nrm_grc_sub {j : ℕ} (hj : j < 2) :
    nrm (fun m => grc j m - gtc j m) ≤ gam * nrm (gtc j) :=
  nrm_le_of (by norm_num [gam]) fun m hm => by
    simp only [grc, gtc, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact g_close hj hm

/-- `D_j = Σ_F g̃_j g_j`. -/
def Dj (j : ℕ) : ℝ := ∑ m ∈ F, gtr j m * gr j m

theorem Dj_ge {j : ℕ} (hj : j < 2) : (1 - gam) * Aj j ≤ Dj j := by
  have e : Dj j = Aj j + ∑ m ∈ F, gtr j m * (gr j m - gtr j m) := by
    simp only [Dj, Aj, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    ring
  have hb : ∑ m ∈ F, gtr j m * (gr j m - gtr j m) ≥ -(gam * Aj j) := by
    rw [Aj, mul_sum, ge_iff_le, ← sum_neg_distrib]
    refine sum_le_sum fun m hm => ?_
    have h := g_close hj hm
    have h1 := neg_abs_le (gtr j m * (gr j m - gtr j m))
    rw [abs_mul] at h1
    have h2 : |gtr j m| * |gr j m - gtr j m| ≤ |gtr j m| * (gam * |gtr j m|) :=
      mul_le_mul_of_nonneg_left h (abs_nonneg _)
    have h3 : |gtr j m| * (gam * |gtr j m|) = gam * gtr j m ^ 2 := by
      rw [show |gtr j m| * (gam * |gtr j m|) = gam * (|gtr j m| * |gtr j m|) by ring, ← sq,
        sq_abs]
    linarith
  rw [e]
  linarith

theorem Dj_pos {j : ℕ} (hj : j < 2) : 0 < Dj j := by
  have h1 := Dj_ge hj
  have h2 := Aj_ge hj
  have : 0 < (1 - gam) * Aj j := mul_pos (by norm_num [gam]) (lt_of_lt_of_le (by norm_num) h2)
  linarith

/-! ## Parity -/

theorem sum_gtr1_gr0 : ∑ m ∈ F, gtr 1 m * gr 0 m = 0 :=
  odd_sum (fun m => if m ∈ F then gtr 1 m * gr 0 m else 0) (fun m => by
    by_cases hm : m ∈ F
    · rw [if_pos (neg_mem hm), if_pos hm, gtr_one, gtr_one, gtr_neg hm, gr_neg]
      push_cast; ring
    · have : -m ∉ F := fun h => hm (by simpa using neg_mem h)
      rw [if_neg this, if_neg hm, neg_zero]) |> fun h => by
    rw [← h]; exact sum_congr rfl fun m hm => (if_pos hm).symm

theorem sum_gtr0_gr1 : ∑ m ∈ F, gtr 0 m * gr 1 m = 0 := by
  have e : ∑ m ∈ F, gtr 0 m * gr 1 m = ∑ m ∈ F, gtr 1 m * gr 0 m := by
    refine sum_congr rfl fun m _ => ?_
    rw [gr_one, gtr_one]; ring
  rw [e, sum_gtr1_gr0]

theorem sum_gtr0_gtr1 : ∑ m ∈ F, gtr 0 m * gtr 1 m = 0 :=
  odd_sum (fun m => if m ∈ F then gtr 0 m * gtr 1 m else 0) (fun m => by
    by_cases hm : m ∈ F
    · rw [if_pos (neg_mem hm), if_pos hm, gtr_one, gtr_one, gtr_neg hm]
      push_cast; ring
    · have : -m ∉ F := fun h => hm (by simpa using neg_mem h)
      rw [if_neg this, if_neg hm, neg_zero]) |> fun h => by
    rw [← h]; exact sum_congr rfl fun m hm => (if_pos hm).symm

/-! ## The residual of the low rows -/

def yr (M : ℕ) (c : Fin 139 → ℂ) (m : ℤ) : ℂ := crossRow M (4 / 3) F (acoef c) m

def Nj (M : ℕ) (c : Fin 139 → ℂ) (j : ℕ) : ℂ := ∑ m ∈ F, yr M c m * grc j m

def alj (M : ℕ) (c : Fin 139 → ℂ) (j : ℕ) : ℂ := Nj M c j / ((Dj j : ℝ) : ℂ)

def rr (M : ℕ) (c : Fin 139 → ℂ) (m : ℤ) : ℂ := alj M c 0 * gtc 0 m + alj M c 1 * gtc 1 m

def xx (M : ℕ) (c : Fin 139 → ℂ) (m : ℤ) : ℂ := (yr M c m - rr M c m) / ((fr m : ℝ) : ℂ)

/-- The atom coefficients of the low rows. -/
def lam (M : ℕ) (c : Fin 139 → ℂ) : Fin 139 → ℂ := lamOf (xx M c)

theorem frC_ne (m : ℤ) : ((fr m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast fr_ne m

theorem Dj_ne {j : ℕ} (hj : j < 2) : ((Dj j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Dj_pos hj).ne'

theorem alj_mul {j : ℕ} (hj : j < 2) (M : ℕ) (c : Fin 139 → ℂ) :
    alj M c j * ((Dj j : ℝ) : ℂ) = Nj M c j := by
  rw [alj, div_mul_cancel₀ _ (Dj_ne hj)]

theorem sum_gtc_grc (i j : ℕ) :
    ∑ m ∈ F, gtc i m * grc j m = ((∑ m ∈ F, gtr i m * gr j m : ℝ) : ℂ) := by
  push_cast; rfl

theorem xx_moments (M : ℕ) (c : Fin 139 → ℂ) :
    ∑ k ∈ F, xx M c k = 0 ∧ ∑ k ∈ F, (k : ℂ) * xx M c k = 0 := by
  have e0 : ∀ k, xx M c k = (yr M c k - rr M c k) * grc 0 k := by
    intro k
    simp only [xx, grc, gr0_eq]
    push_cast
    ring
  have e1 : ∀ k : ℤ, (k : ℂ) * xx M c k = (yr M c k - rr M c k) * grc 1 k := by
    intro k
    simp only [xx, grc, gr_one, gr0_eq]
    push_cast
    ring
  have hr : ∀ j, ∑ k ∈ F, rr M c k * grc j k =
      alj M c 0 * ∑ k ∈ F, gtc 0 k * grc j k + alj M c 1 * ∑ k ∈ F, gtc 1 k * grc j k := by
    intro j
    simp only [rr, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    ring
  constructor
  · simp_rw [e0, sub_mul]
    rw [sum_sub_distrib, hr 0, sum_gtc_grc, sum_gtc_grc, sum_gtr1_gr0]
    change Nj M c 0 - (alj M c 0 * ((Dj 0 : ℝ) : ℂ) + alj M c 1 * ((0 : ℝ) : ℂ)) = 0
    rw [alj_mul (by norm_num)]
    simp
  · simp_rw [e1, sub_mul]
    rw [sum_sub_distrib, hr 1, sum_gtc_grc, sum_gtc_grc, sum_gtr0_gr1]
    change Nj M c 1 - (alj M c 0 * ((0 : ℝ) : ℂ) + alj M c 1 * ((Dj 1 : ℝ) : ℂ)) = 0
    rw [alj_mul (by norm_num)]
    simp

/-- **The residual of the low rows is `r`.** -/
theorem resid_eq (M : ℕ) (c : Fin 139 → ℂ) {m : ℤ} (hm : m ∈ F) :
    crossRow M (4 / 3) F (acoef c) m - ∑ i, lam M c i *
      atomRow (4 / 3) (fun i => sinSqSupport (ctr i)) (fun i => sinSqWeight (ctr i)) i m = rr M c m := by
  obtain ⟨h0, h1⟩ := xx_moments M c
  have hinv := inv_coeff (xx M c) h0 h1 hm
  have e : ∑ i, lam M c i *
      atomRow (4 / 3) (fun i => sinSqSupport (ctr i)) (fun i => sinSqWeight (ctr i)) i m =
      (∑ i, lamOf (xx M c) i * wt m i) * ((fr m : ℝ) : ℂ) := by
    rw [sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [atomRow_eq, lam]
    ring
  rw [e, hinv]
  simp only [xx]
  rw [div_mul_cancel₀ _ (frC_ne m)]
  simp only [yr]
  ring

theorem normSq_comb (α β : ℂ) (u v : ℝ) :
    ‖α * (u : ℂ) + β * (v : ℂ)‖ ^ 2 =
      ‖α‖ ^ 2 * u ^ 2 + ‖β‖ ^ 2 * v ^ 2 + 2 * (α * conj β).re * (u * v) := by
  rw [Complex.sq_norm, Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_ofReal, Complex.sq_norm, Complex.sq_norm]
  have : (α * (u : ℂ) * conj (β * (v : ℂ))).re = (α * conj β).re * (u * v) := by
    rw [map_mul, Complex.conj_ofReal]
    rw [show α * (u : ℂ) * (conj β * (v : ℂ)) = (α * conj β) * ((u * v : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.re_mul_ofReal]
  rw [this]
  ring

/-- `Σ_F |r|² = |α₀|² A₀ + |α₁|² A₁`. -/
theorem resid_energy (M : ℕ) (c : Fin 139 → ℂ) :
    ∑ m ∈ F, ‖rr M c m‖ ^ 2 = ‖alj M c 0‖ ^ 2 * Aj 0 + ‖alj M c 1‖ ^ 2 * Aj 1 := by
  simp only [rr, gtc]
  simp_rw [normSq_comb]
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, sum_gtr0_gtr1]
  simp only [Aj]
  ring

/-! ## The kernel rows against `N_j` -/

def piU : ℝ := 31416 / 10000
def dpi : ℝ := 1 / 10 ^ 19

theorem pi_le : Real.pi ≤ piU := by
  have := Real.pi_lt_d20; norm_num [piU] at this ⊢; linarith

theorem pi_close : |Real.pi - (piq : ℝ) / 2 ^ 64| ≤ dpi := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  rw [abs_le]
  constructor <;> norm_num [piq, dpi] at h1 h2 ⊢ <;> linarith

def Dl : ℝ := 2 * piU * (RA * theta * (1 + gam) + RE * (1 + gam) + 987 * gam) + 2 * dpi * 987 +
  384 / 2 ^ 138

theorem Vq_eq {j : ℕ} (hj : j < 2) {n : ℤ} (hn : n ∈ F) :
    Vq j n = 2 * piq * (∑ m ∈ F, Et n m * gv j m) / 2 ^ 154 := by
  have h : Vq j n = Vraw j n := by
    interval_cases j
    · exact ok_at (P := fun x => Vq 0 x = Vraw 0 x) V_ok0 hn
    · exact ok_at (P := fun x => Vq 1 x = Vraw 1 x) V_ok1 hn
  rw [h, Vraw, list_F_sum (fun m => Et n m * gv j m)]

/-- `N_j` as a bilinear form of the actual coefficients. -/
theorem Nj_eq (M : ℕ) (c : Fin 139 → ℂ) (j : ℕ) :
    Nj M c j = ((2 * Real.pi : ℝ) : ℂ) *
      ∑ n ∈ F, ∑ m ∈ F, acoef c n * conj (grc j m) * (cvsEntry M (4 / 3) n m : ℂ) := by
  simp only [Nj, yr, crossRow, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun n _ => ?_
  rw [cvsEntry_symm M (by norm_num) m n]
  simp only [grc, Complex.conj_ofReal]
  push_cast
  ring

/-- The unrounded kernel row `2 π̂ Σ_m Ê(n,m) g̃_j(m)`. -/
def Sh (j : ℕ) (n : ℤ) : ℝ := 2 * ((piq : ℝ) / 2 ^ 64) * ∑ m ∈ F, (Et n m : ℝ) / 2 ^ 128 * gtr j m

theorem Sh_round {j : ℕ} (hj : j < 2) {n : ℤ} (hn : n ∈ F) :
    |Sh j n - (Vq j n : ℝ) / 2 ^ 138| ≤ 1 / 2 ^ 138 := by
  set X : ℤ := 2 * piq * (∑ m ∈ F, Et n m * gv j m)
  have r := ediv_err X (2 ^ 154) (by norm_num)
  have hA : Sh j n = (X : ℝ) / ((2 ^ 154 : ℤ) : ℝ) / 2 ^ 138 := by
    simp only [Sh, X, gtr]
    push_cast
    rw [mul_sum, mul_sum, sum_div, sum_div]
    refine sum_congr rfl fun m _ => ?_
    ring
  have hV : (Vq j n : ℝ) = ((X / 2 ^ 154 : ℤ) : ℝ) := by rw [Vq_eq hj hn]
  rw [hA, hV, show (X : ℝ) / ((2 ^ 154 : ℤ) : ℝ) / 2 ^ 138 - ((X / 2 ^ 154 : ℤ) : ℝ) / 2 ^ 138 =
    ((X : ℝ) / ((2 ^ 154 : ℤ) : ℝ) - ((X / 2 ^ 154 : ℤ) : ℝ)) / 2 ^ 138 by ring,
    abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 138)]
  exact div_le_div_of_nonneg_right r.le (by positivity)

theorem N_close (M : ℕ) (hM : 3 ≤ M) (c : Fin 139 → ℂ) {j : ℕ} (hj : j < 2) :
    ‖Nj M c j - ∑ n ∈ F, ahat c n * (((Vq j n : ℝ) / 2 ^ 138 : ℝ) : ℂ)‖ ≤
      Dl * nrm (ahat c) * nrm (gtc j) := by
  have split : Nj M c j - ∑ n ∈ F, ahat c n * (((Vq j n : ℝ) / 2 ^ 138 : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, (acoef c n - ahat c n) * conj (grc j m) *
          (cvsEntry M (4 / 3) n m : ℂ)) +
      ((2 * Real.pi : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (grc j m) *
          ((cvsEntry M (4 / 3) n m - (Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ)) +
      ((2 * Real.pi : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (grc j m - gtc j m) *
          (((Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ)) +
      ((2 * (Real.pi - (piq : ℝ) / 2 ^ 64) : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (gtc j m) *
          (((Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ)) +
      ∑ n ∈ F, ahat c n * ((Sh j n - (Vq j n : ℝ) / 2 ^ 138 : ℝ) : ℂ) := by
    rw [Nj_eq]
    have hSh : ∑ n ∈ F, ahat c n * ((Sh j n : ℝ) : ℂ) =
        ((2 * ((piq : ℝ) / 2 ^ 64) : ℝ) : ℂ) * ∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (gtc j m) *
          (((Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ) := by
      rw [mul_sum]
      refine sum_congr rfl fun n _ => ?_
      rw [Sh, Complex.ofReal_mul, Complex.ofReal_sum]
      simp only [mul_sum]
      refine sum_congr rfl fun m _ => ?_
      simp only [gtc, Complex.conj_ofReal]
      push_cast
      ring
    have e4 : ∑ n ∈ F, ahat c n * ((Sh j n - (Vq j n : ℝ) / 2 ^ 138 : ℝ) : ℂ) =
        ∑ n ∈ F, ahat c n * ((Sh j n : ℝ) : ℂ) -
          ∑ n ∈ F, ahat c n * (((Vq j n : ℝ) / 2 ^ 138 : ℝ) : ℂ) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun n _ => ?_
      push_cast; ring
    rw [e4, hSh]
    have key : ((2 * Real.pi : ℝ) : ℂ) * ∑ n ∈ F, ∑ m ∈ F, acoef c n * conj (grc j m) *
          (cvsEntry M (4 / 3) n m : ℂ) =
        ((2 * Real.pi : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, (acoef c n - ahat c n) * conj (grc j m) *
          (cvsEntry M (4 / 3) n m : ℂ)) +
        ((2 * Real.pi : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (grc j m) *
          ((cvsEntry M (4 / 3) n m - (Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ)) +
        ((2 * Real.pi : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (grc j m - gtc j m) *
          (((Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ)) +
        ((2 * (Real.pi - (piq : ℝ) / 2 ^ 64) : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (gtc j m) *
          (((Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ)) +
        ((2 * ((piq : ℝ) / 2 ^ 64) : ℝ) : ℂ) * ∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (gtc j m) *
          (((Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ) := by
      simp only [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_
      simp only [map_sub]
      push_cast
      ring
    rw [key]
    ring
  rw [split]
  set b := ahat c
  -- the five bounds
  have hF : ∀ n ∈ F, -70 ≤ n ∧ n ≤ 70 := fun n hn => mem_Icc.mp hn
  have hRA : (0 : ℝ) ≤ RA := by norm_num [RA]
  have b0 := bilin_le (fun n m => cvsEntry M (4 / 3) n m) (fun _ _ => (6 : ℝ)) hRA (fun n hn m hm =>
    E_abs_le hM (hF n hn).1 (hF n hn).2 (hF m hm).1 (hF m hm).2) (fun _ _ _ _ => rfl)
    (fun n _ => by simp [RA]; norm_num) (fun n => acoef c n - b n) (grc j)
  have hRE : (0 : ℝ) ≤ RE := by simp only [RE, rhoD, am, Cu, rho, dC, tm, hB2]; norm_num [rDq, rhoq, tmq]
  have b1 := bilin_le (fun n m => cvsEntry M (4 / 3) n m - (Et n m : ℝ) / 2 ^ 128)
    (fun n m => |cvsEntry M (4 / 3) n m - (Et n m : ℝ) / 2 ^ 128|) hRE
    (fun n _ m _ => le_rfl) (fun n _ m _ => by
      rw [cvsEntry_symm M (by norm_num) n m, AEGIS.CvSRelRowPsdL43V1.Et_symm n m])
    (fun n hn => RE_row hM hn) b (grc j)
  have b2 := bilin_le (fun n m => (Et n m : ℝ) / 2 ^ 128) (fun _ _ => (7 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 987) (fun n hn m hm =>
    Et_abs_le hM (hF n hn).1 (hF n hn).2 (hF m hm).1 (hF m hm).2) (fun _ _ _ _ => rfl)
    (fun n _ => by simp; norm_num) b (fun m => grc j m - gtc j m)
  have b3 := bilin_le (fun n m => (Et n m : ℝ) / 2 ^ 128) (fun _ _ => (7 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 987) (fun n hn m hm =>
    Et_abs_le hM (hF n hn).1 (hF n hn).2 (hF m hm).1 (hF m hm).2) (fun _ _ _ _ => rfl)
    (fun n _ => by simp; norm_num) b (gtc j)
  have b4 : ‖∑ n ∈ F, b n * ((Sh j n - (Vq j n : ℝ) / 2 ^ 138 : ℝ) : ℂ)‖ ≤ 12 / 2 ^ 138 * nrm b := by
    have h := cs_sum F b (fun n => Sh j n - (Vq j n : ℝ) / 2 ^ 138)
    have hs : ∑ n ∈ F, (Sh j n - (Vq j n : ℝ) / 2 ^ 138) ^ 2 ≤ (12 / 2 ^ 138) ^ 2 := by
      calc ∑ n ∈ F, (Sh j n - (Vq j n : ℝ) / 2 ^ 138) ^ 2 ≤ ∑ _n ∈ F, (1 / 2 ^ 138 : ℝ) ^ 2 :=
            sum_le_sum fun n hn => by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (Sh_round hj hn) 2
        _ ≤ (12 / 2 ^ 138) ^ 2 := by simp; norm_num
    have hb2 := nrm_sq b
    have : ‖∑ n ∈ F, b n * ((Sh j n - (Vq j n : ℝ) / 2 ^ 138 : ℝ) : ℂ)‖ ^ 2 ≤ (12 / 2 ^ 138 * nrm b) ^ 2 := by
      calc _ ≤ (∑ n ∈ F, ‖b n‖ ^ 2) * ∑ n ∈ F, (Sh j n - (Vq j n : ℝ) / 2 ^ 138) ^ 2 := h
        _ ≤ (nrm b * nrm b) * (12 / 2 ^ 138) ^ 2 := by
            rw [hb2]; exact mul_le_mul_of_nonneg_left hs (sum_nonneg fun _ _ => sq_nonneg _)
        _ = (12 / 2 ^ 138 * nrm b) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by have := nrm_nonneg b; positivity) two_ne_zero).mp this
  -- assemble
  have hd : nrm (fun n => acoef c n - b n) ≤ theta * nrm b :=
    nrm_le_of theta_nonneg fun n _ => a_sub_ahat c n
  have hg := nrm_grc hj
  have hgs := nrm_grc_sub hj
  have hg1 := nrm_gtc_ge hj
  have hb0 := nrm_nonneg b
  have hgt0 := nrm_nonneg (gtc j)
  have hpi := pi_le
  have hpi0 := Real.pi_pos
  have hdp := pi_close
  have hgam : (0 : ℝ) ≤ gam := by norm_num [gam]
  have hth := theta_nonneg
  have n0 : ‖((2 * Real.pi : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, (acoef c n - b n) * conj (grc j m) *
      (cvsEntry M (4 / 3) n m : ℂ))‖ ≤ 2 * piU * (RA * theta * (1 + gam)) * (nrm b * nrm (gtc j)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : RA * nrm (fun n => acoef c n - b n) * nrm (grc j) ≤ RA * (theta * nrm b) * ((1 + gam) * nrm (gtc j)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd hRA) hg (nrm_nonneg _) (by positivity)
    calc _ ≤ 2 * Real.pi * (RA * (theta * nrm b) * ((1 + gam) * nrm (gtc j))) :=
          mul_le_mul_of_nonneg_left (b0.trans this) (by positivity)
      _ ≤ 2 * piU * (RA * (theta * nrm b) * ((1 + gam) * nrm (gtc j))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  have n1 : ‖((2 * Real.pi : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, b n * conj (grc j m) *
      ((cvsEntry M (4 / 3) n m - (Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ))‖ ≤
      2 * piU * (RE * (1 + gam)) * (nrm b * nrm (gtc j)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : RE * nrm b * nrm (grc j) ≤ RE * nrm b * ((1 + gam) * nrm (gtc j)) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    calc _ ≤ 2 * Real.pi * (RE * nrm b * ((1 + gam) * nrm (gtc j))) :=
          mul_le_mul_of_nonneg_left (b1.trans this) (by positivity)
      _ ≤ 2 * piU * (RE * nrm b * ((1 + gam) * nrm (gtc j))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  have n2 : ‖((2 * Real.pi : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, b n * conj (grc j m - gtc j m) *
      (((Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ))‖ ≤ 2 * piU * (987 * gam) * (nrm b * nrm (gtc j)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : 987 * nrm b * nrm (fun m => grc j m - gtc j m) ≤ 987 * nrm b * (gam * nrm (gtc j)) :=
      mul_le_mul_of_nonneg_left hgs (by positivity)
    calc _ ≤ 2 * Real.pi * (987 * nrm b * (gam * nrm (gtc j))) :=
          mul_le_mul_of_nonneg_left (b2.trans this) (by positivity)
      _ ≤ 2 * piU * (987 * nrm b * (gam * nrm (gtc j))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  have n3 : ‖((2 * (Real.pi - (piq : ℝ) / 2 ^ 64) : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, b n * conj (gtc j m) *
      (((Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ))‖ ≤ 2 * dpi * 987 * (nrm b * nrm (gtc j)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
    calc _ ≤ 2 * dpi * (987 * nrm b * nrm (gtc j)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hdp (by norm_num)) b3 (norm_nonneg _) (by norm_num [dpi])
      _ = _ := by ring
  have n4 : ‖∑ n ∈ F, b n * ((Sh j n - (Vq j n : ℝ) / 2 ^ 138 : ℝ) : ℂ)‖ ≤
      384 / 2 ^ 138 * (nrm b * nrm (gtc j)) := by
    have : 12 / 2 ^ 138 * nrm b ≤ 384 / 2 ^ 138 * (nrm b * nrm (gtc j)) := by
      have := mul_le_mul_of_nonneg_left hg1 hb0
      have e : 384 / 2 ^ 138 * (nrm b * nrm (gtc j)) = 12 / 2 ^ 138 * (32 * (nrm b * nrm (gtc j))) := by ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith
    linarith
  set A0 := ((2 * Real.pi : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, (acoef c n - b n) * conj (grc j m) *
      (cvsEntry M (4 / 3) n m : ℂ))
  set A1 := ((2 * Real.pi : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, b n * conj (grc j m) *
      ((cvsEntry M (4 / 3) n m - (Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ))
  set A2 := ((2 * Real.pi : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, b n * conj (grc j m - gtc j m) *
      (((Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ))
  set A3 := ((2 * (Real.pi - (piq : ℝ) / 2 ^ 64) : ℝ) : ℂ) * (∑ n ∈ F, ∑ m ∈ F, b n * conj (gtc j m) *
      (((Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ))
  set A4 := ∑ n ∈ F, b n * ((Sh j n - (Vq j n : ℝ) / 2 ^ 138 : ℝ) : ℂ)
  have t1 := norm_add_le (A0 + A1 + A2 + A3) A4
  have t2 := norm_add_le (A0 + A1 + A2) A3
  have t3 := norm_add_le (A0 + A1) A2
  have t4 := norm_add_le A0 A1
  simp only [Dl]
  linarith [n0, n1, n2, n3, n4]

/-! ## The bound on the low rows -/

def epsIn : ℝ := 2 * ((1 + 1 / eta) * Dl ^ 2 / (1 - gam) ^ 2)

theorem gamma_ok0 : (1 + eta) / ((1 - gam) ^ 2 * Aj 0) ≤ (G1q : ℝ) / 2 ^ 64 := by
  rw [Aj_eq (by norm_num), if_pos rfl]
  norm_num [eta, gam, A0lit, G1q]

theorem gamma_ok1 : (1 + eta) / ((1 - gam) ^ 2 * Aj 1) ≤ (G2q : ℝ) / 2 ^ 64 := by
  rw [Aj_eq (by norm_num), if_neg one_ne_zero]
  norm_num [eta, gam, A1lit, G2q]

theorem Dl_nonneg : 0 ≤ Dl := by
  have : 0 ≤ RE := by simp only [RE, rhoD, am, Cu, rho, dC, tm, hB2]; norm_num [rDq, rhoq, tmq]
  simp only [Dl, piU, RA, theta, gam, dpi]
  positivity

theorem term_le (M : ℕ) (hM : 3 ≤ M) (c : Fin 139 → ℂ) {j : ℕ} (hj : j < 2) {γ : ℝ}
    (hγ : (1 + eta) / ((1 - gam) ^ 2 * Aj j) ≤ γ) :
    ‖alj M c j‖ ^ 2 * Aj j ≤ γ * ‖∑ n ∈ F, ahat c n * (((Vq j n : ℝ) / 2 ^ 138 : ℝ) : ℂ)‖ ^ 2 +
      (1 + 1 / eta) * Dl ^ 2 / (1 - gam) ^ 2 * (nrm (ahat c) * nrm (ahat c)) := by
  set N := Nj M c j
  set N2 := ∑ n ∈ F, ahat c n * (((Vq j n : ℝ) / 2 ^ 138 : ℝ) : ℂ)
  set D := Dj j
  set A := Aj j
  set nb := nrm (ahat c)
  have hDpos : 0 < D := Dj_pos hj
  have hA : 1 / 2 ^ 10 ≤ A := Aj_ge hj
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hD : (1 - gam) * A ≤ D := Dj_ge hj
  have hg1 : 0 < 1 - gam := by norm_num [gam]
  have hal : ‖alj M c j‖ ^ 2 = ‖N‖ ^ 2 / D ^ 2 := by
    rw [alj, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hDpos, div_pow]
  have hsplit : ‖N‖ ^ 2 ≤ (1 + eta) * ‖N2‖ ^ 2 + (1 + 1 / eta) * ‖N - N2‖ ^ 2 := by
    have := normSq_add_le N2 (N - N2) eta_pos
    rwa [add_sub_cancel] at this
  have hc : ‖N - N2‖ ^ 2 ≤ Dl ^ 2 * (nb * nb) * A := by
    have h := N_close M hM c hj
    have h0 : 0 ≤ Dl * nb * nrm (gtc j) := by
      have := Dl_nonneg; have := nrm_nonneg (ahat c); have := nrm_nonneg (gtc j); positivity
    have := pow_le_pow_left₀ (norm_nonneg _) h 2
    have hA' : A = nrm (gtc j) * nrm (gtc j) := (nrm_gtc j).symm
    rw [hA']
    calc ‖N - N2‖ ^ 2 ≤ (Dl * nb * nrm (gtc j)) ^ 2 := this
      _ = Dl ^ 2 * (nb * nb) * (nrm (gtc j) * nrm (gtc j)) := by ring
  set k := 1 / ((1 - gam) ^ 2 * A)
  have hk0 : 0 < k := by positivity
  have hAD : A / D ^ 2 ≤ k := by
    have h1 : ((1 - gam) * A) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (by positivity) hD 2
    calc A / D ^ 2 ≤ A / ((1 - gam) * A) ^ 2 := div_le_div_of_nonneg_left hA0.le (by positivity) h1
      _ = k := by simp only [k]; field_simp
  have hkA : k * A = 1 / (1 - gam) ^ 2 := by simp only [k]; field_simp
  have hγk : (1 + eta) * k ≤ γ := by simp only [k]; rw [← mul_one_div] at hγ; linarith [hγ]
  have hN2 := sq_nonneg ‖N2‖
  have hN := sq_nonneg ‖N‖
  calc ‖alj M c j‖ ^ 2 * A = ‖N‖ ^ 2 * (A / D ^ 2) := by rw [hal]; ring
    _ ≤ ‖N‖ ^ 2 * k := mul_le_mul_of_nonneg_left hAD hN
    _ ≤ ((1 + eta) * ‖N2‖ ^ 2 + (1 + 1 / eta) * (Dl ^ 2 * (nb * nb) * A)) * k := by
        refine mul_le_mul_of_nonneg_right ?_ hk0.le
        have : (1 + 1 / eta) * ‖N - N2‖ ^ 2 ≤ (1 + 1 / eta) * (Dl ^ 2 * (nb * nb) * A) :=
          mul_le_mul_of_nonneg_left hc (by norm_num [eta])
        linarith
    _ = (1 + eta) * k * ‖N2‖ ^ 2 + (1 + 1 / eta) * Dl ^ 2 * (nb * nb) * (k * A) := by ring
    _ ≤ γ * ‖N2‖ ^ 2 + (1 + 1 / eta) * Dl ^ 2 / (1 - gam) ^ 2 * (nb * nb) := by
        rw [hkA]
        have := mul_le_mul_of_nonneg_right hγk hN2
        have e : (1 + 1 / eta) * Dl ^ 2 * (nb * nb) * (1 / (1 - gam) ^ 2) =
            (1 + 1 / eta) * Dl ^ 2 / (1 - gam) ^ 2 * (nb * nb) := by ring
        linarith

/-- **The low rows.** -/
theorem in_le (M : ℕ) (hM : 3 ≤ M) (c : Fin 139 → ℂ) :
    ∑ m ∈ F, ‖crossRow M (4 / 3) F (acoef c) m - ∑ i, lam M c i *
        atomRow (4 / 3) (fun i => sinSqSupport (ctr i)) (fun i => sinSqWeight (ctr i)) i m‖ ^ 2 ≤
      (G1q : ℝ) / 2 ^ 64 * ‖∑ n ∈ F, ahat c n * (((Vq 0 n : ℝ) / 2 ^ 138 : ℝ) : ℂ)‖ ^ 2 +
      (G2q : ℝ) / 2 ^ 64 * ‖∑ n ∈ F, ahat c n * (((Vq 1 n : ℝ) / 2 ^ 138 : ℝ) : ℂ)‖ ^ 2 +
      epsIn * ∑ n ∈ F, ‖ahat c n‖ ^ 2 := by
  rw [sum_congr rfl fun m hm => by rw [resid_eq M c hm], resid_energy, ← nrm_sq]
  have t0 := term_le M hM c (j := 0) (by norm_num) gamma_ok0
  have t1 := term_le M hM c (j := 1) (by norm_num) gamma_ok1
  simp only [epsIn]
  linarith

end AEGIS.CvSRelRowInL43V1

end

#print axioms AEGIS.CvSRelRowInL43V1.g_close
#print axioms AEGIS.CvSRelRowInL43V1.Dj_pos
#print axioms AEGIS.CvSRelRowInL43V1.sum_gtr0_gtr1
#print axioms AEGIS.CvSRelRowInL43V1.resid_eq
#print axioms AEGIS.CvSRelRowInL43V1.resid_energy
#print axioms AEGIS.CvSRelRowInL43V1.N_close
#print axioms AEGIS.CvSRelRowInL43V1.in_le
