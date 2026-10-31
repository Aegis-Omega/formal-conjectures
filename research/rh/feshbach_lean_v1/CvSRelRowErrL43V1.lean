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
import CvSRelRowBoxL43V1
import CvSRelRowHarmV1

/-!
# The CvS matrix at `L = 4/3` against its integer midpoint `Et/2^128`

* `tau_low`, `tau_all`: `|τ_n − τ̂_n| ≤ ρ` and `|τ̂_n| ≤ t_max` (`|n| ≤ 70`; also `|n| ≤ 200`);
* `C_bounds`: `2/(3π²) ≤ C⁺` and `|2/(3π²) − Cq/2^64| ≤ 10^-18`;
* `E_err_off`, `E_err_diag`: entrywise errors `2a/|n − m| + 2^-128` and `ρ_D`;
* `RE_row`: every row sum of `|E − Et/2^128|` over `F = [−70, 70]` is at most `RE`
  (harmonic row sums kernel-checked through `hupN`);
* `E_abs_le`, `Et_abs_le`: crude entry bounds `6`, `7`.
Not RH.
-/

open Finset
open AEGIS.CvSRelRowDataL43V1 AEGIS.CvSRelRowBoxL43V1 AEGIS.CvSRelRowHarmV1 AEGIS.CvSRowTailV1
  AEGIS.CvSLowBlockMatrixV1

noncomputable section

namespace AEGIS.CvSRelRowErrL43V1

/-! ## Constants -/

def rho : ℝ := (rhoq : ℝ) / 2 ^ 49
def rhoA : ℝ := (max rhoq rhoHq : ℤ) / 2 ^ 49
def rhoD : ℝ := (rDq : ℝ) / 2 ^ 49
def tm : ℝ := (tmq : ℝ) / 2 ^ 49
def tmA : ℝ := (max tmq tmHq : ℤ) / 2 ^ 49
def Cu : ℝ := 6755 / 100000
def dC : ℝ := 1 / 10 ^ 18
def am : ℝ := Cu * rho + dC * tm
def hB2 : ℕ := 178300205636331570812
def RE : ℝ := rhoD + 2 * am * ((hB2 : ℝ) / 2 ^ 64) + 140 / 2 ^ 128

theorem hup_ok : (List.range 141).all (fun k => decide (hupN k + hupN (140 - k) ≤ hB2)) = true := by
  decide +kernel

theorem hup_le {n : ℤ} (h1 : -70 ≤ n) (h2 : n ≤ 70) :
    (harmonic (n + 70).toNat : ℝ) + harmonic (70 - n).toNat ≤ (hB2 : ℝ) / 2 ^ 64 := by
  have h := hup_ok
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have hk := h (n + 70).toNat (by omega)
  rw [show 140 - (n + 70).toNat = (70 - n).toNat by omega] at hk
  have hk' : ((hupN (n + 70).toNat : ℝ) + hupN (70 - n).toNat) ≤ hB2 := by exact_mod_cast hk
  have a1 := harmonic_le_hup (n + 70).toNat
  have a2 := harmonic_le_hup (70 - n).toNat
  have : ((hupN (n + 70).toNat : ℝ) + hupN (70 - n).toNat) / 2 ^ 64 ≤ (hB2 : ℝ) / 2 ^ 64 :=
    div_le_div_of_nonneg_right hk' (by positivity)
  rw [add_div] at this
  linarith

/-! ## The boxes as real bounds -/

theorem tq_abs (n : ℤ) : |tq n| = |tLit.getD n.natAbs 0| := by
  simp only [tq]
  split_ifs with h
  · rw [show n.toNat = n.natAbs by omega]
  · rw [abs_neg, show (-n).toNat = n.natAbs by omega]

theorem tau_low {M : ℕ} (hM : 3 ≤ M) {n : ℤ} (h1 : -70 ≤ n) (h2 : n ≤ 70) :
    |tau M (4 / 3) n - (tq n : ℝ) / 2 ^ 49| ≤ rho ∧ |(tq n : ℝ) / 2 ^ 49| ≤ tm := by
  have hb := tau_box hM (n := n) (by omega)
  obtain ⟨-, hr, ht, -⟩ := max_low (k := n.natAbs) (by omega)
  constructor
  · refine hb.trans ?_
    simp only [rho]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hr) (by positivity)
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 49)]
    simp only [tm]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have : |tq n| ≤ tmq := by rw [tq_abs]; exact ht
    exact_mod_cast this

theorem tau_all {M : ℕ} (hM : 3 ≤ M) {n : ℤ} (h : n.natAbs ≤ 200) :
    |tau M (4 / 3) n - (tq n : ℝ) / 2 ^ 49| ≤ rhoA ∧ |(tq n : ℝ) / 2 ^ 49| ≤ tmA := by
  have hb := tau_box hM h
  obtain ⟨-, hr, ht⟩ := max_all (k := n.natAbs) h
  constructor
  · refine hb.trans ?_
    simp only [rhoA]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hr) (by positivity)
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 49)]
    simp only [tmA]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have : |tq n| ≤ max tmq tmHq := by rw [tq_abs]; exact ht
    exact_mod_cast this

theorem tau_abs_all {M : ℕ} (hM : 3 ≤ M) {n : ℤ} (h : n.natAbs ≤ 200) :
    |tau M (4 / 3) n| ≤ 12 := by
  obtain ⟨h1, h2⟩ := tau_all hM h
  have e : tau M (4 / 3) n = (tau M (4 / 3) n - (tq n : ℝ) / 2 ^ 49) + (tq n : ℝ) / 2 ^ 49 := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have : rhoA + tmA ≤ 12 := by norm_num [rhoA, tmA, rhoq, rhoHq, tmq, tmHq]
  linarith

theorem C_bounds : 2 / (3 * Real.pi ^ 2) ≤ Cu ∧ |2 / (3 * Real.pi ^ 2) - (Cq : ℝ) / 2 ^ 64| ≤ dC := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  have l : (3.14159265358979323846 : ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith
  have u : Real.pi ^ 2 < (3.14159265358979323847 : ℝ) ^ 2 := by nlinarith
  have hp : 0 < 3 * Real.pi ^ 2 := by positivity
  refine ⟨?_, abs_le.mpr ⟨?_, ?_⟩⟩
  · rw [div_le_iff₀ hp]; norm_num [Cu] at l ⊢; nlinarith
  · have : (Cq : ℝ) / 2 ^ 64 - dC ≤ 2 / (3 * Real.pi ^ 2) := by
      rw [le_div_iff₀ hp]; norm_num [Cq, dC] at u ⊢; nlinarith
    linarith
  · have : 2 / (3 * Real.pi ^ 2) ≤ (Cq : ℝ) / 2 ^ 64 + dC := by
      rw [div_le_iff₀ hp]; norm_num [Cq, dC] at l ⊢; nlinarith
    linarith

/-! ## Entry errors -/

theorem E_err_lt {M : ℕ} (hM : 3 ≤ M) {n m : ℤ} (hn1 : -70 ≤ n) (hn2 : n ≤ 70) (hm1 : -70 ≤ m)
    (hm2 : m ≤ 70) (hmn : m < n) :
    |cvsEntry M (4 / 3) n m - (Et n m : ℝ) / 2 ^ 128| ≤ 2 * am / |(n : ℝ) - m| + 1 / 2 ^ 128 := by
  have hk : (0 : ℝ) < (n : ℝ) - m := by
    have : (m : ℝ) < n := by exact_mod_cast hmn
    linarith
  have hkz : (0 : ℤ) < n - m := by omega
  rw [E_off M (by omega : n ≠ m), abs_of_pos hk]
  have he : Et n m = Cq * (tq n - tq m) * 2 ^ 15 / (n - m) := by
    simp only [Et, if_neg (by omega : n ≠ m), if_pos hmn]
  rw [he]
  set X : ℤ := Cq * (tq n - tq m) * 2 ^ 15
  have hr := ediv_err X (n - m) (by omega)
  obtain ⟨hn, htn⟩ := tau_low hM hn1 hn2
  obtain ⟨hm, htm⟩ := tau_low hM hm1 hm2
  obtain ⟨hC1, hC2⟩ := C_bounds
  set C := 2 / (3 * Real.pi ^ 2)
  have hC0 : 0 ≤ C := by positivity
  have hX : (X : ℝ) / ((n - m : ℤ) : ℝ) / 2 ^ 128 =
      (Cq : ℝ) / 2 ^ 64 * ((tq n : ℝ) / 2 ^ 49 - (tq m : ℝ) / 2 ^ 49) / ((n : ℝ) - m) := by
    simp only [X]; push_cast; field_simp; ring
  have split : C * ((tau M (4 / 3) n - tau M (4 / 3) m) / ((n : ℝ) - m)) -
      ((X / (n - m) : ℤ) : ℝ) / 2 ^ 128 =
      (C * (tau M (4 / 3) n - tau M (4 / 3) m) -
        (Cq : ℝ) / 2 ^ 64 * ((tq n : ℝ) / 2 ^ 49 - (tq m : ℝ) / 2 ^ 49)) / ((n : ℝ) - m) +
      ((X : ℝ) / ((n - m : ℤ) : ℝ) - ((X / (n - m) : ℤ) : ℝ)) / 2 ^ 128 := by
    rw [sub_div ((X : ℝ) / _), hX]; field_simp; ring
  rw [split]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hk]
    refine div_le_div_of_nonneg_right ?_ hk.le
    have e : C * (tau M (4 / 3) n - tau M (4 / 3) m) -
        (Cq : ℝ) / 2 ^ 64 * ((tq n : ℝ) / 2 ^ 49 - (tq m : ℝ) / 2 ^ 49) =
        C * ((tau M (4 / 3) n - (tq n : ℝ) / 2 ^ 49) - (tau M (4 / 3) m - (tq m : ℝ) / 2 ^ 49)) +
          (C - (Cq : ℝ) / 2 ^ 64) * ((tq n : ℝ) / 2 ^ 49 - (tq m : ℝ) / 2 ^ 49) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hC0]
    have a1 : |(tau M (4 / 3) n - (tq n : ℝ) / 2 ^ 49) - (tau M (4 / 3) m - (tq m : ℝ) / 2 ^ 49)| ≤
        2 * rho := by
      refine (abs_sub _ _).trans ?_; linarith
    have a2 : |(tq n : ℝ) / 2 ^ 49 - (tq m : ℝ) / 2 ^ 49| ≤ 2 * tm := by
      refine (abs_sub _ _).trans ?_; linarith
    have r0 : 0 ≤ rho := by simp only [rho]; norm_num [rhoq]
    have t0 : 0 ≤ tm := by simp only [tm]; norm_num [tmq]
    have d0 : 0 ≤ dC := by simp only [dC]; norm_num
    have b1 : C * |(tau M (4 / 3) n - (tq n : ℝ) / 2 ^ 49) - (tau M (4 / 3) m - (tq m : ℝ) / 2 ^ 49)|
        ≤ Cu * (2 * rho) := mul_le_mul hC1 a1 (abs_nonneg _) (by simp only [Cu]; norm_num)
    have b2 : |C - (Cq : ℝ) / 2 ^ 64| * |(tq n : ℝ) / 2 ^ 49 - (tq m : ℝ) / 2 ^ 49| ≤ dC * (2 * tm) :=
      mul_le_mul hC2 a2 (abs_nonneg _) d0
    simp only [am]
    linarith
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 128)]
    exact div_le_div_of_nonneg_right hr.le (by positivity)

theorem E_err_off {M : ℕ} (hM : 3 ≤ M) {n m : ℤ} (hn1 : -70 ≤ n) (hn2 : n ≤ 70) (hm1 : -70 ≤ m)
    (hm2 : m ≤ 70) (hmn : m ≠ n) :
    |cvsEntry M (4 / 3) n m - (Et n m : ℝ) / 2 ^ 128| ≤ 2 * am / |(n : ℝ) - m| + 1 / 2 ^ 128 := by
  rcases lt_or_gt_of_ne hmn with h | h
  · exact E_err_lt hM hn1 hn2 hm1 hm2 h
  · rw [cvsEntry_symm M (by norm_num) n m, AEGIS.CvSRelRowPsdL43V1.Et_symm n m, abs_sub_comm (n : ℝ)]
    exact E_err_lt hM hm1 hm2 hn1 hn2 h

theorem E_err_diag {M : ℕ} (hM : 3 ≤ M) {n : ℤ} (hn1 : -70 ≤ n) (hn2 : n ≤ 70) :
    |cvsEntry M (4 / 3) n n - (Et n n : ℝ) / 2 ^ 128| ≤ rhoD := by
  have hb := diag_box hM (n := n) (by omega)
  obtain ⟨-, -, -, -, hr, -⟩ := max_low (k := n.natAbs) (by omega)
  have he : (Et n n : ℝ) / 2 ^ 128 = (dq n : ℝ) / 2 ^ 49 := by
    simp only [Et]; push_cast; field_simp; ring
  rw [he]
  refine hb.trans ?_
  simp only [rhoD]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hr) (by positivity)

/-- **The row sums of the midpoint error.** -/
theorem RE_row {M : ℕ} (hM : 3 ≤ M) {n : ℤ} (hn : n ∈ AEGIS.CvSRelRowFormL43V1.F) :
    ∑ m ∈ AEGIS.CvSRelRowFormL43V1.F, |cvsEntry M (4 / 3) n m - (Et n m : ℝ) / 2 ^ 128| ≤ RE := by
  rw [mem_Icc] at hn
  set F := AEGIS.CvSRelRowFormL43V1.F
  rw [← add_sum_erase F _ (show n ∈ F from mem_Icc.mpr hn)]
  have hd := E_err_diag hM hn.1 hn.2
  have hoff : ∑ m ∈ F.erase n, |cvsEntry M (4 / 3) n m - (Et n m : ℝ) / 2 ^ 128| ≤
      ∑ m ∈ F.erase n, (2 * am * (1 / |(n : ℝ) - m|) + 1 / 2 ^ 128) := by
    refine sum_le_sum fun m hm => ?_
    obtain ⟨hmn, hmF⟩ := mem_erase.mp hm
    rw [mem_Icc] at hmF
    have := E_err_off hM hn.1 hn.2 hmF.1 hmF.2 hmn
    rw [mul_one_div]
    exact this
  rw [sum_add_distrib, ← mul_sum, sum_const, card_erase_of_mem (mem_Icc.mpr hn)] at hoff
  have hcard : F.card = 141 := by simp [F]
  rw [hcard, nsmul_eq_mul, show ((141 - 1 : ℕ) : ℝ) * (1 / 2 ^ 128) = 140 / 2 ^ 128 by norm_num] at hoff
  have hs := inv_sum_le n (F.erase n) (n + 70).toNat (70 - n).toNat fun m hm => by
    obtain ⟨hmn, hmF⟩ := mem_erase.mp hm
    rw [mem_Icc] at hmF
    exact ⟨hmn, by omega, by omega⟩
  have hh := hup_le hn.1 hn.2
  have ham : 0 ≤ am := by
    simp only [am, Cu, rho, dC, tm]; norm_num [rhoq, tmq]
  have h3 : 2 * am * ∑ m ∈ F.erase n, 1 / |(n : ℝ) - m| ≤ 2 * am * ((hB2 : ℝ) / 2 ^ 64) :=
    mul_le_mul_of_nonneg_left (hs.trans hh) (by positivity)
  simp only [RE]
  linarith

/-! ## Crude entry bounds -/

theorem E_abs_le {M : ℕ} (hM : 3 ≤ M) {n m : ℤ} (hn1 : -70 ≤ n) (hn2 : n ≤ 70) (hm1 : -70 ≤ m)
    (hm2 : m ≤ 70) : |cvsEntry M (4 / 3) n m| ≤ 6 := by
  by_cases h : n = m
  · subst h
    have hb := diag_box hM (n := n) (by omega)
    obtain ⟨-, -, -, -, hr, hd⟩ := max_low (k := n.natAbs) (by omega)
    have e : cvsEntry M (4 / 3) n n =
        (cvsEntry M (4 / 3) n n - (dq n : ℝ) / 2 ^ 49) + (dq n : ℝ) / 2 ^ 49 := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h1 : (rdLit.getD n.natAbs 0 : ℝ) / 2 ^ 49 ≤ (rDq : ℝ) / 2 ^ 49 :=
      div_le_div_of_nonneg_right (by exact_mod_cast hr) (by positivity)
    have h2 : |(dq n : ℝ) / 2 ^ 49| ≤ (dmq : ℝ) / 2 ^ 49 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 49)]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have : |dq n| ≤ dmq := hd
      exact_mod_cast this
    have : (rDq : ℝ) / 2 ^ 49 + (dmq : ℝ) / 2 ^ 49 ≤ 6 := by norm_num [rDq, dmq]
    linarith
  · rw [E_off M h]
    have hk : (1 : ℝ) ≤ |(n : ℝ) - m| := by
      have : (1 : ℤ) ≤ |n - m| := Int.one_le_abs (sub_ne_zero.mpr h)
      have := (Int.cast_le (R := ℝ)).mpr this
      push_cast at this
      exact this
    obtain ⟨hn, htn⟩ := tau_low hM hn1 hn2
    obtain ⟨hm, htm⟩ := tau_low hM hm1 hm2
    obtain ⟨hC1, -⟩ := C_bounds
    have ta : |tau M (4 / 3) n - tau M (4 / 3) m| ≤ 2 * (rho + tm) := by
      have e : tau M (4 / 3) n - tau M (4 / 3) m = (tau M (4 / 3) n - (tq n : ℝ) / 2 ^ 49) +
          (tq n : ℝ) / 2 ^ 49 - ((tau M (4 / 3) m - (tq m : ℝ) / 2 ^ 49) + (tq m : ℝ) / 2 ^ 49) := by ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      have := abs_add_le (tau M (4 / 3) n - (tq n : ℝ) / 2 ^ 49) ((tq n : ℝ) / 2 ^ 49)
      have := abs_add_le (tau M (4 / 3) m - (tq m : ℝ) / 2 ^ 49) ((tq m : ℝ) / 2 ^ 49)
      linarith
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / (3 * Real.pi ^ 2)), abs_div]
    have hq : |tau M (4 / 3) n - tau M (4 / 3) m| / |(n : ℝ) - m| ≤ 2 * (rho + tm) :=
      (div_le_self (abs_nonneg _) hk).trans ta
    have : Cu * (2 * (rho + tm)) ≤ 6 := by norm_num [Cu, rho, tm, rhoq, tmq]
    have hC0 : 0 ≤ 2 / (3 * Real.pi ^ 2) := by positivity
    calc 2 / (3 * Real.pi ^ 2) * (|tau M (4 / 3) n - tau M (4 / 3) m| / |(n : ℝ) - m|)
        ≤ Cu * (2 * (rho + tm)) := mul_le_mul hC1 hq (by positivity) (by norm_num [Cu])
      _ ≤ 6 := this

theorem Et_abs_le {M : ℕ} (hM : 3 ≤ M) {n m : ℤ} (hn1 : -70 ≤ n) (hn2 : n ≤ 70) (hm1 : -70 ≤ m)
    (hm2 : m ≤ 70) : |(Et n m : ℝ) / 2 ^ 128| ≤ 7 := by
  have h1 := E_abs_le hM hn1 hn2 hm1 hm2
  have h2 : |cvsEntry M (4 / 3) n m - (Et n m : ℝ) / 2 ^ 128| ≤ 1 := by
    by_cases h : m = n
    · subst h
      refine (E_err_diag hM hn1 hn2).trans ?_
      norm_num [rhoD, rDq]
    · refine (E_err_off hM hn1 hn2 hm1 hm2 h).trans ?_
      have hk : (1 : ℝ) ≤ |(n : ℝ) - m| := by
        have : (1 : ℤ) ≤ |n - m| := Int.one_le_abs (sub_ne_zero.mpr (Ne.symm h))
        have := (Int.cast_le (R := ℝ)).mpr this
        push_cast at this
        exact this
      have ham : 0 ≤ 2 * am := by simp only [am, Cu, rho, dC, tm]; norm_num [rhoq, tmq]
      have : 2 * am / |(n : ℝ) - m| ≤ 2 * am := div_le_self ham hk
      have : 2 * am ≤ 1 / 2 := by simp only [am, Cu, rho, dC, tm]; norm_num [rhoq, tmq]
      have : (1 : ℝ) / 2 ^ 128 ≤ 1 / 2 := by norm_num
      linarith
  have e : (Et n m : ℝ) / 2 ^ 128 = cvsEntry M (4 / 3) n m -
      (cvsEntry M (4 / 3) n m - (Et n m : ℝ) / 2 ^ 128) := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  linarith

end AEGIS.CvSRelRowErrL43V1

end

#print axioms AEGIS.CvSRelRowErrL43V1.RE_row
#print axioms AEGIS.CvSRelRowErrL43V1.E_abs_le
#print axioms AEGIS.CvSRelRowErrL43V1.Et_abs_le
#print axioms AEGIS.CvSRelRowErrL43V1.tau_abs_all
