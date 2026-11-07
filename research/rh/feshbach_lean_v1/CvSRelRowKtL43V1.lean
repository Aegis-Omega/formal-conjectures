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
import CvSRelRowErrL43V1

/-!
# The kernel of the outside rows against its integer table `Kt`

`Hs` is the set of outside rows `70 < |m| ≤ 200` (the list `HL`). With `τ̂_m = tq m/2^49` and
`ŵ(n, m) = (τ̂_n − τ̂_m)/(n − m)`, the kernel `K̂(n, n') = Σ_{m ∈ Hs} ŵ(n, m) ŵ(n', m)` is
`K₂ − (τ̂_n + τ̂_n') K₁ + τ̂_n τ̂_n' K₀` with `K_j(n, n') = Σ_m τ̂_m^j/((m − n)(m − n'))`, and off
the diagonal `K_j(n, n') = (S_j(n) − S_j(n'))/(n − n')` (`Kr_off`). Every rounding of the
integer tables is within one unit, so `|Kt/2^128 − K̂| ≤ 90000/2^128` on `F × F` (`Kt_err`).
Not RH.
-/

open Finset
open AEGIS.CvSRelRowDataL43V1 AEGIS.CvSRelRowFormL43V1 AEGIS.CvSRelRowErrL43V1 AEGIS.CvSRelRowHarmV1
  AEGIS.CvSRelRowBoxL43V1

noncomputable section

namespace AEGIS.CvSRelRowKtL43V1

set_option maxRecDepth 100000

/-! ## The outside rows -/

/-- The outside rows `70 < |m| ≤ 200`. -/
def Hs : Finset ℤ := HL.toFinset

theorem HL_nodup : HL.Nodup := by decide +kernel

theorem HL_eq : HL = ((List.range 130).map fun k : ℕ => (k : ℤ) + 71) ++
    (List.range 130).map fun k : ℕ => -((k : ℤ) + 71) := by
  decide +kernel

theorem mem_HL {m : ℤ} : m ∈ HL ↔ (71 ≤ m ∧ m ≤ 200) ∨ (-200 ≤ m ∧ m ≤ -71) := by
  rw [HL_eq]
  simp only [List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨k, hk, hkm⟩ | ⟨k, hk, hkm⟩)
    · left; omega
    · right; omega
  · rintro (h | h)
    · exact Or.inl ⟨(m - 71).toNat, by omega, by omega⟩
    · exact Or.inr ⟨(-m - 71).toNat, by omega, by omega⟩

theorem mem_Hs {m : ℤ} : m ∈ Hs ↔ (71 ≤ m ∧ m ≤ 200) ∨ (-200 ≤ m ∧ m ≤ -71) := by
  rw [Hs, List.mem_toFinset, mem_HL]

theorem card_Hs : Hs.card = 260 := by
  rw [Hs, List.toFinset_card_of_nodup HL_nodup, HL_eq]
  simp

theorem HL_sum {M : Type*} [AddCommMonoid M] (f : ℤ → M) : (HL.map f).sum = ∑ m ∈ Hs, f m :=
  (List.sum_toFinset f HL_nodup).symm

theorem sub_ne {n m : ℤ} (hn : n ∈ F) (hm : m ∈ Hs) : (m : ℝ) - n ≠ 0 := by
  rw [mem_Icc] at hn
  rw [mem_Hs] at hm
  have : m ≠ n := by omega
  exact sub_ne_zero.mpr (by exact_mod_cast this)

/-! ## Real kernels -/

def th (m : ℤ) : ℝ := (tq m : ℝ) / 2 ^ 49

def Sr (j : ℕ) (n : ℤ) : ℝ := ∑ m ∈ Hs, th m ^ j / ((m : ℝ) - n)

def Tr (j : ℕ) (n : ℤ) : ℝ := ∑ m ∈ Hs, th m ^ j / ((m : ℝ) - n) ^ 2

def Kr (j : ℕ) (n n' : ℤ) : ℝ := ∑ m ∈ Hs, th m ^ j / (((m : ℝ) - n) * ((m : ℝ) - n'))

def wh (n m : ℤ) : ℝ := (th n - th m) / ((n : ℝ) - m)

/-- `K̂(n, n') = Σ_{m ∈ Hs} ŵ(n, m) ŵ(n', m)`. -/
def Kh (n n' : ℤ) : ℝ := ∑ m ∈ Hs, wh n m * wh n' m

theorem Kr_diag (j : ℕ) (n : ℤ) : Kr j n n = Tr j n := by
  simp only [Kr, Tr, sq]

theorem Kr_symm (j : ℕ) (n n' : ℤ) : Kr j n n' = Kr j n' n := by
  simp only [Kr, mul_comm]

theorem Kr_off (j : ℕ) {n n' : ℤ} (hn : n ∈ F) (hn' : n' ∈ F) (h : n ≠ n') :
    Kr j n n' = (Sr j n - Sr j n') / ((n : ℝ) - n') := by
  have hd : (n : ℝ) - n' ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  simp only [Kr, Sr]
  rw [← sum_sub_distrib, sum_div]
  refine sum_congr rfl fun m hm => ?_
  have h1 := sub_ne hn hm
  have h2 := sub_ne hn' hm
  field_simp
  ring

theorem Kh_eq {n n' : ℤ} (hn : n ∈ F) (hn' : n' ∈ F) :
    Kh n n' = Kr 2 n n' - (th n + th n') * Kr 1 n n' + th n * th n' * Kr 0 n n' := by
  simp only [Kh, Kr, wh, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun m hm => ?_
  have h1 := sub_ne hn hm
  have h2 := sub_ne hn' hm
  have h1' : (n : ℝ) - m ≠ 0 := by intro h; apply h1; linarith
  have h2' : (n' : ℝ) - m ≠ 0 := by intro h; apply h2; linarith
  field_simp
  ring

/-! ## The integer tables -/

theorem ok_at {P : ℤ → Prop} [DecidablePred P]
    (h : (List.range 141).all (fun (i : ℕ) => decide (P ((i : ℤ) - 70))) = true) {n : ℤ}
    (hn : n ∈ F) : P n := by
  rw [mem_Icc] at hn
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have := h (n + 70).toNat (by omega)
  rwa [show (((n + 70).toNat : ℕ) : ℤ) - 70 = n by omega] at this

theorem Sq_eq {j : ℕ} (hj : j < 3) {n : ℤ} (hn : n ∈ F) : Sq j n = Sraw j n := by
  interval_cases j
  · exact ok_at (P := fun x => Sq 0 x = Sraw 0 x) S_ok0 hn
  · exact ok_at (P := fun x => Sq 1 x = Sraw 1 x) S_ok1 hn
  · exact ok_at (P := fun x => Sq 2 x = Sraw 2 x) S_ok2 hn

theorem Tq_eq {j : ℕ} (hj : j < 3) {n : ℤ} (hn : n ∈ F) : Tq j n = Traw j n := by
  interval_cases j
  · exact ok_at (P := fun x => Tq 0 x = Traw 0 x) T_ok0 hn
  · exact ok_at (P := fun x => Tq 1 x = Traw 1 x) T_ok1 hn
  · exact ok_at (P := fun x => Tq 2 x = Traw 2 x) T_ok2 hn

theorem pw_eq {j : ℕ} (hj : j < 3) (m : ℤ) : (pw j m : ℝ) = 2 ^ 128 * th m ^ j := by
  interval_cases j <;> simp only [pw, th] <;> push_cast <;> ring

/-- A sum of `260` roundings. -/
theorem sum_round (g : ℤ → ℤ) (d : ℤ → ℤ) (hd : ∀ m ∈ Hs, d m ≠ 0) :
    |(((HL.map fun m => g m / d m).sum : ℤ) : ℝ) - ∑ m ∈ Hs, (g m : ℝ) / (d m : ℝ)| ≤ 260 := by
  rw [HL_sum, Int.cast_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ m ∈ Hs, |((g m / d m : ℤ) : ℝ) - (g m : ℝ) / (d m : ℝ)|
      ≤ ∑ _m ∈ Hs, (1 : ℝ) := sum_le_sum fun m hm => by
        rw [abs_sub_comm]; exact (ediv_err (g m) (d m) (hd m hm)).le
    _ = 260 := by rw [sum_const, card_Hs]; norm_num

theorem Sq_err {j : ℕ} (hj : j < 3) {n : ℤ} (hn : n ∈ F) :
    |(Sq j n : ℝ) - 2 ^ 128 * Sr j n| ≤ 260 := by
  rw [Sq_eq hj hn, Sraw]
  have h := sum_round (fun m => pw j m) (fun m => m - n) fun m hm => by
    have := sub_ne hn hm
    intro h0; apply this; exact_mod_cast h0
  convert h using 3
  rw [Sr, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [pw_eq hj]
  push_cast
  ring

theorem Tq_err {j : ℕ} (hj : j < 3) {n : ℤ} (hn : n ∈ F) :
    |(Tq j n : ℝ) - 2 ^ 128 * Tr j n| ≤ 260 := by
  rw [Tq_eq hj hn, Traw]
  have h := sum_round (fun m => pw j m) (fun m => (m - n) * (m - n)) fun m hm => by
    have := sub_ne hn hm
    intro h0; apply this
    have : (m - n : ℤ) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h <;> exact h
    exact_mod_cast this
  convert h using 3
  rw [Tr, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [pw_eq hj]
  push_cast
  ring

theorem Kj_err_lt {j : ℕ} (hj : j < 3) {n n' : ℤ} (hn : n ∈ F) (hn' : n' ∈ F) (h : n' < n) :
    |(Kj j n n' : ℝ) - 2 ^ 128 * Kr j n n'| ≤ 521 := by
  have hne : n ≠ n' := by omega
  have hk : (0 : ℝ) < (n : ℝ) - n' := by
    have : (n' : ℝ) < n := by exact_mod_cast h
    linarith
  have hk1 : (1 : ℝ) ≤ (n : ℝ) - n' := by
    have : (n' : ℝ) + 1 ≤ n := by exact_mod_cast h
    linarith
  rw [Kr_off j hn hn' hne]
  have e : Kj j n n' = (Sq j n - Sq j n') / (n - n') := by
    simp only [Kj, if_neg hne, if_pos h]
  rw [e]
  set X : ℤ := Sq j n - Sq j n'
  have hr := ediv_err X (n - n') (by omega)
  have hX : |(X : ℝ) - 2 ^ 128 * (Sr j n - Sr j n')| ≤ 520 := by
    have a := Sq_err hj hn
    have b := Sq_err hj hn'
    simp only [X]
    push_cast
    rw [show (Sq j n : ℝ) - Sq j n' - 2 ^ 128 * (Sr j n - Sr j n') =
      ((Sq j n : ℝ) - 2 ^ 128 * Sr j n) - ((Sq j n' : ℝ) - 2 ^ 128 * Sr j n') by ring]
    refine (abs_sub _ _).trans ?_
    linarith
  have e2 : ((X / (n - n') : ℤ) : ℝ) - 2 ^ 128 * ((Sr j n - Sr j n') / ((n : ℝ) - n')) =
      (((X / (n - n') : ℤ) : ℝ) - (X : ℝ) / ((n - n' : ℤ) : ℝ)) +
        ((X : ℝ) - 2 ^ 128 * (Sr j n - Sr j n')) / ((n : ℝ) - n') := by
    push_cast
    field_simp
    ring
  rw [e2]
  refine (abs_add_le _ _).trans ?_
  rw [abs_sub_comm] at hr
  have h3 : |((X : ℝ) - 2 ^ 128 * (Sr j n - Sr j n')) / ((n : ℝ) - n')| ≤ 520 := by
    rw [abs_div, abs_of_pos hk]
    exact (div_le_self (abs_nonneg _) hk1).trans hX
  linarith

theorem Kj_err {j : ℕ} (hj : j < 3) {n n' : ℤ} (hn : n ∈ F) (hn' : n' ∈ F) :
    |(Kj j n n' : ℝ) - 2 ^ 128 * Kr j n n'| ≤ 521 := by
  rcases lt_trichotomy n' n with h | h | h
  · exact Kj_err_lt hj hn hn' h
  · subst h
    have e : Kj j n' n' = Tq j n' := by simp [Kj]
    rw [e, Kr_diag]
    exact (Tq_err hj hn).trans (by norm_num)
  · rw [AEGIS.CvSRelRowPsdL43V1.Kj_symm, Kr_symm]
    exact Kj_err_lt hj hn' hn h

theorem th_le {n : ℤ} (hn : n ∈ F) : |th n| ≤ 12 := by
  rw [mem_Icc] at hn
  have h := (tau_low (M := 3) le_rfl hn.1 hn.2).2
  have : tm ≤ 12 := by norm_num [tm, tmq]
  exact h.trans this

/-- **The integer kernel against `K̂`.** -/
theorem Kt_err {n n' : ℤ} (hn : n ∈ F) (hn' : n' ∈ F) :
    |(Kt n n' : ℝ) / 2 ^ 128 - Kh n n'| ≤ 90000 / 2 ^ 128 := by
  rw [Kh_eq hn hn']
  have e2 := Kj_err (j := 2) (by norm_num) hn hn'
  have e1 := Kj_err (j := 1) (by norm_num) hn hn'
  have e0 := Kj_err (j := 0) (by norm_num) hn hn'
  set P1 : ℤ := (tq n + tq n') * Kj 1 n n'
  set P2 : ℤ := tq n * tq n' * Kj 0 n n'
  have r1 := ediv_err P1 (2 ^ 49) (by norm_num)
  have r2 := ediv_err P2 (2 ^ 98) (by norm_num)
  have hP1 : (P1 : ℝ) / ((2 ^ 49 : ℤ) : ℝ) = (th n + th n') * (Kj 1 n n' : ℝ) := by
    simp only [P1, th]; push_cast; ring
  have hP2 : (P2 : ℝ) / ((2 ^ 98 : ℤ) : ℝ) = th n * th n' * (Kj 0 n n' : ℝ) := by
    simp only [P2, th]; push_cast; ring
  have hKt : (Kt n n' : ℝ) = (Kj 2 n n' : ℝ) - ((P1 / 2 ^ 49 : ℤ) : ℝ) + ((P2 / 2 ^ 98 : ℤ) : ℝ) := by
    simp only [Kt, P1, P2]; push_cast; ring
  have key : (Kt n n' : ℝ) - 2 ^ 128 * (Kr 2 n n' - (th n + th n') * Kr 1 n n' +
      th n * th n' * Kr 0 n n') =
      ((Kj 2 n n' : ℝ) - 2 ^ 128 * Kr 2 n n') -
        (((P1 / 2 ^ 49 : ℤ) : ℝ) - (P1 : ℝ) / ((2 ^ 49 : ℤ) : ℝ)) -
        (th n + th n') * ((Kj 1 n n' : ℝ) - 2 ^ 128 * Kr 1 n n') +
        (((P2 / 2 ^ 98 : ℤ) : ℝ) - (P2 : ℝ) / ((2 ^ 98 : ℤ) : ℝ)) +
        th n * th n' * ((Kj 0 n n' : ℝ) - 2 ^ 128 * Kr 0 n n') := by
    rw [hKt, hP1, hP2]; ring
  have t1 := th_le hn
  have t2 := th_le hn'
  have a1 : |(th n + th n') * ((Kj 1 n n' : ℝ) - 2 ^ 128 * Kr 1 n n')| ≤ 24 * 521 := by
    rw [abs_mul]
    have : |th n + th n'| ≤ 24 := (abs_add_le _ _).trans (by linarith)
    exact mul_le_mul this e1 (abs_nonneg _) (by norm_num)
  have a0 : |th n * th n' * ((Kj 0 n n' : ℝ) - 2 ^ 128 * Kr 0 n n')| ≤ 144 * 521 := by
    rw [abs_mul, abs_mul]
    have : |th n| * |th n'| ≤ 144 := by
      have := mul_le_mul t1 t2 (abs_nonneg _) (by norm_num)
      linarith
    exact mul_le_mul this e0 (abs_nonneg _) (by norm_num)
  rw [abs_sub_comm] at r1 r2
  have total : |(Kt n n' : ℝ) - 2 ^ 128 * (Kr 2 n n' - (th n + th n') * Kr 1 n n' +
      th n * th n' * Kr 0 n n')| ≤ 90000 := by
    rw [key, abs_le]
    rw [abs_le] at e2 a1 a0
    rw [abs_lt] at r1 r2
    constructor <;> linarith [e2.1, e2.2, a1.1, a1.2, a0.1, a0.2, r1.1, r1.2, r2.1, r2.2]
  have e : (Kt n n' : ℝ) / 2 ^ 128 - (Kr 2 n n' - (th n + th n') * Kr 1 n n' +
      th n * th n' * Kr 0 n n') = ((Kt n n' : ℝ) - 2 ^ 128 * (Kr 2 n n' - (th n + th n') * Kr 1 n n' +
      th n * th n' * Kr 0 n n')) / 2 ^ 128 := by field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 128)]
  exact div_le_div_of_nonneg_right total (by positivity)

end AEGIS.CvSRelRowKtL43V1

end

#print axioms AEGIS.CvSRelRowKtL43V1.Kt_err
#print axioms AEGIS.CvSRelRowKtL43V1.card_Hs
