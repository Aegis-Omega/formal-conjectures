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

import CvSProjectedEntryL12V1
import FastKronV1

/-!
# Kernel-feasible replay of `bigCheck`

A streamed, Kronecker-packed integer check `chunkCheck` (odd packing base, strict evaluation) and
a proof that it implies `bigCheck = true`.
-/

open Finset
open AEGIS.CvSPackedGramV1 AEGIS.RHFixIntervalV1 AEGIS.CvSProjectedPackedCertificateL12V1
open AEGIS.CvSProjectedEntryL12V1 AEGIS.FastKronV1

namespace AEGIS.CvSProjectedEntryFastL12V1

set_option maxRecDepth 100000

/-! ## List helpers -/

/-- Second differences `2 b - a - c`. -/
def sd : List ℤ → List ℤ
  | a :: b :: c :: t => (2 * b - a - c) :: sd (b :: c :: t)
  | _ => []

theorem sd_length : ∀ l : List ℤ, (sd l).length = l.length - 2
  | a :: b :: c :: t => by simp [sd, sd_length (b :: c :: t)]
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl

theorem sd_getD : ∀ (l : List ℤ) (k : ℕ), k + 2 < l.length →
    (sd l).getD k 0 = 2 * l.getD (k + 1) 0 - l.getD k 0 - l.getD (k + 2) 0
  | a :: b :: c :: t, 0, _ => by simp [sd]
  | a :: b :: c :: t, k + 1, hk => by
      simp only [sd, List.getD_cons_succ]
      rw [sd_getD (b :: c :: t) k (by simp at hk ⊢; omega)]
      simp
  | [], _, hk => by simp at hk
  | [_], _, hk => by simp at hk
  | [_, _], _, hk => by simp at hk

theorem getD_map_lt {α β : Type} (l : List α) (f : α → β) (d : β) (e : α) {m : ℕ}
    (hm : m < l.length) : (l.map f).getD m d = f (l.getD m e) := by
  simp [List.getD_eq_getElem?_getD, hm]

theorem getD_zipWith {f : ℤ → ℤ → ℤ} {a b : List ℤ} {k : ℕ} (ha : k < a.length)
    (hb : k < b.length) : (List.zipWith f a b).getD k 0 = f (a.getD k 0) (b.getD k 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem ha,
    List.getElem?_eq_getElem hb]

theorem getD_append_lt {a b : List ℤ} {k : ℕ} (h : k < a.length) :
    (a ++ b).getD k 0 = a.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_ge {a b : List ℤ} {k : ℕ} (h : a.length ≤ k) :
    (a ++ b).getD k 0 = b.getD (k - a.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem pad_getD (c : List ℤ) (t : ℕ) :
    (0 :: 0 :: (c ++ [0, 0])).getD t 0 = if 2 ≤ t then c.getD (t - 2) 0 else 0 := by
  rcases t with _ | _ | t
  · simp
  · simp
  · simp only [List.getD_cons_succ, show 2 ≤ t + 2 by omega, if_true, show t + 2 - 2 = t by omega]
    by_cases h : t < c.length
    · exact getD_append_lt h
    · rw [getD_append_ge (by omega), List.getD_eq_default _ _ (by omega : c.length ≤ t)]
      rcases t - c.length with _ | _ | _ <;> simp

/-! ## Data -/

def facL : List ℤ :=
  (List.range 141).map fun k : ℕ => -(25 * (((k : ℤ) - 70) * ((k : ℤ) - 70)) * SI + C68)
def d2L : List ℤ := (List.range 141).map d2
def tKL : List ℤ := (List.range 141).map tK
def drL : List ℤ := (List.range 141).map dr
def trL : List ℤ := (List.range 141).map tr

/-- Odd Kronecker base (a power of two makes many cached literals share their low word). -/
def B0 : ℕ := 2 ^ 580 + 1
def OFF : ℕ := 2 ^ 578

/-- Second-difference transform of a zero-padded column, scaled by `facL`. -/
def sdT (c : List ℤ) : List ℤ := List.zipWith (· * ·) facL (sd (0 :: 0 :: (c ++ [0, 0])))

/-- Zero extension of a list to signed indices. -/
def cz (c : List ℤ) (m : ℤ) : ℤ := if 0 ≤ m then c.getD m.toNat 0 else 0

theorem facL_length : facL.length = 141 := by simp [facL]

theorem facL_getD {k : ℕ} (hk : k < 141) :
    facL.getD k 0 = -(25 * (((k : ℤ) - 70) * ((k : ℤ) - 70)) * SI + C68) := by
  rw [facL, getD_map_range _ 0 hk]

theorem sdT_getD {c : List ℤ} (hc : c.length = 139) {k : ℕ} (hk : k < 141) :
    (sdT c).getD k 0 = facL.getD k 0 * (2 * cz c ((k : ℤ) - 1) - cz c ((k : ℤ) - 2) - cz c k) := by
  have hs : (sd (0 :: 0 :: (c ++ [0, 0]))).length = 141 := by simp [sd_length, hc]
  rw [sdT, getD_zipWith (by rw [facL_length]; exact hk) (by rw [hs]; exact hk),
    sd_getD _ _ (by simp [hc]; omega), pad_getD, pad_getD, pad_getD]
  congr 1
  simp only [cz]
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k <;> simp
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega)]
    rw [show k + 1 - 2 = ((k : ℤ) - 1).toNat by omega, show k - 2 = ((k : ℤ) - 2).toNat by omega,
      show k + 2 - 2 = ((k : ℤ)).toNat by omega]

/-! ## certR -/

theorem certR_length : certR.length = 139 := by decide +kernel

theorem certR_rows : certR.all (fun r => r.length == 139) = true := by decide +kernel

theorem certR_row_length : ∀ r ∈ certR, r.length = 139 := by
  intro r hr
  have := List.all_eq_true.mp certR_rows r hr
  simpa using this

theorem rZ_eq (m : ℤ) (i : ℕ) : rZ m i = if 0 ≤ m then rI m.toNat i else 0 := by
  unfold rZ
  by_cases h0 : 0 ≤ m
  · by_cases h1 : m < 139
    · simp [h0, h1]
    · rw [if_neg (by omega), if_pos h0, rI, List.getD_eq_default certR []
        (by rw [certR_length]; omega)]
      simp
  · simp [h0]

theorem xI_sd {k i : ℕ} (hk : k < 141) :
    xI k i = facL.getD k 0 * (2 * rZ ((k : ℤ) - 1) i - rZ ((k : ℤ) - 2) i - rZ k i) := by
  rw [xI, facL_getD hk, wZ, show (k : ℤ) - 70 + 69 = k - 1 by ring,
    show (k : ℤ) - 70 + 68 = k - 2 by ring, show (k : ℤ) - 70 + 70 = k by ring]

/-- Columns of `certR`. -/
def colsR : List (List ℤ) := transP 139 certR

theorem colsR_getD {i : ℕ} (hi : i < 139) : colsR.getD i [] = certR.map fun r => r.getD i 0 :=
  transP_getD 139 certR certR_row_length i hi

theorem colsR_col_length {i : ℕ} (hi : i < 139) : (colsR.getD i []).length = 139 := by
  rw [colsR_getD hi, List.length_map, certR_length]

theorem cz_colsR {i : ℕ} (hi : i < 139) (m : ℤ) : cz (colsR.getD i []) m = rZ m i := by
  rw [cz, rZ_eq, colsR_getD hi]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0, if_pos h0, rI]
    by_cases h1 : m.toNat < 139
    · rw [getD_map_lt certR (fun r => r.getD i 0) 0 [] (by rw [certR_length]; exact h1)]
    · rw [List.getD_eq_default _ _ (by rw [List.length_map, certR_length]; omega),
        List.getD_eq_default certR [] (by rw [certR_length]; omega)]
      simp
  · rw [if_neg h0, if_neg h0]

/-- `X` columns: `(xsF.getD i []).getD k 0 = xI k i`. -/
def xsF : List (List ℤ) := colsR.map sdT

theorem xsF_getD {i : ℕ} (hi : i < 139) {k : ℕ} (hk : k < 141) :
    ((xsF.getD i []).getD k 0) = xI k i := by
  have hl : i < colsR.length := by rw [colsR, transP_length 139 certR certR_row_length]; exact hi
  rw [xsF, getD_map_lt colsR sdT [] [] hl, sdT_getD (colsR_col_length hi) hk, cz_colsR hi,
    cz_colsR hi, cz_colsR hi, xI_sd hk]

theorem xsF_col_length {i : ℕ} (hi : i < 139) : (xsF.getD i []).length = 141 := by
  have hl : i < colsR.length := by rw [colsR, transP_length 139 certR certR_row_length]; exact hi
  rw [xsF, getD_map_lt colsR sdT [] [] hl, sdT, List.length_zipWith, facL_length, sd_length,
    List.length_cons, List.length_cons, List.length_append, colsR_col_length hi]
  rfl

theorem xsF_length : xsF.length = 139 := by
  rw [xsF, List.length_map, colsR, transP_length 139 certR certR_row_length]

/-- Packed `certR` rows. -/
def PF : List ℤ := certR.map (packS (B0 : ℤ))

theorem PF_length : PF.length = 139 := by rw [PF, List.length_map, certR_length]

theorem cz_PF (m : ℤ) : cz PF m = ∑ i ∈ range 139, rZ m i * (B0 : ℤ) ^ i := by
  rw [cz]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0]
    by_cases h1 : m.toNat < 139
    · rw [PF, getD_map_lt certR (packS (B0 : ℤ)) 0 [] (by rw [certR_length]; exact h1),
        packS_eq, packZ_eq]
      have hr : (certR.getD m.toNat []).length = 139 := certR_row_length _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [certR_length]; exact h1),
          Option.getD_some]
        exact List.getElem_mem _)
      rw [hr]
      exact sum_congr rfl fun i _ => by rw [rZ_eq, if_pos h0, rI]
    · rw [List.getD_eq_default _ _ (by rw [PF_length]; omega)]
      symm
      exact sum_eq_zero fun i _ => by
        rw [rZ_eq, if_pos h0, rI, List.getD_eq_default certR [] (by rw [certR_length]; omega)]
        simp
  · rw [if_neg h0]
    symm
    exact sum_eq_zero fun i _ => by rw [rZ_eq, if_neg h0, zero_mul]

/-- Packed `X` rows: `xpF.getD k 0 = Σ_i xI k i · B0^i`. -/
def xpF : List ℤ := sdT PF

theorem xpF_getD {k : ℕ} (hk : k < 141) :
    xpF.getD k 0 = ∑ i ∈ range 139, xI k i * (B0 : ℤ) ^ i := by
  rw [xpF, sdT_getD PF_length hk, cz_PF, cz_PF, cz_PF, mul_sum, ← sum_sub_distrib,
    ← sum_sub_distrib, mul_sum]
  exact sum_congr rfl fun i _ => by rw [xI_sd hk]; ring

theorem xpF_length : xpF.length = 141 := by
  rw [xpF, sdT, List.length_zipWith, facL_length, sd_length]; simp [PF_length]

/-! ## H = K X -/

/-- `H k j = Σ_l kp k l · xI l j`. -/
def Hm (k j : ℕ) : ℤ := ∑ l ∈ range 141, kp k l * xI l j

theorem kL_length (k : ℕ) : (kL k).length = 141 := by simp [kL]

theorem kL_getD (k : ℕ) {l : ℕ} (hl : l < 141) : (kL k).getD l 0 = kp k l := by
  rw [kL, getD_map_range _ 0 hl]

/-- Packed rows of `H`. -/
def hpF : List ℤ := (List.range 141).map fun k => ldotS (kL k) xpF 0

theorem hpF_length : hpF.length = 141 := by simp [hpF]

theorem hpF_getD {k : ℕ} (hk : k < 141) :
    hpF.getD k 0 = ∑ j ∈ range 139, Hm k j * (B0 : ℤ) ^ j := by
  rw [hpF, getD_map_range _ 0 hk, ldotS_eq _ _ _ (by rw [kL_length, xpF_length]), zero_add,
    kL_length]
  rw [sum_congr rfl fun l hl => by rw [kL_getD k (mem_range.mp hl), xpF_getD (mem_range.mp hl)]]
  simp only [Hm, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun l _ => by ring

/-! ## The collected entry -/

/-- `Em i j = DE · Ê_ij` in collected form (`hI` replaced by `Hm`). -/
def Em (i j : ℕ) : ℤ :=
  C1 * ∑ k ∈ range 141, d2 k * xI k i * xI k j +
    C2 * ∑ k ∈ range 141, (tK k * xI k i * Hm k j + Hm k i * (tK k * xI k j))

theorem Em_symm (i j : ℕ) : Em i j = Em j i := by
  unfold Em
  congr 1
  · congr 1; exact sum_congr rfl fun k _ => by ring
  · congr 1; exact sum_congr rfl fun k _ => by ring

theorem d2L_length : d2L.length = 141 := by simp [d2L]
theorem tKL_length : tKL.length = 141 := by simp [tKL]
theorem d2L_getD {k : ℕ} (hk : k < 141) : d2L.getD k 0 = d2 k := by rw [d2L, getD_map_range _ 0 hk]
theorem tKL_getD {k : ℕ} (hk : k < 141) : tKL.getD k 0 = tK k := by rw [tKL, getD_map_range _ 0 hk]

/-! ## Constants free of large powers of two

A cached literal whose low 64 bits coincide with those of many others degrades the kernel's
expression cache to a linear list; products with `2^64`, `2^192`, `2^282`, `2^70` all end in a
zero word. The streamed check therefore uses the odd parts below. -/

/-- `2^70`; `C2 = 3 · 2^70`. -/
def P70 : ℤ := 1180591620717411303424
/-- `2^64 + 1`. -/
def P64 : ℤ := 18446744073709551617
/-- `2^128 + 1`. -/
def P128 : ℤ := 340282366920938463463374607431768211457
/-- `2^90`. -/
def Q90 : ℤ := 1237940039285380274899124224
/-- Odd part of `DE = 2^282 · DEo`. -/
def DEo : ℤ :=
  307039752043060233304320195872632772598428148419515763236182907483680682117633543125
/-- `2^378 = B2 / 2^70`. -/
def BC : ℕ := 2 ^ 378

theorem C2_split : C2 = 3 * P70 := by decide +kernel
theorem DE_split : DE = 2 ^ 282 * DEo := by decide +kernel
theorem SR_eq : SR = 2 ^ 192 := by decide +kernel
theorem T64_eq : T64 = 2 ^ 64 := by decide +kernel
theorem P64_eq : P64 = 2 ^ 64 + 1 := by decide +kernel
theorem P128_eq : P128 = 2 ^ 128 + 1 := by decide +kernel
theorem Q90_eq : Q90 = 2 ^ 90 := by decide +kernel
theorem P70_BC : P70 * (BC : ℤ) = B2 := by decide +kernel

theorem C2_bound {y : ℤ} (h : |3 * y| ≤ BC) : |C2 * y| ≤ B2 := by
  have hP : (0 : ℤ) < P70 := by decide +kernel
  rw [C2_split, mul_comm 3 P70, mul_assoc, abs_mul, abs_of_pos hP, ← P70_BC]
  exact mul_le_mul_of_nonneg_left h hP.le

/-- `ivOk` on odd parts: `⌊e / 2^90⌋` and `⌈e / 2^90⌉` against `DEo · (lo · 2^128 + r)` and
    `DEo · (hi · 2^128 - r)`. -/
def ivF (I : Iv) (e r : ℤ) : Bool :=
  decide (DEo * (I.lo * P128 + (r - I.lo)) ≤ e / Q90) &&
    decide (-((-e) / Q90) ≤ DEo * (I.hi * P128 - (I.hi + r)))

set_option exponentiation.threshold 600 in
theorem ivF_ivOk {I : Iv} {e r : ℤ} (h : ivF I e r = true) : ivOk I e r = true := by
  simp only [ivF, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hQ : (0 : ℤ) < Q90 := by decide +kernel
  have h1' := (Int.le_ediv_iff_mul_le hQ).mp h1
  have h2' := (Int.le_ediv_iff_mul_le hQ).mp (show -(DEo * (I.hi * P128 - (I.hi + r))) ≤ (-e) / Q90
    by linarith)
  rw [P128_eq, Q90_eq] at h1' h2'
  simp only [ivOk, Bool.and_eq_true, decide_eq_true_eq]
  rw [SR_eq, DE_split, T64_eq]
  constructor
  · calc I.lo * 2 ^ 192 * (2 ^ 282 * DEo) + r * 2 ^ 64 * (2 ^ 282 * DEo) =
          2 ^ 256 * (DEo * (I.lo * (2 ^ 128 + 1) + (r - I.lo)) * 2 ^ 90) := by ring
      _ ≤ 2 ^ 256 * e := mul_le_mul_of_nonneg_left h1' (by positivity)
      _ = e * 2 ^ 64 * 2 ^ 192 := by ring
  · calc e * 2 ^ 64 * 2 ^ 192 + r * 2 ^ 64 * (2 ^ 282 * DEo) =
          2 ^ 256 * e + r * 2 ^ 64 * (2 ^ 282 * DEo) := by ring
      _ ≤ 2 ^ 256 * (DEo * (I.hi * (2 ^ 128 + 1) - (I.hi + r)) * 2 ^ 90) +
          r * 2 ^ 64 * (2 ^ 282 * DEo) := by
          have := mul_le_mul_of_nonneg_left (show e ≤ DEo * (I.hi * (2 ^ 128 + 1) - (I.hi + r)) *
            2 ^ 90 by linarith) (show (0 : ℤ) ≤ 2 ^ 256 by positivity)
          linarith
      _ = I.hi * 2 ^ 192 * (2 ^ 282 * DEo) := by ring

/-- Packed right-hand vectors: `vF k = C1 d2 x̂ + C2 τ ĥ`, `uF k = 3 τ x̂`. -/
def vF : List ℤ :=
  List.zipWith (· + ·) (List.zipWith (fun d x => C1 * (d * x)) d2L xpF)
    (List.zipWith (fun t h => C2 * (t * h)) tKL hpF)

def uF : List ℤ := List.zipWith (fun t x => 3 * (t * x)) tKL xpF

theorem vF_length : vF.length = 141 := by
  simp [vF, d2L_length, xpF_length, tKL_length, hpF_length]

theorem uF_length : uF.length = 141 := by simp [uF, tKL_length, xpF_length]

theorem vF_getD {k : ℕ} (hk : k < 141) :
    vF.getD k 0 = C1 * (d2 k * xpF.getD k 0) + C2 * (tK k * hpF.getD k 0) := by
  rw [vF, getD_zipWith (by simp [d2L_length, xpF_length]; exact hk)
      (by simp [tKL_length, hpF_length]; exact hk),
    getD_zipWith (by rw [d2L_length]; exact hk) (by rw [xpF_length]; exact hk),
    getD_zipWith (by rw [tKL_length]; exact hk) (by rw [hpF_length]; exact hk),
    d2L_getD hk, tKL_getD hk]

theorem uF_getD {k : ℕ} (hk : k < 141) : uF.getD k 0 = 3 * (tK k * xpF.getD k 0) := by
  rw [uF, getD_zipWith (by rw [tKL_length]; exact hk) (by rw [xpF_length]; exact hk), tKL_getD hk]

/-- The packed row value: `Σ_j Em i j · B0^j`. -/
theorem row_value_of {i : ℕ} {x h : List ℤ} (hx : x.length = 141) (hh : h.length = 141)
    (hxk : ∀ k < 141, x.getD k 0 = xI k i) (hhk : ∀ k < 141, h.getD k 0 = Hm k i) :
    ldotS x vF 0 + ldotS h uF 0 * P70 = ∑ j ∈ range 139, Em i j * (B0 : ℤ) ^ j := by
  rw [ldotS_eq _ _ _ (by rw [hx, vF_length]), ldotS_eq _ _ _ (by rw [hh, uF_length]), zero_add,
    zero_add, hx, hh]
  have e1 : ∑ k ∈ range 141, x.getD k 0 * vF.getD k 0 =
      ∑ k ∈ range 141, xI k i * (C1 * (d2 k * xpF.getD k 0) + C2 * (tK k * hpF.getD k 0)) :=
    sum_congr rfl fun k hk => by rw [hxk k (mem_range.mp hk), vF_getD (mem_range.mp hk)]
  have e2 : (∑ k ∈ range 141, h.getD k 0 * uF.getD k 0) * P70 =
      ∑ k ∈ range 141, Hm k i * (C2 * (tK k * xpF.getD k 0)) := by
    rw [sum_mul]
    exact sum_congr rfl fun k hk => by
      rw [hhk k (mem_range.mp hk), uF_getD (mem_range.mp hk), C2_split]; ring
  have hR : ∑ j ∈ range 139, Em i j * (B0 : ℤ) ^ j = ∑ k ∈ range 141, ∑ j ∈ range 139,
      (C1 * (d2 k * xI k i * xI k j) +
        C2 * (tK k * xI k i * Hm k j + Hm k i * (tK k * xI k j))) * (B0 : ℤ) ^ j := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [Em, ← sum_mul, mul_sum, mul_sum, ← sum_add_distrib]
  rw [e1, e2, ← sum_add_distrib, hR]
  refine sum_congr rfl fun k hk => ?_
  rw [xpF_getD (mem_range.mp hk), hpF_getD (mem_range.mp hk)]
  simp only [mul_add, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun j _ => by ring

/-! ## The streamed check -/

/-- Per-column bounds: the `colOk` content, evaluated on the streamed columns. -/
def colChk (d2l tkl drl trl x h : List ℤ) (ad at' bt : ℕ) : Bool :=
  x.all (fun v => v.natAbs ≤ XMI) && h.all (fun v => v.natAbs ≤ HMI) &&
  (List.zipWith (fun d v => C1 * (d * v)) d2l x).all (fun v => v.natAbs ≤ B2) &&
  (List.zipWith (fun t v => 3 * (t * v)) tkl x).all (fun v => v.natAbs ≤ BC) &&
  h.all (fun v => (3 * v).natAbs ≤ BC) &&
  (List.zipWith (fun t v => t * v) tkl x).all (fun v => v.natAbs ≤ B2) &&
  decide (T128 * (List.zipWith (fun r v => r * (v * v)) drl x).sum ≤ (ad : ℤ) * ad * Q49) &&
  decide (T128 * (List.zipWith (fun r v => r * (v * v)) trl x).sum ≤ (at' : ℤ) * at' * Q49) &&
  decide (T128 * (List.zipWith (fun r v => r * (v * v)) trl h).sum ≤
    (bt : ℤ) * bt * (Q49 * LAM * LAM))

/-- Interval test of one row against `certI`. -/
def rowChk (adi ati bti : ℕ) : List ℤ → List ℕ → List ℕ → List ℕ → List Iv → Bool
  | ne :: nes, adj :: as, atj :: ts, btj :: bs, I :: Is =>
      ivF I ne ((adi : ℤ) * adj * P64 +
        (CPI * ((ati : ℤ) * btj + (atj : ℤ) * bti) + RPI - (adi : ℤ) * adj)) &&
      rowChk adi ati bti nes as ts bs Is
  | _, _, _, _, _ => true

def rowsChk (d2l tkl drl trl v u : List ℤ) : List (List ℤ) → List (List ℤ) → List ℕ → List ℕ →
    List ℕ → List (List Iv) → Bool
  | x :: xs, h :: hs, ad :: as, at' :: ts, bt :: bs, I :: Is =>
      colChk d2l tkl drl trl x h ad at' bt &&
      (fI (ldotS x v 0 + ldotS h u 0 * P70) fun T =>
        fL (unpackZ B0 OFF 139 T) fun nes => rowChk ad at' bt nes AD AT BT I) &&
      rowsChk d2l tkl drl trl v u xs hs as ts bs Is
  | _, _, _, _, _, _ => true

theorem rowChk_spec (adi ati bti : ℕ) : ∀ (nes : List ℤ) (as ts bs : List ℕ) (Is : List Iv),
    rowChk adi ati bti nes as ts bs Is = true → ∀ q, q < nes.length → q < as.length →
      q < ts.length → q < bs.length → q < Is.length →
      ivF (Is.getD q ⟨0, 0⟩) (nes.getD q 0) ((adi : ℤ) * as.getD q 0 * P64 +
        (CPI * ((ati : ℤ) * bs.getD q 0 + (ts.getD q 0 : ℤ) * bti) + RPI -
          (adi : ℤ) * as.getD q 0)) = true
  | ne :: nes, adj :: as, atj :: ts, btj :: bs, I :: Is, h, q, h1, h2, h3, h4, h5 => by
      simp only [rowChk, Bool.and_eq_true] at h
      cases q with
      | zero => exact h.1
      | succ q =>
        simp only [List.getD_cons_succ]
        exact rowChk_spec adi ati bti nes as ts bs Is h.2 q (by simpa using h1) (by simpa using h2)
          (by simpa using h3) (by simpa using h4) (by simpa using h5)
  | [], _, _, _, _, _, q, h1, _, _, _, _ => absurd h1 (by simp)
  | _ :: _, [], _, _, _, _, q, _, h2, _, _, _ => absurd h2 (by simp)
  | _ :: _, _ :: _, [], _, _, _, q, _, _, h3, _, _ => absurd h3 (by simp)
  | _ :: _, _ :: _, _ :: _, [], _, _, q, _, _, _, h4, _ => absurd h4 (by simp)
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, q, _, _, _, _, h5 => absurd h5 (by simp)

theorem rowsChk_spec (d2l tkl drl trl v u : List ℤ) : ∀ (xs hs : List (List ℤ))
    (as ts bs : List ℕ) (Is : List (List Iv)),
    rowsChk d2l tkl drl trl v u xs hs as ts bs Is = true →
    ∀ p, p < xs.length → p < hs.length → p < as.length → p < ts.length → p < bs.length →
      p < Is.length →
      colChk d2l tkl drl trl (xs.getD p []) (hs.getD p []) (as.getD p 0) (ts.getD p 0)
          (bs.getD p 0) = true ∧
        rowChk (as.getD p 0) (ts.getD p 0) (bs.getD p 0)
          (unpackZ B0 OFF 139 (ldotS (xs.getD p []) v 0 + ldotS (hs.getD p []) u 0 * P70))
          AD AT BT (Is.getD p []) = true
  | x :: xs, h :: hs, ad :: as, at' :: ts, bt :: bs, I :: Is, hc, p, h1, h2, h3, h4, h5, h6 => by
      simp only [rowsChk, fI_eq, fL_eq, Bool.and_eq_true] at hc
      cases p with
      | zero => exact ⟨hc.1.1, hc.1.2⟩
      | succ p =>
        simp only [List.getD_cons_succ]
        exact rowsChk_spec d2l tkl drl trl v u xs hs as ts bs Is hc.2 p (by simpa using h1)
          (by simpa using h2) (by simpa using h3) (by simpa using h4) (by simpa using h5)
          (by simpa using h6)
  | [], _, _, _, _, _, _, p, h1, _, _, _, _, _ => absurd h1 (by simp)
  | _ :: _, [], _, _, _, _, _, p, _, h2, _, _, _, _ => absurd h2 (by simp)
  | _ :: _, _ :: _, [], _, _, _, _, p, _, _, h3, _, _, _ => absurd h3 (by simp)
  | _ :: _, _ :: _, _ :: _, [], _, _, _, p, _, _, _, h4, _, _ => absurd h4 (by simp)
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, p, _, _, _, _, h5, _ => absurd h5 (by simp)
  | _ :: _, _ :: _, _ :: _, _ :: _, _ :: _, [], _, p, _, _, _, _, _, h6 => absurd h6 (by simp)

/-! ## Small closed checks -/

theorem lam_div : (List.range 140).all (fun m => LAM % ((m : ℤ) + 1) == 0) = true := by
  decide +kernel

theorem kL_B1 : (List.range 141).all (fun k => (kL k).all fun x => x.natAbs ≤ B1) = true := by
  decide +kernel

theorem kS_bound :
    (List.range 141).all (fun k => decide (((kL k).map Int.natAbs).sum * XMI < OFF)) = true := by
  decide +kernel

theorem E_const : C1 * ((d2L.map Int.natAbs).sum : ℤ) * XMI * XMI +
    C2 * (2 * ((tKL.map Int.natAbs).sum : ℤ) * XMI * HMI) < OFF := by
  decide +kernel

theorem certI_length : certI.length = 139 := by decide +kernel
theorem certI_rows : certI.all (fun r => r.length == 139) = true := by decide +kernel
theorem AD_length : AD.length = 139 := by decide +kernel
theorem AT_length : AT.length = 139 := by decide +kernel
theorem BT_length : BT.length = 139 := by decide +kernel

theorem certI_row_length {i : ℕ} (hi : i < 139) : (certI.getD i []).length = 139 := by
  have hm : certI.getD i [] ∈ certI := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [certI_length]; exact hi),
      Option.getD_some]
    exact List.getElem_mem _
  simpa using List.all_eq_true.mp certI_rows _ hm

/-! ## Helpers -/

theorem all_getD {l : List ℤ} {B : ℕ} {f : ℤ → ℤ}
    (h : l.all (fun v => (f v).natAbs ≤ B) = true) {k : ℕ} (hk : k < l.length) :
    |f (l.getD k 0)| ≤ B := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  have := of_decide_eq_true (List.all_eq_true.mp h _ (List.getElem_mem hk))
  rw [Int.abs_eq_natAbs]; exact_mod_cast this

theorem natAbs_dec {x : ℤ} {B : ℕ} (h : |x| ≤ B) : decide (x.natAbs ≤ B) = true := by
  apply decide_eq_true
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

theorem natAbs_sum_cast (L : List ℤ) {n : ℕ} (g : ℕ → ℤ) (hL : L = (List.range n).map g) :
    ((L.map Int.natAbs).sum : ℤ) = ∑ k ∈ range n, |g k| := by
  rw [hL, List.map_map, Nat.cast_list_sum, List.map_map, ← lsum_range]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply, Int.natCast_natAbs]

theorem abs_sum_le (f g : ℕ → ℤ) (B : ℤ) (hb : ∀ k < 141, |g k| ≤ B) :
    |∑ k ∈ range 141, f k * g k| ≤ (∑ k ∈ range 141, |f k|) * B := by
  calc |∑ k ∈ range 141, f k * g k| ≤ ∑ k ∈ range 141, |f k * g k| := abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ range 141, |f k| * |g k| := sum_congr rfl fun k _ => abs_mul _ _
    _ ≤ ∑ k ∈ range 141, |f k| * B :=
        sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hb k (mem_range.mp hk)) (abs_nonneg _)
    _ = (∑ k ∈ range 141, |f k|) * B := by rw [sum_mul]

theorem zipWith_eq_map {f : ℤ → ℤ → ℤ} {a b : List ℤ} {g : ℕ → ℤ} (ha : a.length = 141)
    (hb : b.length = 141) (h : ∀ k < 141, f (a.getD k 0) (b.getD k 0) = g k) :
    List.zipWith f a b = (List.range 141).map g := by
  apply List.ext_getElem (by simp [ha, hb])
  intro k h1 h2
  have hk : k < 141 := by simpa [ha, hb] using h1
  rw [List.getElem_zipWith, List.getElem_map, List.getElem_range, ← h k hk,
    List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]

theorem colChk_spec {d2l tkl drl trl x h : List ℤ} {ad at' bt : ℕ}
    (hc : colChk d2l tkl drl trl x h ad at' bt = true) :
    x.all (fun v => v.natAbs ≤ XMI) = true ∧ h.all (fun v => v.natAbs ≤ HMI) = true ∧
    (List.zipWith (fun d v => C1 * (d * v)) d2l x).all (fun v => v.natAbs ≤ B2) = true ∧
    (List.zipWith (fun t v => 3 * (t * v)) tkl x).all (fun v => v.natAbs ≤ BC) = true ∧
    h.all (fun v => (3 * v).natAbs ≤ BC) = true ∧
    (List.zipWith (fun t v => t * v) tkl x).all (fun v => v.natAbs ≤ B2) = true ∧
    T128 * (List.zipWith (fun r v => r * (v * v)) drl x).sum ≤ (ad : ℤ) * ad * Q49 ∧
    T128 * (List.zipWith (fun r v => r * (v * v)) trl x).sum ≤ (at' : ℤ) * at' * Q49 ∧
    T128 * (List.zipWith (fun r v => r * (v * v)) trl h).sum ≤
      (bt : ℤ) * bt * (Q49 * LAM * LAM) := by
  simp only [colChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem drL_length : drL.length = 141 := by simp [drL]
theorem trL_length : trL.length = 141 := by simp [trL]
theorem drL_getD {k : ℕ} (hk : k < 141) : drL.getD k 0 = dr k := by rw [drL, getD_map_range _ 0 hk]
theorem trL_getD {k : ℕ} (hk : k < 141) : trL.getD k 0 = tr k := by rw [trL, getD_map_range _ 0 hk]

theorem getD_drop' {α : Type} (l : List α) (d : α) (n m : ℕ) :
    (l.drop n).getD m d = l.getD (n + m) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_take_lt {α : Type} (l : List α) (d : α) {n m : ℕ} (h : m < n) :
    (l.take n).getD m d = l.getD m d := by
  simp [List.getD_eq_getElem?_getD, h]

/-! ## The kernel-replayed check, in row chunks -/

/-- Rows `a, …, a+n-1`: `X` columns from `certR`, digits `a, …, a+n-1` of every packed `H` row.
    Every intermediate list is forced once. -/
def chunkCheck (a n : ℕ) : Bool :=
  fL d2L fun d2l => fL tKL fun tkl => fL drL fun drl => fL trL fun trl =>
  fL vF fun v => fL uF fun u =>
  fLL ((xsF.drop a).take n) fun xs =>
  fLL (hpF.map (unpackR B0 OFF 139 a n)) fun hrows =>
  transC n hrows fun hs =>
  rowsChk d2l tkl drl trl v u xs hs (AD.drop a) (AT.drop a) (BT.drop a) (certI.drop a)

/-- What the streamed check provides about row `i`. -/
def RowOk (i : ℕ) : Prop :=
  ∃ x h : List ℤ, x.length = 141 ∧ h.length = 141 ∧ (∀ k < 141, x.getD k 0 = xI k i) ∧
    ((∀ k < 141, ∀ j < 139, |Hm k j| < OFF) → ∀ k < 141, h.getD k 0 = Hm k i) ∧
    colChk d2L tKL drL trL x h (AD.getD i 0) (AT.getD i 0) (BT.getD i 0) = true ∧
    rowChk (AD.getD i 0) (AT.getD i 0) (BT.getD i 0)
      (unpackZ B0 OFF 139 (ldotS x vF 0 + ldotS h uF 0 * P70)) AD AT BT (certI.getD i []) = true

theorem rowOk_of_chunk {a n : ℕ} (han : a + n ≤ 139) (hc : chunkCheck a n = true) :
    ∀ p < n, RowOk (a + p) := by
  intro p hp
  simp only [chunkCheck, fL_eq, fLL_eq, transC_eq] at hc
  set hrows := hpF.map (unpackR B0 OFF 139 a n) with hrows_def
  have hrl : ∀ r ∈ hrows, r.length = n := by
    intro r hr
    obtain ⟨S, _, rfl⟩ := List.mem_map.mp hr
    exact unpackR_length _ _ _ _ _ _
  have hxsl : ((xsF.drop a).take n).length = n := by simp [xsF_length]; omega
  have hd := rowsChk_spec _ _ _ _ _ _ _ _ _ _ _ _ hc p (by rw [hxsl]; exact hp)
    (by rw [transP_length n _ hrl]; exact hp) (by simp [AD_length]; omega)
    (by simp [AT_length]; omega) (by simp [BT_length]; omega) (by simp [certI_length]; omega)
  rw [getD_take_lt _ _ hp, getD_drop', getD_drop', getD_drop', getD_drop', getD_drop'] at hd
  have hhs : (transP n hrows).getD p [] = hrows.map fun r => r.getD p 0 :=
    transP_getD n hrows hrl p hp
  refine ⟨xsF.getD (a + p) [], (transP n hrows).getD p [], xsF_col_length (by omega), ?_,
    fun k hk => xsF_getD (by omega) hk, fun hH k hk => ?_, hd.1, hd.2⟩
  · rw [hhs, List.length_map, hrows_def, List.length_map, hpF_length]
  · have hk1 : k < hrows.length := by rw [hrows_def, List.length_map, hpF_length]; exact hk
    have hk2 : k < hpF.length := by rw [hpF_length]; exact hk
    rw [hhs, getD_map_lt hrows (fun r => r.getD p 0) 0 [] hk1, hrows_def,
      getD_map_lt hpF (unpackR B0 OFF 139 a n) [] 0 hk2, hpF_getD hk]
    refine unpackR_getD (by norm_num [B0]) han (fun j => Hm k j) (fun j' hj' => ?_) p hp
    have h := hH k hk j' hj'
    rw [abs_lt] at h
    have h2 : OFF + OFF < B0 := by decide +kernel
    have : (OFF : ℤ) + OFF < B0 := by exact_mod_cast h2
    constructor <;> linarith

/-! ## Soundness: every row checked → `bigCheck = true` -/

section Sound

variable (hall : ∀ i < 139, RowOk i)
include hall

theorem xI_le {k i : ℕ} (hk : k < 141) (hi : i < 139) : |xI k i| ≤ XMI := by
  obtain ⟨x, _, hx, _, hxk, _, hc, _⟩ := hall i hi
  have h := all_getD (f := fun v => v) (colChk_spec hc).1 (k := k) (by rw [hx]; exact hk)
  rwa [hxk k hk] at h

theorem Hm_lt {k j : ℕ} (hk : k < 141) (hj : j < 139) : |Hm k j| < OFF := by
  have hs : ((kL k).map Int.natAbs).sum * XMI < OFF :=
    of_decide_eq_true (List.all_eq_true.mp kS_bound k (List.mem_range.mpr hk))
  have hsum := natAbs_sum_cast (kL k) (kp k) rfl
  have hb := abs_sum_le (kp k) (fun l => xI l j) XMI fun l hl => xI_le hall hl hj
  calc |Hm k j| ≤ (∑ l ∈ range 141, |kp k l|) * XMI := hb
    _ = ((((kL k).map Int.natAbs).sum * XMI : ℕ) : ℤ) := by rw [Nat.cast_mul, hsum]
    _ < OFF := by exact_mod_cast hs

theorem hH : ∀ k < 141, ∀ j < 139, |Hm k j| < OFF := fun _ hk _ hj => Hm_lt hall hk hj

theorem Hm_le {k j : ℕ} (hk : k < 141) (hj : j < 139) : |Hm k j| ≤ HMI := by
  obtain ⟨_, h, _, hh, _, hhk, hc, _⟩ := hall j hj
  have h1 := all_getD (f := fun v => v) (colChk_spec hc).2.1 (k := k) (by rw [hh]; exact hk)
  rwa [hhk (hH hall) k hk] at h1

theorem Em_lt {i j : ℕ} (hi : i < 139) (hj : j < 139) : |Em i j| < OFF := by
  have hC1 : (0 : ℤ) ≤ C1 := by norm_num [C1, SI, LAM]
  have hC2 : (0 : ℤ) ≤ C2 := by norm_num [C2]
  have hD := natAbs_sum_cast d2L d2 rfl
  have hT := natAbs_sum_cast tKL tK rfl
  have b1 := abs_sum_le d2 (fun k => xI k i * xI k j) ((XMI : ℤ) * XMI) fun k hk => by
    rw [abs_mul]
    exact mul_le_mul (xI_le hall hk hi) (xI_le hall hk hj) (abs_nonneg _) (by positivity)
  have b2 := abs_sum_le tK (fun k => xI k i * Hm k j + Hm k i * xI k j)
    ((XMI : ℤ) * HMI + HMI * XMI) fun k hk => by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul (xI_le hall hk hi) (Hm_le hall hk hj) (abs_nonneg _) (by positivity)
    · exact mul_le_mul (Hm_le hall hk hi) (xI_le hall hk hj) (abs_nonneg _) (by positivity)
  have e1 : ∑ k ∈ range 141, d2 k * xI k i * xI k j =
      ∑ k ∈ range 141, d2 k * (xI k i * xI k j) := sum_congr rfl fun k _ => by ring
  have e2 : ∑ k ∈ range 141, (tK k * xI k i * Hm k j + Hm k i * (tK k * xI k j)) =
      ∑ k ∈ range 141, tK k * (xI k i * Hm k j + Hm k i * xI k j) :=
    sum_congr rfl fun k _ => by ring
  have hE := E_const
  rw [hD, hT] at hE
  calc |Em i j| ≤ |C1 * ∑ k ∈ range 141, d2 k * xI k i * xI k j| +
        |C2 * ∑ k ∈ range 141, (tK k * xI k i * Hm k j + Hm k i * (tK k * xI k j))| :=
        abs_add_le _ _
    _ ≤ C1 * ((∑ k ∈ range 141, |d2 k|) * (XMI * XMI)) +
        C2 * ((∑ k ∈ range 141, |tK k|) * (XMI * HMI + HMI * XMI)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hC1, abs_of_nonneg hC2, e1, e2]
        exact add_le_add (mul_le_mul_of_nonneg_left b1 hC1) (mul_le_mul_of_nonneg_left b2 hC2)
    _ = C1 * (∑ k ∈ range 141, |d2 k|) * XMI * XMI +
        C2 * (2 * (∑ k ∈ range 141, |tK k|) * XMI * HMI) := by ring
    _ < OFF := hE

theorem ivOk_all {i j : ℕ} (hi : i < 139) (hj : j < 139) :
    ivOk (Im certI i j) (Em i j) (radI i j) = true := by
  obtain ⟨x, h, hx, hh, hxk, hhk, _, hrow⟩ := hall i hi
  rw [row_value_of hx hh hxk (hhk (hH hall))] at hrow
  have hne : (unpackZ B0 OFF 139 (∑ j ∈ range 139, Em i j * (B0 : ℤ) ^ j)).getD j 0 = Em i j :=
    unpackZ_getD (by norm_num [B0]) (fun j => Em i j) (fun j' hj' => by
      have h := Em_lt hall hi hj'
      rw [abs_lt] at h
      have h2 : OFF + OFF < B0 := by decide +kernel
      have : (OFF : ℤ) + OFF < B0 := by exact_mod_cast h2
      constructor <;> linarith) j hj
  have h1 := rowChk_spec _ _ _ _ _ _ _ _ hrow j (by rw [unpackZ_length]; exact hj)
    (by rw [AD_length]; exact hj) (by rw [AT_length]; exact hj) (by rw [BT_length]; exact hj)
    (by rw [certI_row_length hi]; exact hj)
  rw [hne] at h1
  have h' := ivF_ivOk h1
  have hr : (AD.getD i 0 : ℤ) * AD.getD j 0 * P64 + (CPI * ((AT.getD i 0 : ℤ) * BT.getD j 0 +
      (AT.getD j 0 : ℤ) * BT.getD i 0) + RPI - (AD.getD i 0 : ℤ) * AD.getD j 0) = radI i j := by
    rw [radI, P64_eq, T64_eq]; ring
  rw [hr] at h'
  exact h'

theorem xL_B1' {i : ℕ} (hi : i < 139) : (xL i).all (fun x => x.natAbs ≤ B1) = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  have hB : (XMI : ℤ) ≤ B1 := by norm_num [XMI, B1]
  exact natAbs_dec ((xI_le hall (List.mem_range.mp hk) hi).trans hB)

theorem hI_eq_Hm {k i : ℕ} (hk : k < 141) (hi : i < 139) : hI k i = Hm k i := by
  have hk' : k < kPk.length := by simp [kPk, hk]
  rw [hI, hL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk',
    Option.map_some, Option.getD_some]
  have e : kPk[k] = (pack b1 (offRow B1 (kL k)), (kL k).sum) := by simp [kPk]
  rw [e]
  exact gram_range (kp k) (fun l => xI l i) (by norm_num)
    (List.all_eq_true.mp kL_B1 k (List.mem_range.mpr hk)) (xL_B1' hall hi) (by decide +kernel)

theorem hL_eq {i : ℕ} (hi : i < 139) : hL i = (List.range 141).map fun k => Hm k i := by
  apply List.ext_getElem (by simp [hL, kPk])
  intro k h1 h2
  have hk : k < 141 := by simpa using h2
  rw [List.getElem_map, List.getElem_range, ← hI_eq_Hm hall hk hi, hI, List.getD_eq_getElem _ _ h1]

theorem colOk_true {i : ℕ} (hi : i < 139) : colOk i = true := by
  obtain ⟨x, h, hx, hh, hxk, hhk', hc, _⟩ := hall i hi
  have hhk := hhk' (hH hall)
  obtain ⟨_, _, c3, c4, c5, c6, c7, c8, c9⟩ := colChk_spec hc
  have hXB2 : XMI ≤ B2 := by decide +kernel
  have hHB2 : HMI ≤ B2 := by decide +kernel
  have hzl : ∀ (f : ℤ → ℤ → ℤ) (a : List ℤ), a.length = 141 →
      (List.zipWith f a x).length = 141 := fun f a ha => by
    rw [List.length_zipWith, ha, hx, min_self]
  simp only [colOk, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · apply List.all_eq_true.mpr
    intro x hx'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx'
    exact natAbs_dec (xI_le hall (List.mem_range.mp hk) hi)
  · rw [hL_eq hall hi]
    apply List.all_eq_true.mpr
    intro x hx'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx'
    exact natAbs_dec (Hm_le hall (List.mem_range.mp hk) hi)
  · apply List.all_eq_true.mpr
    intro x hx'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx'
    have hk' := List.mem_range.mp hk
    apply natAbs_dec
    unfold vI
    split_ifs with h1 h2
    · have := all_getD (f := fun v => v) c3 (k := k) (by rw [hzl _ _ d2L_length]; exact h1)
      rwa [getD_zipWith (by rw [d2L_length]; exact h1) (by rw [hx]; exact h1), d2L_getD h1,
        hxk k h1] at this
    · have hk2 : k - 141 < 141 := by omega
      have := all_getD (f := fun v => v) c4 (k := k - 141) (by rw [hzl _ _ tKL_length]; exact hk2)
      rw [getD_zipWith (by rw [tKL_length]; exact hk2) (by rw [hx]; exact hk2), tKL_getD hk2,
        hxk _ hk2] at this
      exact C2_bound this
    · have hk2 : k - 282 < 141 := by omega
      have := all_getD (f := fun v => 3 * v) c5 (k := k - 282) (by rw [hh]; exact hk2)
      rw [hhk _ hk2] at this
      rw [hI_eq_Hm hall hk2 hi]
      exact C2_bound this
  · apply List.all_eq_true.mpr
    intro x hx'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx'
    have hk' := List.mem_range.mp hk
    apply natAbs_dec
    unfold wI
    split_ifs with h1 h2
    · exact (xI_le hall h1 hi).trans (by exact_mod_cast hXB2)
    · have hk2 : k - 141 < 141 := by omega
      rw [hI_eq_Hm hall hk2 hi]
      exact (Hm_le hall hk2 hi).trans (by exact_mod_cast hHB2)
    · have hk2 : k - 282 < 141 := by omega
      have := all_getD (f := fun v => v) c6 (k := k - 282) (by rw [hzl _ _ tKL_length]; exact hk2)
      rwa [getD_zipWith (by rw [tKL_length]; exact hk2) (by rw [hx]; exact hk2), tKL_getD hk2,
        hxk _ hk2] at this
  · rw [← zipWith_eq_map (f := fun r v => r * (v * v)) drL_length hx (fun k hk => by rw [drL_getD hk, hxk k hk])]
    exact c7
  · rw [← zipWith_eq_map (f := fun r v => r * (v * v)) trL_length hx (fun k hk => by rw [trL_getD hk, hxk k hk])]
    exact c8
  · rw [← zipWith_eq_map (f := fun r v => r * (v * v)) trL_length hh (fun k hk => by
      rw [trL_getD hk, hhk k hk, hI_eq_Hm hall hk hi])]
    exact c9

theorem neI_Em {i j : ℕ} (hi : i < 139) (hj : j < 139) : neI i j = Em i j := by
  have hci := colOk_true hall hi
  have hcj := colOk_true hall hj
  simp only [colOk, Bool.and_eq_true] at hci hcj
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hv⟩, _⟩, _⟩, _⟩, _⟩ := hci
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hw⟩, _⟩, _⟩, _⟩ := hcj
  have ci : cols.getD i default = colPk i := getD_map_range colPk default hi
  have cj : cols.getD j default = colPk j := getD_map_range colPk default hj
  have key : ∑ k ∈ range 423, vI i k * wI j k = C1 * ∑ k ∈ range 141, d2 k * xI k i * xI k j +
      C2 * ∑ k ∈ range 141, (tK k * xI k i * hI k j + hI k i * (tK k * xI k j)) := by
    rw [show (423 : ℕ) = 141 + (141 + 141) from rfl, sum_range_add, sum_range_add, mul_sum,
      mul_sum, ← sum_add_distrib]
    congr 1
    · exact sum_congr rfl fun k hk => by
        have := mem_range.mp hk; simp only [vI, wI, if_pos this]; ring
    · exact sum_congr rfl fun k hk => by
        have := mem_range.mp hk
        simp only [vI, wI, show ¬ 141 + k < 141 by omega, show 141 + k < 282 by omega,
          show ¬ 141 + (141 + k) < 141 by omega, show ¬ 141 + (141 + k) < 282 by omega,
          if_false, if_true, show 141 + k - 141 = k by omega,
          show 141 + (141 + k) - 282 = k by omega]
        ring
  rw [neI, ci, cj]
  simp only [colPk, vL, wL]
  rw [gram_range (vI i) (wI j) (by norm_num) hv hw (by decide +kernel), key, Em]
  congr 2
  exact sum_congr rfl fun k hk => by
    rw [hI_eq_Hm hall (mem_range.mp hk) hj, hI_eq_Hm hall (mem_range.mp hk) hi]

theorem entryOk_true {i j : ℕ} (hi : i < 139) (hj : j < 139) : entryOk i j = true := by
  rw [entryOk, Bool.and_eq_true, neI_Em hall hi hj]
  refine ⟨ivOk_all hall hi hj, ?_⟩
  have h := ivOk_all hall hj hi
  rw [Em_symm] at h
  rwa [show radI j i = radI i j by unfold radI; ring] at h

theorem bigCheck_of_rows : bigCheck = true := by
  unfold bigCheck
  rw [lam_div, kL_B1]
  simp only [Bool.true_and, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun i hi => colOk_true hall (List.mem_range.mp hi), fun i hi j hj => ?_⟩
  have hi' := List.mem_range.mp hi
  have hj' := List.mem_range'_1.mp hj
  exact entryOk_true hall hi' (by omega)

end Sound

/-- The five row chunks cover all 139 rows. -/
theorem rows_ok_of_chunks (h0 : chunkCheck 0 28 = true) (h1 : chunkCheck 28 28 = true)
    (h2 : chunkCheck 56 28 = true) (h3 : chunkCheck 84 28 = true)
    (h4 : chunkCheck 112 27 = true) : ∀ i < 139, RowOk i := by
  intro i hi
  have key : ∀ a n, a + n ≤ 139 → chunkCheck a n = true → a ≤ i → i < a + n → RowOk i :=
    fun a n han hc ha hb => by
      have := rowOk_of_chunk han hc (i - a) (by omega)
      rwa [show a + (i - a) = i by omega] at this
  by_cases c0 : i < 28
  · exact key 0 28 (by norm_num) h0 (by omega) c0
  by_cases c1 : i < 56
  · exact key 28 28 (by norm_num) h1 (by omega) c1
  by_cases c2 : i < 84
  · exact key 56 28 (by norm_num) h2 (by omega) c2
  by_cases c3 : i < 112
  · exact key 84 28 (by norm_num) h3 (by omega) c3
  · exact key 112 27 (by norm_num) h4 (by omega) (by omega)

end AEGIS.CvSProjectedEntryFastL12V1

#print axioms AEGIS.CvSProjectedEntryFastL12V1.xsF_getD
#print axioms AEGIS.CvSProjectedEntryFastL12V1.xpF_getD
#print axioms AEGIS.CvSProjectedEntryFastL12V1.hpF_getD
#print axioms AEGIS.CvSProjectedEntryFastL12V1.row_value_of
#print axioms AEGIS.CvSProjectedEntryFastL12V1.ivF_ivOk
#print axioms AEGIS.CvSProjectedEntryFastL12V1.rowOk_of_chunk
#print axioms AEGIS.CvSProjectedEntryFastL12V1.bigCheck_of_rows
#print axioms AEGIS.CvSProjectedEntryFastL12V1.rows_ok_of_chunks
