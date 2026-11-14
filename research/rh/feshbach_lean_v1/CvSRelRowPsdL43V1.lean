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
import CvSRelRowCheckL43V1

/-!
# The check matrix at `L = 4/3` is positive semidefinite

The chunked kernel checks of `CvSRelRowCheckL43V1` give `CvSPackedGramV1.check` for the interval
table `Itab`; `Itab` encloses the scaled matrix `Pm i j / 2^(488 + d_i + d_j)` (`Itab_mem`), which
is symmetric (`Pm_symm`). `Pm_psd`: `0 ≤ Re Σ c_i conj(c_j) Pm i j` for every `c : Fin 139 → ℂ`.
Not RH.
-/

open Finset
open AEGIS.CvSRelRowDataL43V1 AEGIS.CvSRelRowCertL43V1 AEGIS.CvSPackedGramV1 AEGIS.RHFixIntervalV1
  AEGIS.FastKronV1 AEGIS.CvSRelRowCheckL43V1

namespace AEGIS.CvSRelRowPsdL43V1

/-! ## Symmetry -/

theorem Et_symm (n m : ℤ) : Et n m = Et m n := by
  unfold Et
  rcases lt_trichotomy n m with h | rfl | h
  · rw [if_neg h.ne, if_neg h.ne', if_neg (not_lt.mpr h.le), if_pos h]
  · rfl
  · rw [if_neg h.ne', if_neg h.ne, if_pos h, if_neg (not_lt.mpr h.le)]

theorem Kj_symm (j : ℕ) (n m : ℤ) : Kj j n m = Kj j m n := by
  unfold Kj
  rcases lt_trichotomy n m with h | rfl | h
  · rw [if_neg h.ne, if_neg h.ne', if_neg (not_lt.mpr h.le), if_pos h]
  · rfl
  · rw [if_neg h.ne', if_neg h.ne, if_pos h, if_neg (not_lt.mpr h.le)]

theorem Kt_symm (n m : ℤ) : Kt n m = Kt m n := by
  unfold Kt
  rw [Kj_symm 0 n m, Kj_symm 1 n m, Kj_symm 2 n m, add_comm (tq n), mul_comm (tq n)]

theorem Gt_symm (n m : ℤ) : Gt n m = Gt m n := by
  unfold Gt
  rcases lt_trichotomy n m with h | rfl | h
  · rw [if_neg h.ne, if_neg h.ne', if_neg (not_lt.mpr h.le), if_pos h]
  · rfl
  · rw [if_neg h.ne', if_neg h.ne, if_pos h, if_neg (not_lt.mpr h.le)]

theorem Zt_symm (n m : ℤ) : Zt n m = Zt m n := by
  unfold Zt
  rw [Et_symm n m, Kt_symm n m, Gt_symm n m, mul_comm (tq n) (tq m)]
  by_cases h : n = m
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem Zf_symm (n m : ℤ) : Zf n m = Zf m n := by
  unfold Zf; rw [Zt_symm n m]; ring

theorem Pm_symm (i j : ℕ) : Pm i j = Pm j i := by
  unfold Pm
  rw [sum_comm]
  congr 1
  · congr 1
    exact sum_congr rfl fun t _ => sum_congr rfl fun s _ => by rw [Zf_symm]; ring
  · ring

/-! ## The lookup-free entry is `Zt` -/

theorem zent_eq (n m : ℤ) : zent (rowc n) (col m) = Zt n m := rfl

/-! ## The pipeline is the matrix -/

theorem length_cols141 : cols141.length = 141 := by simp [cols141]

theorem zrowC_getD (n : ℤ) {b : ℕ} (hb : b < 141) :
    (zrowC cols141 n).getD b 0 = Zf n ((b : ℤ) - 70) := by
  have h1 : cols141.getD b (col 0) = col ((b : ℤ) - 70) := by
    unfold cols141; exact getD_map_range' _ _ hb
  have hlen : b < cols141.length := by rw [length_cols141]; exact hb
  simp only [zrowC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlen,
    Option.map_some, Option.getD_some]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some] at h1
  rw [h1, zent_eq]
  rfl

theorem length_zrowC (n : ℤ) : (zrowC cols141 n).length = 141 := by
  simp [zrowC, length_cols141]

/-- Row `i` of the pipeline. -/
def prow (i : ℕ) : List ℤ :=
  Prow (zrowC cols141 ((i : ℤ) - 70)) (zrowC cols141 ((i : ℤ) - 69)) (zrowC cols141 ((i : ℤ) - 68))
    (Ul 0) (Ul 1) i

theorem Pchunk_eq (a k : ℕ) : Pchunk a k = (List.range k).map fun r => prow (a + r) := by
  simp only [Pchunk, fL_eq, fCL_eq, fLL_eq]
  refine List.map_congr_left fun r hr => ?_
  rw [List.mem_range] at hr
  rw [getD_map_range' _ _ (by omega : r < k + 2), getD_map_range' _ _ (by omega : r + 1 < k + 2),
    getD_map_range' _ _ (by omega : r + 2 < k + 2)]
  have c1 : (((a + (r + 1) : ℕ) : ℤ) - 70) = ((a + r : ℕ) : ℤ) - 69 := by push_cast; ring
  have c2 : (((a + (r + 2) : ℕ) : ℤ) - 70) = ((a + r : ℕ) : ℤ) - 68 := by push_cast; ring
  rw [c1, c2]
  rfl

theorem zipWith_map_range {α β γ : Type*} (f : α → β → γ) (g : ℕ → α) (h : ℕ → β) (k : ℕ) :
    List.zipWith f ((List.range k).map g) ((List.range k).map h) =
      (List.range k).map fun r => f (g r) (h r) := by
  rw [List.zipWith_map, List.zipWith_self]

theorem Ichunk_eq (a k : ℕ) :
    Ichunk a k = (List.range' a k).map fun i => Ivrow i (prow i) := by
  rw [Ichunk, Pchunk_eq, zipWith_map_range, List.range'_eq_map_range, List.map_map]
  rfl

theorem Itab_eq : Itab = (List.range 139).map fun i => Ivrow i (prow i) := by
  simp only [Itab, Ichunk_eq, ← List.map_append]
  rw [List.range_eq_range']
  exact congrArg _ (by decide)

/-! ## Lengths and entries -/

theorem length_Ul (jj : ℕ) : (Ul jj).length = 139 := by simp [Ul]

theorem length_prow (i : ℕ) : (prow i).length = 139 := by
  simp only [prow, Prow, length_zipWith3, List.length_tail, length_zrowC, length_Ul]
  rfl

theorem getD_zipWith {α β γ : Type*} (f : α → β → γ) (da : α) (db : β) (dc : γ) :
    ∀ (a : List α) (b : List β) (k : ℕ), k < a.length → k < b.length →
      (List.zipWith f a b).getD k dc = f (a.getD k da) (b.getD k db)
  | [], _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: a, y :: b, 0, _, _ => by simp
  | x :: a, y :: b, k + 1, ha, hb => by
    simp only [List.zipWith_cons_cons, List.getD_cons_succ]
    exact getD_zipWith f da db dc a b k (by simpa using ha) (by simpa using hb)

theorem length_Ivrow (i : ℕ) (r : List ℤ) (hr : r.length = 139) : (Ivrow i r).length = 139 := by
  simp [Ivrow, length_certD, hr]

theorem Ivrow_getD (i : ℕ) (r : List ℤ) (hr : r.length = 139) {j : ℕ} (hj : j < 139) :
    (Ivrow i r).getD j ⟨0, 0⟩ =
      ⟨r.getD j 0 >>> (424 + certD.getD i 0 + certD.getD j 0),
        (r.getD j 0 >>> (424 + certD.getD i 0 + certD.getD j 0)) + 1⟩ := by
  unfold Ivrow
  rw [getD_zipWith _ 0 0 _ _ _ _ (by rw [length_certD]; exact hj) (by rw [hr]; exact hj)]

theorem prow_getD {i j : ℕ} (hi : i < 139) (hj : j < 139) : (prow i).getD j 0 = Pm i j := by
  have hz : ∀ n : ℤ, (zrowC cols141 n).length = 141 := length_zrowC
  set z0 := zrowC cols141 ((i : ℤ) - 70)
  set z1 := zrowC cols141 ((i : ℤ) - 69)
  set z2 := zrowC cols141 ((i : ℤ) - 68)
  set y := List.zipWith3 sd3 z0 z1 z2 with hy
  have hyl : y.length = 141 := by rw [hy, length_zipWith3, hz, hz, hz]; rfl
  have hyg : ∀ b < 141, y.getD b 0 = sd3 (Zf ((i : ℤ) - 70) ((b : ℤ) - 70))
      (Zf ((i : ℤ) - 69) ((b : ℤ) - 70)) (Zf ((i : ℤ) - 68) ((b : ℤ) - 70)) := by
    intro b hb
    rw [hy, getD_zipWith3 _ 0 0 0 _ _ _ _ _ (by rw [hz]; exact hb) (by rw [hz]; exact hb)
      (by rw [hz]; exact hb), zrowC_getD _ hb, zrowC_getD _ hb, zrowC_getD _ hb]
  have hpl : (List.zipWith3 sd3 y y.tail y.tail.tail).length = 139 := by
    rw [length_zipWith3, List.length_tail, List.length_tail, hyl]; rfl
  have hpg : (List.zipWith3 sd3 y y.tail y.tail.tail).getD j 0 =
      sd3 (y.getD j 0) (y.getD (j + 1) 0) (y.getD (j + 2) 0) := by
    rw [getD_zipWith3 _ 0 0 0 _ _ _ _ _ (by rw [hyl]; omega)
      (by rw [List.length_tail, hyl]; omega) (by rw [List.length_tail, List.length_tail, hyl]; omega),
      getD_tail, getD_tail, getD_tail]
  have hu : ∀ jj : ℕ, ∀ k < 139, (Ul jj).getD k 0 = U jj k := fun jj k hk =>
    getD_map_range' _ _ hk
  unfold prow Prow
  rw [getD_zipWith3 _ 0 0 0 _ _ _ _ _ (by rw [hpl]; exact hj) (by rw [length_Ul]; exact hj)
    (by rw [length_Ul]; exact hj), hpg, hyg j (by omega), hyg (j + 1) (by omega),
    hyg (j + 2) (by omega), hu 0 i hi, hu 1 i hi, hu 0 j hj, hu 1 j hj]
  have c1 : (((j + 1 : ℕ) : ℤ) - 70) = (j : ℤ) - 70 + 1 := by push_cast; ring
  have c2 : (((j + 2 : ℕ) : ℤ) - 70) = (j : ℤ) - 70 + 2 := by push_cast; ring
  have d1 : ((i : ℤ) - 69) = (i : ℤ) - 70 + 1 := by ring
  have d2 : ((i : ℤ) - 68) = (i : ℤ) - 70 + 2 := by ring
  rw [c1, c2, d1, d2]
  simp only [Pm, sd3, wq, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, add_zero, zero_add]
  norm_num
  ring

/-! ## The intervals enclose the scaled matrix -/

/-- The scaled check matrix `P̃ = D P D`. -/
noncomputable def Ps (i j : Fin 139) : ℝ :=
  (Pm i j : ℝ) / 2 ^ (488 + certD.getD i 0 + certD.getD j 0)

theorem Itab_getD {i : ℕ} (hi : i < 139) : Itab.getD i [] = Ivrow i (prow i) := by
  rw [Itab_eq, getD_map_range' _ _ hi]

theorem floor_shift (x : ℤ) (s : ℕ) :
    (((x >>> s : ℤ) : ℝ)) ≤ (x : ℝ) / 2 ^ s ∧ (x : ℝ) / 2 ^ s ≤ (((x >>> s) + 1 : ℤ) : ℝ) := by
  rw [Int.shiftRight_eq_div_pow]
  have hp : (0 : ℤ) < ((2 ^ s : ℕ) : ℤ) := by positivity
  have h1 := Int.ediv_mul_le x hp.ne'
  have h2 := Int.lt_ediv_add_one_mul_self x hp
  have hpr : (0 : ℝ) < 2 ^ s := by positivity
  have e : (((2 ^ s : ℕ) : ℤ) : ℝ) = 2 ^ s := by push_cast; ring
  constructor
  · rw [le_div_iff₀ hpr]
    have := (Int.cast_le (R := ℝ)).mpr h1
    push_cast at this ⊢
    linarith
  · rw [div_le_iff₀ hpr]
    have := (Int.cast_lt (R := ℝ)).mpr h2
    push_cast at this ⊢
    linarith

theorem Itab_mem (i j : Fin 139) : (Im Itab i j).Mem 64 (Ps i j) := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Im, Itab_getD hi, Ivrow_getD _ _ (length_prow i) hj, prow_getD hi hj, Iv.Mem, Ps]
  set s := 424 + certD.getD i 0 + certD.getD j 0
  obtain ⟨h1, h2⟩ := floor_shift (Pm i j) s
  have e : (488 + certD.getD (i : ℕ) 0 + certD.getD (j : ℕ) 0) = s + 64 := by simp only [s]; omega
  rw [e, pow_add, ← div_div]
  have hp : (0 : ℝ) < 2 ^ 64 := by positivity
  constructor
  · exact div_le_div_of_nonneg_right h1 hp.le
  · exact div_le_div_of_nonneg_right h2 hp.le

theorem Ps_symm (i j : Fin 139) : Ps i j = Ps j i := by
  simp only [Ps, Pm_symm (i : ℕ) j]
  congr 2
  ring

/-! ## The packed check -/

theorem rowsOk_append (cols : List (ℕ × ℤ)) :
    ∀ (L1 L2 : List (List ℤ)) (I1 I2 : List (List Iv)) (i0 : ℕ), I1.length = L1.length →
      rowsOk certBase certB 139 certEps certEta cols i0 (L1 ++ L2) (I1 ++ I2) =
        (rowsOk certBase certB 139 certEps certEta cols i0 L1 I1 &&
          rowsOk certBase certB 139 certEps certEta cols (i0 + L1.length) L2 I2)
  | [], L2, [], I2, i0, _ => by simp [rowsOk]
  | [], _, _ :: _, _, _, h => by simp at h
  | _ :: _, _, [], _, _, h => by simp at h
  | r :: L1, L2, Ir :: I1, I2, i0, h => by
    simp only [List.cons_append, rowsOk, List.length_cons]
    rw [rowsOk_append cols L1 L2 I1 I2 (i0 + 1) (by simpa using h), Bool.and_assoc]
    congr 3
    omega

theorem length_Ichunk (a k : ℕ) : (Ichunk a k).length = k := by simp [Ichunk_eq]

theorem certL_split : certL = (certL.drop 0).take 20 ++ (certL.drop 20).take 20 ++
    (certL.drop 40).take 20 ++ (certL.drop 60).take 20 ++ (certL.drop 80).take 20 ++
    (certL.drop 100).take 20 ++ (certL.drop 120).take 19 := by rfl

theorem take_len (a k : ℕ) (h : a + k ≤ 139) : ((certL.drop a).take k).length = k := by
  have : certL.length = 139 := by rfl
  simp only [List.length_take, List.length_drop, this]
  omega

theorem rowsOk_true : rowsOk certBase certB 139 certEps certEta cols 0 certL Itab = true := by
  rw [certL_split, Itab]
  simp only [List.append_assoc]
  rw [rowsOk_append _ _ _ _ _ _ (by rw [length_Ichunk, take_len 0 20 (by norm_num)]),
    rowsOk_append _ _ _ _ _ _ (by rw [length_Ichunk, take_len 20 20 (by norm_num)]),
    rowsOk_append _ _ _ _ _ _ (by rw [length_Ichunk, take_len 40 20 (by norm_num)]),
    rowsOk_append _ _ _ _ _ _ (by rw [length_Ichunk, take_len 60 20 (by norm_num)]),
    rowsOk_append _ _ _ _ _ _ (by rw [length_Ichunk, take_len 80 20 (by norm_num)]),
    rowsOk_append _ _ _ _ _ _ (by rw [length_Ichunk, take_len 100 20 (by norm_num)])]
  simp only [take_len 0 20 (by norm_num), take_len 20 20 (by norm_num), take_len 40 20 (by norm_num),
    take_len 60 20 (by norm_num), take_len 80 20 (by norm_num), take_len 100 20 (by norm_num)]
  norm_num only
  simp only [chunk0_ok, chunk1_ok, chunk2_ok, chunk3_ok, chunk4_ok, chunk5_ok, chunk6_ok,
    Bool.and_self]

theorem Itab_length : Itab.length = 139 := by rw [Itab_eq]; simp

theorem Itab_rows : Itab.all (fun r => decide (r.length = 139)) = true := by
  rw [Itab_eq, List.all_map, List.all_eq_true]
  intro i _
  simp [length_Ivrow i (prow i) (length_prow i)]

theorem check_true : check certBase certB 139 certEps certEta certL Itab = true := by
  have h := certL_ok
  have e : check certBase certB 139 certEps certEta certL Itab =
      (decide (0 < 139) && decide (139 * 139 * (2 * certB * (2 * certB)) < certBase) &&
        decide (certL.length = 139) && decide (Itab.length = 139) &&
        certL.all (rowBounded certB 139) && Itab.all (fun r => decide (r.length = 139)) &&
        rowsOk certBase certB 139 certEps certEta cols 0 certL Itab) := rfl
  rw [e, Itab_rows, rowsOk_true, show decide (Itab.length = 139) = true from
    decide_eq_true Itab_length, Bool.and_true, Bool.and_true, Bool.and_true]
  exact h

/-! ## Positivity -/

theorem Pm_psd (c : Fin 139 → ℂ) :
    0 ≤ (∑ i : Fin 139, ∑ j : Fin 139, c i * (starRingEnd ℂ) (c j) * ((Pm i j : ℝ) : ℂ)).re := by
  set K : ℝ := 2 ^ 488 with hKdef
  have hK : 0 < K := by positivity
  set d : Fin 139 → ℕ := fun i => certD.getD i 0 with hd
  have hq := quad_lower_complex 64 certBase certB certEps certEta certL Itab check_true Ps Ps_symm
    Itab_mem (fun i => c i * (((2 : ℝ) ^ d i : ℝ) : ℂ))
  have key : (∑ i : Fin 139, ∑ j : Fin 139, c i * (((2 : ℝ) ^ d i : ℝ) : ℂ) *
      (starRingEnd ℂ) (c j * (((2 : ℝ) ^ d j : ℝ) : ℂ)) * (Ps i j : ℂ)) =
      (((1 / K : ℝ)) : ℂ) * ∑ i : Fin 139, ∑ j : Fin 139,
        c i * (starRingEnd ℂ) (c j) * ((Pm i j : ℝ) : ℂ) := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    have e2 : (2 : ℝ) ^ (488 + certD.getD i 0 + certD.getD j 0) = K * 2 ^ d i * 2 ^ d j := by
      rw [pow_add, pow_add]
    simp only [Ps, map_mul, Complex.conj_ofReal, e2]
    have h1 : (2 : ℝ) ^ d i ≠ 0 := by positivity
    have h2 : (2 : ℝ) ^ d j ≠ 0 := by positivity
    push_cast
    field_simp
  rw [key, Complex.re_ofReal_mul] at hq
  have hm : (0 : ℤ) ≤ certEps - certEta := by decide
  have hn : (0 : ℝ) ≤ ((certEps - certEta : ℤ) : ℝ) *
      ∑ i : Fin 139, ‖c i * (((2 : ℝ) ^ d i : ℝ) : ℂ)‖ ^ 2 :=
    mul_nonneg (by exact_mod_cast hm) (sum_nonneg fun i _ => sq_nonneg _)
  have h3 := hn.trans hq
  have h4 := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 2 ^ 64)).mp h3
  exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 1 / K)).mp h4

end AEGIS.CvSRelRowPsdL43V1

#print axioms AEGIS.CvSRelRowPsdL43V1.Pm_symm
#print axioms AEGIS.CvSRelRowPsdL43V1.zent_eq
#print axioms AEGIS.CvSRelRowPsdL43V1.prow_getD
#print axioms AEGIS.CvSRelRowPsdL43V1.Itab_mem
#print axioms AEGIS.CvSRelRowPsdL43V1.check_true
#print axioms AEGIS.CvSRelRowPsdL43V1.Pm_psd
