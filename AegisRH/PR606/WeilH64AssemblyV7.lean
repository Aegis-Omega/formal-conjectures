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
import WeilH64PrimeV7

/-!
# OPTIMUS V7: coercivity of the actual Weil form on 64 packets

Index the packets by `x = (a, b) ∈ Fin 2 × Fin 32`, with centres
`c(a, b) = ∓ log 2 / 2 + (2b − 31)/2048` (`−` for `a = 0`) and logarithmic radius `R = 1/4096`.
For any smooth compactly supported packets `g x` with `LogRadiusAt (g x) (c x) R` and energy `1`
(arbitrary shapes and phases), `K x y = −B(g x, g y)` on the actual repository functional satisfies

  `(1475/6144) Σ ‖z x‖² ≤ Re Σ_{x,y} z x K x y conj(z y)`   (`h64_coercive`).

The proof is the V7 row budget: diagonal `≥ 13/3 − 1/2048` (`diag_v7`); same-cluster entries
`≤ 1/1024 + ½ log((2m+1)/(2m−1))` (no prime; telescoping to `½ log 1023 < 7/2`); cross-cluster
entries `≤ 1/512`, plus `log 2/√2 < 1/2` on the matched pair only; Gershgorin for Hermitian forms.

This is finite-dimensional coercivity of the restricted Weil form only. Not RH.
-/

open Set Function MeasureTheory Complex Finset
open scoped ComplexConjugate BigOperators

noncomputable section

namespace AEGIS.WeilH64AssemblyV7

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilH64ElementaryV7
open AEGIS.WeilH64DiagonalV7
open AEGIS.WeilH64CrossV7
open AEGIS.WeilH64PrimeV7

abbrev Idx := Fin 2 × Fin 32

/-- The V7 centres. -/
def ctr (x : Idx) : ℝ :=
  (if x.1 = 0 then -(Real.log 2 / 2) else Real.log 2 / 2) + (2 * ((x.2 : ℕ) : ℝ) - 31) / 2048

theorem log3_gt : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  linarith [Real.exp_one_lt_d9]

theorem norm_B_swap (p q : WeilCompactSmoothGV1) : ‖B p q‖ = ‖B q p‖ := by
  rw [B_hermitian p q, Complex.norm_conj]

theorem cross_unit {p q : WeilCompactSmoothGV1} (hEp : energy p.1 = 1) (hEq : energy q.1 = 1) :
    ∀ u, ‖logCrossV28 p q u‖ ≤ 1 := fun u => by
  have := logCross_norm_le p q u
  rw [hEp, hEq] at this
  linarith

/-- **Same-cluster entry** (`q` to the right of `p` by `m/1024`, `1 ≤ m ≤ 31`). -/
theorem entry_same {p q : WeilCompactSmoothGV1} {c m : ℝ} (hm1 : 1 ≤ m) (hm : m ≤ 31)
    (hp : LogRadiusAt p c (1 / 4096)) (hq : LogRadiusAt q (c + m / 1024) (1 / 4096))
    (hEp : energy p.1 = 1) (hEq : energy q.1 = 1) :
    ‖B p q‖ ≤ 1 / 1024 + 1 / 2 * Real.log ((2 * m + 1) / (2 * m - 1)) := by
  have hp' : LogSupportIn p (c - 1 / 4096) (c + 1 / 4096) := hp
  have hq' : LogSupportIn q (c + m / 1024 - 1 / 4096) (c + m / 1024 + 1 / 4096) := hq
  have hsep : c + 1 / 4096 < c + m / 1024 - 1 / 4096 := by linarith
  have hl2 := Real.log_two_gt_d9
  have h3 : (c + m / 1024 + 1 / 4096) - (c - 1 / 4096) < Real.log 3 := by linarith [log3_gt]
  have h2 : (c + m / 1024 + 1 / 4096) - (c - 1 / 4096) < Real.log 2 := by linarith
  have hpz := prime_sum_zero hp' hq' hsep h3 (Or.inr h2)
  have ha := sep_arch_le p q hp' hq' hsep (by linarith) (cross_unit hEp hEq)
  have hB := B_sep_norm_le hp' hq' hsep
  rw [hpz, norm_zero, zero_add] at hB
  refine hB.trans (ha.trans (le_of_eq ?_))
  have e1 : (c + m / 1024 + 1 / 4096) - (c - 1 / 4096) - ((c + m / 1024 - 1 / 4096) - (c + 1 / 4096)) =
      1 / 1024 := by ring
  have hden : (2 * m - 1) ≠ 0 := by linarith
  have e2 : ((c + m / 1024 + 1 / 4096) - (c - 1 / 4096)) / ((c + m / 1024 - 1 / 4096) - (c + 1 / 4096)) =
      (2 * m + 1) / (2 * m - 1) := by
    rw [show (c + m / 1024 + 1 / 4096) - (c - 1 / 4096) = (2 * m + 1) / 2048 by ring,
      show (c + m / 1024 - 1 / 4096) - (c + 1 / 4096) = (2 * m - 1) / 2048 by ring]
    field_simp
  rw [e1, e2]
  ring

/-- **Cross-cluster entry** (`q` to the right of `p` by `log 2 + t/1024`, `|t| ≤ 31`, `t` an integer). -/
theorem entry_cross {p q : WeilCompactSmoothGV1} {c t : ℝ} (ht : |t| ≤ 31) (htz : t = 0 ∨ 1 ≤ |t|)
    (hp : LogRadiusAt p c (1 / 4096)) (hq : LogRadiusAt q (c + Real.log 2 + t / 1024) (1 / 4096))
    (hEp : energy p.1 = 1) (hEq : energy q.1 = 1) :
    ‖B p q‖ ≤ (if t = 0 then Real.log 2 / Real.sqrt 2 else 0) + 1 / 512 := by
  have hp' : LogSupportIn p (c - 1 / 4096) (c + 1 / 4096) := hp
  have hq' : LogSupportIn q (c + Real.log 2 + t / 1024 - 1 / 4096) (c + Real.log 2 + t / 1024 + 1 / 4096) := hq
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hta := abs_le.mp ht
  have hgap : 1 / 2 ≤ (c + Real.log 2 + t / 1024 - 1 / 4096) - (c + 1 / 4096) := by linarith
  have hsep : c + 1 / 4096 < c + Real.log 2 + t / 1024 - 1 / 4096 := by linarith
  have h3 : (c + Real.log 2 + t / 1024 + 1 / 4096) - (c - 1 / 4096) < Real.log 3 := by linarith [log3_gt]
  have ha := sep_arch_le_two p q hp' hq' hgap (by linarith) (cross_unit hEp hEq)
  have hB := B_sep_norm_le hp' hq' hsep
  have ha' : ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤ 1 / 512 := by
    refine ha.trans (le_of_eq ?_); ring
  refine hB.trans (add_le_add ?_ ha')
  split_ifs with h0
  · have := prime_sum_norm_le hp' hq' hsep h3
    rw [hEp, hEq] at this
    linarith
  · have h1 : 1 ≤ |t| := htz.resolve_left h0
    have h2 : Real.log 2 < (c + Real.log 2 + t / 1024 - 1 / 4096) - (c + 1 / 4096) ∨
        (c + Real.log 2 + t / 1024 + 1 / 4096) - (c - 1 / 4096) < Real.log 2 := by
      rcases le_abs'.mp h1 with h | h
      · right; linarith
      · left; linarith
    rw [prime_sum_zero hp' hq' hsep h3 h2, norm_zero]

/-- The row bound of an off-diagonal entry. -/
def bnd (x y : Idx) : ℝ :=
  if y = x then 0
  else if y.1 = x.1 then
    1 / 1024 + 1 / 2 * Real.log ((2 * |((x.2 : ℕ) : ℝ) - ((y.2 : ℕ) : ℝ)| + 1) /
      (2 * |((x.2 : ℕ) : ℝ) - ((y.2 : ℕ) : ℝ)| - 1))
  else (if y.2 = x.2 then Real.log 2 / Real.sqrt 2 else 0) + 1 / 512

theorem fin_dist (b b' : Fin 32) (h : b ≠ b') :
    1 ≤ |((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)| ∧ |((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)| ≤ 31 := by
  have hb := b.isLt
  have hb' := b'.isLt
  have hne : (b : ℕ) ≠ (b' : ℕ) := fun e => h (Fin.ext e)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have : ((b : ℕ) : ℝ) + 1 ≤ ((b' : ℕ) : ℝ) := by exact_mod_cast hlt
    have h31 : ((b' : ℕ) : ℝ) ≤ 31 := by exact_mod_cast (by omega : (b' : ℕ) ≤ 31)
    have h0 : (0 : ℝ) ≤ ((b : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [abs_of_neg (by linarith)]
    constructor <;> linarith
  · have : ((b' : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hlt
    have h31 : ((b : ℕ) : ℝ) ≤ 31 := by exact_mod_cast (by omega : (b : ℕ) ≤ 31)
    have h0 : (0 : ℝ) ≤ ((b' : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [abs_of_pos (by linarith)]
    constructor <;> linarith

/-- **Every off-diagonal entry is within its row bound.** -/
theorem entry_le (g : Idx → WeilCompactSmoothGV1) (hs : ∀ x, LogRadiusAt (g x) (ctr x) (1 / 4096))
    (hE : ∀ x, energy (g x).1 = 1) {x y : Idx} (hxy : y ≠ x) : ‖B (g x) (g y)‖ ≤ bnd x y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  simp only [bnd, if_neg hxy]
  by_cases ha : a' = a
  · subst ha
    rw [if_pos rfl]
    have hb : b ≠ b' := fun e => hxy (by rw [e])
    obtain ⟨h1, h31⟩ := fin_dist b b' hb
    have hbr : ((b : ℕ) : ℝ) ≠ ((b' : ℕ) : ℝ) := fun e => hb (Fin.ext (by exact_mod_cast e))
    rcases lt_or_gt_of_ne hbr with hlt | hlt
    · -- `g (a, b')` lies to the right
      have hm : |((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)| = ((b' : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
        rw [abs_of_neg (by linarith)]; ring
      rw [hm] at h1 h31 ⊢
      have hq : LogRadiusAt (g (a', b')) (ctr (a', b) + (((b' : ℕ) : ℝ) - ((b : ℕ) : ℝ)) / 1024) (1 / 4096) := by
        convert hs (a', b') using 2
        simp only [ctr]; ring
      exact entry_same h1 h31 (hs (a', b)) hq (hE _) (hE _)
    · have hm : |((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)| = ((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ) := by
        rw [abs_of_pos (by linarith)]
      rw [hm] at h1 h31 ⊢
      have hq : LogRadiusAt (g (a', b)) (ctr (a', b') + (((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)) / 1024) (1 / 4096) := by
        convert hs (a', b) using 2
        simp only [ctr]; ring
      rw [norm_B_swap]
      exact entry_same h1 h31 (hs (a', b')) hq (hE _) (hE _)
  · rw [if_neg ha]
    have htz : ∀ t : ℤ, (t : ℝ) = 0 ∨ 1 ≤ |(t : ℝ)| := fun t => by
      rcases eq_or_ne t 0 with h | h
      · left; simp [h]
      · right; rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
    have hdist : ∀ u v : Fin 32, |((u : ℕ) : ℝ) - ((v : ℕ) : ℝ)| ≤ 31 := fun u v => by
      by_cases h : u = v
      · subst h; simp
      · exact (fin_dist u v h).2
    have hcast : ∀ u v : Fin 32, ((u : ℕ) : ℝ) - ((v : ℕ) : ℝ) = (((u : ℕ) : ℤ) - ((v : ℕ) : ℤ) : ℤ) := by
      intro u v; push_cast; ring
    have hiff : ∀ u v : Fin 32, (((u : ℕ) : ℝ) - ((v : ℕ) : ℝ) = 0 ↔ u = v) := fun u v => by
      constructor
      · intro h; exact Fin.ext (by exact_mod_cast (sub_eq_zero.mp h))
      · intro h; subst h; ring
    fin_cases a <;> fin_cases a' <;> simp at ha ⊢
    · -- x in the low cluster, y in the high cluster: y to the right
      have hq : LogRadiusAt (g (1, b')) (ctr (0, b) + Real.log 2 + (((b' : ℕ) : ℝ) - ((b : ℕ) : ℝ)) / 1024) (1 / 4096) := by
        convert hs (1, b') using 2
        simp only [ctr]; norm_num; ring
      have h := entry_cross (hdist b' b) (by rw [hcast]; exact htz _) (hs (0, b)) hq (hE _) (hE _)
      have e : (((b' : ℕ) : ℝ) - ((b : ℕ) : ℝ) = 0) ↔ b' = b := hiff b' b
      simp only [e] at h
      convert h using 2
      norm_num
    · -- x in the high cluster, y in the low cluster: x to the right
      have hq : LogRadiusAt (g (1, b)) (ctr (0, b') + Real.log 2 + (((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)) / 1024) (1 / 4096) := by
        convert hs (1, b) using 2
        simp only [ctr]; norm_num; ring
      have h := entry_cross (hdist b b') (by rw [hcast]; exact htz _) (hs (0, b')) hq (hE _) (hE _)
      have e : (((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ) = 0) ↔ b' = b := by rw [hiff b b']; exact eq_comm
      simp only [e] at h
      rw [norm_B_swap]
      convert h using 2
      norm_num

/-- The same-cluster logarithm ratios multiply to `(2b+1)(63−2b) ≤ 1023` (checked in the kernel). -/
def rrQ (b b' : Fin 32) : ℚ :=
  (2 * |((b : ℕ) : ℚ) - ((b' : ℕ) : ℚ)| + 1) / (2 * |((b : ℕ) : ℚ) - ((b' : ℕ) : ℚ)| - 1)

theorem rrQ_prod_le : ∀ b : Fin 32, ∏ b' ∈ univ.erase b, rrQ b b' ≤ 1023 := by
  decide +kernel

theorem same_block_le (b : Fin 32) :
    ∑ b' : Fin 32, (if b' = b then (0 : ℝ) else 1 / 1024 + 1 / 2 * Real.log
      ((2 * |((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)| + 1) / (2 * |((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)| - 1))) ≤
      31 / 1024 + 7 / 2 := by
  set f : Fin 32 → ℝ := fun b' => (2 * |((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)| + 1) /
    (2 * |((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)| - 1) with hf
  have hpos : ∀ b' ∈ univ.erase b, 0 < f b' := by
    intro b' hb'
    have h := (fin_dist b b' (Ne.symm (Finset.ne_of_mem_erase hb'))).1
    simp only [hf]
    apply div_pos <;> linarith
  have hcastf : ∀ b', f b' = ((rrQ b b' : ℚ) : ℝ) := by
    intro b'; simp only [hf, rrQ]; push_cast; rfl
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_ne', Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum, ← Real.log_prod (fun b' hb' => (hpos b' hb').ne')]
  have hprod : ∏ b' ∈ univ.erase b, f b' ≤ 1023 := by
    have e : ∏ b' ∈ univ.erase b, f b' = ((∏ b' ∈ univ.erase b, rrQ b b' : ℚ) : ℝ) := by
      rw [Rat.cast_prod]; exact Finset.prod_congr rfl fun b' _ => hcastf b'
    rw [e]
    exact_mod_cast rrQ_prod_le b
  have hlog : Real.log (∏ b' ∈ univ.erase b, f b') ≤ Real.log 1023 :=
    Real.log_le_log (Finset.prod_pos hpos) hprod
  have := log_1023_lt
  norm_num
  linarith

theorem cross_block (b : Fin 32) :
    ∑ b' : Fin 32, ((if b' = b then Real.log 2 / Real.sqrt 2 else 0) + 1 / 512 : ℝ) =
      Real.log 2 / Real.sqrt 2 + 1 / 16 := by
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  norm_num

/-- **Row budget.** -/
theorem row_le (x : Idx) : ∑ y, bnd x y ≤ 31 / 1024 + 7 / 2 + 1 / 2 + 1 / 16 := by
  obtain ⟨a, b⟩ := x
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have hp := prime_coeff_lt
  have hs := same_block_le b
  have hc := cross_block b
  fin_cases a
  · simp only [bnd, Prod.mk.injEq, Fin.zero_eta, Fin.isValue, true_and, Fin.reduceEq, false_and,
      if_false, if_true] at hs hc ⊢
    linarith
  · simp only [bnd, Prod.mk.injEq, Fin.mk_one, Fin.isValue, true_and, Fin.reduceEq, false_and,
      if_false, if_true] at hs hc ⊢
    linarith

/-- **OPTIMUS V7, formalized**: the actual Weil form is coercive on the 64 packets. -/
theorem h64_coercive (g : Idx → WeilCompactSmoothGV1) (hs : ∀ x, LogRadiusAt (g x) (ctr x) (1 / 4096))
    (hE : ∀ x, energy (g x).1 = 1) (z : Idx → ℂ) :
    (1475 / 6144 : ℝ) * ∑ x, ‖z x‖ ^ 2 ≤ (∑ x, ∑ y, z x * (-B (g x) (g y)) * conj (z y)).re := by
  apply herm_form_ge (fun x y => -B (g x) (g y))
  · intro x y
    simp only [B_hermitian (g x) (g y), map_neg]
  · intro x
    have hd := diag_v7 (g x) (hs x)
    rw [hE x, mul_one] at hd
    have hoff : ∑ y, off (fun x y => -B (g x) (g y)) x y ≤ ∑ y, bnd x y := by
      refine Finset.sum_le_sum fun y _ => ?_
      unfold off
      by_cases h : y = x
      · simp [h, bnd]
      · rw [if_neg h, norm_neg]
        exact entry_le g hs hE h
    have hr := row_le x
    have hre : (-B (g x) (g x)).re = -(B (g x) (g x)).re := Complex.neg_re _
    simp only [hre]
    have := margin_eq
    linarith

end AEGIS.WeilH64AssemblyV7

#print axioms AEGIS.WeilH64AssemblyV7.rrQ_prod_le
#print axioms AEGIS.WeilH64AssemblyV7.entry_le
#print axioms AEGIS.WeilH64AssemblyV7.h64_coercive
