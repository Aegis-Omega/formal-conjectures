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
import WeilH64WitnessV7

/-!
# OPTIMUS V7.1: the sharp margin `7/6`

The V7.1 addendum on the same 64 packets:

* `w_eq`: `e^{−u/2}/(1 − e^{−2u}) = 1/(4 sinh(u/2)) + 1/(4 cosh(u/2))`, hence `w_le_sharp`:
  `w(u) ≤ 1/4 + 1/(2u)` and `w(u) ≤ 5/4` for `u ≥ 1/2`;
* same-cluster entries `≤ R + ½ log((2m+1)/(2m−1))`, cross-cluster Archimedean entries `≤ 5R`;
* diagonal `≥ log 4095 − log 4π − γ − 2R` with `γ < H₃₂ − 5 log 2` (`eulerMascheroniSeq'`) and
  `log π < 23/20` (`π < 3.15 < e · (1 + 3/20 + (3/20)²/2)`);
* row budget `31R + 5 log 2 + 5/128 + log 2/√2`, and `h64_coercive_sharp`:
  `(7/6) Σ ‖z x‖² ≤ Re Σ_{x,y} z x K x y conj(z y)`; `h64_sharp_nonvacuous` on the moment-zero witnesses.

Finite-dimensional coercivity of the restricted Weil form only. Not RH.
-/

open Set Function MeasureTheory Complex Finset
open scoped ComplexConjugate BigOperators

noncomputable section

namespace AEGIS.WeilH64SharpV71

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilH64ElementaryV7
open AEGIS.WeilH64DiagonalV7
open AEGIS.WeilH64CrossV7
open AEGIS.WeilH64PrimeV7
open AEGIS.WeilH64AssemblyV7

/-- **The kernel identity** `w(u) = 1/(4 sinh(u/2)) + 1/(4 cosh(u/2))`. -/
theorem w_eq {u : ℝ} (hu : 0 < u) :
    Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) =
      1 / (4 * Real.sinh (u / 2)) + 1 / (4 * Real.cosh (u / 2)) := by
  set t := Real.exp (-u / 2) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs : Real.exp (u / 2) = t⁻¹ := by
    rw [ht, ← Real.exp_neg]; congr 1; ring
  have h4 : Real.exp (-2 * u) = t ^ 4 := by
    rw [ht, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hsinh : Real.sinh (u / 2) = (t⁻¹ - t) / 2 := by
    rw [Real.sinh_eq, hs, show -(u / 2) = -u / 2 by ring]
  have hcosh : Real.cosh (u / 2) = (t⁻¹ + t) / 2 := by
    rw [Real.cosh_eq, hs, show -(u / 2) = -u / 2 by ring]
  rw [h4, hsinh, hcosh]
  have hne : t ≠ 0 := ht0.ne'
  have h2 : 1 - t ^ 2 ≠ 0 := by nlinarith
  have h2' : 1 + t ^ 2 ≠ 0 := by positivity
  have h4' : 1 - t ^ 4 ≠ 0 := by nlinarith [pow_pos ht0 4, pow_lt_one₀ ht0.le ht1 (by norm_num : 4 ≠ 0)]
  have e1 : t⁻¹ - t = (1 - t ^ 2) / t := by field_simp
  have e2 : t⁻¹ + t = (1 + t ^ 2) / t := by field_simp
  rw [e1, e2]
  field_simp
  ring

/-- **V7.1 kernel bound**: `w(u) ≤ 1/4 + 1/(2u)`. -/
theorem w_le_sharp {u : ℝ} (hu : 0 < u) :
    Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) ≤ 1 / 4 + 1 / (2 * u) := by
  rw [w_eq hu]
  have hv : 0 < u / 2 := by linarith
  have hsh : u / 2 ≤ Real.sinh (u / 2) := Real.self_le_sinh_iff.mpr hv.le
  have hch : 1 ≤ Real.cosh (u / 2) := Real.one_le_cosh _
  have h1 : 1 / (4 * Real.sinh (u / 2)) ≤ 1 / (2 * u) := by
    apply one_div_le_one_div_of_le (by linarith); linarith
  have h2 : 1 / (4 * Real.cosh (u / 2)) ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  linarith

theorem w_le_five_quarters {u : ℝ} (hu : 1 / 2 ≤ u) :
    Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) ≤ 5 / 4 := by
  have h := w_le_sharp (show 0 < u by linarith)
  have : 1 / (2 * u) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  linarith

/-- Same-cluster Archimedean bound with the sharp kernel: `E ((hi − lo)/4 + ½ log(hi/lo))`. -/
theorem sep_arch_le_sharp (p q : WeilCompactSmoothGV1) {plo phi qlo qhi E : ℝ}
    (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi) (hsep : phi < qlo)
    (hlohi : qlo - phi ≤ qhi - plo) (hE : ∀ u, ‖logCrossV28 p q u‖ ≤ E) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤
      E * (((qhi - plo) - (qlo - phi)) / 4 + 1 / 2 * Real.log ((qhi - plo) / (qlo - phi))) := by
  set lo := qlo - phi
  set hi := qhi - plo
  have hlo : 0 < lo := by simp only [lo]; linarith
  have hb : ContinuousOn (fun u : ℝ => 1 / 4 + 1 / 2 * u⁻¹) (Icc lo hi) :=
    continuousOn_const.add (continuousOn_const.mul (continuousOn_inv₀.mono fun u hu =>
      (ne_of_gt (lt_of_lt_of_le hlo hu.1))))
  have hwb : ∀ u ∈ Icc lo hi, wK u ≤ 1 / 4 + 1 / 2 * u⁻¹ := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hlo hu.1
    have := w_le_sharp hu0
    have e : 1 / (2 * u) = 1 / 2 * u⁻¹ := by field_simp
    rw [← e]; exact this
  refine (sep_arch_norm_le_integral p q hp hq hsep hE hb hwb).trans (le_of_eq ?_)
  congr 1
  have hhi : 0 < hi := lt_of_lt_of_le hlo hlohi
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 / 4 : ℝ)) volume lo hi := intervalIntegrable_const
  have h2 : IntervalIntegrable (fun x : ℝ => 1 / 2 * x⁻¹) volume lo hi := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.mul
    apply continuousOn_inv₀.mono
    intro u hu
    rw [Set.uIcc_of_le hlohi] at hu
    exact ne_of_gt (lt_of_lt_of_le hlo hu.1)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlohi,
    intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_inv_of_pos hlo hhi, smul_eq_mul]
  ring

/-- Cross-cluster Archimedean bound with `w ≤ 5/4`. -/
theorem sep_arch_le_five (p q : WeilCompactSmoothGV1) {plo phi qlo qhi E : ℝ}
    (hp : LogSupportIn p plo phi) (hq : LogSupportIn q qlo qhi) (hgap : 1 / 2 ≤ qlo - phi)
    (hlohi : qlo - phi ≤ qhi - plo) (hE : ∀ u, ‖logCrossV28 p q u‖ ≤ E) :
    ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤ E * (5 / 4 * ((qhi - plo) - (qlo - phi))) := by
  have hsep : phi < qlo := by linarith
  have hwb : ∀ u ∈ Icc (qlo - phi) (qhi - plo), wK u ≤ (fun _ => (5 / 4 : ℝ)) u := fun u hu =>
    w_le_five_quarters (le_trans hgap hu.1)
  refine (sep_arch_norm_le_integral p q hp hq hsep hE continuousOn_const hwb).trans (le_of_eq ?_)
  rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le hlohi]
  ring

theorem entry_same_sharp {p q : WeilCompactSmoothGV1} {c m : ℝ} (hm1 : 1 ≤ m) (hm : m ≤ 31)
    (hp : LogRadiusAt p c (1 / 4096)) (hq : LogRadiusAt q (c + m / 1024) (1 / 4096))
    (hEp : energy p.1 = 1) (hEq : energy q.1 = 1) :
    ‖B p q‖ ≤ 1 / 4096 + 1 / 2 * Real.log ((2 * m + 1) / (2 * m - 1)) := by
  have hp' : LogSupportIn p (c - 1 / 4096) (c + 1 / 4096) := hp
  have hq' : LogSupportIn q (c + m / 1024 - 1 / 4096) (c + m / 1024 + 1 / 4096) := hq
  have hsep : c + 1 / 4096 < c + m / 1024 - 1 / 4096 := by linarith
  have hl2 := Real.log_two_gt_d9
  have h3 : (c + m / 1024 + 1 / 4096) - (c - 1 / 4096) < Real.log 3 := by linarith [log3_gt]
  have h2 : (c + m / 1024 + 1 / 4096) - (c - 1 / 4096) < Real.log 2 := by linarith
  have hpz := prime_sum_zero hp' hq' hsep h3 (Or.inr h2)
  have ha := sep_arch_le_sharp p q hp' hq' hsep (by linarith) (cross_unit hEp hEq)
  have hB := B_sep_norm_le hp' hq' hsep
  rw [hpz, norm_zero, zero_add] at hB
  refine hB.trans (ha.trans (le_of_eq ?_))
  have e1 : ((c + m / 1024 + 1 / 4096) - (c - 1 / 4096) - ((c + m / 1024 - 1 / 4096) - (c + 1 / 4096))) / 4 =
      1 / 4096 := by ring
  have hden : (2 * m - 1) ≠ 0 := by linarith
  have e2 : ((c + m / 1024 + 1 / 4096) - (c - 1 / 4096)) / ((c + m / 1024 - 1 / 4096) - (c + 1 / 4096)) =
      (2 * m + 1) / (2 * m - 1) := by
    rw [show (c + m / 1024 + 1 / 4096) - (c - 1 / 4096) = (2 * m + 1) / 2048 by ring,
      show (c + m / 1024 - 1 / 4096) - (c + 1 / 4096) = (2 * m - 1) / 2048 by ring]
    field_simp
  rw [e1, e2]
  ring

theorem entry_cross_sharp {p q : WeilCompactSmoothGV1} {c t : ℝ} (ht : |t| ≤ 31) (htz : t = 0 ∨ 1 ≤ |t|)
    (hp : LogRadiusAt p c (1 / 4096)) (hq : LogRadiusAt q (c + Real.log 2 + t / 1024) (1 / 4096))
    (hEp : energy p.1 = 1) (hEq : energy q.1 = 1) :
    ‖B p q‖ ≤ (if t = 0 then Real.log 2 / Real.sqrt 2 else 0) + 5 / 4096 := by
  have hp' : LogSupportIn p (c - 1 / 4096) (c + 1 / 4096) := hp
  have hq' : LogSupportIn q (c + Real.log 2 + t / 1024 - 1 / 4096) (c + Real.log 2 + t / 1024 + 1 / 4096) := hq
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hta := abs_le.mp ht
  have hgap : 1 / 2 ≤ (c + Real.log 2 + t / 1024 - 1 / 4096) - (c + 1 / 4096) := by linarith
  have hsep : c + 1 / 4096 < c + Real.log 2 + t / 1024 - 1 / 4096 := by linarith
  have h3 : (c + Real.log 2 + t / 1024 + 1 / 4096) - (c - 1 / 4096) < Real.log 3 := by linarith [log3_gt]
  have ha := sep_arch_le_five p q hp' hq' hgap (by linarith) (cross_unit hEp hEq)
  have hB := B_sep_norm_le hp' hq' hsep
  have ha' : ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤ 5 / 4096 := by
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

/-- The sharp row bound of an off-diagonal entry. -/
def bnd2 (x y : Idx) : ℝ :=
  if y = x then 0
  else if y.1 = x.1 then
    1 / 4096 + 1 / 2 * Real.log ((2 * |((x.2 : ℕ) : ℝ) - ((y.2 : ℕ) : ℝ)| + 1) /
      (2 * |((x.2 : ℕ) : ℝ) - ((y.2 : ℕ) : ℝ)| - 1))
  else (if y.2 = x.2 then Real.log 2 / Real.sqrt 2 else 0) + 5 / 4096

theorem entry_le_sharp (g : Idx → WeilCompactSmoothGV1) (hs : ∀ x, LogRadiusAt (g x) (ctr x) (1 / 4096))
    (hE : ∀ x, energy (g x).1 = 1) {x y : Idx} (hxy : y ≠ x) : ‖B (g x) (g y)‖ ≤ bnd2 x y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  simp only [bnd2, if_neg hxy]
  by_cases ha : a' = a
  · subst ha
    rw [if_pos rfl]
    have hb : b ≠ b' := fun e => hxy (by rw [e])
    obtain ⟨h1, h31⟩ := fin_dist b b' hb
    have hbr : ((b : ℕ) : ℝ) ≠ ((b' : ℕ) : ℝ) := fun e => hb (Fin.ext (by exact_mod_cast e))
    rcases lt_or_gt_of_ne hbr with hlt | hlt
    · have hm : |((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)| = ((b' : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
        rw [abs_of_neg (by linarith)]; ring
      rw [hm] at h1 h31 ⊢
      have hq : LogRadiusAt (g (a', b')) (ctr (a', b) + (((b' : ℕ) : ℝ) - ((b : ℕ) : ℝ)) / 1024) (1 / 4096) := by
        convert hs (a', b') using 2
        simp only [ctr]; ring
      exact entry_same_sharp h1 h31 (hs (a', b)) hq (hE _) (hE _)
    · have hm : |((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)| = ((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ) := by
        rw [abs_of_pos (by linarith)]
      rw [hm] at h1 h31 ⊢
      have hq : LogRadiusAt (g (a', b)) (ctr (a', b') + (((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)) / 1024) (1 / 4096) := by
        convert hs (a', b) using 2
        simp only [ctr]; ring
      rw [norm_B_swap]
      exact entry_same_sharp h1 h31 (hs (a', b')) hq (hE _) (hE _)
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
    · have hq : LogRadiusAt (g (1, b')) (ctr (0, b) + Real.log 2 + (((b' : ℕ) : ℝ) - ((b : ℕ) : ℝ)) / 1024) (1 / 4096) := by
        convert hs (1, b') using 2
        simp only [ctr]; norm_num; ring
      have h := entry_cross_sharp (hdist b' b) (by rw [hcast]; exact htz _) (hs (0, b)) hq (hE _) (hE _)
      have e : (((b' : ℕ) : ℝ) - ((b : ℕ) : ℝ) = 0) ↔ b' = b := hiff b' b
      simp only [e] at h
      convert h using 2
    · have hq : LogRadiusAt (g (1, b)) (ctr (0, b') + Real.log 2 + (((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)) / 1024) (1 / 4096) := by
        convert hs (1, b) using 2
        simp only [ctr]; norm_num; ring
      have h := entry_cross_sharp (hdist b b') (by rw [hcast]; exact htz _) (hs (0, b')) hq (hE _) (hE _)
      have e : (((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ) = 0) ↔ b' = b := by rw [hiff b b']; exact eq_comm
      simp only [e] at h
      rw [norm_B_swap]
      convert h using 2

theorem same_block_le_sharp (b : Fin 32) :
    ∑ b' : Fin 32, (if b' = b then (0 : ℝ) else 1 / 4096 + 1 / 2 * Real.log
      ((2 * |((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)| + 1) / (2 * |((b : ℕ) : ℝ) - ((b' : ℕ) : ℝ)| - 1))) ≤
      31 / 4096 + 5 * Real.log 2 := by
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
  have h1024 : Real.log 1023 < 10 * Real.log 2 := by
    have : Real.log 1023 < Real.log 1024 := Real.log_lt_log (by norm_num) (by norm_num)
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow] at this
    norm_num at this
    linarith
  norm_num
  linarith

theorem cross_block_sharp (b : Fin 32) :
    ∑ b' : Fin 32, ((if b' = b then Real.log 2 / Real.sqrt 2 else 0) + 5 / 4096 : ℝ) =
      Real.log 2 / Real.sqrt 2 + 5 / 128 := by
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  norm_num

theorem row_le_sharp (x : Idx) : ∑ y, bnd2 x y ≤ 31 / 4096 + 5 * Real.log 2 + 1 / 2 + 5 / 128 := by
  obtain ⟨a, b⟩ := x
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have hp := prime_coeff_lt
  have hs := same_block_le_sharp b
  have hc := cross_block_sharp b
  fin_cases a
  · simp only [bnd2, Prod.mk.injEq, Fin.zero_eta, Fin.isValue, true_and, Fin.reduceEq, false_and,
      if_false, if_true] at hs hc ⊢
    linarith
  · simp only [bnd2, Prod.mk.injEq, Fin.mk_one, Fin.isValue, true_and, Fin.reduceEq, false_and,
      if_false, if_true] at hs hc ⊢
    linarith

/-- `log π < 23/20`. -/
theorem log_pi_lt : Real.log Real.pi < 23 / 20 := by
  rw [Real.log_lt_iff_lt_exp Real.pi_pos]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 20 by norm_num)
  have h3 : Real.exp (23 / 20) = Real.exp 1 * Real.exp (3 / 20) := by
    rw [← Real.exp_add]; norm_num
  have hp := Real.pi_lt_d2
  rw [h3]
  nlinarith [Real.exp_pos 1, Real.exp_pos (3 / 20)]

/-- `γ < H₃₂ − 5 log 2`. -/
theorem gamma_lt : Real.eulerMascheroniConstant < 586061125622639 / 144403552893600 - 5 * Real.log 2 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 32
  have hH : (harmonic 32 : ℝ) = 586061125622639 / 144403552893600 := by
    simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have hl : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
  simp only [Real.eulerMascheroniSeq', if_neg (by norm_num : (32 : ℕ) ≠ 0)] at h
  push_cast at h
  rw [hH, hl] at h
  exact h

/-- **The V7.1 diagonal constant**. -/
theorem diag_sharp (g : WeilCompactSmoothGV1) {a : ℝ} (hw : LogRadiusAt g a (1 / 4096)) :
    (15 * Real.log 2 - 586061125622639 / 144403552893600 - 23 / 20 - 2 / 4096 - 1 / 4095) * energy g.1 ≤
      -(B g g).re := by
  have hd := diag_radius g (by norm_num) (by norm_num) hw
  have hT := sinhTail_ge (w := 2 * (1 / 4096)) (by norm_num) (by norm_num)
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hlog : 12 * Real.log 2 - 1 / 4095 ≤ Real.log ((2 - 2 * (1 / 4096)) / (2 * (1 / 4096))) := by
    rw [show (2 - 2 * (1 / 4096 : ℝ)) / (2 * (1 / 4096)) = 4096 * (4095 / 4096) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4095 / 4096 by norm_num)
    norm_num at this ⊢
    linarith
  have h4pi : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hpi := log_pi_lt
  have hg := gamma_lt
  have hconst : 15 * Real.log 2 - 586061125622639 / 144403552893600 - 23 / 20 - 2 / 4096 - 1 / 4095 ≤
      sinhTail (2 * (1 / 4096)) - diagonalKappaV21 - 2 * (1 / 4096) := by
    unfold diagonalKappaV21
    rw [h4pi]
    linarith
  calc (15 * Real.log 2 - 586061125622639 / 144403552893600 - 23 / 20 - 2 / 4096 - 1 / 4095) * energy g.1
      ≤ (sinhTail (2 * (1 / 4096)) - diagonalKappaV21 - 2 * (1 / 4096)) * energy g.1 :=
        mul_le_mul_of_nonneg_right hconst hE
    _ = energy g.1 * (sinhTail (2 * (1 / 4096)) - diagonalKappaV21 - 2 * (1 / 4096)) := by ring
    _ ≤ -(B g g).re := hd

/-- **OPTIMUS V7.1, formalized**: the sharp margin `7/6`. -/
theorem h64_coercive_sharp (g : Idx → WeilCompactSmoothGV1)
    (hs : ∀ x, LogRadiusAt (g x) (ctr x) (1 / 4096)) (hE : ∀ x, energy (g x).1 = 1) (z : Idx → ℂ) :
    (7 / 6 : ℝ) * ∑ x, ‖z x‖ ^ 2 ≤ (∑ x, ∑ y, z x * (-B (g x) (g y)) * conj (z y)).re := by
  apply herm_form_ge (fun x y => -B (g x) (g y))
  · intro x y
    simp only [B_hermitian (g x) (g y), map_neg]
  · intro x
    have hd := diag_sharp (g x) (hs x)
    rw [hE x, mul_one] at hd
    have hoff : ∑ y, off (fun x y => -B (g x) (g y)) x y ≤ ∑ y, bnd2 x y := by
      refine Finset.sum_le_sum fun y _ => ?_
      unfold off
      by_cases h : y = x
      · simp [h, bnd2]
      · rw [if_neg h, norm_neg]
        exact entry_le_sharp g hs hE h
    have hr := row_le_sharp x
    have hre : (-B (g x) (g x)).re = -(B (g x) (g x)).re := Complex.neg_re _
    simp only [hre]
    have hl := Real.log_two_gt_d9
    linarith

/-- The sharp bound on the 64 moment-zero witnesses. -/
theorem h64_sharp_nonvacuous :
    ∃ g : Idx → WeilCompactSmoothGV1,
      (∀ x, LogRadiusAt (g x) (ctr x) (1 / 4096)) ∧ (∀ x, energy (g x).1 = 1) ∧
      (∀ x, WeilMomentConditionsV1 (g x)) ∧
      ∀ z : Idx → ℂ, (7 / 6 : ℝ) * ∑ x, ‖z x‖ ^ 2 ≤
        (∑ x, ∑ y, z x * (-B (g x) (g y)) * conj (z y)).re :=
  ⟨fun x => AEGIS.WeilH64WitnessV7.pkt (ctr x), fun _ => AEGIS.WeilH64WitnessV7.pkt_logRadius _,
    fun _ => AEGIS.WeilH64WitnessV7.pkt_energy _, fun _ => AEGIS.WeilH64WitnessV7.pkt_moments _,
    h64_coercive_sharp _ (fun _ => AEGIS.WeilH64WitnessV7.pkt_logRadius _)
      (fun _ => AEGIS.WeilH64WitnessV7.pkt_energy _)⟩

end AEGIS.WeilH64SharpV71

#print axioms AEGIS.WeilH64SharpV71.w_le_sharp
#print axioms AEGIS.WeilH64SharpV71.gamma_lt
#print axioms AEGIS.WeilH64SharpV71.log_pi_lt
#print axioms AEGIS.WeilH64SharpV71.h64_coercive_sharp
#print axioms AEGIS.WeilH64SharpV71.h64_sharp_nonvacuous
