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
import CvSRelRowFormL118V1
import CvSTauR1PrimeL118V1
import CvSDiagL118V1

/-!
# The true CvS data at `L = 11/8` against the integer midpoints

* `tau_box`: `|τ_n − tq n/2^49| ≤ rt_n/2^49` for `|n| ≤ 250` (the kernel-checked boxes of
  `CvSTauPrimeL118V1`, `CvSTauR1PrimeL118V1` and `τ_{-n} = −τ_n`);
* `diag_box`: the same for `cvsEntry M (11/8) n n`, `|n| ≤ 70`;
* `E_off`: off the diagonal `cvsEntry M (11/8) n m = (11/(16π²)) (τ_n − τ_m)/(n − m)`;
* `acoef_eq`, `a_sub_ahat`: the low-block coefficients are `a_n = f_n u_n` with
  `f_n = −(16πn/11)² − 1/4`, and `‖a_n − â_n‖ ≤ 10^-19 ‖â_n‖` (`π²` against `SI/2^70`).
Not RH.
-/

open Finset
open scoped ComplexConjugate
open AEGIS.CvSRelRowDataL118V1 AEGIS.CvSRelRowFormL118V1 AEGIS.CvSRowTailV1
  AEGIS.CvSMomentBasisV1 AEGIS.CvSLowBlockMatrixV1

noncomputable section

namespace AEGIS.CvSRelRowBoxL118V1

set_option maxRecDepth 100000

/-! ## Maxima of the box data (kernel-checked) -/

def rhoq : ℤ := 5619065
def rhoHq : ℤ := 43578786
def rDq : ℤ := 4933081
def tmq : ℤ := 6435811284768227
def tmHq : ℤ := 6700840789457906
def dmq : ℤ := 3185043643941904

theorem maxima_ok : ((List.range 71).all fun k =>
    decide (0 ≤ rtLit.getD k 0 ∧ rtLit.getD k 0 ≤ rhoq ∧ |tLit.getD k 0| ≤ tmq ∧
      0 ≤ rdLit.getD k 0 ∧ rdLit.getD k 0 ≤ rDq ∧ |dLit.getD k 0| ≤ dmq)) &&
    ((List.range 251).all fun k => decide (0 ≤ rtLit.getD k 0 ∧ rtLit.getD k 0 ≤ max rhoq rhoHq ∧
      |tLit.getD k 0| ≤ max tmq tmHq)) = true := by
  decide +kernel

theorem max_low {k : ℕ} (hk : k ≤ 70) :
    0 ≤ rtLit.getD k 0 ∧ rtLit.getD k 0 ≤ rhoq ∧ |tLit.getD k 0| ≤ tmq ∧
      0 ≤ rdLit.getD k 0 ∧ rdLit.getD k 0 ≤ rDq ∧ |dLit.getD k 0| ≤ dmq := by
  have h := maxima_ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h.1 k (by omega)

theorem max_all {k : ℕ} (hk : k ≤ 250) :
    0 ≤ rtLit.getD k 0 ∧ rtLit.getD k 0 ≤ max rhoq rhoHq ∧ |tLit.getD k 0| ≤ max tmq tmHq := by
  have h := maxima_ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h.2 k (by omega)

/-! ## The boxes -/

theorem boxes_at {k : ℕ} (hk : k ≤ 250) :
    ((tLit.getD k 0 : ℤ) : ℝ) = ((boxLo k : ℚ) + (boxHi k : ℚ) : ℝ) * 2 ^ 48 ∧
      ((rtLit.getD k 0 : ℤ) : ℝ) = ((boxHi k : ℚ) - (boxLo k : ℚ) : ℝ) * 2 ^ 48 := by
  have h := boxes_ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h.1 k (by omega)
  constructor
  · have := congrArg (fun q : ℚ => (q : ℝ)) h1; push_cast at this ⊢; exact this
  · have := congrArg (fun q : ℚ => (q : ℝ)) h2; push_cast at this ⊢; exact this

theorem dboxes_at {n : ℕ} (hn : n ≤ 70) :
    ((dLit.getD n 0 : ℤ) : ℝ) = (((AEGIS.CvSDiagL118V1.diagLo.getD n 0 : ℚ) : ℝ) +
        ((AEGIS.CvSDiagL118V1.diagHi.getD n 0 : ℚ) : ℝ)) * 2 ^ 48 ∧
      ((rdLit.getD n 0 : ℤ) : ℝ) = (((AEGIS.CvSDiagL118V1.diagHi.getD n 0 : ℚ) : ℝ) -
        ((AEGIS.CvSDiagL118V1.diagLo.getD n 0 : ℚ) : ℝ)) * 2 ^ 48 := by
  have h := boxes_ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h.2 n (by omega)
  constructor
  · have := congrArg (fun q : ℚ => (q : ℝ)) h1; push_cast at this ⊢; exact this
  · have := congrArg (fun q : ℚ => (q : ℝ)) h2; push_cast at this ⊢; exact this

theorem mid_le {x lo hi t r : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) (ht : t = (lo + hi) * 2 ^ 48)
    (hr : r = (hi - lo) * 2 ^ 48) : |x - t / 2 ^ 49| ≤ r / 2 ^ 49 := by
  subst ht hr
  rw [abs_le]; constructor <;> nlinarith

theorem tau_pos_box {M : ℕ} (hM : 3 ≤ M) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 250) :
    ((boxLo k : ℚ) : ℝ) ≤ tau M (11 / 8) k ∧ tau M (11 / 8) k ≤ ((boxHi k : ℚ) : ℝ) := by
  by_cases h70 : k ≤ 70
  · have e1 : boxLo k = AEGIS.CvSTauPrimeL118V1.tauFLo.getD (k - 1) 0 := by
      simp [boxLo, show k ≠ 0 by omega, h70]
    have e2 : boxHi k = AEGIS.CvSTauPrimeL118V1.tauFHi.getD (k - 1) 0 := by
      simp [boxHi, show k ≠ 0 by omega, h70]
    rw [e1, e2]
    exact AEGIS.CvSTauPrimeL118V1.tau_mem hM hk1 h70
  · have e1 : boxLo k = AEGIS.CvSTauR1PrimeL118V1.tauFLoExtra.getD (k - 71) 0 := by
      simp [boxLo, show k ≠ 0 by omega, h70]
    have e2 : boxHi k = AEGIS.CvSTauR1PrimeL118V1.tauFHiExtra.getD (k - 71) 0 := by
      simp [boxHi, show k ≠ 0 by omega, h70]
    rw [e1, e2]
    exact AEGIS.CvSTauR1PrimeL118V1.tau_mem_R1 hM (by omega) hk

theorem tLit_zero : tLit.getD 0 0 = 0 ∧ rtLit.getD 0 0 = 0 := by decide

/-- **The `τ` boxes in integer form.** -/
theorem tau_box {M : ℕ} (hM : 3 ≤ M) {n : ℤ} (hn : n.natAbs ≤ 250) :
    |tau M (11 / 8) n - (tq n : ℝ) / 2 ^ 49| ≤ (rtLit.getD n.natAbs 0 : ℝ) / 2 ^ 49 := by
  have pos : ∀ k : ℕ, k ≤ 250 →
      |tau M (11 / 8) k - (tLit.getD k 0 : ℝ) / 2 ^ 49| ≤ (rtLit.getD k 0 : ℝ) / 2 ^ 49 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [tLit_zero.1, tLit_zero.2]
      simp [AEGIS.CvSTauPrimeL12V1.tau_zero]
    · obtain ⟨b1, b2⟩ := tau_pos_box hM hk1 hk
      obtain ⟨e1, e2⟩ := boxes_at hk
      exact mid_le b1 b2 e1 e2
  rcases le_or_gt 0 n with h | h
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, (Int.toNat_of_nonneg h).symm⟩
    have := pos k (by simpa using hn)
    simpa [tq] using this
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
    subst hk
    have hk' : k ≤ 250 := by simpa using hn
    have := pos k hk'
    have e : tq (-(k : ℤ)) = -tLit.getD k 0 := by
      simp only [tq]
      rw [if_neg (by omega)]
      simp
    rw [AEGIS.CvSTauPrimeL12V1.tau_neg, e]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    push_cast
    rw [show -tau M (11 / 8) (k : ℤ) - -(tLit.getD k 0 : ℝ) / 2 ^ 49 =
      -(tau M (11 / 8) k - (tLit.getD k 0 : ℝ) / 2 ^ 49) by ring, abs_neg]
    exact this

/-- **The diagonal boxes in integer form.** -/
theorem diag_box {M : ℕ} (hM : 3 ≤ M) {n : ℤ} (hn : n.natAbs ≤ 70) :
    |cvsEntry M (11 / 8) n n - (dq n : ℝ) / 2 ^ 49| ≤ (rdLit.getD n.natAbs 0 : ℝ) / 2 ^ 49 := by
  have hd : cvsEntry M (11 / 8) n n = cvsEntry M (11 / 8) (n.natAbs : ℤ) (n.natAbs : ℤ) := by
    rcases Int.natAbs_eq n with h | h
    · rw [← h]
    · conv_lhs => rw [h]
      exact AEGIS.CvSDiagL118V1.cvsEntry_diag_neg hM _
  obtain ⟨b1, b2⟩ := AEGIS.CvSDiagL118V1.diag_mem hM hn
  obtain ⟨e1, e2⟩ := dboxes_at hn
  rw [hd]
  exact mid_le b1 b2 e1 e2

/-- Off the diagonal the CvS matrix is a divided difference of `τ`. -/
theorem E_off (M : ℕ) {n m : ℤ} (h : n ≠ m) :
    cvsEntry M (11 / 8) n m =
      11 / (16 * Real.pi ^ 2) * ((tau M (11 / 8) n - tau M (11 / 8) m) / (n - m)) := by
  rw [cvsEntry_off M (by norm_num) h]
  congr 1
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ## `π²` and the frequency factors -/

def SIr : ℝ := (SI : ℝ) / 2 ^ 70

theorem pi_sq_bounds : |Real.pi ^ 2 - SIr| ≤ 1 / 2 ^ 63 ∧ (9 : ℝ) ≤ SIr ∧ (9 : ℝ) ≤ Real.pi ^ 2 := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  have l : (3.14159265358979323846 : ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith
  have u : Real.pi ^ 2 < (3.14159265358979323847 : ℝ) ^ 2 := by nlinarith
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, by norm_num [SIr, SI], by nlinarith⟩
  · norm_num [SIr, SI] at l ⊢; linarith
  · norm_num [SIr, SI] at u ⊢; linarith

/-- `f_n = (iω_n)² − 1/4` at `L = 11/8`, real. -/
def fr (n : ℤ) : ℝ := -(256 / 121) * Real.pi ^ 2 * (n : ℝ) ^ 2 - 1 / 4

theorem fC_eq (n : ℤ) : iw (11 / 8) n * iw (11 / 8) n - 1 / 4 = ((fr n : ℝ) : ℂ) := by
  simp only [iw, fr]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem phi_div (n : ℤ) :
    (phi n : ℝ) / (121 * 2 ^ 72) = -(256 / 121) * SIr * (n : ℝ) ^ 2 - 1 / 4 := by
  simp only [phi, SIr]
  push_cast
  ring

def theta : ℝ := 1 / 10 ^ 19

theorem fr_sub (n : ℤ) :
    |fr n - (phi n : ℝ) / (121 * 2 ^ 72)| ≤ theta * |(phi n : ℝ) / (121 * 2 ^ 72)| := by
  obtain ⟨hs, h9, -⟩ := pi_sq_bounds
  rw [phi_div]
  have hn : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have e : fr n - (-(256 / 121) * SIr * (n : ℝ) ^ 2 - 1 / 4) =
      -(256 / 121) * (n : ℝ) ^ 2 * (Real.pi ^ 2 - SIr) := by
    simp only [fr]; ring
  rw [e, abs_of_neg (show -(256 / 121) * SIr * (n : ℝ) ^ 2 - 1 / 4 < 0 by nlinarith), abs_mul,
    abs_mul, abs_of_nonneg hn]
  have ha := abs_nonneg (Real.pi ^ 2 - SIr)
  simp only [theta]
  norm_num
  nlinarith [mul_le_mul_of_nonneg_left hs hn]

/-! ## The low-block coefficients -/

/-- The actual low-block coefficients at `L = 11/8`. -/
def acoef (c : Fin 139 → ℂ) (n : ℤ) : ℂ :=
  lowCoeff (11 / 8) (fun i => sinSqSupport (ctr i)) (fun i => sinSqWeight (ctr i)) c n

theorem acoef_eq (c : Fin 139 → ℂ) (n : ℤ) : acoef c n = ((fr n : ℝ) : ℂ) * uvec c n := by
  simp only [acoef, lowCoeff, uvec, wt, Finset.mul_sum, ← fC_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

theorem a_sub_ahat (c : Fin 139 → ℂ) (n : ℤ) :
    ‖acoef c n - ahat c n‖ ≤ theta * ‖ahat c n‖ := by
  rw [acoef_eq, ahat, ← sub_mul, norm_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (fr_sub n) (norm_nonneg _)

end AEGIS.CvSRelRowBoxL118V1

end

#print axioms AEGIS.CvSRelRowBoxL118V1.tau_box
#print axioms AEGIS.CvSRelRowBoxL118V1.diag_box
#print axioms AEGIS.CvSRelRowBoxL118V1.E_off
#print axioms AEGIS.CvSRelRowBoxL118V1.a_sub_ahat
