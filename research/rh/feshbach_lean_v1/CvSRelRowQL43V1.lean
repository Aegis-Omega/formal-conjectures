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
import CvSRelRowAlgebraV1
import CvSSchurClosureFromBoundsV1

/-!
# The low form at `L = 4/3` from below by its midpoint

`Q_ge`: `Q_CvS M (4/3) ctr c ≥ Re Σ_{n,m ∈ F} â_n conj(â_m) Et(n,m)/2^128 − ε_Q Σ_F |â_n|²` with
`ε_Q = RE + RA (2θ + θ²)`, `RA = 6 · 141`. The coefficients `a = â + d`, `|d_n| ≤ θ |â_n|`
(`a_sub_ahat`); the bilinear terms are bounded by the Schur test (`bilin_le`). Not RH.
-/

open Finset
open scoped ComplexConjugate
open AEGIS.CvSRelRowDataL43V1 AEGIS.CvSRelRowBoxL43V1 AEGIS.CvSRelRowFormL43V1
  AEGIS.CvSRelRowErrL43V1 AEGIS.CvSRelRowAlgebraV1 AEGIS.CvSLowBlockMatrixV1
  AEGIS.CvSSchurClosureFromBoundsV1 AEGIS.CvSMomentBasisV1

noncomputable section

namespace AEGIS.CvSRelRowQL43V1

/-! ## Generic helpers -/

/-- `√(Σ_F |v_n|²)`. -/
def nrm (v : ℤ → ℂ) : ℝ := √(∑ n ∈ F, ‖v n‖ ^ 2)

theorem nrm_nonneg (v : ℤ → ℂ) : 0 ≤ nrm v := Real.sqrt_nonneg _

theorem nrm_sq (v : ℤ → ℂ) : nrm v * nrm v = ∑ n ∈ F, ‖v n‖ ^ 2 :=
  Real.mul_self_sqrt (sum_nonneg fun _ _ => sq_nonneg _)

/-- The Schur test for a bilinear form, unsquared. -/
theorem bilin_le (X e : ℤ → ℤ → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hX : ∀ n ∈ F, ∀ m ∈ F, |X n m| ≤ e n m) (hsym : ∀ n ∈ F, ∀ m ∈ F, e n m = e m n)
    (hrow : ∀ n ∈ F, ∑ m ∈ F, e n m ≤ R) (x y : ℤ → ℂ) :
    ‖∑ n ∈ F, ∑ m ∈ F, x n * conj (y m) * (X n m : ℂ)‖ ≤ R * nrm x * nrm y := by
  have h := schur_bilin F X e hX hsym hrow x y
  have hA : 0 ≤ ∑ n ∈ F, ‖x n‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hB : 0 ≤ ∑ n ∈ F, ‖y n‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have e : R * nrm x * nrm y = √(R ^ 2 * ((∑ n ∈ F, ‖x n‖ ^ 2) * ∑ m ∈ F, ‖y m‖ ^ 2)) := by
    rw [Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR, Real.sqrt_mul hA, nrm, nrm, mul_assoc]
  rw [e]
  exact Real.le_sqrt_of_sq_le h

/-- A pointwise relative bound gives the same bound on `nrm`. -/
theorem nrm_le_of {v w : ℤ → ℂ} {k : ℝ} (hk : 0 ≤ k) (h : ∀ n ∈ F, ‖v n‖ ≤ k * ‖w n‖) :
    nrm v ≤ k * nrm w := by
  have hs : ∑ n ∈ F, ‖v n‖ ^ 2 ≤ k ^ 2 * ∑ n ∈ F, ‖w n‖ ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    have := h n hn
    have := norm_nonneg (v n)
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h n hn) 2
  rw [nrm, nrm, ← Real.sqrt_sq hk, ← Real.sqrt_mul (sq_nonneg k)]
  exact Real.sqrt_le_sqrt hs

/-! ## The low form -/

/-- `Q_CvS` at `L = 4/3` is the form of the actual coefficients on `F`. -/
theorem Q_eq (M : ℕ) (c : Fin 139 → ℂ) :
    Q_CvS M (4 / 3) ctr c =
      (∑ n ∈ F, ∑ m ∈ F, acoef c n * conj (acoef c m) * (cvsEntry M (4 / 3) n m : ℂ)).re := by
  simp only [Q_CvS, A_CvS]
  rw [show (lowFreq fun i => sinSqSupport (ctr i)) = F from lowFreq_eq]
  rfl

def RA : ℝ := 6 * 141

def epsQ : ℝ := RE + RA * (2 * theta + theta ^ 2)

theorem theta_nonneg : 0 ≤ theta := by simp only [theta]; norm_num

theorem ahat_d (c : Fin 139 → ℂ) (n : ℤ) : ‖acoef c n - ahat c n‖ ≤ theta * ‖ahat c n‖ :=
  a_sub_ahat c n

theorem acoef_le (c : Fin 139 → ℂ) (n : ℤ) : ‖acoef c n‖ ≤ (1 + theta) * ‖ahat c n‖ := by
  have e : acoef c n = ahat c n + (acoef c n - ahat c n) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have := a_sub_ahat c n
  linarith

/-- **The low form against its midpoint.** -/
theorem Q_ge (M : ℕ) (hM : 3 ≤ M) (c : Fin 139 → ℂ) :
    (∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (ahat c m) * (((Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ)).re -
      epsQ * ∑ n ∈ F, ‖ahat c n‖ ^ 2 ≤ Q_CvS M (4 / 3) ctr c := by
  rw [Q_eq]
  set a := acoef c
  set b := ahat c
  set d : ℤ → ℂ := fun n => a n - b n
  set E : ℤ → ℤ → ℝ := fun n m => cvsEntry M (4 / 3) n m
  set Eh : ℤ → ℤ → ℝ := fun n m => (Et n m : ℝ) / 2 ^ 128
  have split : ∑ n ∈ F, ∑ m ∈ F, a n * conj (a m) * (E n m : ℂ) =
      ∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * (Eh n m : ℂ) +
      ∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * ((E n m - Eh n m : ℝ) : ℂ) +
      ∑ n ∈ F, ∑ m ∈ F, b n * conj (d m) * (E n m : ℂ) +
      ∑ n ∈ F, ∑ m ∈ F, d n * conj (a m) * (E n m : ℂ) := by
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_
    simp only [d, map_sub]
    push_cast
    ring
  have hF : ∀ n ∈ F, -70 ≤ n ∧ n ≤ 70 := fun n hn => mem_Icc.mp hn
  -- the three error terms
  have t1 : ‖∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * ((E n m - Eh n m : ℝ) : ℂ)‖ ≤
      RE * nrm b * nrm b := by
    refine bilin_le (fun n m => E n m - Eh n m) (fun n m => |E n m - Eh n m|) ?_ (fun n _ m _ => le_rfl)
      ?_ (fun n hn => RE_row hM hn) b b
    · simp only [RE, rhoD, am, Cu, rho, dC, tm, hB2]; norm_num [rDq, rhoq, tmq]
    · intro n hn m hm
      simp only [E, Eh]
      rw [AEGIS.CvSRowTailV1.cvsEntry_symm M (by norm_num) n m, AEGIS.CvSRelRowPsdL43V1.Et_symm n m]
  have hE : ∀ n ∈ F, ∀ m ∈ F, |E n m| ≤ (fun _ _ => (6 : ℝ)) n m := fun n hn m hm =>
    E_abs_le hM (hF n hn).1 (hF n hn).2 (hF m hm).1 (hF m hm).2
  have hrow : ∀ n ∈ F, ∑ m ∈ F, (fun _ _ => (6 : ℝ)) n m ≤ RA := fun n _ => by
    simp [RA]; norm_num
  have hRA : (0 : ℝ) ≤ RA := by norm_num [RA]
  have t2 := bilin_le E (fun _ _ => (6 : ℝ)) hRA hE (fun _ _ _ _ => rfl) hrow b d
  have t3 := bilin_le E (fun _ _ => (6 : ℝ)) hRA hE (fun _ _ _ _ => rfl) hrow d a
  have hd : nrm d ≤ theta * nrm b := nrm_le_of theta_nonneg fun n _ => ahat_d c n
  have ha : nrm a ≤ (1 + theta) * nrm b := nrm_le_of (by linarith [theta_nonneg]) fun n _ => acoef_le c n
  have hb0 := nrm_nonneg b
  have hd0 := nrm_nonneg d
  have hth := theta_nonneg
  have hbb := nrm_sq b
  have b2 : RA * nrm b * nrm d ≤ RA * theta * (nrm b * nrm b) := by
    calc RA * nrm b * nrm d ≤ RA * nrm b * (theta * nrm b) :=
          mul_le_mul_of_nonneg_left hd (mul_nonneg hRA hb0)
      _ = _ := by ring
  have b3 : RA * nrm d * nrm a ≤ RA * (theta * (1 + theta)) * (nrm b * nrm b) := by
    calc RA * nrm d * nrm a ≤ RA * (theta * nrm b) * ((1 + theta) * nrm b) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hd hRA) ha (nrm_nonneg _)
            (mul_nonneg hRA (mul_nonneg hth hb0))
      _ = _ := by ring
  have hT0 : ∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * (((Et n m : ℝ) / 2 ^ 128 : ℝ) : ℂ) =
      ∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * (Eh n m : ℂ) := rfl
  rw [split, ← hbb, hT0]
  simp only [Complex.add_re]
  have r1 := Complex.abs_re_le_norm (∑ n ∈ F, ∑ m ∈ F, b n * conj (b m) * ((E n m - Eh n m : ℝ) : ℂ))
  have r2 := Complex.abs_re_le_norm (∑ n ∈ F, ∑ m ∈ F, b n * conj (d m) * (E n m : ℂ))
  have r3 := Complex.abs_re_le_norm (∑ n ∈ F, ∑ m ∈ F, d n * conj (a m) * (E n m : ℂ))
  rw [abs_le] at r1 r2 r3
  simp only [epsQ]
  nlinarith [t1, t2, t3, b2, b3]

end AEGIS.CvSRelRowQL43V1

end

#print axioms AEGIS.CvSRelRowQL43V1.Q_ge
