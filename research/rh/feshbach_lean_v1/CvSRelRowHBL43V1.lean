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
import CvSRelRowInL43V1

/-!
# The relative row budget at `L = 4/3`: `Brow ≤ 52 Q`

`Brow M c` is the row quantity of `window_of_certificate_gram_moment` at `NP = 200`, `T = 13`,
`ε = 7/10` with the atom coefficients `lam M c` of `CvSRelRowInL43V1`. The rows `|m| ≤ 70`
(`in_le`), `70 < |m| ≤ 200` (`out_le`) and the Gram tail (`tail_le`) are bounded by the forms of
the kernel tables, the low form from below by its midpoint (`Q_ge`), and the kernel-checked
inequality `midpoint_ge` closes the budget because the constants add up to
`K' = 52 ε_Q + ε_in + ε_out + ε_T ≤ Kq/2^64` (`K_ok`). `hB`: `Brow M c ≤ 52 Q_CvS M (4/3) c`.
Not RH.
-/

open Finset
open scoped ComplexConjugate
open AEGIS.CvSRelRowDataL43V1 AEGIS.CvSRelRowBoxL43V1 AEGIS.CvSRelRowFormL43V1
  AEGIS.CvSRelRowErrL43V1 AEGIS.CvSRelRowQL43V1 AEGIS.CvSRelRowKtL43V1 AEGIS.CvSRelRowOutL43V1
  AEGIS.CvSRelRowTailL43V1 AEGIS.CvSRelRowInvL43V1 AEGIS.CvSRelRowInL43V1 AEGIS.CvSRowTailV1
  AEGIS.CvSCrossCertV1 AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSMomentBasisV1 AEGIS.CvSGramTailV1
  AEGIS.CvSSchurClosureFromBoundsV1

noncomputable section

namespace AEGIS.CvSRelRowHBL43V1

set_option maxRecDepth 100000

/-! ## The constants -/

def Kp : ℝ := 52 * epsQ + epsIn + epsOut + epsT

theorem K_ok : Kp ≤ (Kq : ℝ) / 2 ^ 64 := by
  simp only [Kp, epsQ, epsIn, epsOut, epsT, Dl, RE, RA, rhoD, am, Cu, rho, dC, tm, hB2, theta, gam,
    piU, dpi, eta, LP, eK, w0, rhoA, H270]
  norm_num [rDq, rhoq, rhoHq, tmq, LPq, T1q, T2q, Kq]

/-! ## The row budget -/

/-- The rows `|a| ≤ 200` against the atoms, plus the Gram tail. -/
def Brow (M : ℕ) (c : Fin 139 → ℂ) : ℝ :=
  (∑ a ∈ Icc (-((200 : ℕ) : ℤ)) ((200 : ℕ) : ℤ),
    ‖crossRow M (4 / 3) (lowFreq fun i => sinSqSupport (ctr i))
        (lowCoeff (4 / 3) (fun i => sinSqSupport (ctr i)) (fun i => sinSqWeight (ctr i)) c) a -
      ∑ i, lam M c i * atomRow (4 / 3) (fun i => sinSqSupport (ctr i))
        (fun i => sinSqWeight (ctr i)) i a‖ ^ 2) +
  gramTail M (4 / 3) (lowFreq fun i => sinSqSupport (ctr i))
    (lowCoeff (4 / 3) (fun i => sinSqSupport (ctr i)) (fun i => sinSqWeight (ctr i)) c) 13 (7 / 10) 200

theorem Icc_split : Icc (-((200 : ℕ) : ℤ)) ((200 : ℕ) : ℤ) = F ∪ Hs := by
  ext m
  rw [mem_union, mem_Icc, mem_Icc, mem_Hs]
  push_cast
  omega

theorem F_Hs_disj : Disjoint F Hs := by
  rw [Finset.disjoint_left]
  intro m h1 h2
  rw [mem_Icc] at h1
  rw [mem_Hs] at h2
  omega

theorem atoms_out {m : ℤ} (hm : m ∈ Hs) (x : Fin 139 → ℂ) :
    ∑ i, x i * atomRow (4 / 3) (fun i => sinSqSupport (ctr i)) (fun i => sinSqWeight (ctr i)) i m = 0 := by
  refine sum_eq_zero fun i _ => ?_
  have hmF : m ∉ lowFreq (fun i : Fin 139 => sinSqSupport (ctr i)) := by
    rw [lowFreq_eq]; exact not_mem_F hm
  rw [atomRow, lowCoeff_eq_zero _ _ _ _ hmF, mul_zero]

/-- The double form of a real kernel. -/
def S (c : Fin 139 → ℂ) (X : ℤ → ℤ → ℝ) : ℝ :=
  (∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (ahat c m) * ((X n m : ℝ) : ℂ)).re

theorem S_Zt (c : Fin 139 → ℂ) :
    S c (fun n m => (Zt n m : ℝ) / 2 ^ 128) =
      52 * S c (fun n m => (Et n m : ℝ) / 2 ^ 128) -
      S c (fun n m => ((LPq * Kt n m / 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128) -
      S c (fun n m => (((T1q * (tq n * tq m * Gt n m / 2 ^ 98) / 2 ^ 64 : ℤ) : ℝ) +
        ((T2q * Gt n m / 2 ^ 64 : ℤ) : ℝ)) / 2 ^ 128) -
      (Kq : ℝ) / 2 ^ 64 * ∑ n ∈ F, ‖ahat c n‖ ^ 2 := by
  have hterm : ∀ n m : ℤ, (Zt n m : ℝ) / 2 ^ 128 = 52 * ((Et n m : ℝ) / 2 ^ 128) -
      ((LPq * Kt n m / 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128 -
      (((T1q * (tq n * tq m * Gt n m / 2 ^ 98) / 2 ^ 64 : ℤ) : ℝ) +
        ((T2q * Gt n m / 2 ^ 64 : ℤ) : ℝ)) / 2 ^ 128 -
      (if n = m then (Kq : ℝ) / 2 ^ 64 else 0) := by
    intro n m
    rw [Zt]
    generalize LPq * Kt n m / 2 ^ 64 = A
    generalize T1q * (tq n * tq m * Gt n m / 2 ^ 98) / 2 ^ 64 = B
    generalize T2q * Gt n m / 2 ^ 64 = C
    split_ifs <;> push_cast <;> ring
  have hdiag : (∑ n ∈ F, ∑ m ∈ F, ahat c n * conj (ahat c m) *
      (((if n = m then (Kq : ℝ) / 2 ^ 64 else 0) : ℝ) : ℂ)).re =
      (Kq : ℝ) / 2 ^ 64 * ∑ n ∈ F, ‖ahat c n‖ ^ 2 := by
    have e : ∀ n ∈ F, ∑ m ∈ F, ahat c n * conj (ahat c m) *
        (((if n = m then (Kq : ℝ) / 2 ^ 64 else 0) : ℝ) : ℂ) =
        ahat c n * conj (ahat c n) * (((Kq : ℝ) / 2 ^ 64 : ℝ) : ℂ) := by
      intro n hn
      rw [sum_eq_single n]
      · rw [if_pos rfl]
      · intro m _ hm; rw [if_neg (Ne.symm hm)]; simp
      · intro h; exact absurd hn h
    rw [sum_congr rfl e, Complex.re_sum, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [Complex.re_mul_ofReal, normSq_eq_mul_conj, mul_comm]
  simp only [S]
  rw [← hdiag]
  simp only [← Complex.re_ofReal_mul, ← Complex.sub_re, mul_sum, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_
  rw [hterm n m]
  push_cast
  ring

/-- **The relative row budget at `L = 4/3`.** -/
theorem hB (M : ℕ) (hM : 3 ≤ M) (c : Fin 139 → ℂ) : Brow M c ≤ 52 * Q_CvS M (4 / 3) ctr c := by
  have hlf : (lowFreq fun i : Fin 139 => sinSqSupport (ctr i)) = F := lowFreq_eq
  have hlc : lowCoeff (4 / 3) (fun i => sinSqSupport (ctr i)) (fun i => sinSqWeight (ctr i)) c =
      acoef c := rfl
  simp only [Brow, hlf, hlc]
  rw [Icc_split, sum_union F_Hs_disj]
  have hout : ∑ x ∈ Hs, ‖crossRow M (4 / 3) F (acoef c) x - ∑ i, lam M c i *
      atomRow (4 / 3) (fun i => sinSqSupport (ctr i)) (fun i => sinSqWeight (ctr i)) i x‖ ^ 2 =
      ∑ x ∈ Hs, ‖crossRow M (4 / 3) F (acoef c) x‖ ^ 2 :=
    sum_congr rfl fun x hx => by rw [atoms_out hx, sub_zero]
  rw [hout]
  have hin := in_le M hM c
  have hO := out_le M hM c
  have hT := tail_le M hM c
  have hQ := Q_ge M hM c
  have hmid := midpoint_ge c
  have hZ := S_Zt c
  have hK := K_ok
  have hN : 0 ≤ ∑ n ∈ F, ‖ahat c n‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  simp only [S] at hZ
  have hKN := mul_le_mul_of_nonneg_right hK hN
  simp only [Kp] at hKN
  linarith

theorem Brow_nonneg (M : ℕ) (c : Fin 139 → ℂ) : 0 ≤ Brow M c := by
  have hlf : (lowFreq fun i : Fin 139 => sinSqSupport (ctr i)) = F := lowFreq_eq
  simp only [Brow, hlf]
  refine add_nonneg (sum_nonneg fun _ _ => sq_nonneg _) ?_
  simp only [gramTail]
  have h1 := G_psd (fun n => lowCoeff (4 / 3) (fun i => sinSqSupport (ctr i))
    (fun i => sinSqWeight (ctr i)) c n * (tau M (4 / 3) n : ℂ))
  have h2 := G_psd (lowCoeff (4 / 3) (fun i => sinSqSupport (ctr i)) (fun i => sinSqWeight (ctr i)) c)
  positivity

/-- The low form at `L = 4/3` is nonnegative (from `hB` and `Brow ≥ 0`). -/
theorem Q_nonneg (M : ℕ) (hM : 3 ≤ M) (c : Fin 139 → ℂ) : 0 ≤ Q_CvS M (4 / 3) ctr c := by
  have := hB M hM c
  have := Brow_nonneg M c
  linarith

end AEGIS.CvSRelRowHBL43V1

end

#print axioms AEGIS.CvSRelRowHBL43V1.K_ok
#print axioms AEGIS.CvSRelRowHBL43V1.hB
#print axioms AEGIS.CvSRelRowHBL43V1.Q_nonneg
