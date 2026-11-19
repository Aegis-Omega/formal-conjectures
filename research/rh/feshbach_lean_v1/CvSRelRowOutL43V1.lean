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
import CvSRelRowKtL43V1
import CvSRelRowQL43V1
import CvSGramTailV1

/-!
# The outside rows `70 < |m| ≤ 200` at `L = 4/3`

`out_le`: `Σ_{m ∈ Hs} |crossRow m|² ≤ Re Σ_{n,n' ∈ F} â_n conj(â_n') ⌊LPq Kt(n,n')/2^64⌋/2^128 +
ε_out Σ_F |â_n|²`. A row is `(L/π) z_m` with `z_m = Σ_n a_n (τ_n − τ_m)/(n − m)`
(`crossRow_off`); `|z_m|² ≤ (1 + η)|ẑ_m|² + (1 + 1/η)|z_m − ẑ_m|²` with the midpoint row `ẑ_m`;
`Σ_m |ẑ_m|²` is the form of `K̂` (`Kt_err`), and `Σ_m |z_m − ẑ_m|²` is bounded by the Schur test
with the harmonic row sums. Not RH.
-/

open Finset
open scoped ComplexConjugate
open AEGIS.CvSRelRowDataL43V1 AEGIS.CvSRelRowBoxL43V1 AEGIS.CvSRelRowFormL43V1
  AEGIS.CvSRelRowErrL43V1 AEGIS.CvSRelRowAlgebraV1 AEGIS.CvSRelRowHarmV1 AEGIS.CvSRelRowQL43V1
  AEGIS.CvSRelRowKtL43V1 AEGIS.CvSRowTailV1 AEGIS.CvSCrossCertV1 AEGIS.CvSLowBlockMatrixV1

noncomputable section

namespace AEGIS.CvSRelRowOutL43V1

def eta : ℝ := 1 / 1000

def LP : ℝ := (LPq : ℝ) / 2 ^ 64

def eK : ℝ := 90000 / 2 ^ 128

def w0 : ℝ := 24 * theta + 2 * rhoA

def H270 : ℕ := 113954546290442749430

theorem hup270 : hupN 270 ≤ H270 := by decide +kernel

def epsOut : ℝ := LP * (141 * eK) + 141 / 2 ^ 128 +
  LP * (1 + 1 / eta) * ((141 * w0) * (w0 * (2 * ((H270 : ℝ) / 2 ^ 64))))

theorem LP_ge : (1 + eta) * ((4 / 3 : ℝ) / Real.pi) ^ 2 ≤ LP := by
  have h1 := Real.pi_gt_d20
  have hp : 0 < Real.pi := Real.pi_pos
  rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
  have l : (3.14159265358979323846 : ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith
  norm_num [eta, LP, LPq] at l ⊢
  nlinarith

theorem LP_pos : 0 < LP := by norm_num [LP, LPq]

theorem eta_pos : 0 < eta := by norm_num [eta]

/-- The midpoint outside row `ẑ_m = Σ_n â_n ŵ(n, m)`. -/
def zh (c : Fin 139 → ℂ) (m : ℤ) : ℂ := ∑ n ∈ F, ahat c n * (wh n m : ℂ)

/-- The actual outside row without the factor `L/π`. -/
def zr (M : ℕ) (c : Fin 139 → ℂ) (m : ℤ) : ℂ :=
  ∑ n ∈ F, acoef c n * (((tau M (4 / 3) n - tau M (4 / 3) m) / (n - m) : ℝ) : ℂ)

theorem not_mem_F {m : ℤ} (hm : m ∈ Hs) : m ∉ F := by
  rw [mem_Hs] at hm
  rw [mem_Icc]
  omega

theorem crossRow_eq (M : ℕ) (c : Fin 139 → ℂ) {m : ℤ} (hm : m ∈ Hs) :
    crossRow M (4 / 3) F (acoef c) m = (((4 / 3 : ℝ) / Real.pi : ℝ) : ℂ) * zr M c m :=
  crossRow_off M (by norm_num) (acoef c) (not_mem_F hm)

/-- `Σ_m |ẑ_m|²` is the form of `K̂`. -/
theorem zh_energy (c : Fin 139 → ℂ) :
    ∑ m ∈ Hs, ‖zh c m‖ ^ 2 = (∑ n ∈ F, ∑ n' ∈ F, ahat c n * conj (ahat c n') * (Kh n n' : ℂ)).re := by
  have h : ∀ m, ‖zh c m‖ ^ 2 = (∑ n ∈ F, ∑ n' ∈ F, ahat c n * conj (ahat c n') *
      ((wh n m * wh n' m : ℝ) : ℂ)).re := fun m =>
    AEGIS.CvSGramTailV1.norm_sq_sum_eq F (ahat c) (fun n => wh n m)
  rw [sum_congr rfl fun m _ => h m, ← Complex.re_sum]
  refine congrArg Complex.re ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n' _ => ?_
  rw [Kh, ← Finset.mul_sum, Complex.ofReal_sum]

theorem inv_le_one_of_ne {n m : ℤ} (h : n ≠ m) : 1 / |(n : ℝ) - m| ≤ 1 := by
  have hk : (1 : ℝ) ≤ |(n : ℝ) - m| := by
    have : (1 : ℤ) ≤ |n - m| := Int.one_le_abs (sub_ne_zero.mpr h)
    have := (Int.cast_le (R := ℝ)).mpr this
    push_cast at this
    exact this
  rw [div_le_one (by linarith)]
  exact hk

theorem w0_nonneg : 0 ≤ w0 := by
  simp only [w0, theta, rhoA]; norm_num [rhoq, rhoHq]

/-- The difference of the rows, entrywise. -/
theorem row_diff (M : ℕ) (hM : 3 ≤ M) (c : Fin 139 → ℂ) {m : ℤ} (hm : m ∈ Hs) :
    ‖zr M c m - zh c m‖ ≤ ∑ n ∈ F, w0 * (1 / |(n : ℝ) - m|) * ‖ahat c n‖ := by
  simp only [zr, zh, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
  have hmn : n ≠ m := fun h => not_mem_F hm (h ▸ hn)
  have hd : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  have hpos : 0 < |(n : ℝ) - m| := abs_pos.mpr hd
  rw [mem_Icc] at hn
  have hmb : m.natAbs ≤ 200 := by rw [mem_Hs] at hm; omega
  have hnb : n.natAbs ≤ 200 := by omega
  obtain ⟨tn, -⟩ := tau_all hM hnb
  obtain ⟨tm', -⟩ := tau_all hM hmb
  have an := tau_abs_all hM hnb
  have am' := tau_abs_all hM hmb
  set w := (tau M (4 / 3) n - tau M (4 / 3) m) / ((n : ℝ) - m)
  have e : acoef c n * (w : ℂ) - ahat c n * (wh n m : ℂ) =
      (acoef c n - ahat c n) * (w : ℂ) + ahat c n * ((w - wh n m : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hw : |w| ≤ 24 * (1 / |(n : ℝ) - m|) := by
    simp only [w]
    rw [abs_div, div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine (abs_sub _ _).trans ?_
    linarith
  have hww : |w - wh n m| ≤ 2 * rhoA * (1 / |(n : ℝ) - m|) := by
    have e2 : w - wh n m = ((tau M (4 / 3) n - th n) - (tau M (4 / 3) m - th m)) / ((n : ℝ) - m) := by
      simp only [w, wh]; field_simp; ring
    rw [e2, abs_div, div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine (abs_sub _ _).trans ?_
    simp only [th]
    linarith
  have hd' := a_sub_ahat c n
  have h1 : ‖acoef c n - ahat c n‖ * |w| ≤ theta * ‖ahat c n‖ * (24 * (1 / |(n : ℝ) - m|)) :=
    mul_le_mul hd' hw (abs_nonneg _) (mul_nonneg theta_nonneg (norm_nonneg _))
  have h2 : ‖ahat c n‖ * |w - wh n m| ≤ ‖ahat c n‖ * (2 * rhoA * (1 / |(n : ℝ) - m|)) :=
    mul_le_mul_of_nonneg_left hww (norm_nonneg _)
  have : w0 * (1 / |(n : ℝ) - m|) * ‖ahat c n‖ =
      theta * ‖ahat c n‖ * (24 * (1 / |(n : ℝ) - m|)) + ‖ahat c n‖ * (2 * rhoA * (1 / |(n : ℝ) - m|)) := by
    simp only [w0]; ring
  rw [this]
  linarith

/-- **The outside rows.** -/
theorem out_le (M : ℕ) (hM : 3 ≤ M) (c : Fin 139 → ℂ) :
    ∑ m ∈ Hs, ‖crossRow M (4 / 3) F (acoef c) m‖ ^ 2 ≤
      (∑ n ∈ F, ∑ n' ∈ F, ahat c n * conj (ahat c n') *
        ((((LPq * Kt n n' / 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128 : ℝ) : ℂ)).re +
      epsOut * ∑ n ∈ F, ‖ahat c n‖ ^ 2 := by
  set b := ahat c
  set LT2 := ((4 / 3 : ℝ) / Real.pi) ^ 2
  have hLT2 : 0 ≤ LT2 := sq_nonneg _
  -- the rows
  have hrow : ∀ m ∈ Hs, ‖crossRow M (4 / 3) F (acoef c) m‖ ^ 2 ≤
      LT2 * ((1 + eta) * ‖zh c m‖ ^ 2 + (1 + 1 / eta) * ‖zr M c m - zh c m‖ ^ 2) := by
    intro m hm
    rw [crossRow_eq M c hm, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    refine mul_le_mul_of_nonneg_left ?_ hLT2
    have := normSq_add_le (zh c m) (zr M c m - zh c m) eta_pos
    rwa [add_sub_cancel] at this
  have hsum := sum_le_sum hrow
  rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
  -- the difference rows by the Schur test
  have hcolF : ∀ n ∈ F, ∑ m ∈ Hs, w0 * (1 / |(n : ℝ) - m|) ≤ w0 * (2 * ((H270 : ℝ) / 2 ^ 64)) := by
    intro n hn
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ w0_nonneg
    rw [mem_Icc] at hn
    have h := inv_sum_le n Hs 270 270 fun m hm => by
      rw [mem_Hs] at hm
      refine ⟨by omega, by push_cast; omega, by push_cast; omega⟩
    have h2 := harmonic_le_hup 270
    have h3 : (hupN 270 : ℝ) ≤ H270 := by exact_mod_cast hup270
    have : (hupN 270 : ℝ) / 2 ^ 64 ≤ (H270 : ℝ) / 2 ^ 64 := div_le_div_of_nonneg_right h3 (by positivity)
    linarith
  have hrowH : ∀ m ∈ Hs, ∑ n ∈ F, w0 * (1 / |(n : ℝ) - m|) ≤ 141 * w0 := by
    intro m hm
    calc ∑ n ∈ F, w0 * (1 / |(n : ℝ) - m|) ≤ ∑ _n ∈ F, w0 := sum_le_sum fun n hn => by
          have hmn : n ≠ m := fun h => not_mem_F hm (h ▸ hn)
          exact mul_le_of_le_one_right w0_nonneg (inv_le_one_of_ne hmn)
      _ = 141 * w0 := by rw [sum_const]; simp
  have hdiff := schur_vec Hs F (fun m => zr M c m - zh c m) b (fun m n => w0 * (1 / |(n : ℝ) - m|))
    (by have := w0_nonneg; positivity) (fun m _ n _ => by have := w0_nonneg; positivity)
    (fun m hm => row_diff M hM c hm) hrowH (fun n hn => hcolF n hn)
  -- the midpoint rows: the form of `K̂`, against `Kt`
  have hK := bilin_le (fun n n' => Kh n n' - (Kt n n' : ℝ) / 2 ^ 128) (fun _ _ => eK)
    (by norm_num [eK] : (0 : ℝ) ≤ 141 * eK)
    (fun n hn n' hn' => by rw [abs_sub_comm]; exact Kt_err hn hn') (fun _ _ _ _ => rfl)
    (fun n _ => by simp) b b
  have hR := bilin_le (fun n n' => LP * ((Kt n n' : ℝ) / 2 ^ 128) -
      (((LPq * Kt n n' / 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128)) (fun _ _ => (1 : ℝ) / 2 ^ 128)
    (by norm_num : (0 : ℝ) ≤ 141 * (1 / 2 ^ 128))
    (fun n _ n' _ => by
      have h := ediv_err (LPq * Kt n n') (2 ^ 64) (by norm_num)
      have e : LP * ((Kt n n' : ℝ) / 2 ^ 128) - (((LPq * Kt n n' / 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128) =
          (((LPq * Kt n n' : ℤ) : ℝ) / ((2 ^ 64 : ℤ) : ℝ) - ((LPq * Kt n n' / 2 ^ 64 : ℤ) : ℝ)) / 2 ^ 128 := by
        simp only [LP]; push_cast; ring
      rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 128)]
      exact div_le_div_of_nonneg_right h.le (by positivity))
    (fun _ _ _ _ => rfl) (fun n _ => by simp) b b
  have hbb := nrm_sq b
  set X := (∑ n ∈ F, ∑ n' ∈ F, b n * conj (b n') * (Kh n n' : ℂ)).re
  set Y := (∑ n ∈ F, ∑ n' ∈ F, b n * conj (b n') * ((((Kt n n' : ℝ) / 2 ^ 128 : ℝ)) : ℂ)).re
  set Z := (∑ n ∈ F, ∑ n' ∈ F, b n * conj (b n') *
    ((((LPq * Kt n n' / 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128 : ℝ) : ℂ)).re
  have hX0 : 0 ≤ X := by
    have h : X = ∑ m ∈ Hs, ‖zh c m‖ ^ 2 := (zh_energy c).symm
    rw [h]; exact sum_nonneg fun _ _ => sq_nonneg _
  have hXY : X ≤ Y + 141 * eK * (nrm b * nrm b) := by
    have e : X = Y + (∑ n ∈ F, ∑ n' ∈ F, b n * conj (b n') *
        (((Kh n n' - (Kt n n' : ℝ) / 2 ^ 128 : ℝ)) : ℂ)).re := by
      simp only [X, Y, ← Complex.add_re, ← sum_add_distrib]
      congr 1
      refine sum_congr rfl fun n _ => sum_congr rfl fun n' _ => ?_
      push_cast; ring
    have := Complex.re_le_norm (∑ n ∈ F, ∑ n' ∈ F, b n * conj (b n') *
        (((Kh n n' - (Kt n n' : ℝ) / 2 ^ 128 : ℝ)) : ℂ))
    rw [e]
    have : 141 * eK * nrm b * nrm b = 141 * eK * (nrm b * nrm b) := by ring
    linarith
  have hYZ : LP * Y ≤ Z + 141 * (1 / 2 ^ 128) * (nrm b * nrm b) := by
    have e : LP * Y = Z + (∑ n ∈ F, ∑ n' ∈ F, b n * conj (b n') *
        (((LP * ((Kt n n' : ℝ) / 2 ^ 128) - (((LPq * Kt n n' / 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128) : ℝ)) : ℂ)).re := by
      simp only [Y, Z]
      rw [← Complex.re_ofReal_mul, mul_sum, ← Complex.add_re, ← sum_add_distrib]
      congr 1
      refine sum_congr rfl fun n _ => ?_
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun n' _ => ?_
      push_cast; ring
    have := Complex.re_le_norm (∑ n ∈ F, ∑ n' ∈ F, b n * conj (b n') *
        (((LP * ((Kt n n' : ℝ) / 2 ^ 128) - (((LPq * Kt n n' / 2 ^ 64 : ℤ) : ℝ) / 2 ^ 128) : ℝ)) : ℂ))
    rw [e]
    have : 141 * (1 / 2 ^ 128) * nrm b * nrm b = 141 * (1 / 2 ^ 128) * (nrm b * nrm b) := by ring
    linarith
  have hE := zh_energy c
  rw [← hbb]
  -- combine
  have hLP := LP_ge
  have c1 : LT2 * ((1 + eta) * X) ≤ LP * X := by
    have := mul_le_mul_of_nonneg_right hLP hX0
    nlinarith
  have hD0 : 0 ≤ ∑ m ∈ Hs, ‖zr M c m - zh c m‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have c2 : LT2 * ((1 + 1 / eta) * ∑ m ∈ Hs, ‖zr M c m - zh c m‖ ^ 2) ≤
      LP * (1 + 1 / eta) * ((141 * w0) * (w0 * (2 * ((H270 : ℝ) / 2 ^ 64)))) * (nrm b * nrm b) := by
    have hle : LT2 ≤ LP := by
      have : LT2 ≤ (1 + eta) * LT2 := by
        have := eta_pos
        nlinarith
      linarith
    have he : 0 ≤ 1 + 1 / eta := by norm_num [eta]
    rw [hbb]
    calc LT2 * ((1 + 1 / eta) * ∑ m ∈ Hs, ‖zr M c m - zh c m‖ ^ 2)
        ≤ LP * ((1 + 1 / eta) * ((141 * w0) * (w0 * (2 * ((H270 : ℝ) / 2 ^ 64))) *
            ∑ n ∈ F, ‖b n‖ ^ 2)) := by
          refine mul_le_mul hle (mul_le_mul_of_nonneg_left hdiff he) (mul_nonneg he hD0) LP_pos.le
      _ = _ := by ring
  have hzh : ∑ m ∈ Hs, ‖zh c m‖ ^ 2 = X := hE
  rw [hzh] at hsum
  have c3 : LP * X ≤ LP * Y + LP * (141 * eK) * (nrm b * nrm b) := by
    have := mul_le_mul_of_nonneg_left hXY LP_pos.le
    linarith
  simp only [epsOut]
  nlinarith [c1, c2, c3, hYZ, hsum]

end AEGIS.CvSRelRowOutL43V1

end

#print axioms AEGIS.CvSRelRowOutL43V1.out_le
