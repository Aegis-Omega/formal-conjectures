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

import CvSTraceCoefV1

/-!
# The moment correction of the trace coefficients (CvS step K3b)

With `q_σ = û_σ`, `ĉ_t = f̂_t` on `K = [−N, N]`, the Gram matrix `G_{sr} = L Σ_K q_r conj q_s`
and `a_s(t) = L Σ_K ĉ_t conj q_s`, Cramer's rule gives `γ(t)` with `G γ = a`. Then
`v = ĉ_t − γ₀ q₀ − γ₁ q₁` satisfies

* `cramer`: `Σ_K v_k conj(q_s(k)) = 0`;
* `cond_r`: `Σ_K v_k / (iω_k + σ_s) = 0` for `σ = ∓1/2` (closed form of `conj q`);
* `moment_conds`: `Σ_K b_k = 0` and `Σ_K k b_k = 0` for `b_k = v_k / ((iω_k)² − 1/4)`,
  the two conditions of the second-difference inversion.

Not RH.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate

noncomputable section

namespace AEGIS.CvSTraceCramerV1

open AEGIS.CvSPrimeBlockV1 AEGIS.CvSFourierIntervalV1 AEGIS.CvSMomentV1 AEGIS.CvSTraceCoefV1

/-- The two moment exponents: `σ₀ = −1/2` (`e^{−x/2}`) and `σ₁ = 1/2` (`e^{x/2}`). -/
def sig (s : Fin 2) : ℝ := if s = 0 then -1 / 2 else 1 / 2

theorem sig_ne_zero (s : Fin 2) : sig s ≠ 0 := by
  fin_cases s <;> norm_num [sig]

def K (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

/-- `iω_k = 2πik/L`. -/
def om (LT : ℝ) (k : ℤ) : ℂ := 2 * Real.pi * I * k / LT

variable {LT : ℝ} (hLT : 0 < LT) (N : ℕ)

def q (s : Fin 2) (k : ℤ) : ℂ := fourierCoeffOn hLT (uS LT (sig s)) k

def cT (t : ℝ) (k : ℤ) : ℂ := fourierCoeffOn hLT (fT LT t) k

def gram (s r : Fin 2) : ℂ := LT * ∑ k ∈ K N, q hLT r k * conj (q hLT s k)

def rhs (t : ℝ) (s : Fin 2) : ℂ := LT * ∑ k ∈ K N, cT hLT t k * conj (q hLT s k)

def detG : ℂ := gram hLT N 0 0 * gram hLT N 1 1 - gram hLT N 0 1 * gram hLT N 1 0

def gam (t : ℝ) (s : Fin 2) : ℂ :=
  if s = 0 then (gram hLT N 1 1 * rhs hLT N t 0 - gram hLT N 0 1 * rhs hLT N t 1) / detG hLT N
  else (gram hLT N 0 0 * rhs hLT N t 1 - gram hLT N 1 0 * rhs hLT N t 0) / detG hLT N

def vC (t : ℝ) (k : ℤ) : ℂ := cT hLT t k - gam hLT N t 0 * q hLT 0 k - gam hLT N t 1 * q hLT 1 k

def bC (t : ℝ) (k : ℤ) : ℂ := vC hLT N t k / (om LT k ^ 2 - 1 / 4)

theorem gam_zero (t : ℝ) : gam hLT N t 0 =
    (gram hLT N 1 1 * rhs hLT N t 0 - gram hLT N 0 1 * rhs hLT N t 1) / detG hLT N := by
  simp [gam]

theorem gam_one (t : ℝ) : gam hLT N t 1 =
    (gram hLT N 0 0 * rhs hLT N t 1 - gram hLT N 1 0 * rhs hLT N t 0) / detG hLT N := by
  simp [gam]

/-- **Cramer**: the corrected coefficients are orthogonal to both truncated moments. -/
theorem cramer (hdet : detG hLT N ≠ 0) (t : ℝ) (s : Fin 2) :
    ∑ k ∈ K N, vC hLT N t k * conj (q hLT s k) = 0 := by
  have hL0 : (LT : ℂ) ≠ 0 := by exact_mod_cast hLT.ne'
  have e : ∑ k ∈ K N, vC hLT N t k * conj (q hLT s k) =
      (rhs hLT N t s - gam hLT N t 0 * gram hLT N s 0 - gam hLT N t 1 * gram hLT N s 1) / LT := by
    simp only [vC, rhs, gram, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    field_simp
  rw [e, div_eq_zero_iff]
  left
  have c0 : rhs hLT N t 0 - gam hLT N t 0 * gram hLT N 0 0 - gam hLT N t 1 * gram hLT N 0 1 = 0 := by
    rw [gam_zero, gam_one]
    field_simp
    unfold detG
    ring
  have c1 : rhs hLT N t 1 - gam hLT N t 0 * gram hLT N 1 0 - gam hLT N t 1 * gram hLT N 1 1 = 0 := by
    rw [gam_zero, gam_one]
    field_simp
    unfold detG
    ring
  fin_cases s
  · exact c0
  · exact c1

theorem conj_q (s : Fin 2) (k : ℤ) :
    conj (q hLT s k) = (cexp ((sig s : ℂ) * LT) - 1) / (LT * (om LT k + sig s)) := by
  have h := coef_uS hLT (sig_ne_zero s) k
  have hL0 : (LT : ℂ) ≠ 0 := by exact_mod_cast hLT.ne'
  have hd := half_add_ne_zero LT (-k) (sig_ne_zero s)
  have hq : q hLT s k = (cexp ((sig s : ℂ) * LT) - 1) /
      ((sig s : ℂ) + 2 * Real.pi * I * ((-k : ℤ) : ℂ) / LT) / LT := by
    simp only [q]
    rw [← h]
    field_simp
  rw [hq]
  simp only [map_div₀, map_sub, map_one, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    map_intCast, map_ofNat, om, ← Complex.exp_conj]
  push_cast
  rw [div_div]
  congr 1
  ring

include hLT in
theorem exp_sig_sub_one_ne (s : Fin 2) : cexp ((sig s : ℂ) * LT) - 1 ≠ 0 := by
  intro h
  have h1 : cexp ((sig s : ℂ) * LT) = 1 := sub_eq_zero.mp h
  have h2 : (((Real.exp (sig s * LT) : ℝ)) : ℂ) = 1 := by
    rw [Complex.ofReal_exp]; push_cast; exact h1
  have h3 : Real.exp (sig s * LT) = 1 := by exact_mod_cast h2
  rw [Real.exp_eq_one_iff] at h3
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact sig_ne_zero s h4
  · exact hLT.ne' h4

theorem om_add_sig_ne (k : ℤ) (s : Fin 2) : om LT k + sig s ≠ 0 := by
  have := half_add_ne_zero LT k (sig_ne_zero s)
  simp only [om]
  intro h
  apply this
  rw [← h]
  ring

/-- **The two weighted conditions** `Σ_K v_k / (iω_k + σ_s) = 0`. -/
theorem cond_r (hdet : detG hLT N ≠ 0) (t : ℝ) (s : Fin 2) :
    ∑ k ∈ K N, vC hLT N t k / (om LT k + sig s) = 0 := by
  have h := cramer hLT N hdet t s
  simp_rw [conj_q hLT s] at h
  have hL0 : (LT : ℂ) ≠ 0 := by exact_mod_cast hLT.ne'
  have he := exp_sig_sub_one_ne hLT s
  have e : ∑ k ∈ K N, vC hLT N t k * ((cexp ((sig s : ℂ) * LT) - 1) / (LT * (om LT k + sig s))) =
      ((cexp ((sig s : ℂ) * LT) - 1) / LT) * ∑ k ∈ K N, vC hLT N t k / (om LT k + sig s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := om_add_sig_ne (LT := LT) k s
    field_simp
  rw [e] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 (div_ne_zero he hL0)
  · exact h1

/-- **The two moment conditions of the second-difference inversion.** -/
theorem moment_conds (hdet : detG hLT N ≠ 0) (t : ℝ) :
    ∑ k ∈ K N, bC hLT N t k = 0 ∧ ∑ k ∈ K N, (k : ℂ) * bC hLT N t k = 0 := by
  have h0 := cond_r hLT N hdet t 0
  have h1 := cond_r hLT N hdet t 1
  have hs0 : sig 0 = -1 / 2 := by simp [sig]
  have hs1 : sig 1 = 1 / 2 := by simp [sig]
  rw [hs0] at h0
  rw [hs1] at h1
  have hm : ∀ k : ℤ, om LT k + ((-1 / 2 : ℝ) : ℂ) ≠ 0 := fun k => by
    have := om_add_sig_ne (LT := LT) k 0; simpa [sig] using this
  have hp : ∀ k : ℤ, om LT k + ((1 / 2 : ℝ) : ℂ) ≠ 0 := fun k => by
    have := om_add_sig_ne (LT := LT) k 1; simpa [sig] using this
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) I_ne_zero
  have hL0 : (LT : ℂ) ≠ 0 := by exact_mod_cast hLT.ne'
  constructor
  · have e : ∀ k : ℤ, bC hLT N t k = vC hLT N t k / (om LT k + ((-1 / 2 : ℝ) : ℂ)) -
        vC hLT N t k / (om LT k + ((1 / 2 : ℝ) : ℂ)) := by
      intro k
      have c : om LT k ^ 2 - 1 / 4 =
          (om LT k + ((-1 / 2 : ℝ) : ℂ)) * (om LT k + ((1 / 2 : ℝ) : ℂ)) := by push_cast; ring
      simp only [bC]
      rw [div_sub_div _ _ (hm k) (hp k), c]
      congr 1
      push_cast
      ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, h0, h1, sub_zero]
  · have e : ∀ k : ℤ, (k : ℂ) * bC hLT N t k = (LT / (2 * (2 * Real.pi * I))) *
        (vC hLT N t k / (om LT k + ((-1 / 2 : ℝ) : ℂ)) +
          vC hLT N t k / (om LT k + ((1 / 2 : ℝ) : ℂ))) := by
      intro k
      have c : om LT k ^ 2 - 1 / 4 =
          (om LT k + ((-1 / 2 : ℝ) : ℂ)) * (om LT k + ((1 / 2 : ℝ) : ℂ)) := by push_cast; ring
      have hk : (k : ℂ) = LT / (2 * Real.pi * I) * om LT k := by
        simp only [om]
        field_simp
      simp only [bC]
      rw [div_add_div _ _ (hm k) (hp k), c, hk]
      push_cast
      ring
    simp_rw [e]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, h0, h1, add_zero, mul_zero]

end AEGIS.CvSTraceCramerV1

#print axioms AEGIS.CvSTraceCramerV1.cramer
#print axioms AEGIS.CvSTraceCramerV1.conj_q
#print axioms AEGIS.CvSTraceCramerV1.cond_r
#print axioms AEGIS.CvSTraceCramerV1.moment_conds
