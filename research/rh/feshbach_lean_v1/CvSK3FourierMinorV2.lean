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

import CvSK3DetGBridgeV2

/-!
# K3: the Fourier minor and unconditional nondegeneracy of the moment Gram.

All window lengths are strictly positive. All truncations have N ≥ 1.
This theorem does not establish the Riemann hypothesis.
-/

open Complex
noncomputable section

namespace AEGIS.CvSK3FourierMinorV2

open AEGIS.CvSTraceCramerV1 AEGIS.CvSTraceCoefV1 AEGIS.CvSMomentV1

private theorem q_closed {LT : ℝ} (hLT : 0 < LT) (s : Fin 2) (k : ℤ) :
    q hLT s k =
      (cexp ((sig s : ℂ) * LT) - 1) / ((LT : ℂ) * ((sig s : ℂ) - om LT k)) := by
  have hL : (LT : ℂ) ≠ 0 := by exact_mod_cast hLT.ne'
  have hh := half_add_ne_zero LT (-k) (sig_ne_zero s)
  have hw : (sig s : ℂ) + 2 * Real.pi * I * ((-k : ℤ) : ℂ) / LT =
      (sig s : ℂ) - om LT k := by
    simp only [Int.cast_neg, om]
    ring
  have hd : (sig s : ℂ) - om LT k ≠ 0 := by
    rw [← hw]
    exact hh
  have hc := coef_uS hLT (sig_ne_zero s) k
  rw [hw] at hc
  have hcmul := (eq_div_iff hd).mp hc
  apply (eq_div_iff (mul_ne_zero hL hd)).2
  calc
    q hLT s k * ((LT : ℂ) * ((sig s : ℂ) - om LT k)) =
        ((LT : ℂ) * fourierCoeffOn hLT (uS LT (sig s)) k) *
          ((sig s : ℂ) - om LT k) := by simp only [q]; ring
    _ = cexp ((sig s : ℂ) * LT) - 1 := hcmul

private theorem rational_minor_ne {L a b d A B : ℂ}
    (hL : L ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (had : a - d ≠ 0) (hbd : b - d ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hd : d ≠ 0) (hab : a ≠ b) :
    (A / (L * a)) * (B / (L * (b - d))) -
      (B / (L * b)) * (A / (L * (a - d))) ≠ 0 := by
  have hn : A * B * d * (a - b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hA hB) hd) (sub_ne_zero.mpr hab)
  have hden : L ^ 2 * a * b * (b - d) * (a - d) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (pow_ne_zero 2 hL) ha) hb) hbd) had
  have heq :
      (A / (L * a)) * (B / (L * (b - d))) -
          (B / (L * b)) * (A / (L * (a - d))) =
        A * B * d * (a - b) / (L ^ 2 * a * b * (b - d) * (a - d)) := by
    field_simp [hL, ha, hb, had, hbd]
    ring
  rw [heq]
  exact div_ne_zero hn hden

theorem q_two_sample_minor_ne {LT : ℝ} (hLT : 0 < LT) :
    q hLT 0 0 * q hLT 1 1 - q hLT 1 0 * q hLT 0 1 ≠ 0 := by
  let a : ℂ := (sig (0 : Fin 2) : ℂ)
  let b : ℂ := (sig (1 : Fin 2) : ℂ)
  let d : ℂ := om LT 1
  let A : ℂ := cexp ((sig (0 : Fin 2) : ℂ) * LT) - 1
  let B : ℂ := cexp ((sig (1 : Fin 2) : ℂ) * LT) - 1
  have hL : (LT : ℂ) ≠ 0 := by exact_mod_cast hLT.ne'
  have ha : a ≠ 0 := by norm_num [a, sig]
  have hb : b ≠ 0 := by norm_num [b, sig]
  have hab : a ≠ b := by norm_num [a, b, sig]
  have hA : A ≠ 0 := exp_sig_sub_one_ne hLT 0
  have hB : B ≠ 0 := exp_sig_sub_one_ne hLT 1
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) hp) I_ne_zero
  have hd : d ≠ 0 := by
    change om LT 1 ≠ 0
    have hv : om LT 1 = (2 * Real.pi * I) / (LT : ℂ) := by simp [om]
    rw [hv]
    exact div_ne_zero hpi hL
  have hden (s : Fin 2) : (sig s : ℂ) - om LT 1 ≠ 0 := by
    have h := half_add_ne_zero LT (-1) (sig_ne_zero s)
    have he : (sig s : ℂ) - om LT 1 =
        (sig s : ℂ) + 2 * Real.pi * I * ((-1 : ℤ) : ℂ) / LT := by
      simp only [om, Int.cast_neg, Int.cast_one]
      ring
    rw [he]
    exact h
  have had : a - d ≠ 0 := hden 0
  have hbd : b - d ≠ 0 := hden 1
  have hrat :
      (A / ((LT : ℂ) * a)) * (B / ((LT : ℂ) * (b - d))) -
        (B / ((LT : ℂ) * b)) * (A / ((LT : ℂ) * (a - d))) ≠ 0 :=
    rational_minor_ne hL ha hb had hbd hA hB hd hab
  rw [q_closed hLT 0 0, q_closed hLT 1 1,
      q_closed hLT 1 0, q_closed hLT 0 1]
  have hz : om LT 0 = 0 := by simp [om]
  simpa only [hz, sub_zero] using hrat

theorem detG_ne_zero_of_posN {LT : ℝ} (hLT : 0 < LT) (N : ℕ) (hN : 0 < N) :
    detG hLT N ≠ 0 := by
  have hk0 : (0 : ℤ) ∈ K N := by
    simp [K]
  have hk1 : (1 : ℤ) ∈ K N := by
    have hNi : (1 : ℤ) ≤ (N : ℤ) := by
      exact_mod_cast (show 1 ≤ N by omega)
    simp only [K, Finset.mem_Icc]
    omega
  exact AEGIS.CvSK3DetGBridgeV2.detG_ne_zero_of_two_sample_minor hLT N
    hk0 hk1 (q_two_sample_minor_ne hLT)

theorem detG70_ne_zero {LT : ℝ} (hLT : 0 < LT) : detG hLT 70 ≠ 0 := by
  exact detG_ne_zero_of_posN hLT 70 (by norm_num)

theorem moment_conds70 {LT : ℝ} (hLT : 0 < LT) (t : ℝ) :
    (∑ k ∈ K 70, bC hLT 70 t k = 0) ∧
    (∑ k ∈ K 70, (k : ℂ) * bC hLT 70 t k = 0) := by
  exact moment_conds hLT 70 (detG70_ne_zero hLT) t

end AEGIS.CvSK3FourierMinorV2

#print axioms AEGIS.CvSK3FourierMinorV2.q_two_sample_minor_ne
#print axioms AEGIS.CvSK3FourierMinorV2.detG_ne_zero_of_posN
#print axioms AEGIS.CvSK3FourierMinorV2.detG70_ne_zero
#print axioms AEGIS.CvSK3FourierMinorV2.moment_conds70
