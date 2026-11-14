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

import CvSTraceGramPertV1

/-!
# A bound for the Cramer coefficients γ (CvS step K3e, part 2)

* `cramer_pert`: for `g = G − E`, `a = Y − e` (2×2), Cramer's `γ₀ = (g₁₁a₀ − g₀₁a₁)/det g`
  satisfies `‖γ₀‖ ≤ (‖G₁₁Y₀ − G₀₁Y₁‖ + δ)/(D − dd)` from norm bounds on `E`, `e`, `Y`;
* `num_normSq`: `‖cA Y₀ + cB Y₁‖² (t² + 1/4)² = P − 2Q cos tL + 2R t sin tL` for
  `Y_s = (e^{(it+σ_s)L} − 1)/(it + σ_s)`, the closed form that keeps the cancellation at small `t`.

Not RH.
-/

open Complex

noncomputable section

namespace AEGIS.CvSTraceGammaV1

/-- **The perturbed determinant stays away from zero.** -/
theorem det_pert_ge {G00 G01 G10 G11 E00 E01 E10 E11 : ℂ} {nG00 nG01 nG10 nG11 r00 r01 r10 r11 D : ℝ}
    (hG00 : ‖G00‖ ≤ nG00) (hG01 : ‖G01‖ ≤ nG01) (hG10 : ‖G10‖ ≤ nG10) (hG11 : ‖G11‖ ≤ nG11)
    (hE00 : ‖E00‖ ≤ r00) (hE01 : ‖E01‖ ≤ r01) (hE10 : ‖E10‖ ≤ r10) (hE11 : ‖E11‖ ≤ r11)
    (hD : D ≤ ‖G00 * G11 - G01 * G10‖) :
    D - (nG00 * r11 + nG11 * r00 + nG01 * r10 + nG10 * r01 + r00 * r11 + r01 * r10) ≤
      ‖(G00 - E00) * (G11 - E11) - (G01 - E01) * (G10 - E10)‖ := by
  have n0 : ∀ z : ℂ, 0 ≤ ‖z‖ := fun z => norm_nonneg z
  have e : (G00 - E00) * (G11 - E11) - (G01 - E01) * (G10 - E10) =
      (G00 * G11 - G01 * G10) -
        (G00 * E11 + E00 * G11 - G01 * E10 - E01 * G10 - E00 * E11 + E01 * E10) := by
    ring
  rw [e]
  have hb : ‖G00 * E11 + E00 * G11 - G01 * E10 - E01 * G10 - E00 * E11 + E01 * E10‖ ≤
      nG00 * r11 + nG11 * r00 + nG01 * r10 + nG10 * r01 + r00 * r11 + r01 * r10 := by
    calc _ ≤ ‖G00 * E11‖ + ‖E00 * G11‖ + ‖G01 * E10‖ + ‖E01 * G10‖ + ‖E00 * E11‖ + ‖E01 * E10‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
          exact norm_add_le _ _
      _ ≤ _ := by
          simp only [norm_mul]
          have := mul_le_mul hG00 hE11 (n0 _) ((n0 _).trans hG00)
          have := mul_le_mul hE00 hG11 (n0 _) ((n0 _).trans hE00)
          have := mul_le_mul hG01 hE10 (n0 _) ((n0 _).trans hG01)
          have := mul_le_mul hE01 hG10 (n0 _) ((n0 _).trans hE01)
          have := mul_le_mul hE00 hE11 (n0 _) ((n0 _).trans hE00)
          have := mul_le_mul hE01 hE10 (n0 _) ((n0 _).trans hE01)
          linarith
  have := norm_sub_norm_le (G00 * G11 - G01 * G10)
    (G00 * E11 + E00 * G11 - G01 * E10 - E01 * G10 - E00 * E11 + E01 * E10)
  linarith

/-- **Perturbed Cramer numerator and determinant.** -/
theorem cramer_pert {G00 G01 G10 G11 E00 E01 E10 E11 Y0 Y1 e0 e1 : ℂ}
    {nG00 nG01 nG10 nG11 r00 r01 r10 r11 y0 y1 f0 f1 D : ℝ}
    (hG00 : ‖G00‖ ≤ nG00) (hG01 : ‖G01‖ ≤ nG01) (hG10 : ‖G10‖ ≤ nG10) (hG11 : ‖G11‖ ≤ nG11)
    (hE00 : ‖E00‖ ≤ r00) (hE01 : ‖E01‖ ≤ r01) (hE10 : ‖E10‖ ≤ r10) (hE11 : ‖E11‖ ≤ r11)
    (hY0 : ‖Y0‖ ≤ y0) (hY1 : ‖Y1‖ ≤ y1) (he0 : ‖e0‖ ≤ f0) (he1 : ‖e1‖ ≤ f1)
    (hD : D ≤ ‖G00 * G11 - G01 * G10‖)
    (hpos : 0 < D - (nG00 * r11 + nG11 * r00 + nG01 * r10 + nG10 * r01 + r00 * r11 + r01 * r10)) :
    ‖((G11 - E11) * (Y0 - e0) - (G01 - E01) * (Y1 - e1)) /
        ((G00 - E00) * (G11 - E11) - (G01 - E01) * (G10 - E10))‖ ≤
      (‖G11 * Y0 - G01 * Y1‖ + (nG11 * f0 + r11 * y0 + r11 * f0 + nG01 * f1 + r01 * y1 + r01 * f1)) /
        (D - (nG00 * r11 + nG11 * r00 + nG01 * r10 + nG10 * r01 + r00 * r11 + r01 * r10)) := by
  set dd := nG00 * r11 + nG11 * r00 + nG01 * r10 + nG10 * r01 + r00 * r11 + r01 * r10
  have n0 : ∀ z : ℂ, 0 ≤ ‖z‖ := fun z => norm_nonneg z
  have hnum : ‖(G11 - E11) * (Y0 - e0) - (G01 - E01) * (Y1 - e1)‖ ≤
      ‖G11 * Y0 - G01 * Y1‖ + (nG11 * f0 + r11 * y0 + r11 * f0 + nG01 * f1 + r01 * y1 + r01 * f1) := by
    have e : (G11 - E11) * (Y0 - e0) - (G01 - E01) * (Y1 - e1) =
        (G11 * Y0 - G01 * Y1) + (-(G11 * e0) - E11 * Y0 + E11 * e0 + G01 * e1 + E01 * Y1 - E01 * e1) := by
      ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    calc ‖-(G11 * e0) - E11 * Y0 + E11 * e0 + G01 * e1 + E01 * Y1 - E01 * e1‖
        ≤ ‖G11 * e0‖ + ‖E11 * Y0‖ + ‖E11 * e0‖ + ‖G01 * e1‖ + ‖E01 * Y1‖ + ‖E01 * e1‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
          rw [norm_neg]
      _ ≤ _ := by
          simp only [norm_mul]
          gcongr <;> linarith [n0 G11, n0 E11, n0 G01, n0 E01, n0 Y0, n0 Y1, n0 e0, n0 e1]
  have hdet := det_pert_ge hG00 hG01 hG10 hG11 hE00 hE01 hE10 hE11 hD
  rw [norm_div]
  exact div_le_div₀ ((norm_nonneg _).trans hnum) hnum hpos hdet

/-- **The closed form of a Cramer numerator.** -/
theorem num_normSq (L t cA cB u1 u2 v1 v2 : ℝ)
    (hu1 : u1 = (cA * Real.exp (-L / 2) - cB * Real.exp (L / 2)) / 2)
    (hu2 : u2 = cA * Real.exp (-L / 2) + cB * Real.exp (L / 2))
    (hv1 : v1 = (cA - cB) / 2) (hv2 : v2 = cA + cB) :
    ‖(cA : ℂ) * ((cexp (((t : ℂ) * I - 1 / 2) * L) - 1) / ((t : ℂ) * I - 1 / 2)) +
        (cB : ℂ) * ((cexp (((t : ℂ) * I + 1 / 2) * L) - 1) / ((t : ℂ) * I + 1 / 2))‖ ^ 2 *
        (t ^ 2 + 1 / 4) ^ 2 =
      u1 ^ 2 + v1 ^ 2 + (u2 ^ 2 + v2 ^ 2) * t ^ 2 -
        2 * Real.cos (t * L) * (u1 * v1 + u2 * v2 * t ^ 2) +
          2 * Real.sin (t * L) * (t * (u2 * v1 - u1 * v2)) := by
  have hm : (t : ℂ) * I - 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  have hp : (t : ℂ) * I + 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  set z : ℂ := cexp ((t : ℂ) * I * L) with hz
  have em : cexp (((t : ℂ) * I - 1 / 2) * L) = z * (Real.exp (-L / 2) : ℂ) := by
    rw [hz, Complex.ofReal_exp, ← Complex.exp_add]
    push_cast
    ring_nf
  have ep : cexp (((t : ℂ) * I + 1 / 2) * L) = z * (Real.exp (L / 2) : ℂ) := by
    rw [hz, Complex.ofReal_exp, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [em, ep]
  set W := (cA : ℂ) * ((z * (Real.exp (-L / 2) : ℂ) - 1) / ((t : ℂ) * I - 1 / 2)) +
      (cB : ℂ) * ((z * (Real.exp (L / 2) : ℂ) - 1) / ((t : ℂ) * I + 1 / 2))
  have hW : W * (((t : ℂ) * I - 1 / 2) * ((t : ℂ) * I + 1 / 2)) =
      z * ((u1 : ℂ) + t * u2 * I) - ((v1 : ℂ) + t * v2 * I) := by
    have h1 : ∀ X : ℂ, X / ((t : ℂ) * I - 1 / 2) * (((t : ℂ) * I - 1 / 2) * ((t : ℂ) * I + 1 / 2)) =
        X * ((t : ℂ) * I + 1 / 2) := fun X => by rw [← mul_assoc, div_mul_cancel₀ _ hm]
    have h2 : ∀ X : ℂ, X / ((t : ℂ) * I + 1 / 2) * (((t : ℂ) * I - 1 / 2) * ((t : ℂ) * I + 1 / 2)) =
        X * ((t : ℂ) * I - 1 / 2) := fun X => by
      rw [mul_comm ((t : ℂ) * I - 1 / 2), ← mul_assoc, div_mul_cancel₀ _ hp]
    simp only [W, add_mul, mul_assoc, h1, h2, hu1, hu2, hv1, hv2]
    push_cast
    ring
  have hden : ‖((t : ℂ) * I - 1 / 2) * ((t : ℂ) * I + 1 / 2)‖ = t ^ 2 + 1 / 4 := by
    have e : ((t : ℂ) * I - 1 / 2) * ((t : ℂ) * I + 1 / 2) = ((-(t ^ 2 + 1 / 4) : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  have hzc : z = (Real.cos (t * L) : ℂ) + (Real.sin (t * L) : ℂ) * I := by
    rw [hz, show (t : ℂ) * I * L = ((t * L : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
    push_cast
    ring
  have hsq : ‖W‖ ^ 2 * (t ^ 2 + 1 / 4) ^ 2 =
      ‖z * ((u1 : ℂ) + t * u2 * I) - ((v1 : ℂ) + t * v2 * I)‖ ^ 2 := by
    rw [← hW, norm_mul, hden, mul_pow]
  rw [hsq, hzc, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hcs := Real.cos_sq_add_sin_sq (t * L)
  linear_combination (u1 ^ 2 + u2 ^ 2 * t ^ 2) * hcs

end AEGIS.CvSTraceGammaV1

#print axioms AEGIS.CvSTraceGammaV1.det_pert_ge
#print axioms AEGIS.CvSTraceGammaV1.cramer_pert
#print axioms AEGIS.CvSTraceGammaV1.num_normSq
