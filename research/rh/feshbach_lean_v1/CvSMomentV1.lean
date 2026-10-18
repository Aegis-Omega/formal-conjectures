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
import CvSPrimeBlockV1

/-!
# Moments of the trigonometric atoms (CvS step 5.3)

In log coordinates `G(t) = e^{t/2} g(e^t)`, the repository's moment conditions
`WeilMomentConditionsV1` read `∫ G(t) e^{±t/2} dt = 0`. For the atoms
`e_n = 𝟙_[0,L] e^{2πint/L}` of `feshbach_blocks_arb.py` this file proves

`∫ e_n(t) e^{st} dt = (e^{sL} − 1)/(s + 2πin/L)`,

which is `mom(n, s)` there; so for `G = ∑ v_n e_n` the moment conditions are the two linear
constraints `∑ v_n mom(n, ±1/2) = 0` that define the moment-zero basis `Z`.
-/

open MeasureTheory Complex Set

noncomputable section

namespace AEGIS.CvSMomentV1

open AEGIS.CvSPrimeBlockV1

/-- **Moment of an atom.** -/
theorem trigAtom_moment {L : ℝ} (hL : 0 < L) (n : ℤ) {s : ℂ}
    (hs : s + 2 * Real.pi * I * n / L ≠ 0) :
    ∫ x, trigAtom L n x * exp (s * x) = (exp (s * L) - 1) / (s + 2 * Real.pi * I * n / L) := by
  have hfun : (fun x : ℝ => trigAtom L n x * exp (s * x)) =
      indicator (Icc 0 L) (fun x : ℝ => exp ((s + 2 * Real.pi * I * n / L) * x)) := by
    funext x
    by_cases hx : x ∈ Icc 0 L
    · simp only [trigAtom, indicator_of_mem hx, ← Complex.exp_add]
      congr 1; ring
    · simp [trigAtom, indicator_of_notMem hx]
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hL.le, integral_exp_mul_complex hs]
  have h2 : (s + 2 * Real.pi * I * n / L) * (L : ℂ) = s * L + n * (2 * Real.pi * I) := by
    field_simp
  rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- **Moments of a trigonometric polynomial.** -/
theorem trigPoly_moment {L : ℝ} (hL : 0 < L) (N : Finset ℤ) (v : ℤ → ℂ) {s : ℂ}
    (hs : ∀ n ∈ N, s + 2 * Real.pi * I * n / L ≠ 0) :
    ∫ x, (∑ n ∈ N, v n * trigAtom L n x) * exp (s * x) =
      ∑ n ∈ N, v n * ((exp (s * L) - 1) / (s + 2 * Real.pi * I * n / L)) := by
  have hint : ∀ n ∈ N, Integrable (fun x : ℝ => v n * trigAtom L n x * exp (s * x)) := by
    intro n _
    simp_rw [mul_assoc]
    refine Integrable.const_mul ?_ _
    have hfun : (fun x : ℝ => trigAtom L n x * exp (s * x)) =
        indicator (Icc 0 L) (fun x : ℝ => exp ((s + 2 * Real.pi * I * n / L) * x)) := by
      funext x
      by_cases hx : x ∈ Icc 0 L
      · simp only [trigAtom, indicator_of_mem hx, ← Complex.exp_add]
        congr 1; ring
      · simp [trigAtom, indicator_of_notMem hx]
    rw [hfun, integrable_indicator_iff measurableSet_Icc]
    exact (Continuous.integrableOn_Icc (by fun_prop))
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum N hint]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [show (fun x : ℝ => v n * trigAtom L n x * exp (s * x)) =
      fun x => v n * (trigAtom L n x * exp (s * x)) by funext x; ring,
    integral_const_mul, trigAtom_moment hL n (hs n hn)]

/-- At `s = ±1/2` the denominators never vanish. -/
theorem half_add_ne_zero (L : ℝ) (n : ℤ) {s : ℝ} (hs : s ≠ 0) :
    (s : ℂ) + 2 * Real.pi * I * n / L ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [Complex.div_re] at this
  exact hs (by simpa using this)

end AEGIS.CvSMomentV1

#print axioms AEGIS.CvSMomentV1.trigAtom_moment
#print axioms AEGIS.CvSMomentV1.trigPoly_moment
#print axioms AEGIS.CvSMomentV1.half_add_ne_zero
