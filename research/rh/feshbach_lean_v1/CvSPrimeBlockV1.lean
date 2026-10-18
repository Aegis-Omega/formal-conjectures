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
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral

/-!
# Prime block of the trigonometric-basis Weil matrix (CvS step 5.1)

`feshbach_blocks_arb.py` uses the basis `e_m(x) = 𝟙_[0,L](x) e^{2πimx/L}` and the prime part
`wp(n, m) = Σ_q w_q B_{nm}(log q)` with `B_{nn}(y) = 2 (1 − y/L) cos(2πny/L)` and
`B_{nm}(y) = (sin(2πmy/L) − sin(2πny/L)) / (π(n − m))` (normalized by `L`). The atom autocorrelation
below is the elementary integral behind these entries.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate

noncomputable section

namespace AEGIS.CvSPrimeBlockV1

/-- The trigonometric atom `𝟙_[0,L](x) e^{2πinx/L}`. -/
def trigAtom (L : ℝ) (n : ℤ) (x : ℝ) : ℂ :=
  indicator (Icc 0 L) (fun x : ℝ => exp (2 * Real.pi * I * n * x / L)) x

theorem trigAtom_mul_conj {L y : ℝ} (hy0 : 0 ≤ y) (n m : ℤ) (x : ℝ) :
    trigAtom L n (x + y) * conj (trigAtom L m x) =
      indicator (Icc 0 (L - y))
        (fun x : ℝ => exp (2 * Real.pi * I * n * y / L) *
          exp (2 * Real.pi * I * (n - m) * x / L)) x := by
  by_cases hx : x ∈ Icc 0 (L - y)
  · have h1 : x + y ∈ Icc 0 L := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h2 : x ∈ Icc 0 L := ⟨hx.1, by linarith [hx.2]⟩
    simp only [trigAtom, indicator_of_mem h1, indicator_of_mem h2, indicator_of_mem hx]
    rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat]
    push_cast
    ring
  · rw [indicator_of_notMem hx]
    rcases not_and_or.mp hx with h | h
    · have h2 : x ∉ Icc 0 L := fun h' => h h'.1
      simp [trigAtom, indicator_of_notMem h2]
    · have h1 : x + y ∉ Icc 0 L := fun h' => h (by linarith [h'.2])
      simp [trigAtom, indicator_of_notMem h1]

/-- Autocorrelation of two atoms at a shift `0 ≤ y ≤ L`. -/
theorem trigAtom_autocorrelation {L y : ℝ} (hL : 0 < L) (hy0 : 0 ≤ y) (hyL : y ≤ L) (n m : ℤ) :
    ∫ x, trigAtom L n (x + y) * conj (trigAtom L m x) =
      if n = m then ((L - y : ℝ) : ℂ) * exp (2 * Real.pi * I * n * y / L)
      else L * (exp (2 * Real.pi * I * m * y / L) - exp (2 * Real.pi * I * n * y / L)) /
        (2 * Real.pi * I * (n - m)) := by
  simp_rw [trigAtom_mul_conj hy0 n m]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul]
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  split_ifs with hnm
  · subst hnm
    simp only [sub_self, mul_zero, zero_mul, zero_div, Complex.exp_zero,
      intervalIntegral.integral_const, sub_zero, Complex.real_smul, mul_one]
    push_cast
    ring
  · have hd : ((n : ℂ) - m) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hnm
    set c : ℂ := 2 * Real.pi * I * (n - m) / L with hc
    have hc0 : c ≠ 0 := by
      rw [hc]; exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi)
        Complex.I_ne_zero) hd) hL0
    have hint : (∫ x in (0 : ℝ)..(L - y), exp (2 * Real.pi * I * (n - m) * x / L)) =
        (exp (c * ((L - y : ℝ) : ℂ)) - exp (c * ((0 : ℝ) : ℂ))) / c := by
      rw [← integral_exp_mul_complex hc0]
      congr 1
      funext x
      rw [hc]
      ring_nf
    rw [hint]
    have hper : exp (c * ((L - y : ℝ) : ℂ)) =
        exp (-(2 * Real.pi * I * (n - m) * y / L)) := by
      have hk : c * ((L - y : ℝ) : ℂ) =
          ((n - m : ℤ) : ℂ) * (2 * Real.pi * I) + -(2 * Real.pi * I * (n - m) * y / L) := by
        rw [hc]; push_cast; field_simp; ring
      rw [hk, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
    rw [hper]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have e1 : exp (2 * Real.pi * I * n * y / L) * exp (-(2 * Real.pi * I * (n - m) * y / L)) =
        exp (2 * Real.pi * I * m * y / L) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [mul_div_assoc', mul_sub, e1, mul_one, hc]
    field_simp

/-- The atom exponential as `cos + i sin` of the real phase `2πny/L`. -/
theorem atom_exp_eq (L y : ℝ) (n : ℤ) :
    exp (2 * Real.pi * I * n * y / L) =
      (Real.cos (2 * Real.pi * n * y / L) : ℂ) + (Real.sin (2 * Real.pi * n * y / L) : ℂ) * I := by
  rw [show (2 * Real.pi * I * n * y / L : ℂ) = ((2 * Real.pi * n * y / L : ℝ) : ℂ) * I by
    push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- **Hermitian prime block.** `A(n, m) + conj A(m, n)` is the real entry `B_{nm}(y)` used by
`feshbach_blocks_arb.py` (before normalization by `L`). -/
theorem trigAtom_hermitian_block {L y : ℝ} (hL : 0 < L) (hy0 : 0 ≤ y) (hyL : y ≤ L) (n m : ℤ) :
    (∫ x, trigAtom L n (x + y) * conj (trigAtom L m x)) +
        conj (∫ x, trigAtom L m (x + y) * conj (trigAtom L n x)) =
      ((if n = m then 2 * (L - y) * Real.cos (2 * Real.pi * n * y / L)
        else L * (Real.sin (2 * Real.pi * m * y / L) - Real.sin (2 * Real.pi * n * y / L)) /
          (Real.pi * (n - m)) : ℝ) : ℂ) := by
  rw [trigAtom_autocorrelation hL hy0 hyL n m, trigAtom_autocorrelation hL hy0 hyL m n]
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases hnm : n = m
  · subst hnm
    simp only [if_true, atom_exp_eq]
    simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  · have hmn : ¬ m = n := fun h => hnm h.symm
    have hd : ((n : ℂ) - m) ≠ 0 := by rw [sub_ne_zero]; exact_mod_cast hnm
    have hd' : ((n : ℝ) - m) ≠ 0 := by rw [sub_ne_zero]; exact_mod_cast hnm
    simp only [hnm, hmn, if_false, atom_exp_eq]
    simp only [map_div₀, map_mul, map_sub, map_add, Complex.conj_ofReal, Complex.conj_I,
      map_intCast, map_ofNat]
    have hmd : ((m : ℂ) - n) = -((n : ℂ) - m) := by ring
    rw [hmd]
    push_cast
    field_simp
    ring_nf

/-- A trigonometric polynomial on `[0, L]`. -/
def trigPoly (L : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ S, v n * trigAtom L n x

theorem trigAtom_mul_conj_integrable {L y : ℝ} (hy0 : 0 ≤ y) (n m : ℤ) :
    Integrable (fun x => trigAtom L n (x + y) * conj (trigAtom L m x)) := by
  simp_rw [trigAtom_mul_conj hy0 n m]
  refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
  exact (by fun_prop : Continuous fun x : ℝ => exp (2 * Real.pi * I * n * y / L) *
    exp (2 * Real.pi * I * (n - m) * x / L)).integrableOn_Icc

theorem trigPoly_autocorrelation {L y : ℝ} (hy0 : 0 ≤ y) (S : Finset ℤ) (v : ℤ → ℂ) :
    ∫ x, trigPoly L S v (x + y) * conj (trigPoly L S v x) =
      ∑ n ∈ S, ∑ m ∈ S, v n * conj (v m) *
        ∫ x, trigAtom L n (x + y) * conj (trigAtom L m x) := by
  have hexp : ∀ x, trigPoly L S v (x + y) * conj (trigPoly L S v x) =
      ∑ n ∈ S, ∑ m ∈ S, v n * conj (v m) * (trigAtom L n (x + y) * conj (trigAtom L m x)) := by
    intro x
    simp only [trigPoly, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ =>
    (trigAtom_mul_conj_integrable hy0 n m).const_mul _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_finsetSum _ fun m _ => (trigAtom_mul_conj_integrable hy0 n m).const_mul _]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact integral_const_mul _ _

/-- The negative shift is the conjugate of the positive shift. -/
theorem trigPoly_autocorrelation_neg (L y : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) :
    ∫ x, trigPoly L S v (x - y) * conj (trigPoly L S v x) =
      conj (∫ x, trigPoly L S v (x + y) * conj (trigPoly L S v x)) := by
  rw [← integral_add_right_eq_self (fun x => trigPoly L S v (x - y) * conj (trigPoly L S v x)) y,
    ← integral_conj]
  congr 1
  funext x
  simp only [add_sub_cancel_right, map_mul, Complex.conj_conj]
  ring

/-- **Prime block of the trigonometric-basis matrix.** For `0 ≤ y ≤ L` the symmetric
autocorrelation `(G ⋆ G̃)(y) + (G ⋆ G̃)(−y)` of `G = ∑ vₙ eₙ` is the Hermitian form with the real
entries `B_{nm}(y)` of `feshbach_blocks_arb.py` (times `L`). -/
theorem trigPoly_prime_block {L y : ℝ} (hL : 0 < L) (hy0 : 0 ≤ y) (hyL : y ≤ L)
    (S : Finset ℤ) (v : ℤ → ℂ) :
    (∫ x, trigPoly L S v (x + y) * conj (trigPoly L S v x)) +
        (∫ x, trigPoly L S v (x - y) * conj (trigPoly L S v x)) =
      ∑ n ∈ S, ∑ m ∈ S, v n * conj (v m) *
        ((if n = m then 2 * (L - y) * Real.cos (2 * Real.pi * n * y / L)
          else L * (Real.sin (2 * Real.pi * m * y / L) - Real.sin (2 * Real.pi * n * y / L)) /
            (Real.pi * (n - m)) : ℝ) : ℂ) := by
  rw [trigPoly_autocorrelation_neg, trigPoly_autocorrelation hy0]
  simp only [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm (s := S) (t := S)
    (f := fun n m => conj (v n) * v m * conj (∫ x, trigAtom L n (x + y) * conj (trigAtom L m x)))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← trigAtom_hermitian_block hL hy0 hyL n m]
  ring

end AEGIS.CvSPrimeBlockV1

#print axioms AEGIS.CvSPrimeBlockV1.trigAtom_mul_conj
#print axioms AEGIS.CvSPrimeBlockV1.trigAtom_autocorrelation
#print axioms AEGIS.CvSPrimeBlockV1.atom_exp_eq
#print axioms AEGIS.CvSPrimeBlockV1.trigAtom_hermitian_block
#print axioms AEGIS.CvSPrimeBlockV1.trigAtom_mul_conj_integrable
#print axioms AEGIS.CvSPrimeBlockV1.trigPoly_autocorrelation
#print axioms AEGIS.CvSPrimeBlockV1.trigPoly_autocorrelation_neg
#print axioms AEGIS.CvSPrimeBlockV1.trigPoly_prime_block
