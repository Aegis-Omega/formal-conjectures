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
import CvSLowBlockMatrixV1

/-!
# The cross term of two trigonometric polynomials is the CvS matrix (CvS step 6f, ring tree)

A trigonometric polynomial is a low block over the exponentials (`trigPoly_eq_lowBlock`), so
`ScertM · E(trigPoly)` is integrable and `Q(trigPoly L H a) = 2π Σ a_n conj(a_m) cvsEntry M L n m`
(`trigPoly_quad_eq`). With `CvSFeshbachWindowV1.quad_add` this gives, for
`v = trigPoly L H a`, `u = trigPoly L H b`,

  `∫ ScertM · Re(𝓕v conj 𝓕u)(t/2π) dt = π Re Σ_{n,m ∈ H} (a_n conj b_m + b_n conj a_m) cvsEntry`
  (`cross_trigPoly`),

the entries `X(v_c, e_k)` of the cross block of the Arb certificate. Not RH.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate FourierTransform ContDiff

noncomputable section

namespace AEGIS.CvSCrossMatrixV1

open AEGIS.CvSRoughV1 AEGIS.CvSFeshbachWindowV1 AEGIS.CvSWindowCertV1
open AEGIS.CvSLowBlockDecayV1 AEGIS.CvSMomentBasisV1 AEGIS.CvSLowBlockMatrixV1
open AEGIS.CvSPrimeBlockV1 AEGIS.CvSMassV1 AEGIS.CvSRingBridgeV1
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

/-- **A trigonometric polynomial is a low block over the exponentials.** -/
theorem trigPoly_eq_lowBlock (L : ℝ) (H : Finset ℤ) (a : ℤ → ℂ) :
    trigPoly L H a = lowBlock L (fun j x => cexp (iw L (H.equivFin.symm j : ℤ) * x))
      (fun j => a (H.equivFin.symm j : ℤ)) := by
  funext x
  simp only [lowBlock, trigPoly, trigAtom]
  by_cases hx : x ∈ Icc 0 L
  · simp only [indicator_of_mem hx]
    rw [← Finset.sum_coe_sort H]
    refine Fintype.sum_equiv H.equivFin _ _ fun n => ?_
    simp only [Equiv.symm_apply_apply]
    congr 2
    simp only [iw]
    ring
  · simp [indicator_of_notMem hx]

theorem trigPoly_scertM_integrable (M : ℕ) {L : ℝ} (hL : 0 ≤ L) (H : Finset ℤ) (a : ℤ → ℂ) :
    Integrable fun t => ScertM M t * energy (trigPoly L H a) t := by
  rw [trigPoly_eq_lowBlock]
  exact lowBlock_scertM_integrable M hL (fun j =>
    Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)) _

/-- **`Q` of a trigonometric polynomial is the CvS matrix form.** -/
theorem trigPoly_quad_eq (M : ℕ) {L : ℝ} (hL : 0 < L) (H : Finset ℤ) (a : ℤ → ℂ) :
    ((∫ t, ScertM M t * energy (trigPoly L H a) t : ℝ) : ℂ) =
      2 * Real.pi * ∑ n ∈ H, ∑ m ∈ H, a n * conj (a m) * (cvsEntry M L n m : ℂ) := by
  rw [quad_eq_symm M _ (trigPoly_scertM_integrable M hL.le H a), Complex.ofReal_mul,
    scertM_quad_trigPoly hL]
  simp only [cvsEntry]
  push_cast
  ring

theorem re_two_pi_mul (z : ℂ) : (2 * (Real.pi : ℂ) * z).re = 2 * Real.pi * z.re := by
  rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]

/-- **The cross term of two trigonometric polynomials.** -/
theorem cross_trigPoly (M : ℕ) {L : ℝ} (hL : 0 < L) (H : Finset ℤ) (a b : ℤ → ℂ) :
    ∫ t, ScertM M t * cross (trigPoly L H a) (trigPoly L H b) t =
      Real.pi * (∑ n ∈ H, ∑ m ∈ H, (a n * conj (b m) + b n * conj (a m)) *
        (cvsEntry M L n m : ℂ)).re := by
  have hadd : (fun u => trigPoly L H a u + trigPoly L H b u) = trigPoly L H (a + b) := by
    funext u
    simp only [trigPoly, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hq := quad_add (ScertM M) (scertM_measurable M).aestronglyMeasurable
    (trigPoly_integrable L H a) (trigPoly_integrable L H b)
    (trigPoly_scertM_integrable M hL.le H a) (trigPoly_scertM_integrable M hL.le H b)
  rw [hadd] at hq
  have e : ∀ c : ℤ → ℂ, ∫ t, ScertM M t * energy (trigPoly L H c) t =
      2 * Real.pi * (∑ n ∈ H, ∑ m ∈ H, c n * conj (c m) * (cvsEntry M L n m : ℂ)).re := by
    intro c
    have h := congrArg Complex.re (trigPoly_quad_eq M hL H c)
    rwa [Complex.ofReal_re, re_two_pi_mul] at h
  rw [e (a + b), e a, e b] at hq
  have hs : ∑ n ∈ H, ∑ m ∈ H, (a + b) n * conj ((a + b) m) * (cvsEntry M L n m : ℂ) =
      (∑ n ∈ H, ∑ m ∈ H, a n * conj (a m) * (cvsEntry M L n m : ℂ)) +
        (∑ n ∈ H, ∑ m ∈ H, (a n * conj (b m) + b n * conj (a m)) * (cvsEntry M L n m : ℂ)) +
          ∑ n ∈ H, ∑ m ∈ H, b n * conj (b m) * (cvsEntry M L n m : ℂ) := by
    simp only [Pi.add_apply, map_add, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
  rw [hs, Complex.add_re, Complex.add_re] at hq
  linear_combination (-1 / 2 : ℝ) * hq

end AEGIS.CvSCrossMatrixV1

#print axioms AEGIS.CvSCrossMatrixV1.trigPoly_eq_lowBlock
#print axioms AEGIS.CvSCrossMatrixV1.trigPoly_scertM_integrable
#print axioms AEGIS.CvSCrossMatrixV1.trigPoly_quad_eq
#print axioms AEGIS.CvSCrossMatrixV1.cross_trigPoly
