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

import CvSRelRowHBL32V1
import CvSActualMomentWindowJoinV1
import CvSTraceCertL32V1
import CvSTauFarL32V1

/-!
# The window `2r ≤ 3/2`

`window_of_certificate_gram_moment` with `M = 4`, `L = 2`, `LT = 3/2`, `m = 33/20`, no correction
terms (`H` and `d` empty), the slack step function and trace coefficients of
`CvSTraceCertL32V1` (`trace_premises_L32`, `66 ≤ (2π)² LT (m − T/(2π))`), the 299 atoms centred
at `−149, …, 149`, the rows up to `NP = 900` with `|τ_m| ≤ 15` beyond (`tau_abs_le_far`), and the
relative row budget `Brow ≤ 60 Q` of `CvSRelRowHBL32V1`. The conclusion holds for every
moment-zero test function of half-width `r` with `2r ≤ 3/2`.

This is one window. It is not Weil positivity for all test functions, and it is not RH.
-/

open MeasureTheory FourierTransform Complex Set Filter
open scoped ComplexConjugate

noncomputable section

namespace AEGIS.CvSWindowL32V1

open AEGIS.CvSActualMomentWindowJoinV1 AEGIS.CvSMomentTraceV1 AEGIS.CvSMomentBasisV1
open AEGIS.CvSTraceCertL32V1 AEGIS.CvSTraceIntegralL32V1 AEGIS.CvSTraceDistK150V1
open AEGIS.CvSTraceCellL32V1 AEGIS.CvSTraceV1 AEGIS.CvSTraceCramerV1
open AEGIS.CvSFeshbachWindowV1 AEGIS.CvSWindowCertV1 AEGIS.CvSLowBlockDecayV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3
open AEGIS.CvSRelRowFormL32V1 AEGIS.CvSRelRowInL32V1 AEGIS.CvSRelRowHBL32V1
open AEGIS.CvSSchurClosureFromBoundsV1 AEGIS.CvSLowBlockMatrixV1

/-- The 301-function trace family at `LT = 3/2` is a `TraceFamily`. -/
theorem augment_family :
    TraceFamily (3 / 2) (augment (fun i : Fin 299 => momentAtom (3 / 2) (ctr i))) where
  atom i x := by simp only [augment, Fin.append_left, ctr]
  mom s x := by
    fin_cases s
    · simp only [augment, Fin.append_right, momentFunction, sig]
      norm_num
      ring_nf
    · simp only [augment, Fin.append_right, momentFunction, sig]
      norm_num
      ring_nf

theorem augment_cont :
    ∀ i, Continuous (augment (fun i : Fin 299 => momentAtom (3 / 2) (ctr i)) i) :=
  augment_continuous fun _ => (basisFun_contDiff _ _ _).continuous

theorem log_five_gt : (3 / 2 : ℝ) < Real.log ((4 + 1 : ℕ) : ℝ) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos (3 / 2)
  have e : Real.exp (3 / 2) ^ 2 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h1 : Real.exp 1 ^ 3 < 25 := by
    have := pow_lt_pow_left₀ h (Real.exp_pos 1).le (by norm_num : (3 : ℕ) ≠ 0)
    linarith [show (2.7182818286 : ℝ) ^ 3 < 25 by norm_num]
  push_cast
  nlinarith

/-- **The window `2r ≤ 3/2`.** -/
theorem window_L32 (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ 3 / 2) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  obtain ⟨hsm, hsB, hs0, hc, hR, hT, hk⟩ := trace_premises_L32 augment_family augment_cont
  set gap := 33 / 20 - (Tq : ℝ) / (2 * Real.pi) with hgap_def
  have hP : 0 < (2 * Real.pi) ^ 2 * (3 / 2 : ℝ) := by have := Real.pi_pos; positivity
  have hgap : 0 < gap := by
    by_contra h
    have : (2 * Real.pi) ^ 2 * (3 / 2 : ℝ) * gap ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hP.le (not_lt.mp h)
    linarith
  refine window_of_certificate_gram_moment 4 2 (3 / 2) (33 / 20) (by norm_num) (by norm_num) log_five_gt
    (sFun cells) hsm _ hsB hs0 (n := 0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
    (fun i => i.elim0) (fun i => i.elim0) (k := 0) (fun i => i.elim0) (fun i => i.elim0)
    (fun t => ?_) ctr (cfC h32) hR hT hgap 151 900 (fun i => ?_) (by norm_num) (Tτ := 15)
    (fun x hx => ?_) (ε := 1) (by norm_num) (lam 4) (Brow 4) (fun c => le_rfl) (fun c => ?_)
    g hm r a hw h2r
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, Complex.zero_re, add_zero]
    exact hc t
  · have hi := i.isLt
    have h1 : |ctr i| ≤ 149 := abs_le.mpr ⟨by simp only [ctr]; omega, by simp only [ctr]; omega⟩
    push_cast
    linarith
  · refine AEGIS.CvSTauFarL32V1.tau_abs_le_far le_rfl ?_
    rw [Int.abs_eq_natAbs]
    omega
  · have hB' := hB 4 le_rfl c
    have hQ := Q_nonneg 4 le_rfl c
    show Brow 4 c / (2 * Real.pi * (3 / 2)) / gap ≤ 2 * Real.pi * Q_CvS 4 (3 / 2) ctr c
    have hden : 0 < 2 * Real.pi * (3 / 2 : ℝ) := by have := Real.pi_pos; positivity
    rw [div_div, div_le_iff₀ (mul_pos hden hgap)]
    have h1 := mul_le_mul_of_nonneg_right hk hQ
    have e : 2 * Real.pi * Q_CvS 4 (3 / 2) ctr c * (2 * Real.pi * (3 / 2) * gap) =
        (2 * Real.pi) ^ 2 * (3 / 2) * gap * Q_CvS 4 (3 / 2) ctr c := by ring
    rw [e]
    linarith

end AEGIS.CvSWindowL32V1

#print axioms AEGIS.CvSWindowL32V1.augment_family
#print axioms AEGIS.CvSWindowL32V1.window_L32
