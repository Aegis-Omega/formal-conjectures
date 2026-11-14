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

import CvSRelRowHBL43V1
import CvSActualMomentWindowJoinV1
import CvSTraceCertL43V1
import CvSTauFarL43V1

/-!
# The window `2r ≤ 4/3`

`window_of_certificate_gram_moment` with `M = 3`, `L = 2`, `LT = 4/3`, `m = 8/5`, no correction
terms (`H` and `d` empty), the slack step function and trace coefficients of
`CvSTraceCertL43V1` (`trace_premises_L43`, `52 ≤ (2π)² LT (m − T/(2π))`), the 139 atoms centred
at `−69, …, 69`, the rows up to `NP = 200` with `|τ_m| ≤ 13` beyond (`tau_abs_le_far`), and the
relative row budget `Brow ≤ 52 Q` of `CvSRelRowHBL43V1`. The conclusion holds for every
moment-zero test function of half-width `r` with `2r ≤ 4/3`.

This is one window. It is not Weil positivity for all test functions, and it is not RH.
-/

open MeasureTheory FourierTransform Complex Set Filter
open scoped ComplexConjugate

noncomputable section

namespace AEGIS.CvSWindowL43V1

open AEGIS.CvSActualMomentWindowJoinV1 AEGIS.CvSMomentTraceV1 AEGIS.CvSMomentBasisV1
open AEGIS.CvSTraceCertL43V1 AEGIS.CvSTraceIntegralL43V1 AEGIS.CvSTraceDistV1
open AEGIS.CvSTraceCellL43V1 AEGIS.CvSTraceV1 AEGIS.CvSTraceCramerV1
open AEGIS.CvSFeshbachWindowV1 AEGIS.CvSWindowCertV1 AEGIS.CvSLowBlockDecayV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3
open AEGIS.CvSRelRowFormL43V1 AEGIS.CvSRelRowInL43V1 AEGIS.CvSRelRowHBL43V1
open AEGIS.CvSSchurClosureFromBoundsV1 AEGIS.CvSLowBlockMatrixV1

/-- The 141-function trace family at `LT = 4/3` is a `TraceFamily`. -/
theorem augment_family :
    TraceFamily (4 / 3) (augment (fun i : Fin 139 => momentAtom (4 / 3) (ctr i))) where
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
    ∀ i, Continuous (augment (fun i : Fin 139 => momentAtom (4 / 3) (ctr i)) i) :=
  augment_continuous fun _ => (basisFun_contDiff _ _ _).continuous

theorem log_four_gt : (4 / 3 : ℝ) < Real.log ((3 + 1 : ℕ) : ℝ) := by
  have h := Real.log_two_gt_d9
  have e : Real.log ((3 + 1 : ℕ) : ℝ) = 2 * Real.log 2 := by
    rw [show (((3 + 1 : ℕ) : ℝ)) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [e]
  linarith

/-- **The window `2r ≤ 4/3`.** -/
theorem window_L43 (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ 4 / 3) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  obtain ⟨hsm, hsB, hs0, hc, hR, hT, hk⟩ := trace_premises_L43 augment_family augment_cont
  set gap := 8 / 5 - (Tq : ℝ) / (2 * Real.pi) with hgap_def
  have hP : 0 < (2 * Real.pi) ^ 2 * (4 / 3 : ℝ) := by have := Real.pi_pos; positivity
  have hgap : 0 < gap := by
    by_contra h
    have : (2 * Real.pi) ^ 2 * (4 / 3 : ℝ) * gap ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hP.le (not_lt.mp h)
    linarith
  refine window_of_certificate_gram_moment 3 2 (4 / 3) (8 / 5) (by norm_num) (by norm_num) log_four_gt
    (sFun cells) hsm _ hsB hs0 (n := 0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
    (fun i => i.elim0) (fun i => i.elim0) (k := 0) (fun i => i.elim0) (fun i => i.elim0)
    (fun t => ?_) ctr (cfC h43) hR hT hgap 71 200 (fun i => ?_) (by norm_num) (Tτ := 13)
    (fun x hx => ?_) (ε := 7 / 10) (by norm_num) (lam 3) (Brow 3) (fun c => le_rfl) (fun c => ?_)
    g hm r a hw h2r
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, Complex.zero_re, add_zero]
    exact hc t
  · have hi := i.isLt
    have h1 : |ctr i| ≤ 69 := abs_le.mpr ⟨by simp only [ctr]; omega, by simp only [ctr]; omega⟩
    push_cast
    linarith
  · refine AEGIS.CvSTauFarL43V1.tau_abs_le_far le_rfl ?_
    rw [Int.abs_eq_natAbs]
    omega
  · have hB' := hB 3 le_rfl c
    have hQ := Q_nonneg 3 le_rfl c
    show Brow 3 c / (2 * Real.pi * (4 / 3)) / gap ≤ 2 * Real.pi * Q_CvS 3 (4 / 3) ctr c
    have hden : 0 < 2 * Real.pi * (4 / 3 : ℝ) := by have := Real.pi_pos; positivity
    rw [div_div, div_le_iff₀ (mul_pos hden hgap)]
    have h1 := mul_le_mul_of_nonneg_right hk hQ
    have e : 2 * Real.pi * Q_CvS 3 (4 / 3) ctr c * (2 * Real.pi * (4 / 3) * gap) =
        (2 * Real.pi) ^ 2 * (4 / 3) * gap * Q_CvS 3 (4 / 3) ctr c := by ring
    rw [e]
    linarith

end AEGIS.CvSWindowL43V1

#print axioms AEGIS.CvSWindowL43V1.augment_family
#print axioms AEGIS.CvSWindowL43V1.window_L43
