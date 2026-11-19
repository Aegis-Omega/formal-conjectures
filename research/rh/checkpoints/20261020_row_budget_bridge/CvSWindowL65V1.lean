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

import CvSActualMomentWindowJoinV1
import CvSTraceCertL65V1

/-!
# The window `2r ≤ 6/5` (CvS step K3f)

`window_of_actual_rows_moment` with `M = 3`, `L = 2`, `m = 3/2`, no correction terms
(`H` and `d` empty), the slack step function `sFun cells` and the explicit trace coefficients
`cfC` of `CvSTraceDistV1`. Every premise is discharged by `trace_premises_L65`; the
conclusion holds for every moment-zero test function of half-width `r` with `2r ≤ 6/5`.

This is one window. It is not Weil positivity for all test functions, and it is not RH.
-/

open MeasureTheory FourierTransform Complex Set Filter
open scoped ComplexConjugate

noncomputable section

namespace AEGIS.CvSWindowL65V1

open AEGIS.CvSActualMomentWindowJoinV1 AEGIS.CvSMomentTraceV1 AEGIS.CvSMomentBasisV1
open AEGIS.CvSProjectedPackedCertificateL12V1 AEGIS.CvSTraceCertL65V1 AEGIS.CvSTraceIntegralV1
open AEGIS.CvSTraceDistV1 AEGIS.CvSTraceCellL65V1 AEGIS.CvSTraceV1 AEGIS.CvSTraceCramerV1
open AEGIS.CvSFeshbachWindowV1 AEGIS.CvSWindowCertV1 AEGIS.CvSLowBlockDecayV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

/-- The 141-function trace family of the join is a `TraceFamily`. -/
theorem augment_family :
    TraceFamily (6 / 5) (augment (fun i : Fin 139 => momentAtom (6 / 5) (atomCenter i))) where
  atom i x := by simp only [augment, Fin.append_left, atomCenter]
  mom s x := by
    fin_cases s
    · simp only [augment, Fin.append_right, momentFunction, sig]
      norm_num
      ring_nf
    · simp only [augment, Fin.append_right, momentFunction, sig]
      norm_num
      ring_nf

theorem augment_cont :
    ∀ i, Continuous (augment (fun i : Fin 139 => momentAtom (6 / 5) (atomCenter i)) i) :=
  augment_continuous fun _ => (basisFun_contDiff _ _ _).continuous

/-- **The window `2r ≤ 6/5`.** -/
theorem window_L65 (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ 6 / 5) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  obtain ⟨hsm, hsB, hs0, hc, hR, hT, hk⟩ := trace_premises_L65 augment_family augment_cont
  refine window_of_actual_rows_moment 3 le_rfl 2 (3 / 2) (by norm_num) (sFun cells) hsm _ hsB hs0
    (n := 0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
    (fun i => i.elim0) (k := 0) (fun i => i.elim0) (fun i => i.elim0) (fun t => ?_) (cfC h65)
    hR hT hk g hm r a hw h2r
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Complex.zero_re, add_zero]
  exact hc t

end AEGIS.CvSWindowL65V1

#print axioms AEGIS.CvSWindowL65V1.augment_family
#print axioms AEGIS.CvSWindowL65V1.window_L65
