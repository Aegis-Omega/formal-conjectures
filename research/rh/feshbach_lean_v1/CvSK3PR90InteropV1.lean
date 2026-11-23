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

import CvSTraceDistV1
import CvSMomentTraceV1
import CvSCheckedLowBridgeV1

/-!
# Exact-source K3 × PR90 type-coherence probe

The 139 moment atoms and two exponential moments are precisely the augmented
family used by the source-bound actual-row window theorem. The PR90 low-block
bridge and K3 pointwise trace bound are imported in one Lean environment.
This theorem does not close the determinant or numeric integral premises.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.CvSK3PR90InteropV1

/-- The existing augmented 141-dimensional family satisfies K3's trace interface. -/
theorem augmented_trace_family (LT : ℝ) :
    AEGIS.CvSTraceDistV1.TraceFamily LT
      (AEGIS.CvSMomentTraceV1.augment
        (fun i : Fin 139 =>
          AEGIS.CvSMomentBasisV1.momentAtom LT ((i : ℤ) - 69))) := by
  constructor
  · intro i x
    simp only [AEGIS.CvSMomentTraceV1.augment, Fin.append_left]
  · intro s x
    fin_cases s
    · change (Real.exp (-x / 2) : ℂ) = (Real.exp ((-1 / 2 : ℝ) * x) : ℂ)
      congr 1
      ring_nf
    · change (Real.exp (x / 2) : ℂ) = (Real.exp ((1 / 2 : ℝ) * x) : ℂ)
      congr 1
      ring_nf

#check AEGIS.CvSTraceDistV1.trialDist_le
#check AEGIS.CvSCheckedLowBridgeV1.hlow_of_checked_projected_source
#print axioms AEGIS.CvSK3PR90InteropV1.augmented_trace_family

end AEGIS.CvSK3PR90InteropV1
