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
import CvSProjectedEntryReplayL12V1
import CvSProjectedSchurBridgeL12V1

open Finset
open scoped BigOperators ComplexConjugate
open AEGIS.CvSProjectedEntryL12V1
open AEGIS.CvSProjectedPackedCertificateL12V1
open AEGIS.CvSProjectedSchurBridgeL12V1
open AEGIS.CvSPackedGramV1
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHCvSKernelFiniteV1

/-- The kernel-checked packed projected source is nonnegative for every
    certified prime cutoff and every complex source coefficient vector. -/
theorem certified_source_projectedQ_nonneg
    (M : ℕ) (hM : 3 ≤ M) (v : Fin 139 → ℂ) :
    0 ≤ projectedQ M v := by
  have hpacked :=
    AEGIS.CvSProjectedEntryL12V1.projected_lower_L12_of_check
      (M := M) hM v
  have hmargin : (0 : ℝ) ≤ ((certEps - certEta : ℤ) : ℝ) := by
    exact_mod_cast cert_margin_positive.le
  have hnorm : (0 : ℝ) ≤ ∑ i : Fin 139, ‖v i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hscale : (0 : ℝ) < (2 : ℝ) ^ certQ := by positivity
  have hbound : (0 : ℝ) ≤ (2 : ℝ) ^ certQ * projectedQ M v := by
    have hp : (0 : ℝ) ≤
        ((certEps - certEta : ℤ) : ℝ) * ∑ i : Fin 139, ‖v i‖ ^ 2 :=
      mul_nonneg hmargin hnorm
    apply hp.trans
    simpa only [projectedQ] using hpacked
  by_contra hn
  have hnegative : projectedQ M v < 0 := lt_of_not_ge hn
  have hcontra : (2 : ℝ) ^ certQ * projectedQ M v < 0 :=
    mul_neg_of_pos_of_neg hscale hnegative
  exact (not_lt_of_ge hbound) hcontra


end AEGIS.RHCvSKernelFiniteV1

#print axioms AEGIS.RHCvSKernelFiniteV1.certified_source_projectedQ_nonneg
