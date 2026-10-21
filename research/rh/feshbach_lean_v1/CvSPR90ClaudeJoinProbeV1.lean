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

import CvSCheckedLowBridgeV1
import CvSProjectedEntryReplayL12V1
import CvSProjectedBasisL12V1
import CvSRelativeBudgetL12V1
import CvSResidualRowBudgetV1

open AEGIS.CvSProjectedEntryL12V1
open AEGIS.CvSProjectedEntryReplayL12V1
open AEGIS.CvSProjectedBasisL12V1
open AEGIS.CvSMomentBasisV1
open AEGIS.CvSSchurClosureFromBoundsV1
open AEGIS.CvSProjectedPackedCertificateL12V1
open AEGIS.CvSLowBlockMatrixV1

namespace AEGIS.CvSPR90ClaudeJoinProbeV1
theorem identical_bigCheck_closed : bigCheck = true :=
  AEGIS.CvSProjectedEntryReplayL12V1.bigCheck_true

example : Fact (bigCheck = true) := ⟨identical_bigCheck_closed⟩
#synth Fact (bigCheck = true)

theorem pr90_checked_hlow_replayed
    (M : ℕ) (hM : 3 ≤ M)
    (m T_trace beta kappa : ℝ) (Brow : (Fin 139 → ℂ) → ℝ)
    (hkappa : 0 < kappa) (hgap : 0 < m - T_trace / (2 * Real.pi))
    (hRsurj : Function.Surjective AEGIS.CvSProjectedSchurBridgeL12V1.R_basis)
    (hRnorm : ∀ v, normSqCoeffs (AEGIS.CvSProjectedSchurBridgeL12V1.R_basis v) ≤ kappa * normSqCoeffs v)
    (hBrow : ∀ c, Brow c ≤ beta * normSqCoeffs c)
    (hbeta : beta ≤ (2 * Real.pi) ^ 2 * (6 / 5 : ℝ) *
       (m - T_trace / (2 * Real.pi)) * (AEGIS.CvSProjectedSchurBridgeL12V1.certifiedMu / kappa)) :
    ∀ c, Brow c / (2 * Real.pi * (6 / 5 : ℝ)) /
      (m - T_trace / (2 * Real.pi)) ≤
      2 * Real.pi * Q_CvS M (6 / 5) atomCenter c := by
  exact AEGIS.CvSCheckedLowBridgeV1.hlow_of_checked_projected_source
    M hM m T_trace beta kappa Brow hkappa hgap hRsurj hRnorm hBrow hbeta

theorem pr90_checked_hlow_with_basis
    (M : ℕ) (hM : 3 ≤ M)
    (m T_trace beta : ℝ) (Brow : (Fin 139 → ℂ) → ℝ)
    (hgap : 0 < m - T_trace / (2 * Real.pi))
    (hBrow : ∀ c, Brow c ≤ beta * normSqCoeffs c)
    (hbeta : beta ≤ (2 * Real.pi) ^ 2 * (6 / 5 : ℝ) *
       (m - T_trace / (2 * Real.pi)) * (AEGIS.CvSProjectedSchurBridgeL12V1.certifiedMu / basisFrobenius)) :
    ∀ c, Brow c / (2 * Real.pi * (6 / 5 : ℝ)) /
      (m - T_trace / (2 * Real.pi)) ≤
      2 * Real.pi * Q_CvS M (6 / 5) atomCenter c := by
  exact pr90_checked_hlow_replayed M hM m T_trace beta basisFrobenius Brow
    basisFrobenius_pos hgap R_basis_surjective R_basis_frobenius_bound hBrow hbeta

#check AEGIS.CvSRelativeBudgetL12V1.hlow_L12_relative
#check AEGIS.CvSResidualRowBudgetV1.radius_row_real
#print axioms AEGIS.CvSPR90ClaudeJoinProbeV1.identical_bigCheck_closed
#print axioms AEGIS.CvSPR90ClaudeJoinProbeV1.pr90_checked_hlow_replayed
#print axioms AEGIS.CvSPR90ClaudeJoinProbeV1.pr90_checked_hlow_with_basis
end AEGIS.CvSPR90ClaudeJoinProbeV1
