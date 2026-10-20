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
import CvSProjectedBasisL12V1

/-!
# Unconditional low-block coercivity at L = 6/5

The kernel replay instance `bigCheck_fact` discharges the `Fact (bigCheck = true)` premise of
`CvSProjectedBasisL12V1`. The source CvS form at L = 6/5 is then coercive on every coefficient
vector, for every `M ≥ 3`, with an explicit positive constant. In the low-block consumer only the
row budget and the scalar Schur gap remain as premises. Not RH.
-/

open AEGIS.CvSProjectedPackedCertificateL12V1 AEGIS.CvSProjectedSchurBridgeL12V1
open AEGIS.CvSSchurClosureFromBoundsV1 AEGIS.CvSProjectedBasisL12V1

namespace AEGIS.CvSLowCoercivityL12V1

theorem certifiedMu_pos : 0 < certifiedMu := by
  unfold certifiedMu
  apply div_pos _ (by positivity)
  have h : (0 : ℤ) < certEps - certEta := by decide +kernel
  exact_mod_cast h

/-- The coercivity constant is positive. -/
theorem coercivity_const_pos : 0 < certifiedMu / basisFrobenius :=
  div_pos certifiedMu_pos basisFrobenius_pos

/-- Source coercivity at L = 6/5, with no remaining premise. -/
theorem original_atom_coercivity_L12 (M : ℕ) (hM : 3 ≤ M) :
    ∀ c, (certifiedMu / basisFrobenius) * normSqCoeffs c ≤
      Q_CvS M (6 / 5) atomCenter c :=
  original_atom_coercivity_of_checked_source M hM

/-- The low-block consumer with the entry check, basis and transport discharged. -/
theorem hlow_L12 (M : ℕ) (hM : 3 ≤ M) (m T_trace beta : ℝ) (Brow : (Fin 139 → ℂ) → ℝ)
    (hgap : 0 < m - T_trace / (2 * Real.pi))
    (hBrow : ∀ c, Brow c ≤ beta * normSqCoeffs c)
    (hbeta : beta ≤ (2 * Real.pi) ^ 2 * (6 / 5 : ℝ) *
      (m - T_trace / (2 * Real.pi)) * (certifiedMu / basisFrobenius)) :
    ∀ c, Brow c / (2 * Real.pi * (6 / 5 : ℝ)) /
      (m - T_trace / (2 * Real.pi)) ≤
      2 * Real.pi * Q_CvS M (6 / 5) atomCenter c :=
  hlow_of_checked_source M hM m T_trace beta Brow hgap hBrow hbeta

end AEGIS.CvSLowCoercivityL12V1

#print axioms AEGIS.CvSLowCoercivityL12V1.coercivity_const_pos
#print axioms AEGIS.CvSLowCoercivityL12V1.original_atom_coercivity_L12
#print axioms AEGIS.CvSLowCoercivityL12V1.hlow_L12
