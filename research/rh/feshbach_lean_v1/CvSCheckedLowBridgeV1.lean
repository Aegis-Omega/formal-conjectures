/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
see https://www.apache.org/licenses/LICENSE-2.0
-/
import CvSProjectedEntryL12V1
import CvSProjectedTransportL12V1

/-! Exact-source low-block bridge. No existing lemma, data or workflow changes.
The remaining `Fact` is the finite Boolean computation, not a new axiom. -/
open AEGIS.CvSProjectedEntryL12V1
open AEGIS.CvSProjectedSchurBridgeL12V1
open AEGIS.CvSProjectedPackedCertificateL12V1
open AEGIS.CvSPackedGramV1
open AEGIS.CvSLowBlockMatrixV1
open AEGIS.CvSMomentBasisV1

namespace AEGIS.CvSCheckedLowBridgeV1
noncomputable section

/-- Source enclosure and exact Fourier transport are no longer caller premises. -/
theorem hlow_of_checked_projected_source
    [Fact (bigCheck = true)] (M : ℕ) (hM : 3 ≤ M)
    (m T_trace beta kappa : ℝ) (Brow : (Fin 139 → ℂ) → ℝ)
    (hkappa : 0 < kappa) (hgap : 0 < m - T_trace / (2 * Real.pi))
    (hRsurj : Function.Surjective R_basis)
    (hRnorm : ∀ v, normSqCoeffs (R_basis v) ≤ kappa * normSqCoeffs v)
    (hBrow : ∀ c, Brow c ≤ beta * normSqCoeffs c)
    (hbeta : beta ≤ (2 * Real.pi) ^ 2 * (6 / 5 : ℝ) *
       (m - T_trace / (2 * Real.pi)) * (certifiedMu / kappa)) :
    ∀ c, Brow c / (2 * Real.pi * (6 / 5 : ℝ)) /
      (m - T_trace / (2 * Real.pi)) ≤
      2 * Real.pi * Q_CvS M (6 / 5) atomCenter c := by
  exact AEGIS.CvSProjectedTransportL12V1.hlow_of_projected_packed_of_transport
    M m T_trace beta kappa Brow hkappa hgap
    (projectedEntry_mem_certI_of_check hM)
    hRsurj hRnorm hBrow hbeta

end AEGIS.CvSCheckedLowBridgeV1

#print axioms AEGIS.CvSCheckedLowBridgeV1.hlow_of_checked_projected_source
