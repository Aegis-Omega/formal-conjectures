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

import CvSRelativeBudgetL12V1

/-!
# The L = 6/5 window, reduced to its numerical certificates

`CvSRowTailV1.window_of_certificate_tail` at `LT = 6/5` with the 139 atoms `atomCenter` and
`R = 70`. The low-block premise `hlow` is discharged by the kernel-checked coercivity and the
relative row budget (`CvSRelativeBudgetL12V1.hlow_L12_relative`); `LT < log (M + 1)` and the
atom range are discharged here. What remains are the numerical certificates: the Krein
inequality `hcert`, the trace bound `hT` with the Schur gap `hcpos`, the finite rows plus row
tail `hfin`, and the relative budget `hB`, `hk`. Not RH: one window, test functions with
`2r ≤ 6/5`.
-/

open MeasureTheory Complex
open scoped ComplexConjugate
open AEGIS.CvSRowTailV1 AEGIS.CvSCrossCertV1 AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSMomentBasisV1
open AEGIS.CvSTraceV1 AEGIS.CvSWindowCertV1 AEGIS.CvSFeshbachWindowV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3
open AEGIS.CvSSchurClosureFromBoundsV1 AEGIS.CvSProjectedPackedCertificateL12V1

namespace AEGIS.CvSWindowL12V1

/-- `6/5 < log 4 ≤ log (M + 1)` for every prime cutoff `M ≥ 3`. -/
theorem lt_log_of_three_le {M : ℕ} (hM : 3 ≤ M) : (6 / 5 : ℝ) < Real.log ((M + 1 : ℕ) : ℝ) := by
  have h4 : (4 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ M + 1)
  have hl : Real.log 4 ≤ Real.log ((M + 1 : ℕ) : ℝ) := Real.log_le_log (by norm_num) h4
  have h42 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  linarith [Real.log_two_gt_d9]

/-- The atom centres `i - 69` lie in `[-69, 69]`. -/
theorem atomCenter_range (i : Fin 139) : |atomCenter i| + 1 ≤ (70 : ℤ) := by
  have h := i.isLt
  simp only [atomCenter]
  have : |(i.val : ℤ) - 69| ≤ 69 := abs_le.mpr ⟨by omega, by omega⟩
  omega

/-- **The L = 6/5 window from its numerical certificates.** Every moment-zero packet of
log-width `2r ≤ 6/5` has `Re Σ_ρ Z_ρ ≥ 0`, given the Krein inequality, the trace bound with a
positive Schur gap, the finite rows with their tail, and a row budget relative to `Q_CvS`. -/
theorem window_L12 (M : ℕ) (hM : 3 ≤ M) (L m : ℝ) (hLTL : (6 / 5 : ℝ) < L)
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (FourierTransform.fourier (H i)))
    (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) +
      (∑ i, FourierTransform.fourier (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    (cf : ℝ → Fin 139 → ℂ)
    (hR : Integrable fun t =>
      s t * trialDist 0 (6 / 5) (fun i => momentAtom (6 / 5) (atomCenter i)) cf t)
    {T : ℝ}
    (hT : ∫ t, s t * trialDist 0 (6 / 5) (fun i => momentAtom (6 / 5) (atomCenter i)) cf t ≤ T)
    (hcpos : 0 < m - T / (2 * Real.pi))
    (NP K : ℕ) (hRNP : 70 < NP)
    (lam : (Fin 139 → ℂ) → Fin 139 → ℂ) (Brow : (Fin 139 → ℂ) → ℝ)
    (hfin : ∀ c, (∑ a ∈ Finset.Icc (-(NP : ℤ)) NP,
      ‖crossRow M (6 / 5) (lowFreq fun i => sinSqSupport (atomCenter i))
          (lowCoeff (6 / 5) (fun i => sinSqSupport (atomCenter i))
            (fun i => sinSqWeight (atomCenter i)) c) a -
        ∑ i, lam c i * atomRow (6 / 5) (fun i => sinSqSupport (atomCenter i))
          (fun i => sinSqWeight (atomCenter i)) i a‖ ^ 2) +
      rowTail M (6 / 5) (lowFreq fun i => sinSqSupport (atomCenter i))
        (lowCoeff (6 / 5) (fun i => sinSqSupport (atomCenter i))
          (fun i => sinSqWeight (atomCenter i)) c) K (tauBound M) 70 NP ≤ Brow c)
    (kappa : ℝ) (hB : ∀ c, Brow c ≤ kappa * Q_CvS M (6 / 5) atomCenter c)
    (hk : kappa ≤ (2 * Real.pi) ^ 2 * (6 / 5 : ℝ) * (m - T / (2 * Real.pi)))
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ 6 / 5) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  window_of_certificate_tail M L (6 / 5) m (by norm_num) hLTL (lt_log_of_three_le hM)
    s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert atomCenter cf hR hT hcpos 70 NP K
    atomCenter_range hRNP lam Brow hfin
    (fun c => AEGIS.CvSRelativeBudgetL12V1.hlow_L12_relative M hM m T kappa Brow hcpos hB hk c)
    g hm r a hw h2r

end AEGIS.CvSWindowL12V1

#print axioms AEGIS.CvSWindowL12V1.lt_log_of_three_le
#print axioms AEGIS.CvSWindowL12V1.atomCenter_range
#print axioms AEGIS.CvSWindowL12V1.window_L12
