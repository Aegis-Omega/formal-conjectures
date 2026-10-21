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

import CvSGramTailV1
import CvSWindowL12V1
import CvSTauFarL12V1

/-!
# The L = 6/5 window with the Gram row tail

`CvSGramTailV1.window_of_certificate_gram` at `LT = 6/5` with the 139 atoms `atomCenter`,
`R = 70`, and `|τ_m| ≤ 13` for `|m| > NP ≥ 71` from `CvSTauFarL12V1.tau_abs_le_far`. Compared
with `CvSWindowL12V1.window_L12`, the row tail is the Hermitian form of the rational kernel
`gramUp NP` and needs no `τ` values beyond the finite rows `|m| ≤ NP`. The remaining premises
are the numerical certificates `hcert`, `hT`, `hcpos`, `hfin` and `hB`, `hk`. Not RH: one window,
test functions with `2r ≤ 6/5`.
-/

open MeasureTheory Complex
open scoped ComplexConjugate
open AEGIS.CvSRowTailV1 AEGIS.CvSCrossCertV1 AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSMomentBasisV1
open AEGIS.CvSTraceV1 AEGIS.CvSWindowCertV1 AEGIS.CvSFeshbachWindowV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3
open AEGIS.CvSSchurClosureFromBoundsV1 AEGIS.CvSProjectedPackedCertificateL12V1
open AEGIS.CvSGramTailV1 AEGIS.CvSWindowL12V1

namespace AEGIS.CvSWindowGramL12V1

/-- `|τ_m| ≤ 13` on the rows `|m| > NP` when `NP ≥ 71`. -/
theorem tau_far_rows {M : ℕ} (hM : 3 ≤ M) {NP : ℕ} (hNP : 70 < NP) (x : ℤ)
    (hx : NP < x.natAbs) : |tau M (6 / 5) x| ≤ 13 :=
  AEGIS.CvSTauFarL12V1.tau_abs_le_far hM (by rw [← Int.natCast_natAbs]; omega)

/-- **The L = 6/5 window with the Gram row tail.** -/
theorem window_L12_gram (M : ℕ) (hM : 3 ≤ M) (L m : ℝ) (hLTL : (6 / 5 : ℝ) < L)
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
    (NP : ℕ) (hRNP : 70 < NP) {ε : ℝ} (hε : 0 < ε)
    (lam : (Fin 139 → ℂ) → Fin 139 → ℂ) (Brow : (Fin 139 → ℂ) → ℝ)
    (hfin : ∀ c, (∑ a ∈ Finset.Icc (-(NP : ℤ)) NP,
      ‖crossRow M (6 / 5) (lowFreq fun i => sinSqSupport (atomCenter i))
          (lowCoeff (6 / 5) (fun i => sinSqSupport (atomCenter i))
            (fun i => sinSqWeight (atomCenter i)) c) a -
        ∑ i, lam c i * atomRow (6 / 5) (fun i => sinSqSupport (atomCenter i))
          (fun i => sinSqWeight (atomCenter i)) i a‖ ^ 2) +
      gramTail M (6 / 5) (lowFreq fun i => sinSqSupport (atomCenter i))
        (lowCoeff (6 / 5) (fun i => sinSqSupport (atomCenter i))
          (fun i => sinSqWeight (atomCenter i)) c) 13 ε NP ≤ Brow c)
    (kappa : ℝ) (hB : ∀ c, Brow c ≤ kappa * Q_CvS M (6 / 5) atomCenter c)
    (hk : kappa ≤ (2 * Real.pi) ^ 2 * (6 / 5 : ℝ) * (m - T / (2 * Real.pi)))
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ 6 / 5) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  window_of_certificate_gram M L (6 / 5) m (by norm_num) hLTL (lt_log_of_three_le hM)
    s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert atomCenter cf hR hT hcpos 70 NP
    atomCenter_range hRNP (tau_far_rows hM hRNP) hε lam Brow hfin
    (fun c => AEGIS.CvSRelativeBudgetL12V1.hlow_L12_relative M hM m T kappa Brow hcpos hB hk c)
    g hm r a hw h2r

end AEGIS.CvSWindowGramL12V1

#print axioms AEGIS.CvSWindowGramL12V1.tau_far_rows
#print axioms AEGIS.CvSWindowGramL12V1.window_L12_gram
