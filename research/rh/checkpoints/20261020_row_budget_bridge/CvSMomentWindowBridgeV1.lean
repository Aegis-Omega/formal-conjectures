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
import CvSMomentTraceV1
import CvSWindowCertV1

/-!
# Finite CvS low space with moment-augmented trace
The original finite low-block (139 atoms), exact row and cross/Schur budgets
stay unchanged. Only the independent trial-distance space gains the two
exponential moments already orthogonal to any moment-zero complement.
Both pointwise Krein and augmented trial trace integrals remain hypotheses.
No unconditional RH claim.
-/
open MeasureTheory FourierTransform Complex Set
open scoped ComplexConjugate
noncomputable section
namespace AEGIS.CvSMomentWindowBridgeV1
open AEGIS.CvSFeshbachWindowV1 AEGIS.CvSWindowCertV1 AEGIS.CvSRingBridgeV1
open AEGIS.CvSMomentTraceV1 AEGIS.CvSRoughV1 AEGIS.CvSTraceV1
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13

/-- The old admissible complement is automatically orthogonal to the augmented
trace functions; the low basis and its actual source rows are unchanged. -/
theorem admissible_augmented_orthogonal {p : ℕ} {LT : ℝ}
    {U : Fin p → ℝ → ℂ} {w : ℝ → ℂ}
    (hw : Admissible LT U w) :
    ∀ i : Fin (p + 2),
      (∫ x in Icc (0 : ℝ) LT, w x * conj (augment U i x)) = 0 := by
  rcases hw with ⟨_hwi, _hbound, hsupp, hmom, horth, _hE⟩
  exact augment_orthogonal hsupp hmom horth

/-- Feshbach sign with unchanged low and mixed Schur data, but augmented trace. -/
theorem window_nonneg_of_augmented_trace (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r a : ℝ) (hw : HalfWidthAt g r a) (M : ℕ) (hM : 2 * r < Real.log ((M + 1 : ℕ) : ℝ))
    (L m : ℝ) (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B)
    (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    (v w : ℝ → ℂ) (hdec : Gm g = fun u => v u + w u) (hv : Integrable v) (hwi : Integrable w)
    {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) {lo hi : ℝ} (hlh : lo ≤ hi)
    (hsupp : Function.support w ⊆ Icc lo hi) (hlen : hi - lo < L) (hmomw : MomentZero w)
    (hEw : Integrable (energy w))
    (hSv : Integrable fun t => ScertM M t * energy v t)
    (hSw : Integrable fun t => ScertM M t * energy w t)
    {p : ℕ} (U : Fin p → ℝ → ℂ) (hU : ∀ i, Continuous (U i))
    (horth : ∀ i, ∫ x in Icc lo hi, w x * conj (U i x) = 0)
    (cf : ℝ → Fin (p + 2) → ℂ) (hR : Integrable fun t => s t * trialDist lo hi (augment U) cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist lo hi (augment U) cf t ≤ T) (hcpos : 0 < m - T / (2 * Real.pi))
    {K : ℝ} (hK : 0 ≤ K)
    (hcross : (∫ t, ScertM M t * cross v w t) ^ 2 ≤ K * ∫ t, energy w t)
    (hlow : K / (m - T / (2 * Real.pi)) ≤ ∫ t, ScertM M t * energy v t) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  window_nonneg g hm r a hw M hM v w hdec hv hwi hSv hSw hcpos hK
    (complement_bound_with_moments M L m s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert hwi hC hlh hsupp hlen
      hmomw hEw hSw U hU horth cf hR hT)
    hcross hlow

/-- The original 139-dimensional low family enlarged to 141 for trace only. -/
def actualTraceBasis (U : Fin 139 → ℝ → ℂ) : Fin 141 → ℝ → ℂ :=
  augment U

theorem actualTraceBasis_continuous {U : Fin 139 → ℝ → ℂ}
    (hU : ∀ i, Continuous (U i)) :
    ∀ i, Continuous (actualTraceBasis U i) :=
  augment_continuous hU

end AEGIS.CvSMomentWindowBridgeV1

#print axioms AEGIS.CvSMomentWindowBridgeV1.admissible_augmented_orthogonal
#print axioms AEGIS.CvSMomentWindowBridgeV1.window_nonneg_of_augmented_trace
#print axioms AEGIS.CvSMomentWindowBridgeV1.actualTraceBasis_continuous
