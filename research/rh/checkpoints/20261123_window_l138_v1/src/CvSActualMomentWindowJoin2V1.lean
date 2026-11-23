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
import CvSGramTail2V1

/-!
# The moment window theorem with the sharp Gram diagonal

`CvSActualMomentWindowJoinV1.window_of_certificate_gram_moment` with `gramTail2` (`CvSGramTail2V1`) in place of
`gramTail` in the row hypothesis `hfin`: the body is the original one with `rows_gram_le2` for `rows_gram_le`
(`window_of_certificate_gram2_moment`). Since `gramUp2 ≤ gramUp` on the diagonal and they agree off it, every
row budget for `gramTail` is one for `gramTail2` (`gramTail2_le`), so the existing windows stay valid; the gain
is that the budget can now be met with far fewer explicit rows `NP`. Not RH.
-/

open MeasureTheory FourierTransform Complex Set Filter
open scoped ComplexConjugate ContDiff InnerProductSpace
open AEGIS.CvSMomentWindowBridgeV1 AEGIS.CvSMomentTraceV1
open AEGIS.CvSActualGramWindowV1 AEGIS.CvSKreinScalarUniformV1
open AEGIS.CvSActualRowConsumerV1 AEGIS.CvSProjectedPackedCertificateL12V1
open AEGIS.CvSWindowCertV1 AEGIS.CvSLowBlockDecayV1 AEGIS.CvSMomentBasisV1
open AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSCrossCertV1 AEGIS.CvSGramTailV1
open AEGIS.CvSFeshbachWindowV1 AEGIS.CvSRowTailV1
open AEGIS.CvSRoughV1 AEGIS.CvSKreinRoughV1 AEGIS.CvSPlancherelRoughV1
open AEGIS.CvSTraceV1 AEGIS.CvSCrossBoundV1 AEGIS.CvSRingBridgeV1
open AEGIS.CvSFeshbachWindowV1 AEGIS.CvSDigammaSeriesV1
open AEGIS.CvSLowBlockMatrixV1 AEGIS.CvSWindowCertV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3
open AEGIS.CvSActualMomentWindowJoinV1 AEGIS.CvSGramTail2V1

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace AEGIS.CvSActualMomentWindowJoin2V1

theorem window_of_certificate_gram2_moment (M : ℕ) (L LT m : ℝ) (hLT0 : 0 < LT) (hLTL : LT < L)
    (hLTM : LT < Real.log ((M + 1 : ℕ) : ℝ))
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (FourierTransform.fourier (H i)))
    (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) +
      (∑ i, FourierTransform.fourier (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    {p : ℕ} (ι : Fin p → ℤ)
    (cf : ℝ → Fin (p + 2) → ℂ)
    (hR : Integrable fun t => s t * trialDist 0 LT (augment (fun i => momentAtom LT (ι i))) cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist 0 LT (augment (fun i => momentAtom LT (ι i))) cf t ≤ T)
    (hcpos : 0 < m - T / (2 * Real.pi))
    (R NP : ℕ) (hRι : ∀ i, |ι i| + 1 ≤ (R : ℤ)) (hRNP : R < NP)
    {Tτ : ℝ} (hTτ : ∀ x : ℤ, NP < x.natAbs → |tau M LT x| ≤ Tτ) {ε : ℝ} (hε : 0 < ε)
    (lam : (Fin p → ℂ) → Fin p → ℂ) (Brow : (Fin p → ℂ) → ℝ)
    (hfin : ∀ c, (∑ a ∈ Finset.Icc (-(NP : ℤ)) NP,
      ‖crossRow M LT (lowFreq fun i => sinSqSupport (ι i))
          (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c) a -
        ∑ i, lam c i *
          atomRow LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) i a‖ ^ 2) +
      gramTail2 M LT (lowFreq fun i => sinSqSupport (ι i))
        (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c) Tτ ε NP ≤
        Brow c)
    (hlow : ∀ c, Brow c / (2 * Real.pi * LT) / (m - T / (2 * Real.pi)) ≤ 2 * Real.pi *
      (∑ a ∈ lowFreq (fun i => sinSqSupport (ι i)), ∑ b ∈ lowFreq (fun i => sinSqSupport (ι i)),
        lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c a *
          conj (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c b) *
            (cvsEntry M LT a b : ℂ)).re)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ LT) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  set S : Fin p → Finset ℤ := fun i => sinSqSupport (ι i)
  set β : Fin p → ℤ → ℂ := fun i => sinSqWeight (ι i)
  have hF : ∀ n ∈ lowFreq S, |(n : ℝ)| ≤ R := by
    intro n hn
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hn
    have hn' : n = ι i - 1 ∨ n = ι i ∨ n = ι i + 1 := by
      simpa [S, sinSqSupport] using hi
    have h1 := hRι i
    have h2 := neg_abs_le (ι i)
    have h3 := le_abs_self (ι i)
    have hz : |n| ≤ (R : ℤ) := by
      rw [abs_le]
      rcases hn' with h | h | h <;> subst h <;> constructor <;> linarith
    have := (Int.cast_le (R := ℝ)).mpr hz
    rwa [Int.cast_abs, Int.cast_natCast] at this
  refine window_of_certificate_rows_moment M L LT m hLT0 hLTL hLTM s hsm B hsB hs0 H hHc hHi hFH hHs
    d j hcert ι cf hR hT hcpos lam Brow (fun c N => ?_) hlow g hm r a hw h2r
  have hz : ∀ x : ℤ, NP < x.natAbs → ∑ i, lam c i * atomRow LT S β i x = 0 := by
    intro x hx
    have hxF : x ∉ lowFreq S := fun h => by
      have h1 := hF x h
      have h2 : |(x : ℝ)| = (x.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
      have h3 : (NP : ℝ) < x.natAbs := by exact_mod_cast hx
      have h4 : (R : ℝ) < NP := by exact_mod_cast hRNP
      linarith
    exact Finset.sum_eq_zero fun i _ => by rw [atomRow, lowCoeff_eq_zero LT S β _ hxF, mul_zero]
  refine (rows_split hz N).trans ?_
  refine le_trans (add_le_add le_rfl ?_) (hfin c)
  exact rows_gram_le2 M hLT0 hF hRNP _ hTτ hε N

end AEGIS.CvSActualMomentWindowJoin2V1

#print axioms AEGIS.CvSActualMomentWindowJoin2V1.window_of_certificate_gram2_moment
