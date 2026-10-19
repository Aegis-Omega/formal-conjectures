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
import CvSMomentBasisV1

/-!
# The low-block bound is a finite Hermitian matrix inequality (CvS step 6e, ring tree)

`ScertM` is even (`scertM_neg`, from the digamma series of `h₊`), so
`Q(G) = ∫ ScertM · |𝓕G(t/2π)|²` is `2π` times the symmetrized form of `CvSQuadV1`
(`quad_eq_symm`). A low block over a basis `U_i = basisFun L (S i) (β i)` is the trigonometric
polynomial `trigPoly L F v_c` with `F = ⋃ S i` and `v_c(k) = Σ_i c_i β_i(k) (iω_k² − 1/4)`
(`lowBlock_eq_trigPoly`), so by `CvSRingBridgeV1.scertM_quad_trigPoly`

  `Q(v_c) = 2π Σ_{n,m ∈ F} v_c(n) conj(v_c(m)) cvsEntry M L n m`   (`lowBlock_quad_eq`),

with `cvsEntry M L n m = (1/2π)(∫ h₊ cosB_nm − Σ_{j<M} ppw_j π B_nm(min(log(j+1), L)))`; the
archimedean integrals have the closed forms `CvSQuadV1.hplus_cosB_diag`, `hplus_cosB_off` and
`CvSDigammaSeriesV1.hplus_source_integral`. `window_of_certificate_matrix` is
`window_of_certificate_basis` with the low-block hypothesis `hlow` stated for this finite matrix.
Not RH.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate FourierTransform ContDiff

noncomputable section

namespace AEGIS.CvSLowBlockMatrixV1

open AEGIS.CvSRoughV1 AEGIS.CvSTraceV1 AEGIS.CvSFeshbachWindowV1 AEGIS.CvSWindowCertV1
open AEGIS.CvSLowBlockDecayV1 AEGIS.CvSMomentBasisV1
open AEGIS.CvSArchSourceV1 AEGIS.CvSDigammaSeriesV1 AEGIS.CvSPrimeBlockV1 AEGIS.CvSQuadV1
open AEGIS.CvSRingBridgeV1 AEGIS.CvSMassV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

theorem hplus_neg (t : ℝ) : hplus (-t) = hplus t := by
  rw [hplus_eq_tsum, hplus_eq_tsum]
  simp only [archTerm, neg_sq]

/-- **`ScertM` is even.** -/
theorem scertM_neg (M : ℕ) (t : ℝ) : ScertM M (-t) = ScertM M t := by
  rw [scertM_eq_qsym]
  simp only [qsym, hplus_neg, neg_mul, Real.cos_neg]

/-- `Q(G)` is `2π` times the symmetrized form. -/
theorem quad_eq_symm (M : ℕ) (G : ℝ → ℂ) (hi : Integrable fun t => ScertM M t * energy G t) :
    ∫ t, ScertM M t * energy G t = 2 * Real.pi * ((1 / (4 * Real.pi)) * ∫ t, ScertM M t *
      (Complex.normSq (𝓕 G (t / (2 * Real.pi))) + Complex.normSq (𝓕 G (-t / (2 * Real.pi))))) := by
  have hneg : (fun t => ScertM M t * Complex.normSq (𝓕 G (-t / (2 * Real.pi)))) =
      fun t => (fun s => ScertM M s * energy G s) (-t) := by
    funext t
    simp only [energy, scertM_neg, neg_div]
  have hi' : Integrable fun t => ScertM M t * Complex.normSq (𝓕 G (-t / (2 * Real.pi))) := by
    rw [hneg]
    exact hi.comp_neg
  have e : ∫ t, ScertM M t * Complex.normSq (𝓕 G (-t / (2 * Real.pi))) =
      ∫ t, ScertM M t * energy G t := by
    rw [hneg]
    exact integral_neg_eq_self (fun s => ScertM M s * energy G s) volume
  have hsplit : (fun t => ScertM M t * (Complex.normSq (𝓕 G (t / (2 * Real.pi))) +
      Complex.normSq (𝓕 G (-t / (2 * Real.pi))))) = fun t => ScertM M t * energy G t +
        ScertM M t * Complex.normSq (𝓕 G (-t / (2 * Real.pi))) := by
    funext t
    simp only [energy]
    ring
  rw [hsplit, integral_add hi hi', e]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem basisFun_eq (L : ℝ) (S : Finset ℤ) (β : ℤ → ℂ) (x : ℝ) :
    basisFun L S β x = ∑ k ∈ S, β k * (iw L k * iw L k - 1 / 4) * cexp (iw L k * x) := by
  simp only [basisFun, expSum, Finset.sum_div, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The frequencies of the low block. -/
def lowFreq {p : ℕ} (S : Fin p → Finset ℤ) : Finset ℤ := Finset.univ.biUnion S

/-- The coefficients of the low block in the basis `e_k = 𝟙_[0,L] e^{iω_k x}`. -/
def lowCoeff {p : ℕ} (L : ℝ) (S : Fin p → Finset ℤ) (β : Fin p → ℤ → ℂ) (c : Fin p → ℂ)
    (k : ℤ) : ℂ :=
  ∑ i, c i * (if k ∈ S i then β i k * (iw L k * iw L k - 1 / 4) else 0)

/-- **The low block is a trigonometric polynomial.** -/
theorem lowBlock_eq_trigPoly {p : ℕ} (L : ℝ) (S : Fin p → Finset ℤ) (β : Fin p → ℤ → ℂ)
    (c : Fin p → ℂ) :
    lowBlock L (fun i => basisFun L (S i) (β i)) c = trigPoly L (lowFreq S) (lowCoeff L S β c) := by
  funext x
  simp only [lowBlock, trigPoly, trigAtom]
  by_cases hx : x ∈ Icc 0 L
  · simp only [indicator_of_mem hx]
    have hterm : ∀ k : ℤ, lowCoeff L S β c k * cexp (2 * Real.pi * I * k * x / L) =
        ∑ i, (if k ∈ S i then c i * (β i k * (iw L k * iw L k - 1 / 4) * cexp (iw L k * x))
          else 0) := by
      intro k
      rw [lowCoeff, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have he : (2 * Real.pi * I * k * x / L : ℂ) = iw L k * x := by
        simp only [iw]
        ring
      rw [he]
      split_ifs <;> ring
    simp_rw [hterm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsub : S i ⊆ lowFreq S := Finset.subset_biUnion_of_mem S (Finset.mem_univ i)
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub, basisFun_eq, Finset.mul_sum]
  · simp [indicator_of_notMem hx]

/-- The CvS matrix entry for the symbol `ScertM M` on `[0, L]`. -/
def cvsEntry (M : ℕ) (L : ℝ) (n m : ℤ) : ℝ :=
  (1 / (2 * Real.pi)) * ((∫ t, hplus t * cosB L n m t) -
    ∑ j ∈ Finset.range M, ppw j * (Real.pi * blockFn L n m (min |Real.log ((j + 1 : ℕ) : ℝ)| L)))

/-- **`Q(v_c)` is the finite CvS matrix form.** -/
theorem lowBlock_quad_eq {p : ℕ} (M : ℕ) {L : ℝ} (hL : 0 < L) (S : Fin p → Finset ℤ)
    (β : Fin p → ℤ → ℂ) (c : Fin p → ℂ) :
    ((∫ t, ScertM M t * energy (lowBlock L (fun i => basisFun L (S i) (β i)) c) t : ℝ) : ℂ) =
      2 * Real.pi * ∑ n ∈ lowFreq S, ∑ m ∈ lowFreq S,
        lowCoeff L S β c n * conj (lowCoeff L S β c m) * (cvsEntry M L n m : ℂ) := by
  have hU : ∀ i, ContDiff ℝ 1 (basisFun L (S i) (β i)) := fun i =>
    (basisFun_contDiff _ _ _).of_le (by norm_cast)
  rw [quad_eq_symm M _ (lowBlock_scertM_integrable M hL.le hU c), lowBlock_eq_trigPoly,
    Complex.ofReal_mul, scertM_quad_trigPoly hL]
  simp only [cvsEntry]
  push_cast
  ring

theorem lowBlock_quad_re {p : ℕ} (M : ℕ) {L : ℝ} (hL : 0 < L) (S : Fin p → Finset ℤ)
    (β : Fin p → ℤ → ℂ) (c : Fin p → ℂ) :
    ∫ t, ScertM M t * energy (lowBlock L (fun i => basisFun L (S i) (β i)) c) t =
      2 * Real.pi * (∑ n ∈ lowFreq S, ∑ m ∈ lowFreq S,
        lowCoeff L S β c n * conj (lowCoeff L S β c m) * (cvsEntry M L n m : ℂ)).re := by
  have h := congrArg Complex.re (lowBlock_quad_eq M hL S β c)
  rw [Complex.ofReal_re] at h
  rw [h, show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]

/-- **`window_of_certificate_basis` with the low-block bound as a finite matrix inequality.** -/
theorem window_of_certificate_matrix (M : ℕ) (L LT m : ℝ) (hLT0 : 0 < LT) (hLTL : LT < L)
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
    (cf : ℝ → Fin p → ℂ)
    (hR : Integrable fun t => s t * trialDist 0 LT (fun i => momentAtom LT (ι i)) cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist 0 LT (fun i => momentAtom LT (ι i)) cf t ≤ T)
    (hcpos : 0 < m - T / (2 * Real.pi))
    (K : (Fin p → ℂ) → ℝ) (hK : ∀ c, 0 ≤ K c)
    (hcross : ∀ c w, Admissible LT (fun i => momentAtom LT (ι i)) w →
      (∫ t, ScertM M t * cross (lowBlock LT (fun i => momentAtom LT (ι i)) c) w t) ^ 2 ≤
        K c * ∫ t, energy w t)
    (hlow : ∀ c, K c / (m - T / (2 * Real.pi)) ≤ 2 * Real.pi *
      (∑ a ∈ lowFreq (fun i => sinSqSupport (ι i)), ∑ b ∈ lowFreq (fun i => sinSqSupport (ι i)),
        lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c a *
          conj (lowCoeff LT (fun i => sinSqSupport (ι i)) (fun i => sinSqWeight (ι i)) c b) *
            (cvsEntry M LT a b : ℂ)).re)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ LT) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  window_of_certificate_basis M L LT m hLT0 hLTL hLTM s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert
    ι cf hR hT hcpos K hK hcross
    (fun c => (lowBlock_quad_re M hLT0 (fun i => sinSqSupport (ι i))
      (fun i => sinSqWeight (ι i)) c).symm ▸ hlow c) g hm r a hw h2r

end AEGIS.CvSLowBlockMatrixV1

#print axioms AEGIS.CvSLowBlockMatrixV1.scertM_neg
#print axioms AEGIS.CvSLowBlockMatrixV1.quad_eq_symm
#print axioms AEGIS.CvSLowBlockMatrixV1.lowBlock_eq_trigPoly
#print axioms AEGIS.CvSLowBlockMatrixV1.lowBlock_quad_eq
#print axioms AEGIS.CvSLowBlockMatrixV1.window_of_certificate_matrix
