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
import CvSWindowCertV1

/-!
# Decay of the low block and the integrability hypotheses (CvS step 6c, ring tree)

For a `C¹` function `f`, integration by parts on `[0, L_T]` gives

  `|2πξ · 𝓕(1_{[0, L_T]} f)(ξ)| ≤ |f(0)| + |f(L_T)| + ∫_0^{L_T} |f'|`   (`fourier_indicator_bound`),

so the energy `E(t) = |𝓕v(t/2π)|²` of the low block `v = 1_{[0, L_T]} Σ cᵢ Uᵢ` is bounded and
`t² E(t)` is bounded. Then `E` is integrable (`CvSArchDiagV1.integrable_of_bounds`) and so is
`ScertM M · E` (`CvSArchIntegrableV1.arch_mul_integrable` for the digamma part). This discharges
the hypotheses `hEU`, `hSU` of `CvSWindowCertV1.window_of_certificate` for `C¹` low-block bases
(`window_of_certificate_C1`). Not RH.
-/

open MeasureTheory FourierTransform Complex Set Filter
open scoped ComplexConjugate ContDiff

noncomputable section

namespace AEGIS.CvSLowBlockDecayV1

open AEGIS.CvSRoughV1 AEGIS.CvSPlancherelRoughV1 AEGIS.CvSTraceV1 AEGIS.CvSFeshbachWindowV1
open AEGIS.CvSWindowCertV1 AEGIS.CvSArchSourceV1 AEGIS.CvSArchDiagV1 AEGIS.CvSArchIntegrableV1
open AEGIS.CvSDigammaSeriesV1 AEGIS.CvSQuadV1 AEGIS.CvSRingBridgeV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

theorem fourier_indicator_eq (f : ℝ → ℂ) {LT : ℝ} (hLT : 0 ≤ LT) (ξ : ℝ) :
    𝓕 (Set.indicator (Icc 0 LT) f) ξ =
      ∫ x in (0 : ℝ)..LT, f x * cexp ((-(2 * Real.pi * ξ) * I) * x) := by
  rw [Real.fourier_real_eq_integral_exp_smul, intervalIntegral.integral_of_le hLT,
    ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
  congr 1
  funext x
  by_cases hx : x ∈ Icc 0 LT
  · simp only [Set.indicator_of_mem hx, smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  · simp only [Set.indicator_of_notMem hx, smul_zero]

/-- **Integration by parts.** -/
theorem fourier_indicator_bound {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) {LT : ℝ} (hLT : 0 ≤ LT)
    (ξ : ℝ) :
    ‖((2 * Real.pi * ξ : ℝ) : ℂ) * 𝓕 (Set.indicator (Icc 0 LT) f) ξ‖ ≤
      ‖f 0‖ + ‖f LT‖ + ∫ x in (0 : ℝ)..LT, ‖deriv f x‖ := by
  have hD : 0 ≤ ‖f 0‖ + ‖f LT‖ + ∫ x in (0 : ℝ)..LT, ‖deriv f x‖ :=
    add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (intervalIntegral.integral_nonneg hLT fun x _ => norm_nonneg _)
  by_cases hξ : ξ = 0
  · simp [hξ, hD]
  set c : ℂ := -(2 * Real.pi * ξ) * I with hcdef
  have hc : c ≠ 0 := by
    simp [hcdef, hξ, Real.pi_ne_zero, I_ne_zero]
  set E : ℝ → ℂ := fun x => cexp (c * x) with hEdef
  have hE : ∀ x, HasDerivAt E (c * E x) x := fun x => by
    have h := ((hasDerivAt_id x).ofReal_comp.const_mul c).cexp
    simpa [hEdef, mul_comm] using h
  have hEn : ∀ x : ℝ, ‖E x‖ = 1 := fun x => by
    simp [hEdef, hcdef, Complex.norm_exp]
  have hV : ∀ x ∈ uIcc (0 : ℝ) LT, HasDerivAt (fun x => E x / c) (E x) x := fun x _ => by
    have h := (hE x).div_const c
    rwa [mul_div_cancel_left₀ _ hc] at h
  have hfd : ∀ x ∈ uIcc (0 : ℝ) LT, HasDerivAt f (deriv f x) x := fun x _ =>
    ((hf.differentiable one_ne_zero) x).hasDerivAt
  have hf'c : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hEc : Continuous E := by
    simp only [hEdef]; fun_prop
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hfd hV
    (hf'c.intervalIntegrable 0 LT) (hEc.intervalIntegrable 0 LT)
  have hkey : ((2 * Real.pi * ξ : ℝ) : ℂ) = I * c := by
    rw [hcdef]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hdiv : (∫ x in (0 : ℝ)..LT, deriv f x * (E x / c)) =
      (∫ x in (0 : ℝ)..LT, deriv f x * E x) / c := by
    rw [← intervalIntegral.integral_div]
    congr 1
    funext x
    ring
  rw [fourier_indicator_eq f hLT ξ]
  change ‖((2 * Real.pi * ξ : ℝ) : ℂ) * ∫ x in (0 : ℝ)..LT, f x * E x‖ ≤ _
  rw [ibp, hdiv, hkey]
  have e : I * c * (f LT * (E LT / c) - f 0 * (E 0 / c) -
      (∫ x in (0 : ℝ)..LT, deriv f x * E x) / c) =
      I * (f LT * E LT - f 0 * E 0 - ∫ x in (0 : ℝ)..LT, deriv f x * E x) := by
    field_simp
  rw [e, norm_mul, Complex.norm_I, one_mul]
  have hint : ‖∫ x in (0 : ℝ)..LT, deriv f x * E x‖ ≤ ∫ x in (0 : ℝ)..LT, ‖deriv f x‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hLT).trans (le_of_eq ?_)
    congr 1
    funext x
    rw [norm_mul, hEn, mul_one]
  calc ‖f LT * E LT - f 0 * E 0 - ∫ x in (0 : ℝ)..LT, deriv f x * E x‖
      ≤ ‖f LT * E LT‖ + ‖f 0 * E 0‖ + ‖∫ x in (0 : ℝ)..LT, deriv f x * E x‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ‖f 0‖ + ‖f LT‖ + ∫ x in (0 : ℝ)..LT, ‖deriv f x‖ := by
        rw [norm_mul, norm_mul, hEn, hEn, mul_one, mul_one]
        linarith

theorem lowBlock_energy_bounds {p : ℕ} {LT : ℝ} (hLT : 0 ≤ LT) {U : Fin p → ℝ → ℂ}
    (hU : ∀ i, ContDiff ℝ 1 (U i)) (c : Fin p → ℂ) :
    ∃ M0 M2 : ℝ, (∀ t, |energy (lowBlock LT U c) t| ≤ M0) ∧
      ∀ t, |t ^ 2 * energy (lowBlock LT U c) t| ≤ M2 := by
  set f : ℝ → ℂ := fun x => ∑ i, c i * U i x with hfdef
  have hf : ContDiff ℝ 1 f := ContDiff.sum fun i _ => contDiff_const.mul (hU i)
  refine ⟨(∫ x, ‖lowBlock LT U c x‖) ^ 2,
    (‖f 0‖ + ‖f LT‖ + ∫ x in (0 : ℝ)..LT, ‖deriv f x‖) ^ 2, fun t => ?_, fun t => ?_⟩
  · rw [abs_of_nonneg (show 0 ≤ energy (lowBlock LT U c) t from Complex.normSq_nonneg _), energy,
      Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fourier_le_L1 _ _) 2
  · have h := fourier_indicator_bound hf hLT (t / (2 * Real.pi))
    have e : ((2 * Real.pi * (t / (2 * Real.pi)) : ℝ) : ℂ) = (t : ℂ) := by
      congr 1; field_simp
    rw [e] at h
    have h0 : 0 ≤ t ^ 2 * energy (lowBlock LT U c) t :=
      mul_nonneg (sq_nonneg t) (Complex.normSq_nonneg _)
    rw [abs_of_nonneg h0, energy, Complex.normSq_eq_norm_sq]
    have e2 : t ^ 2 * ‖𝓕 (lowBlock LT U c) (t / (2 * Real.pi))‖ ^ 2 =
        ‖(t : ℂ) * 𝓕 (lowBlock LT U c) (t / (2 * Real.pi))‖ ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [e2]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem lowBlock_energy_integrable {p : ℕ} {LT : ℝ} (hLT : 0 ≤ LT) {U : Fin p → ℝ → ℂ}
    (hU : ∀ i, ContDiff ℝ 1 (U i)) (c : Fin p → ℂ) :
    Integrable (energy (lowBlock LT U c)) := by
  obtain ⟨M0, M2, h0, h2⟩ := lowBlock_energy_bounds hLT hU c
  exact integrable_of_bounds
    (energy_continuous (lowBlock_integrable (fun i => (hU i).continuous) c)) h0 h2

theorem lowBlock_scertM_integrable (M : ℕ) {p : ℕ} {LT : ℝ} (hLT : 0 ≤ LT)
    {U : Fin p → ℝ → ℂ} (hU : ∀ i, ContDiff ℝ 1 (U i)) (c : Fin p → ℂ) :
    Integrable fun t => ScertM M t * energy (lowBlock LT U c) t := by
  obtain ⟨M0, M2, h0, h2⟩ := lowBlock_energy_bounds hLT hU c
  set E := energy (lowBlock LT U c)
  have hEc : Continuous E := energy_continuous (lowBlock_integrable (fun i => (hU i).continuous) c)
  have hEi : Integrable E := integrable_of_bounds hEc h0 h2
  have harch := arch_mul_integrable hEc h0 h2
    (Real.eulerMascheroniConstant + Real.log Real.pi)
  have hcos : ∀ j : ℕ, Integrable fun t =>
      ppw j * (Real.cos (t * Real.log ((j + 1 : ℕ) : ℝ)) * E t) := fun j => by
    refine (hEi.bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun t => ?_)).const_mul _
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  refine (harch.sub (integrable_finsetSum (Finset.range M) fun j _ => hcos j)).congr
    (Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply]
  rw [scertM_eq_qsym, qsym, hplus_eq_tsum]
  have hs : (∑ j ∈ Finset.range M, ppw j * Real.cos (t * Real.log ((j + 1 : ℕ) : ℝ))) * E t =
      ∑ j ∈ Finset.range M, ppw j * (Real.cos (t * Real.log ((j + 1 : ℕ) : ℝ)) * E t) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [← hs]
  ring

/-- **`window_of_certificate` for a `C¹` low-block basis**: the integrability hypotheses of the
low block are discharged. -/
theorem window_of_certificate_C1 (M : ℕ) (L LT m : ℝ) (hLT0 : 0 ≤ LT) (hLTL : LT < L)
    (hLTM : LT < Real.log ((M + 1 : ℕ) : ℝ))
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    {p : ℕ} (U : Fin p → ℝ → ℂ) (hU : ∀ i, ContDiff ℝ 1 (U i))
    (hUmom : ∀ i, MomentZero (Set.indicator (Icc 0 LT) (U i)))
    (cf : ℝ → Fin p → ℂ) (hR : Integrable fun t => s t * trialDist 0 LT U cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist 0 LT U cf t ≤ T) (hcpos : 0 < m - T / (2 * Real.pi))
    (K : (Fin p → ℂ) → ℝ) (hK : ∀ c, 0 ≤ K c)
    (hcross : ∀ c w, Admissible LT U w →
      (∫ t, ScertM M t * cross (lowBlock LT U c) w t) ^ 2 ≤ K c * ∫ t, energy w t)
    (hlow : ∀ c, K c / (m - T / (2 * Real.pi)) ≤ ∫ t, ScertM M t * energy (lowBlock LT U c) t)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ LT) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  window_of_certificate M L LT m hLT0 hLTL hLTM s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert U
    (fun i => (hU i).continuous) hUmom cf hR hT hcpos
    (fun c => lowBlock_energy_integrable hLT0 hU c)
    (fun c => lowBlock_scertM_integrable M hLT0 hU c) K hK hcross hlow g hm r a hw h2r

end AEGIS.CvSLowBlockDecayV1

#print axioms AEGIS.CvSLowBlockDecayV1.fourier_indicator_bound
#print axioms AEGIS.CvSLowBlockDecayV1.lowBlock_energy_bounds
#print axioms AEGIS.CvSLowBlockDecayV1.lowBlock_energy_integrable
#print axioms AEGIS.CvSLowBlockDecayV1.lowBlock_scertM_integrable
#print axioms AEGIS.CvSLowBlockDecayV1.window_of_certificate_C1
