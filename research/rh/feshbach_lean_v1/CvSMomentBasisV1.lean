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
import CvSLowBlockDecayV1

/-!
# An exactly moment-zero trigonometric basis (CvS step 6d, ring tree)

If `φ` and `φ'` vanish at `0` and `L`, two integrations by parts give
`∫_0^L e^{cx} φ'' = c² ∫_0^L e^{cx} φ`, so for `c = ±1/2`

  `U = φ'' − φ/4` satisfies `∫_0^L e^{∓x/2} U = 0`   (`momentZero_of_ode`).

For `φ = Σ_k β_k e^{iω_k x}`, `ω_k = 2πk/L`, the boundary conditions are the two linear conditions
`Σ β_k = 0`, `Σ k β_k = 0` (`basisFun_momentZero`), and `U = Σ_k β_k (−ω_k² − 1/4) e^{iω_k x}`.
The choice
`β = (−1/4, 1/2, −1/4)` at `k = n − 1, n, n + 1`, i.e. `φ_n = sin²(πx/L) e^{iω_n x}`, gives the
basis `momentAtom L n` of the moment-zero trigonometric polynomials with algebraic coefficients
(no `e^{±L/2}`). `window_of_certificate_basis` is `window_of_certificate_C1` for this basis, so the
moment hypothesis `hUmom` is discharged. Not RH.
-/

open MeasureTheory Complex Set Filter
open scoped ContDiff

noncomputable section

namespace AEGIS.CvSMomentBasisV1

open AEGIS.CvSRoughV1 AEGIS.CvSTraceV1 AEGIS.CvSFeshbachWindowV1 AEGIS.CvSWindowCertV1
open AEGIS.CvSLowBlockDecayV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

/-- `∫_0^L e^{cx} φ'' = c² ∫_0^L e^{cx} φ` when `φ` and `φ'` vanish at the ends. -/
theorem ibp_twice {L : ℝ} {φ φ1 φ2 : ℝ → ℂ} (hd1 : ∀ x, HasDerivAt φ (φ1 x) x)
    (hd2 : ∀ x, HasDerivAt φ1 (φ2 x) x) (hc1 : Continuous φ1) (hc2 : Continuous φ2)
    (h0 : φ 0 = 0) (hL : φ L = 0) (h0' : φ1 0 = 0) (hL' : φ1 L = 0) (c : ℂ) :
    ∫ x in (0 : ℝ)..L, cexp (c * x) * φ2 x = c ^ 2 * ∫ x in (0 : ℝ)..L, cexp (c * x) * φ x := by
  have hE : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (c * x)) (c * cexp (c * x)) x := fun x => by
    have h := ((hasDerivAt_id x).ofReal_comp.const_mul c).cexp
    simpa [mul_comm] using h
  have hEc : Continuous fun x : ℝ => c * cexp (c * x) := by fun_prop
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun x => (hd1 x).continuousAt
  have i1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := L)
    (fun x _ => hE x) (fun x _ => hd2 x) (hEc.intervalIntegrable 0 L) (hc2.intervalIntegrable 0 L)
  have i2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := L)
    (fun x _ => hE x) (fun x _ => hd1 x) (hEc.intervalIntegrable 0 L) (hc1.intervalIntegrable 0 L)
  rw [hL', h0', mul_zero, mul_zero, sub_zero, zero_sub] at i1
  rw [hL, h0, mul_zero, mul_zero, sub_zero, zero_sub] at i2
  have e1 : (∫ x in (0 : ℝ)..L, c * cexp (c * x) * φ1 x) =
      c * ∫ x in (0 : ℝ)..L, cexp (c * x) * φ1 x := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
  have e2 : (∫ x in (0 : ℝ)..L, c * cexp (c * x) * φ x) =
      c * ∫ x in (0 : ℝ)..L, cexp (c * x) * φ x := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
  rw [i1, e1, i2, e2]
  ring

theorem setIntegral_indicator_Icc {L : ℝ} (hL : 0 ≤ L) (F : ℝ → ℂ) (E : ℝ → ℂ) :
    ∫ u, E u * Set.indicator (Icc 0 L) F u = ∫ x in (0 : ℝ)..L, E x * F x := by
  have e : (fun u => E u * Set.indicator (Icc 0 L) F u) =
      Set.indicator (Icc 0 L) (fun u => E u * F u) := by
    funext u
    by_cases hu : u ∈ Icc 0 L <;> simp [hu]
  rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hL]

/-- **Moment-zero from the ODE form.** -/
theorem momentZero_of_ode {L : ℝ} (hLpos : 0 ≤ L) {φ φ1 φ2 : ℝ → ℂ}
    (hd1 : ∀ x, HasDerivAt φ (φ1 x) x) (hd2 : ∀ x, HasDerivAt φ1 (φ2 x) x)
    (hc1 : Continuous φ1) (hc2 : Continuous φ2)
    (h0 : φ 0 = 0) (hL : φ L = 0) (h0' : φ1 0 = 0) (hL' : φ1 L = 0) :
    MomentZero (Set.indicator (Icc 0 L) fun x => φ2 x - φ x / 4) := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun x => (hd1 x).continuousAt
  have key : ∀ c : ℂ, c ^ 2 = 1 / 4 →
      ∫ x in (0 : ℝ)..L, cexp (c * x) * (φ2 x - φ x / 4) = 0 := fun c hc => by
    have hsplit : (∫ x in (0 : ℝ)..L, cexp (c * x) * (φ2 x - φ x / 4)) =
        (∫ x in (0 : ℝ)..L, cexp (c * x) * φ2 x) -
          (1 / 4) * ∫ x in (0 : ℝ)..L, cexp (c * x) * φ x := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
      · congr 1; funext x; ring
      · exact ((by fun_prop : Continuous fun x : ℝ => cexp (c * x)).mul hc2).intervalIntegrable 0 L
      · exact (continuous_const.mul ((by fun_prop : Continuous fun x : ℝ => cexp (c * x)).mul
          hφc)).intervalIntegrable 0 L
    rw [hsplit, ibp_twice hd1 hd2 hc1 hc2 h0 hL h0' hL' c, hc, sub_self]
  refine ⟨?_, ?_⟩
  · rw [setIntegral_indicator_Icc hLpos]
    have e : ∀ x : ℝ, ((Real.exp (-x / 2) : ℝ) : ℂ) = cexp ((-1 / 2 : ℂ) * x) := fun x => by
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    simp_rw [e]
    exact key _ (by norm_num)
  · rw [setIntegral_indicator_Icc hLpos]
    have e : ∀ x : ℝ, ((Real.exp (x / 2) : ℝ) : ℂ) = cexp ((1 / 2 : ℂ) * x) := fun x => by
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    simp_rw [e]
    exact key _ (by norm_num)

/-- The frequency `iω_k = 2πik/L`. -/
def iw (L : ℝ) (k : ℤ) : ℂ := 2 * Real.pi * I * k / L

/-- `φ = Σ_k β_k e^{iω_k x}`. -/
def expSum (L : ℝ) (S : Finset ℤ) (β : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ S, β k * cexp (iw L k * x)

theorem hasDerivAt_expSum (L : ℝ) (S : Finset ℤ) (β : ℤ → ℂ) (x : ℝ) :
    HasDerivAt (expSum L S β) (expSum L S (fun k => β k * iw L k) x) x := by
  unfold expSum
  have h : ∀ k ∈ S, HasDerivAt (fun x : ℝ => β k * cexp (iw L k * x))
      (β k * iw L k * cexp (iw L k * x)) x := fun k _ => by
    have h1 := (((hasDerivAt_id x).ofReal_comp.const_mul (iw L k)).cexp).const_mul (β k)
    simp only [id, Complex.ofReal_one, mul_one] at h1
    exact h1.congr_deriv (by ring)
  exact HasDerivAt.fun_sum h

theorem expSum_continuous (L : ℝ) (S : Finset ℤ) (β : ℤ → ℂ) : Continuous (expSum L S β) := by
  unfold expSum
  fun_prop

theorem expSum_contDiff (L : ℝ) (S : Finset ℤ) (β : ℤ → ℂ) :
    ContDiff ℝ ∞ (expSum L S β) := by
  unfold expSum
  refine ContDiff.sum fun k _ => contDiff_const.mul ?_
  exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem exp_iw_L {L : ℝ} (hL : L ≠ 0) (k : ℤ) : cexp (iw L k * L) = 1 := by
  rw [iw, Complex.exp_eq_one_iff]
  refine ⟨k, ?_⟩
  have : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  field_simp

theorem expSum_zero (L : ℝ) (S : Finset ℤ) (β : ℤ → ℂ) : expSum L S β 0 = ∑ k ∈ S, β k := by
  simp [expSum]

theorem expSum_L {L : ℝ} (hL : L ≠ 0) (S : Finset ℤ) (β : ℤ → ℂ) :
    expSum L S β L = ∑ k ∈ S, β k := by
  simp only [expSum, exp_iw_L hL, mul_one]

/-- The basis function `U = φ'' − φ/4` for `φ = expSum L S β`. -/
def basisFun (L : ℝ) (S : Finset ℤ) (β : ℤ → ℂ) (x : ℝ) : ℂ :=
  expSum L S (fun k => β k * iw L k * iw L k) x - expSum L S β x / 4

theorem basisFun_contDiff (L : ℝ) (S : Finset ℤ) (β : ℤ → ℂ) :
    ContDiff ℝ ∞ (basisFun L S β) :=
  (expSum_contDiff L S _).sub ((expSum_contDiff L S β).div_const 4)

/-- **The two boundary conditions give an exactly moment-zero basis function.** -/
theorem basisFun_momentZero {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (β : ℤ → ℂ)
    (hβ0 : ∑ k ∈ S, β k = 0) (hβ1 : ∑ k ∈ S, β k * (k : ℂ) = 0) :
    MomentZero (Set.indicator (Icc 0 L) (basisFun L S β)) := by
  have hL0 : L ≠ 0 := hL.ne'
  have h1 : ∑ k ∈ S, β k * iw L k = 0 := by
    have : ∑ k ∈ S, β k * iw L k = (2 * Real.pi * I / L) * ∑ k ∈ S, β k * (k : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [iw]
      ring
    rw [this, hβ1, mul_zero]
  exact momentZero_of_ode hL.le (hasDerivAt_expSum L S β)
    (hasDerivAt_expSum L S (fun k => β k * iw L k)) (expSum_continuous L S _)
    (expSum_continuous L S _) (by rw [expSum_zero, hβ0]) (by rw [expSum_L hL0, hβ0])
    (by rw [expSum_zero, h1]) (by rw [expSum_L hL0, h1])

/-- The weights `(−1/4, 1/2, −1/4)` at `n − 1, n, n + 1`, i.e. `φ_n = sin²(πx/L) e^{iω_n x}`. -/
def sinSqWeight (n : ℤ) (k : ℤ) : ℂ :=
  if k = n then 1 / 2 else if k = n - 1 ∨ k = n + 1 then -1 / 4 else 0

def sinSqSupport (n : ℤ) : Finset ℤ := {n - 1, n, n + 1}

theorem sinSqWeight_sum (n : ℤ) : ∑ k ∈ sinSqSupport n, sinSqWeight n k = 0 := by
  simp only [sinSqSupport, sinSqWeight]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton]
  simp
  norm_num

theorem sinSqWeight_sum_k (n : ℤ) : ∑ k ∈ sinSqSupport n, sinSqWeight n k * (k : ℂ) = 0 := by
  simp only [sinSqSupport, sinSqWeight]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton]
  simp
  ring

/-- The moment-zero atom `U_n = φ_n'' − φ_n/4`, `φ_n = sin²(πx/L) e^{iω_n x}`. -/
def momentAtom (L : ℝ) (n : ℤ) : ℝ → ℂ := basisFun L (sinSqSupport n) (sinSqWeight n)

theorem momentAtom_momentZero {L : ℝ} (hL : 0 < L) (n : ℤ) :
    MomentZero (Set.indicator (Icc 0 L) (momentAtom L n)) :=
  basisFun_momentZero hL _ _ (sinSqWeight_sum n) (sinSqWeight_sum_k n)

/-- **`window_of_certificate_C1` for the moment-zero atoms**: the moment hypothesis is
discharged. The atoms are indexed by any `ι : Fin p → ℤ`. -/
theorem window_of_certificate_basis (M : ℕ) (L LT m : ℝ) (hLT0 : 0 < LT) (hLTL : LT < L)
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
    (hlow : ∀ c, K c / (m - T / (2 * Real.pi)) ≤
      ∫ t, ScertM M t * energy (lowBlock LT (fun i => momentAtom LT (ι i)) c) t)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ LT) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  window_of_certificate_C1 M L LT m hLT0.le hLTL hLTM s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert
    (fun i => momentAtom LT (ι i)) (fun i => (basisFun_contDiff _ _ _).of_le (by norm_cast))
    (fun i => momentAtom_momentZero hLT0 (ι i)) cf hR hT hcpos K hK hcross hlow g hm r a hw h2r

end AEGIS.CvSMomentBasisV1

#print axioms AEGIS.CvSMomentBasisV1.ibp_twice
#print axioms AEGIS.CvSMomentBasisV1.momentZero_of_ode
#print axioms AEGIS.CvSMomentBasisV1.basisFun_momentZero
#print axioms AEGIS.CvSMomentBasisV1.momentAtom_momentZero
#print axioms AEGIS.CvSMomentBasisV1.window_of_certificate_basis
